#include "skip_file.h"

#include <chrono>
#include <fstream>
#include <mutex>
#include <sstream>
#include <stdexcept>
#include <thread>

#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <cerrno>
#include <cstring>
#include <fcntl.h>
#include <sys/file.h>
#include <unistd.h>
#endif

namespace fs = std::filesystem;

namespace amicable {

namespace {

// threads of one process take this first; the lock file then orders processes
std::recursive_mutex& process_mutex() {
    static std::recursive_mutex mu;
    return mu;
}

fs::path lock_path(const fs::path& file) { return fs::path(file.string() + ".lock"); }

std::string trim(const std::string& t) {
    const auto b = t.find_first_not_of(" \t\r\n");
    const auto e = t.find_last_not_of(" \t\r\n");
    return (b == std::string::npos) ? std::string() : t.substr(b, e - b + 1);
}

SkipLine parse_line(const std::string& raw) {
    SkipLine line;
    line.raw = raw;
    std::istringstream in(raw);
    std::string tok;
    if (!(in >> tok)) return line;
    std::uint64_t k = 0;
    try {
        std::size_t used = 0;
        k = std::stoull(tok, &used);
        if (used != tok.size()) return line;
    } catch (...) {
        return line;
    }
    line.k = k;
    while (in >> tok) {
        if (tok.rfind("resume=", 0) == 0) {
            line.resume = tok.substr(7);
        } else {
            if (!line.reason.empty()) line.reason += ' ';
            line.reason += tok;
        }
    }
    return line;
}

// Replaces dst by src in one step.
void replace_file(const fs::path& src, const fs::path& dst) {
#ifdef _WIN32
    for (int attempt = 0;; ++attempt) {
        if (MoveFileExW(src.wstring().c_str(), dst.wstring().c_str(),
                        MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH))
            return;
        // another program may have the file open for a moment (an editor, a virus scanner)
        if (attempt >= 100)
            throw std::runtime_error("cannot replace " + dst.string() + " (Windows error " +
                                     std::to_string(GetLastError()) + "); the new contents are in " +
                                     src.string());
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
#else
    std::error_code ec;
    fs::rename(src, dst, ec);
    if (ec) throw std::runtime_error("cannot replace " + dst.string() + ": " + ec.message());
#endif
}

void write_lines(const fs::path& file, const std::vector<SkipLine>& lines) {
    const fs::path tmp(file.string() + ".tmp");
    {
        std::ofstream out(tmp, std::ios::out | std::ios::trunc);
        if (!out) throw std::runtime_error("cannot write " + tmp.string());
        for (const SkipLine& l : lines) out << format_skip_line(l) << '\n';
        out.flush();
        if (!out) throw std::runtime_error("cannot write " + tmp.string());
    }
    replace_file(tmp, file);
}

} // namespace

FileLock::FileLock(const fs::path& file) {
    process_mutex().lock();
    const fs::path lp = lock_path(file);
#ifdef _WIN32
    for (;;) {
        // no sharing: a second opener (any process) waits here until we close it
        HANDLE h = CreateFileW(lp.wstring().c_str(), GENERIC_READ | GENERIC_WRITE, 0, nullptr,
                               OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, nullptr);
        if (h != INVALID_HANDLE_VALUE) { handle_ = h; return; }
        const DWORD err = GetLastError();
        if (err != ERROR_SHARING_VIOLATION && err != ERROR_ACCESS_DENIED && err != ERROR_LOCK_VIOLATION) {
            process_mutex().unlock();
            throw std::runtime_error("cannot open lock file " + lp.string() + " (Windows error " +
                                     std::to_string(err) + ")");
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(5));
    }
#else
    fd_ = ::open(lp.c_str(), O_RDWR | O_CREAT, 0644);
    if (fd_ < 0) {
        process_mutex().unlock();
        throw std::runtime_error("cannot open lock file " + lp.string() + ": " + std::strerror(errno));
    }
    while (::flock(fd_, LOCK_EX) != 0) {
        if (errno == EINTR) continue;
        ::close(fd_);
        process_mutex().unlock();
        throw std::runtime_error("cannot lock " + lp.string() + ": " + std::strerror(errno));
    }
#endif
}

FileLock::~FileLock() {
#ifdef _WIN32
    if (handle_) CloseHandle(static_cast<HANDLE>(handle_));
#else
    if (fd_ >= 0) ::close(fd_);              // releases the flock
#endif
    process_mutex().unlock();
}

std::vector<SkipLine> read_skip_file(const fs::path& file) {
    std::vector<SkipLine> lines;
    std::ifstream in;
    for (int attempt = 0;; ++attempt) {
        in.open(file);
        if (in) break;
        std::error_code ec;
        if (!fs::exists(file, ec) && !ec) return lines;      // no file: no lines
        // The file is there but cannot be opened: another program may hold it for a
        // moment (an editor, a scanner, a sync client).  Reading it as empty would let
        // the next rewrite (edit_skip_file) replace it with nothing, so wait, then fail.
        if (attempt >= 100) throw std::runtime_error("cannot read " + file.string());
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
    std::string raw;
    while (std::getline(in, raw)) {
        raw = trim(raw);
        if (raw.empty()) continue;
        lines.push_back(parse_line(raw));
    }
    if (in.bad()) throw std::runtime_error("error reading " + file.string());
    return lines;
}

std::string format_skip_line(const SkipLine& line) {
    if (line.k == 0) return line.raw;
    std::string s = std::to_string(line.k);
    if (!line.reason.empty()) s += ' ' + line.reason;
    if (!line.resume.empty()) s += " resume=" + line.resume;
    return s;
}

void append_skip_line(const fs::path& file, std::uint64_t k, const std::string& reason) {
    FileLock lock(file);
    for (int attempt = 0;; ++attempt) {
        std::ofstream out(file, std::ios::out | std::ios::app);
        if (out) {
            out << k << ' ' << reason << '\n';
            out.flush();
            if (out) return;
        }
        // another program may hold the file for a moment (an editor, a scanner, a sync client)
        if (attempt >= 100) throw std::runtime_error("cannot append to " + file.string());
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
}

void edit_skip_file(const fs::path& file, const std::function<void(std::vector<SkipLine>&)>& edit) {
    FileLock lock(file);
    std::vector<SkipLine> lines = read_skip_file(file);
    edit(lines);
    write_lines(file, lines);
}

std::size_t remove_skip_k(const fs::path& file, std::uint64_t k) {
    std::size_t removed = 0;
    edit_skip_file(file, [&](std::vector<SkipLine>& lines) {
        std::vector<SkipLine> keep;
        for (SkipLine& l : lines) {
            if (l.k == k) ++removed;
            else keep.push_back(std::move(l));
        }
        lines.swap(keep);
    });
    return removed;
}

void set_skip_k(const fs::path& file, std::uint64_t k, const std::string& reason, const std::string& resume) {
    edit_skip_file(file, [&](std::vector<SkipLine>& lines) {
        std::vector<SkipLine> out;
        bool placed = false;
        for (SkipLine& l : lines) {
            if (l.k != k) { out.push_back(std::move(l)); continue; }
            if (placed) continue;
            SkipLine nl;
            nl.k = k;
            nl.reason = reason;
            nl.resume = resume;
            out.push_back(std::move(nl));
            placed = true;
        }
        if (!placed) {
            SkipLine nl;
            nl.k = k;
            nl.reason = reason;
            nl.resume = resume;
            out.push_back(std::move(nl));
        }
        lines.swap(out);
    });
}

std::vector<std::pair<std::string, std::string>> read_status_file(const fs::path& file) {
    std::vector<std::pair<std::string, std::string>> kv;
    std::ifstream in(file);
    std::string raw;
    bool first = true;
    while (std::getline(in, raw)) {
        raw = trim(raw);
        if (raw.empty()) continue;
        if (first) {
            first = false;
            if (raw.find('=') == std::string::npos) { kv.emplace_back("state", raw); continue; }
        }
        const auto eq = raw.find('=');
        if (eq == std::string::npos) continue;
        kv.emplace_back(trim(raw.substr(0, eq)), trim(raw.substr(eq + 1)));
    }
    return kv;
}

std::string status_value(const std::vector<std::pair<std::string, std::string>>& kv, const std::string& key) {
    for (const auto& [k, v] : kv)
        if (k == key) return v;
    return {};
}

} // namespace amicable
