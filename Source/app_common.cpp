#include "app_common.h"

#include "external_factoring.h"
#include "prime_iterator.h"

#include <cctype>
#include <ctime>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>

#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#endif

namespace fs = std::filesystem;

namespace amicable {

bool parse_u64(const std::string& text, std::uint64_t& out) {
    std::istringstream input(text);
    return static_cast<bool>(input >> out) && input.eof();
}

bool normalize_mode(const std::string& text, std::string& mode) {
    std::string t;
    for (char ch : text) t += static_cast<char>(std::tolower(static_cast<unsigned char>(ch)));
    if (t == "range" || t == "multi" || t == "multi_k") { mode = "range"; return true; }
    if (t == "single" || t == "single_k") { mode = "single"; return true; }
    if (t == "skipped" || t == "skip" || t == "incomplete") { mode = "skipped"; return true; }
    return false;
}

namespace {

fs::path executable_path(const char* argv0) {
#ifdef _WIN32
    std::wstring buf(32768, L'\0');
    const DWORD n = GetModuleFileNameW(nullptr, buf.data(), static_cast<DWORD>(buf.size()));
    if (n > 0 && n < buf.size()) return fs::path(buf.substr(0, n));
#else
    std::error_code ec;
    const fs::path p = fs::read_symlink("/proc/self/exe", ec);
    if (!ec) return p;
#endif
    return fs::absolute(fs::path(argv0 ? argv0 : "."));
}

std::string trim(const std::string& t) {
    const auto b = t.find_first_not_of(" \t\r\n");
    const auto e = t.find_last_not_of(" \t\r\n");
    return (b == std::string::npos) ? std::string() : t.substr(b, e - b + 1);
}

} // namespace

fs::path find_root(const char* argv0) {
    const fs::path exe_dir = executable_path(argv0).parent_path();
    if (exe_dir.filename() == "Build") return exe_dir.parent_path();
    if (fs::exists(exe_dir / "config.txt")) return exe_dir;
    if (fs::exists(exe_dir.parent_path() / "config.txt")) return exe_dir.parent_path();
    return fs::current_path();
}

bool load_config_file(const fs::path& file, AppConfig& cfg) {
    std::ifstream in(file);
    if (!in) return true;   // optional
    std::string line;
    int line_no = 0;
    while (std::getline(in, line)) {
        ++line_no;
        if (const auto hash_pos = line.find('#'); hash_pos != std::string::npos) line.erase(hash_pos);
        const auto eq = line.find('=');
        if (eq == std::string::npos) continue;
        const std::string key = trim(line.substr(0, eq));
        const std::string val = trim(line.substr(eq + 1));
        std::uint64_t n = 0;
        auto bad = [&]() {
            std::cerr << "[error] " << file.string() << ':' << line_no << ": bad value for " << key << '\n';
            return false;
        };
        if (key == "hash") {
            if (!cfg.hash_given) cfg.hash_text = val;
        } else if (key == "start_k") {
            if (!parse_u64(val, n) || n < 1) return bad();
            if (!cfg.start_given) cfg.start_k = n;
        } else if (key == "end_k") {
            if (!parse_u64(val, n)) return bad();
            if (!cfg.end_given) cfg.end_k = n;
        } else if (key == "timeout_seconds") {
            if (!parse_u64(val, n)) return bad();
            if (!cfg.timeout_given) cfg.timeout_seconds = n;
        } else if (key == "report_seconds") {
            if (!parse_u64(val, n)) return bad();
            if (!cfg.report_given) cfg.report_seconds = n;
        } else if (key == "workers") {
            if (!parse_u64(val, n) || n > 4096) return bad();
            if (!cfg.workers_given) cfg.workers = static_cast<int>(n);
        } else if (key == "author") {
            if (val.empty() || val.find_first_of(" \t") != std::string::npos) return bad();
            cfg.author = val;
        } else if (key == "engine") {
            // older config.txt files: the general engine is the only one now
            if (val != "auto" && val != "general") {
                std::cerr << file.string() << ':' << line_no << ": engine = " << val
                          << " was removed; only the general engine is left (delete the line)\n";
                return false;
            }
        } else if (key == "mode") {
            std::string m;
            if (!normalize_mode(val, m)) return bad();
            if (!cfg.mode_given) cfg.mode = m;
        } else if (key == "single_k") {
            if (val.empty()) { cfg.single_k = 0; continue; }
            if (!parse_u64(val, n) || n < 1) return bad();
            cfg.single_k = n;
        } else if (key == "single_timeout_seconds") {
            if (!parse_u64(val, n)) return bad();
            cfg.single_timeout_seconds = n;
        } else if (key == "year") {
            if (!val.empty() && !parse_u64(val, n)) return bad();
            cfg.year = val;
        } else {
            std::cerr << "[warn] " << file.string() << ':' << line_no << ": unknown setting " << key << '\n';
        }
    }
    return true;
}

bool parse_common_args(int argc, char* argv[], AppConfig& cfg,
                       std::vector<std::string>& positional, bool& help)
{
    help = false;
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        auto need = [&](std::string& dst) {
            if (i + 1 >= argc) return false;
            dst = argv[++i];
            return true;
        };
        std::string v;
        std::uint64_t n = 0;
        if (a == "--help" || a == "-h") { help = true; return true; }
        else if (a == "--hash") { if (!need(cfg.hash_text)) return false; cfg.hash_given = true; }
        else if (a.rfind("--hash=", 0) == 0) { cfg.hash_text = a.substr(7); cfg.hash_given = true; }
        else if (a == "--mode") {
            if (!need(v)) return false;
            if (!normalize_mode(v, cfg.mode)) { std::cerr << "Unknown mode " << v << " (range, single or skipped)\n"; return false; }
            cfg.mode_given = true;
        }
        else if (a == "--workers") {
            if (!need(v) || !parse_u64(v, n) || n > 4096) return false;
            cfg.workers = static_cast<int>(n);
            cfg.workers_given = true;
        } else if (a == "--timeout") {
            if (!need(v) || !parse_u64(v, cfg.timeout_seconds)) return false;
            cfg.timeout_given = true;
        } else if (a == "--report") {
            if (!need(v) || !parse_u64(v, cfg.report_seconds)) return false;
            cfg.report_given = true;
        } else if (a == "--plan") {
            cfg.show_plan = true;
        } else if (a == "--root") {
            if (!need(v)) return false;
            cfg.root = v;
        } else if (!a.empty() && a[0] == '-') {
            std::cerr << "Unknown option " << a << '\n';
            return false;
        } else {
            positional.push_back(a);
        }
    }
    return true;
}

bool open_session(const AppConfig& cfg, Session& session, std::string& error) {
    if (!parse_hash_spec(cfg.hash_text, session.hash, error)) return false;
    session.data_dir = cfg.root / "Data" / session.hash.folder();
    fs::create_directories(session.data_dir);

    session.year = cfg.year;
    if (session.year.empty()) {
        const std::time_t now = std::time(nullptr);
        std::tm tm_now{};
#ifdef _WIN32
        localtime_s(&tm_now, &now);
#else
        localtime_r(&now, &tm_now);
#endif
        session.year = std::to_string(tm_now.tm_year + 1900);
    }
    configure_external_factoring();
    try {
        check_prime_iterator();           // assumption A2 of the proof, on this machine
    } catch (const std::exception& ex) {
        error = ex.what();
        return false;
    }
    return true;
}

} // namespace amicable

