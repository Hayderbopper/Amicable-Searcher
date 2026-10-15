// collect_results: every pair in the results files under Data/ (all hashes,
// range and single/skipped runs alike) in one file, smallest pair first, each
// pair once, ready to submit.
//
//   collect_results [--root DIR] [--out FILE] [--known FILE] [--no-check] [FILE or FOLDER ...]
//
// Folders are searched, with their subfolders, for files named *results.txt
// (multi_k_results.txt, single_k_results.txt).  Without FILE/FOLDER arguments
// it reads DIR/Data.  The output (default DIR/all_pairs.txt) has the same
// format as the results files:
//
//   23 Amicable-Searcher 2026
//   1511930=2*5*7*21599
//   1598470=2*5*19*47*179
//   (blank line)
//
// Every pair is checked before it is written: each factorization multiplies
// to its number, every factor is prime (GMP's test), and
// sigma(m) = sigma(n) = m + n with m < n.  A pair that fails is left out and
// listed with the reason.  A pair found in several files (a k searched by a
// range run and again by mode skipped) is written once, with the earliest year.
// --known FILE (any number of times) leaves out the pairs listed in FILE, e.g.
// a list downloaded from sech.me, so that only new pairs remain.
// The results files are only read, never changed.

#include "app_common.h"
#include "factoring.h"
#include "numeric_utils.h"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#endif

namespace fs = std::filesystem;
using amicable::BigInt;

namespace {

struct Pair {
    BigInt small, large;
    std::string small_text, large_text;         // "m=factors", "n=factors" as read
    std::string header;                         // "23 Amicable-Searcher 2026" (may be empty)
    std::string source;                         // file:line, for messages
};

std::string trim(const std::string& t) {
    const auto b = t.find_first_not_of(" \t\r\n");
    const auto e = t.find_last_not_of(" \t\r\n");
    return (b == std::string::npos) ? std::string() : t.substr(b, e - b + 1);
}

bool all_digits(const std::string& s) {
    return !s.empty() && s.find_first_not_of("0123456789") == std::string::npos;
}

// "m=..." with m a decimal number
bool number_line(const std::string& line) {
    const auto eq = line.find('=');
    return eq != std::string::npos && eq > 0 && all_digits(line.substr(0, eq));
}

// "2^3*13*990719" -> factors; false if it is not of that form
bool parse_factors(const std::string& text, amicable::FactorBuffer& out) {
    out.clear();
    std::stringstream ss(text);
    std::string term;
    while (std::getline(ss, term, '*')) {
        const auto caret = term.find('^');
        const std::string p = term.substr(0, caret);
        int e = 1;
        if (caret != std::string::npos) {
            const std::string es = term.substr(caret + 1);
            if (!all_digits(es) || es.size() > 6) return false;
            e = std::stoi(es);
            if (e < 1) return false;
        }
        if (!all_digits(p)) return false;
        out.add(BigInt(p), e);
    }
    if (out.empty()) return false;
    out.sort_by_prime();
    return true;
}

BigInt sigma_of(const amicable::FactorBuffer& f) {
    BigInt s = 1, t;
    for (std::size_t i = 0; i < f.size(); ++i) {
        const BigInt& p = f[i].prime;
        mpz_pow_ui(t.get_mpz_t(), p.get_mpz_t(), static_cast<unsigned long>(f[i].exponent) + 1);
        t -= 1;
        t /= p - 1;
        s *= t;
    }
    return s;
}

BigInt product_of(const amicable::FactorBuffer& f) {
    BigInt n = 1, t;
    for (std::size_t i = 0; i < f.size(); ++i) {
        mpz_pow_ui(t.get_mpz_t(), f[i].prime.get_mpz_t(), static_cast<unsigned long>(f[i].exponent));
        n *= t;
    }
    return n;
}

// The checks described at the top; why = the reason when false.  type = the
// sech.me type of the pair (e.g. "23", "X22") when the factorizations parse.
bool check_pair(const Pair& p, std::string& why, std::string& type) {
    amicable::FactorBuffer fs_, fl;
    const std::string sf = p.small_text.substr(p.small_text.find('=') + 1);
    const std::string lf = p.large_text.substr(p.large_text.find('=') + 1);
    if (!parse_factors(sf, fs_) || !parse_factors(lf, fl)) { why = "factorization cannot be read"; return false; }
    type = amicable::sech_type(fs_, fl);
    if (!(p.small < p.large)) { why = "first number is not the smaller one"; return false; }
    if (product_of(fs_) != p.small) { why = "factors of the smaller number do not multiply to it"; return false; }
    if (product_of(fl) != p.large) { why = "factors of the larger number do not multiply to it"; return false; }
    for (const amicable::FactorBuffer* f : {&fs_, &fl})
        for (std::size_t i = 0; i < f->size(); ++i)
            if (mpz_probab_prime_p((*f)[i].prime.get_mpz_t(), 30) == 0) {
                why = "factor " + (*f)[i].prime.get_str() + " is not prime";
                return false;
            }
    const BigInt total = p.small + p.large;
    if (sigma_of(fs_) != total || sigma_of(fl) != total) { why = "not an amicable pair (sigma check failed)"; return false; }
    return true;
}

// header "type author year" -> year as a number (0 if none)
int header_year(const std::string& header) {
    const auto sp = header.find_last_of(' ');
    const std::string y = header.substr(sp == std::string::npos ? 0 : sp + 1);
    return (all_digits(y) && y.size() <= 6) ? std::stoi(y) : 0;
}

struct FileStats { std::size_t pairs = 0, unfinished = 0; };

// Reads the pairs of one results file.  A pair is a header line (optional)
// followed by "m=factors" and "n=factors".  A lone first line at the very end
// is a pair still being written (or cut by a power cut): skipped and counted.
FileStats read_file(const fs::path& file, std::vector<Pair>& out, std::vector<std::string>& problems) {
    FileStats st;
    std::ifstream in(file, std::ios::binary);
    if (!in) { problems.push_back(file.string() + ": cannot be read"); return st; }
    std::string raw, header;
    std::size_t line_no = 0, pending_line = 0;
    bool have_small = false;
    Pair cur;
    while (std::getline(in, raw)) {
        ++line_no;
        const std::string line = trim(raw);
        if (!number_line(line)) {
            if (have_small)
                problems.push_back(file.string() + ":" + std::to_string(pending_line) +
                                   ": a pair with only its first line, skipped");
            have_small = false;
            header = line;                       // a blank line ends the header too
            continue;
        }
        if (!have_small) {
            cur = Pair();
            cur.small_text = line;
            cur.header = header;
            pending_line = line_no;
            have_small = true;
            continue;
        }
        cur.large_text = line;
        cur.small = BigInt(cur.small_text.substr(0, cur.small_text.find('=')));
        cur.large = BigInt(line.substr(0, line.find('=')));
        cur.source = file.string() + ":" + std::to_string(pending_line);
        out.push_back(cur);
        ++st.pairs;
        have_small = false;
        // the header stays until the next blank line: this program writes one
        // per pair, and a file with one header over a block of pairs keeps it
        // for all of them
    }
    if (have_small) ++st.unfinished;
    return st;
}

void collect_files(const fs::path& p, std::vector<fs::path>& files, std::vector<std::string>& problems) {
    std::error_code ec;
    if (fs::is_regular_file(p, ec)) { files.push_back(p); return; }
    if (!fs::is_directory(p, ec)) { problems.push_back(p.string() + ": no such file or folder"); return; }
    for (auto it = fs::recursive_directory_iterator(p, fs::directory_options::skip_permission_denied, ec);
         !ec && it != fs::recursive_directory_iterator(); it.increment(ec)) {
        if (!it->is_regular_file(ec)) continue;
        const std::string name = it->path().filename().string();
        if (name.size() >= 11 && name.compare(name.size() - 11, 11, "results.txt") == 0) files.push_back(it->path());
    }
    if (ec) problems.push_back(p.string() + ": " + ec.message());
}

std::string current_year() {
    const std::time_t now = std::time(nullptr);
    std::tm tm_now{};
#ifdef _WIN32
    localtime_s(&tm_now, &now);
#else
    localtime_r(&now, &tm_now);
#endif
    return std::to_string(tm_now.tm_year + 1900);
}

// tmp file swapped in, so an old all_pairs.txt is never left half-written
void replace_file(const fs::path& src, const fs::path& dst) {
#ifdef _WIN32
    for (int attempt = 0;; ++attempt) {
        if (MoveFileExW(src.wstring().c_str(), dst.wstring().c_str(),
                        MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH))
            return;
        if (attempt >= 50)                       // open in an editor?
            throw std::runtime_error("cannot replace " + dst.string() + " (is it open in another program?); "
                                     "the new list is in " + src.string());
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
#else
    std::error_code ec;
    fs::rename(src, dst, ec);
    if (ec) throw std::runtime_error("cannot replace " + dst.string() + ": " + ec.message());
#endif
}

// Started by a double click on Windows: keep the window open to show the summary.
void pause_if_own_console() {
#ifdef _WIN32
    DWORD ids[2];
    if (GetConsoleProcessList(ids, 2) == 1) {
        std::cout << "\nPress Enter to close.";
        std::cout.flush();
        std::getchar();
    }
#endif
}

void usage() {
    std::cout
        << "collect_results: all pairs of the results files in one file, smallest first\n\n"
        << "  collect_results [--root DIR] [--out FILE] [--known FILE] [--no-check] [FILE or FOLDER ...]\n\n"
        << "  FILE/FOLDER   results files, or folders searched (with subfolders) for\n"
        << "                *results.txt.  Default: DIR/Data\n"
        << "  --root DIR    the Amicable_Search folder (default: found from this program)\n"
        << "  --out FILE    the file to write (default: DIR/all_pairs.txt)\n"
        << "  --known FILE  leave out the pairs listed in FILE (e.g. AP23.txt from sech.me),\n"
        << "                so only new pairs remain; can be given several times\n"
        << "  --no-check    skip the check of each pair (faster, not recommended)\n";
}

int run(int argc, char** argv) {
    fs::path root, out_file;
    bool check = true;
    std::vector<fs::path> inputs, known_files;
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        if (a == "--help" || a == "-h") { usage(); return 0; }
        if (a == "--no-check") { check = false; continue; }
        if (a == "--known" && i + 1 < argc) { known_files.emplace_back(argv[++i]); continue; }
        if ((a == "--root" || a == "--out") && i + 1 < argc) {
            (a == "--root" ? root : out_file) = fs::path(argv[++i]);
            continue;
        }
        if (a.rfind("--", 0) == 0) { std::cerr << "unknown option " << a << "\n\n"; usage(); return 2; }
        inputs.emplace_back(a);
    }
    if (root.empty()) root = amicable::find_root(argc > 0 ? argv[0] : nullptr);
    if (inputs.empty()) inputs.push_back(root / "Data");
    if (out_file.empty()) out_file = root / "all_pairs.txt";

    amicable::AppConfig cfg;                     // author and year for a pair without a header line
    (void)amicable::load_config_file(root / "config.txt", cfg);
    const std::string year = cfg.year.empty() ? current_year() : cfg.year;

    std::vector<std::string> problems;
    std::vector<fs::path> files;
    for (const fs::path& p : inputs) collect_files(p, files, problems);
    std::error_code ec;
    const fs::path out_abs = fs::weakly_canonical(out_file, ec);
    files.erase(std::remove_if(files.begin(), files.end(), [&](const fs::path& f) {
                    std::error_code e2;
                    return fs::weakly_canonical(f, e2) == out_abs;    // never read our own output
                }), files.end());
    std::sort(files.begin(), files.end());
    files.erase(std::unique(files.begin(), files.end()), files.end());

    std::vector<Pair> pairs;
    std::size_t unfinished = 0;
    for (const fs::path& f : files) {
        const FileStats st = read_file(f, pairs, problems);
        unfinished += st.unfinished;
        std::cout << "  " << st.pairs << " pair(s)  " << f.string() << '\n';
    }

    // pairs already known (--known): their smaller members
    std::set<BigInt> known;
    for (const fs::path& f : known_files) {
        std::vector<Pair> listed;
        std::vector<std::string> kp;
        const FileStats st = read_file(f, listed, kp);
        for (const std::string& s : kp) problems.push_back(s);
        for (const Pair& p : listed) known.insert(p.small);
        std::cout << "  " << st.pairs << " known pair(s)  " << f.string() << '\n';
    }

    // check, then keep one entry per smaller member (earliest year)
    std::map<BigInt, Pair> unique;
    std::vector<std::pair<BigInt, std::string>> rejected;   // smaller member, message
    std::map<std::string, std::size_t> by_type;
    std::size_t repeats = 0, type_notes = 0;
    std::set<BigInt> known_hit;
    for (Pair& p : pairs) {
        if (known.count(p.small)) { known_hit.insert(p.small); continue; }
        std::string why, type;
        if (check && !check_pair(p, why, type)) {
            rejected.emplace_back(p.small, p.source + ": " + why + "  (" +
                                           p.small_text.substr(0, p.small_text.find('=')) + ")");
            continue;
        }
        if (type.empty()) {                      // --no-check: the type for a missing header
            amicable::FactorBuffer a, b;
            if (parse_factors(p.small_text.substr(p.small_text.find('=') + 1), a) &&
                parse_factors(p.large_text.substr(p.large_text.find('=') + 1), b))
                type = amicable::sech_type(a, b);
        }
        if (p.header.empty()) p.header = (type.empty() ? std::string("?") : type) + ' ' + cfg.author + ' ' + year;
        else if (!type.empty() && p.header.substr(0, p.header.find(' ')) != type) {
            // the type follows from the factorizations: correct it, keep author and year
            const auto sp = p.header.find(' ');
            p.header = type + (sp == std::string::npos ? std::string() : p.header.substr(sp));
            ++type_notes;
        }
        auto [it, inserted] = unique.try_emplace(p.small, p);
        if (inserted) continue;
        ++repeats;
        if (it->second.large != p.large) {
            rejected.emplace_back(BigInt(-1), p.source + ": same smaller number as " + it->second.source +
                                                  " but a different partner; kept the first");
            continue;
        }
        const int y_old = header_year(it->second.header), y_new = header_year(p.header);
        if (y_new != 0 && (y_old == 0 || y_new < y_old)) it->second = p;   // earliest year wins
    }
    for (const auto& [n, p] : unique) ++by_type[p.header.substr(0, p.header.find(' '))];

    const fs::path tmp(out_file.string() + ".tmp");
    {
        std::ofstream out(tmp, std::ios::out | std::ios::trunc);
        if (!out) throw std::runtime_error("cannot write " + tmp.string());
        for (const auto& [n, p] : unique)        // std::map: smallest first
            out << p.header << '\n' << p.small_text << '\n' << p.large_text << "\n\n";
        out.flush();
        if (!out) throw std::runtime_error("cannot write " + tmp.string());
    }
    replace_file(tmp, out_file);

    std::cout << "\nread " << files.size() << " file(s), " << pairs.size() << " pair line(s)\n";
    if (!known_files.empty())
        std::cout << "  " << known_hit.size() << " pair(s) left out because they are already known (--known)\n";
    if (repeats) std::cout << "  " << repeats << " pair(s) found in more than one place, written once\n";
    if (unfinished) std::cout << "  " << unfinished << " pair(s) with only their first line (a search still writing, or a power cut), skipped\n";
    if (!check) std::cout << "  pairs NOT checked (--no-check)\n";
    if (type_notes) std::cout << "  " << type_notes << " pair(s) whose header type differed from the type of its factorizations (corrected)\n";
    for (const std::string& s : problems) std::cout << "  note: " << s << '\n';
    if (!rejected.empty()) {
        std::cout << "  " << rejected.size() << " entr" << (rejected.size() == 1 ? "y" : "ies")
                  << " LEFT OUT, they failed the check:\n";
        for (std::size_t i = 0; i < rejected.size() && i < 50; ++i)
            std::cout << "    " << rejected[i].second
                      << (unique.count(rejected[i].first) ? "  [a correct copy from another file was written]" : "")
                      << '\n';
        if (rejected.size() > 50) std::cout << "    ... and " << rejected.size() - 50 << " more\n";
    }
    std::cout << "\nwrote " << unique.size() << " pair(s), smallest first" << (check ? ", every one checked" : "")
              << ":\n  " << out_file.string() << '\n';
    if (!by_type.empty()) {
        std::cout << "  by type:";
        for (const auto& [t, c] : by_type) std::cout << "  " << t << ": " << c;
        std::cout << '\n';
    }
    return rejected.empty() ? 0 : 1;
}

} // namespace

int main(int argc, char** argv) {
    int rc;
    try {
        rc = run(argc, argv);
    } catch (const std::exception& e) {
        std::cerr << "collect_results: " << e.what() << '\n';
        rc = 1;
    }
    pause_if_own_console();
    return rc;
}
