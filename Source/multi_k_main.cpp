// multi_k_searcher -- exhaustive amicable pair search for ANY hash, three modes
// (config.txt "mode =")
//
//   range    every k in [start_k, end_k): many k at once.  Every pair with
//            gcd(N1,N2) = k and this hash is found, or the k is written to
//            Data/<hash>/incomplete.txt with the reason (a per-k time limit,
//            timeout_seconds, or a bound that is astronomically large).
//            Resumes from Data/<hash>/multi_k_state.txt.
//   single   one k (single_k) with every thread on it.  Continues by itself
//            from Data/<hash>/single_k_status.txt when the last run on that k
//            was stopped.
//   skipped  works through Data/<hash>/incomplete.txt, smallest k first, every
//            thread on each k.  A k searched completely is deleted from the
//            file; one stopped by single_timeout_seconds keeps its line with
//            the point to continue from (resume=general:root,q1,q2[,q3,...]).
//
// Command line (overrides config.txt):
//   multi_k_searcher [options] [start_k] [end_k_exclusive]               mode range
//   multi_k_searcher --mode single [options] [k] [resume point]
//   multi_k_searcher --mode skipped [options]
//
// Every hash runs on the general engine (general.cpp, engine.cpp).

#include "app_common.h"
#include "engine.h"
#include "fpu.h"
#include "general.h"
#include "skip_file.h"

#include <cstdint>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace fs = std::filesystem;
using namespace amicable;

namespace {

void usage(const char* argv0) {
    std::cerr
        << "Usage: " << argv0 << " [options] [start_k] [end_k_exclusive]           (mode range)\n"
        << "       " << argv0 << " --mode single [options] [k] [resume point]\n"
        << "       " << argv0 << " --mode skipped [options]\n"
        << "  --mode M           range | single | skipped (default: config.txt \"mode\")\n"
        << "  --hash \"[(a,b),...] _ [(c,d),...]\"  smaller member _ larger member\n"
        << "  --workers N        threads (0 = all cores)\n"
        << "  --timeout S        time limit per k in seconds (0 = none); range mode uses\n"
        << "                     timeout_seconds, single/skipped single_timeout_seconds\n"
        << "  --report S         progress line every S seconds (0 = off)\n"
        << "  --plan             print how the hash is solved for start_k (single: k), then exit\n"
        << "  --root DIR         folder holding config.txt and Data/\n"
        << "  Settings not given here are read from config.txt.\n"
        << "  range:   end_k_exclusive = 0 means run until stopped.  Without start_k the\n"
        << "           search resumes from Data/<hash>/multi_k_state.txt.\n"
        << "  single:  k defaults to single_k.  The resume point is root q1 q2 [q3 ...];\n"
        << "           without one, a stopped run on the same k continues from\n"
        << "           Data/<hash>/single_k_status.txt.\n"
        << "  skipped: works through Data/<hash>/incomplete.txt and deletes each k from it\n"
        << "           once that k has been searched completely.\n";
}

void write_range_status(const fs::path& state, const fs::path& status, const std::string& engine,
                        const std::string& hash, std::uint64_t end_k, bool finished, std::uint64_t next_k,
                        std::uint64_t completed, std::uint64_t incomplete, std::uint64_t active,
                        std::uint64_t pairs, std::uint64_t elapsed, std::uint64_t resume_k) {
    {
        std::ofstream out(state, std::ios::out | std::ios::trunc);
        out << resume_k << '\n';
    }
    std::ofstream out(status, std::ios::out | std::ios::trunc);
    out << (finished ? "done" : "running") << '\n'
        << "mode=range\n"
        << "hash=" << hash << '\n'
        << "engine=" << engine << '\n'
        << "current_k=" << next_k << '\n'
        << "end_k_exclusive=" << end_k << '\n'
        << "completed_k=" << completed << '\n'
        << "incomplete_k=" << incomplete << '\n'
        << "in_flight=" << active << '\n'
        << "pairs_found=" << pairs << '\n'
        << "elapsed_sec=" << elapsed << '\n'
        << "resume_k=" << resume_k << '\n';
}

std::string join(const std::vector<std::uint64_t>& v, char sep) {
    std::string s;
    for (std::size_t i = 0; i < v.size(); ++i) s += (i ? std::string(1, sep) : std::string()) + std::to_string(v[i]);
    return s;
}

std::string pairs_text(std::uint64_t pairs, std::uint64_t repeated) {
    std::string s = "pairs=" + std::to_string(pairs);
    if (repeated) s += " (" + std::to_string(repeated) + " already in the results file)";
    return s;
}

// ------------------------------------------------------------------ one k

struct OneK {
    bool complete = false;      // every candidate of this k was searched
    bool timed_out = false;     // stopped by the time limit (resume holds the point)
    bool permanent = false;     // cannot be finished by this engine (reason says why)
    std::string reason;
    std::uint64_t pairs = 0, repeated = 0, elapsed = 0;
    std::vector<std::uint64_t> resume;   // root q1 q2 [q3 ...]
};

// A general-engine point (root, q1, q2, ...) with at least three entries: a
// missing entry is 0, the start of that level, so the meaning is unchanged.
std::vector<std::uint64_t> point3(std::vector<std::uint64_t> p) {
    while (p.size() < 3) p.push_back(0);
    return p;
}

// Longest point accepted: the root and one prime per free slot (at most 16).
constexpr std::size_t MAX_POINT = 17;

// The single-k search of one k with every thread (modes single and skipped).
// Writes single_k_status.txt about once a second.  The caller keeps the skip
// file up to date (so the engine does not add lines of its own).
OneK search_one_k(const AppConfig& cfg, const Session& session, ResultWriter& writer, const std::string& exe,
                  const std::string& mode, std::uint64_t k,
                  const std::vector<std::uint64_t>& resume, std::uint64_t timeout)
{
    const fs::path status = session.data_dir / "single_k_status.txt";
    const std::string engine_name = "general";
    const std::string hash_arg = " --mode single --hash \"" + session.hash.text() + "\" ";
    writer.refresh_known();     // a range run may have written pairs of this k before giving up on it
    const std::uint64_t pairs_before = writer.total_pairs.load();
    const std::uint64_t repeated_before = writer.repeated_pairs.load();
    OneK r;

    EngineOptions opt;
    opt.hash = &session.hash;
    opt.start_k = k;
    opt.stop_k = k + 1;
    opt.threads = cfg.workers;
    opt.timeout_seconds = timeout;
    opt.report_seconds = cfg.report_seconds;
    opt.writer = &writer;
    opt.track_resume = true;
    if (resume.size() >= 3) opt.resume = resume;
    opt.on_tick = [&](const EngineStatus& st) {
        std::ofstream out(status, std::ios::out | std::ios::trunc);
        // a flag raised anywhere makes the k permanent: no resume point that could skip it
        const bool inc = (st.incomplete_k > 0 && !st.timed_out) || st.flags != 0;
        const std::vector<std::uint64_t> p = point3(st.resume);
        // resume_deeper (q3, q4, ...) is the last field a restart reads: a
        // write cut short by a kill can only drop it or shorten its last
        // number, and either moves the point earlier
        out << (inc ? "incomplete" : st.timed_out ? "timeout" : st.finished ? "done" : "running") << '\n'
            << "mode=" << mode << '\n'
            << "hash=" << session.hash.text() << '\n'
            << "engine=" << engine_name << '\n'
            << "k=" << k << '\n'
            << "roots=" << st.roots_total << '\n'
            << "resume_root=" << p[0] << '\n'
            << "resume_q1=" << p[1] << '\n'
            << "resume_q2=" << p[2] << '\n';
        if (p.size() > 3)
            out << "resume_deeper=" << join(std::vector<std::uint64_t>(p.begin() + 3, p.end()), ',') << '\n';
        out << "pairs_found=" << (st.pairs - pairs_before) << '\n'
            << "elapsed_sec=" << st.elapsed_seconds << '\n';
        if ((!st.finished || st.timed_out) && !inc)
            out << "resume_with=" << exe << hash_arg << k << ' ' << join(p, ' ') << '\n';
    };
    const EngineStatus st = run_engine(opt);
    int flags = st.flags;                   // raised while running, or reported when the k ended
    if (st.incomplete_reason.find("bound_not_finite") != std::string::npos) flags |= INC_UNBOUNDED;
    if (st.incomplete_reason.find("range_beyond_2^64") != std::string::npos) flags |= INC_SCAN_LIMIT;
    r.permanent = flags != 0 || (!st.timed_out && st.incomplete_k > 0);
    r.timed_out = st.timed_out && !r.permanent;
    if (r.permanent) {
        r.reason.clear();
        if (flags & INC_UNBOUNDED) r.reason += "bound_not_finite";
        if (flags & INC_SCAN_LIMIT) r.reason += std::string(r.reason.empty() ? "" : ",") + "range_beyond_2^64";
        if (r.reason.empty()) r.reason = st.incomplete_reason;
    }
    r.complete = st.finished && !st.timed_out && st.incomplete_k == 0;
    r.pairs = st.pairs - pairs_before;
    r.elapsed = st.elapsed_seconds;
    r.resume = point3(st.resume);
    r.repeated = writer.repeated_pairs.load() - repeated_before;
    return r;
}

// Resume point left by an earlier stopped run on k with this engine (empty if none).
std::vector<std::uint64_t> status_resume(const Session& session, std::uint64_t k,
                                         const std::string& mode) {
    const auto kv = read_status_file(session.data_dir / "single_k_status.txt");
    // modes single and skipped write different results files: a point made by
    // the other mode would leave the pairs before it in the other file
    if (status_value(kv, "mode") != mode) return {};
    const std::string state = status_value(kv, "state");
    if (state != "running" && state != "timeout") return {};
    std::uint64_t sk = 0;
    if (!parse_u64(status_value(kv, "k"), sk) || sk != k) return {};
    if (status_value(kv, "hash") != session.hash.text()) return {};
    if (status_value(kv, "engine") != "general") return {};
    std::vector<std::uint64_t> r;
    for (const char* key : {"resume_root", "resume_q1", "resume_q2"}) {
        std::uint64_t v = 0;
        if (!parse_u64(status_value(kv, key), v)) return {};
        r.push_back(v);
    }
    // deeper levels, if any: a list cut short keeps its whole numbers in
    // front, and a cut number is smaller, so the point only moves earlier
    std::stringstream in(status_value(kv, "resume_deeper"));
    std::string part;
    while (r.size() < MAX_POINT && std::getline(in, part, ',')) {
        std::uint64_t v = 0;
        if (!parse_u64(part, v)) break;
        r.push_back(v);
    }
    return r;
}

// "general:root,q1,q2[,q3,...]" (a skip line's resume= field)
std::string resume_token(const std::vector<std::uint64_t>& v) {
    return "general:" + join(v, ',');
}

std::vector<std::uint64_t> parse_resume_token(const std::string& text) {
    const std::string tag = "general:";
    if (text.rfind(tag, 0) != 0) return {};
    std::vector<std::uint64_t> v;
    std::stringstream in(text.substr(tag.size()));
    std::string part;
    while (std::getline(in, part, ',')) {
        std::uint64_t x = 0;
        if (!parse_u64(part, x)) return {};
        v.push_back(x);
    }
    if (v.size() < 3u || v.size() > MAX_POINT) return {};
    return v;
}

// Reasons a retry cannot remove: a bound with no finite cap and a prime range
// past 2^64 (both properties of k itself).
bool permanent_reason(const std::string& reason) {
    if (reason.find("bound_not_finite") != std::string::npos) return true;
    if (reason.find("range_beyond_2^64") != std::string::npos) return true;
    return false;
}

std::string time_limit_text(std::uint64_t t) { return t ? std::to_string(t) + "s" : std::string("none"); }

// ------------------------------------------------------------------ modes

int run_range(const AppConfig& cfg, const Session& session) {
    const fs::path results = session.data_dir / "multi_k_results.txt";
    const fs::path state = session.data_dir / "multi_k_state.txt";
    const fs::path status = session.data_dir / "multi_k_status.txt";
    const fs::path incomplete = session.data_dir / "incomplete.txt";

    std::uint64_t start_k = cfg.start_k;
    if (!cfg.start_given) {
        std::ifstream in(state);
        std::uint64_t resume = 0;
        if (in >> resume && resume >= 1) start_k = resume;
    }
    const std::uint64_t end_k = cfg.end_k;
    if (end_k != 0 && end_k <= start_k) {
        std::cerr << "Nothing to do: start_k=" << start_k << " end_k_exclusive=" << end_k
                  << " (end_k must be greater than start_k, or 0 for open-ended)\n";
        return 1;
    }

    ResultWriter writer(results, cfg.author, session.year);
    const std::string engine_name = "general";
    std::cerr << "[multi-k] mode=range  hash " << session.hash.text() << "  engine=" << engine_name
              << "  k=[" << start_k << ", " << (end_k == 0 ? std::string("inf") : std::to_string(end_k)) << ")"
              << "  timeout=" << time_limit_text(cfg.timeout_seconds) << '\n'
              << "[multi-k] data: " << session.data_dir.string() << '\n';

    EngineOptions opt;
    opt.hash = &session.hash;
    opt.start_k = start_k;
    opt.stop_k = end_k;
    opt.threads = cfg.workers;
    opt.timeout_seconds = cfg.timeout_seconds;
    opt.report_seconds = cfg.report_seconds;
    opt.writer = &writer;
    opt.incomplete_file = incomplete;
    opt.on_tick = [&](const EngineStatus& st) {
        write_range_status(state, status, engine_name, session.hash.text(), end_k, st.finished, st.next_k,
                           st.completed_k, st.incomplete_k, st.active_k, st.pairs, st.elapsed_seconds, st.resume_k);
    };
    const EngineStatus st = run_engine(opt);
    const std::uint64_t checked = st.completed_k, pairs = st.pairs, elapsed = st.elapsed_seconds,
                        incomplete_k = st.incomplete_k;
    std::cerr << "[multi-k] done: checked=" << checked << " " << pairs_text(pairs, writer.repeated_pairs.load())
              << " elapsed=" << elapsed << "s\n";
    if (incomplete_k == 0)
        std::cerr << "[multi-k] complete: every k in the range was searched exhaustively\n";
    else
        std::cerr << "[multi-k] " << incomplete_k << " k value(s) NOT complete, listed in "
                  << incomplete.string() << " (finish them with mode = skipped)\n";
    return 0;
}

int run_single(const AppConfig& cfg, const Session& session, std::uint64_t k,
               const std::vector<std::uint64_t>& given_resume, const std::string& exe)
{
    std::vector<std::uint64_t> resume = given_resume;
    const bool from_status = resume.empty() && !(resume = status_resume(session, k, "single")).empty();
    const std::uint64_t timeout = cfg.timeout_given ? cfg.timeout_seconds : cfg.single_timeout_seconds;
    const fs::path incomplete = session.data_dir / "incomplete.txt";

    ResultWriter writer(session.data_dir / "single_k_results.txt", cfg.author, session.year);
    std::cerr << "[single-k] mode=single  hash " << session.hash.text() << "  engine=general  k=" << k;
    if (!resume.empty())
        std::cerr << "  resume=(" << join(resume, ',') << ")" << (from_status ? " from single_k_status.txt" : "");
    std::cerr << "  time limit=" << time_limit_text(timeout) << '\n'
              << "[single-k] data: " << session.data_dir.string() << '\n';

    const OneK r = search_one_k(cfg, session, writer, exe, "single", k, resume, timeout);
    if (r.complete) {
        const std::size_t removed = remove_skip_k(incomplete, k);
        std::cerr << "[done] k=" << k << " searched completely  " << pairs_text(r.pairs, r.repeated)
                  << "  elapsed=" << r.elapsed << "s" << (removed ? "  (removed from incomplete.txt)" : "") << '\n';
    } else if (r.permanent) {
        set_skip_k(incomplete, k, r.reason, "");
        std::cerr << "[incomplete] k=" << k << " " << r.reason << " (listed in incomplete.txt)\n";
    } else {
        // no resume= here: that point refers to single_k_results.txt, and mode skipped
        // writes multi_k_results.txt (mode single itself resumes from single_k_status.txt)
        set_skip_k(incomplete, k, "timeout>" + std::to_string(timeout) + "s", "");
        std::cerr << "[timeout] k=" << k << " stopped at (" << join(r.resume, ',')
                  << "); run again to continue (single_k_status.txt / incomplete.txt)\n";
    }
    std::cout << "[pairs_found=" << r.pairs << "]\n";
    return 0;
}

int run_skipped(const AppConfig& cfg, const Session& session, const std::string& exe) {
    const fs::path incomplete = session.data_dir / "incomplete.txt";
    const std::uint64_t timeout = cfg.timeout_given ? cfg.timeout_seconds : cfg.single_timeout_seconds;
    ResultWriter writer(session.data_dir / "multi_k_results.txt", cfg.author, session.year);
    {
        std::set<std::uint64_t> ks;
        for (const SkipLine& l : read_skip_file(incomplete)) if (l.k) ks.insert(l.k);
        std::cerr << "[skipped] mode=skipped  hash " << session.hash.text() << "  engine=general"
                  << "\n[skipped] file: " << incomplete.string()
                  << "  (" << ks.size() << " k value(s))  time limit per k=" << time_limit_text(timeout) << '\n';
        if (ks.empty()) {
            std::cerr << "[skipped] nothing to do: the file is empty or missing\n";
            return 0;
        }
    }

    // a k the previous skipped/single run was in the middle of goes first
    std::uint64_t hint_k = 0;
    std::vector<std::uint64_t> hint_resume;
    {
        const auto kv = read_status_file(session.data_dir / "single_k_status.txt");
        std::uint64_t sk = 0;
        if (parse_u64(status_value(kv, "k"), sk) && sk > 0) {
            hint_resume = status_resume(session, sk, "skipped");
            if (!hint_resume.empty()) hint_k = sk;
        }
    }

    std::set<std::uint64_t> attempted;
    std::uint64_t done = 0, stopped = 0, pairs = 0, repeated = 0;
    for (;;) {
        // re-read every time: a range run may have added k values meanwhile
        const auto lines = read_skip_file(incomplete);
        std::set<std::uint64_t> candidates;
        for (const SkipLine& l : lines)
            if (l.k && !attempted.count(l.k) && !permanent_reason(l.reason)) candidates.insert(l.k);
        if (candidates.empty()) break;
        const std::uint64_t k = (hint_k && candidates.count(hint_k)) ? hint_k : *candidates.begin();
        attempted.insert(k);

        std::vector<std::uint64_t> resume;
        const char* from = "";
        if (k == hint_k) { resume = hint_resume; from = " (from single_k_status.txt)"; }
        else {
            for (const SkipLine& l : lines)
                if (l.k == k && !l.resume.empty()) { resume = parse_resume_token(l.resume); break; }
            if (!resume.empty()) from = " (from incomplete.txt)";
        }
        hint_k = 0;

        std::cerr << "[skipped] k=" << k << "  " << candidates.size() << " k value(s) left to try";
        if (!resume.empty()) std::cerr << "  resume=(" << join(resume, ',') << ")" << from;
        std::cerr << '\n';

        const OneK r = search_one_k(cfg, session, writer, exe, "skipped", k, resume, timeout);
        pairs += r.pairs;
        repeated += r.repeated;
        if (r.complete) {
            (void)remove_skip_k(incomplete, k);
            ++done;
            std::cerr << "[skipped] k=" << k << " searched completely  " << pairs_text(r.pairs, r.repeated)
                      << "  elapsed=" << r.elapsed << "s  -> removed from incomplete.txt\n";
        } else if (r.permanent) {
            set_skip_k(incomplete, k, r.reason, "");
            ++stopped;
            std::cerr << "[skipped] k=" << k << " " << r.reason << ": cannot be finished; kept in incomplete.txt\n";
        } else {
            set_skip_k(incomplete, k, "timeout>" + std::to_string(timeout) + "s", resume_token(r.resume));
            ++stopped;
            std::cerr << "[skipped] k=" << k << " stopped at the time limit; kept in incomplete.txt with resume="
                      << resume_token(r.resume) << '\n';
        }
    }

    std::set<std::uint64_t> left, perm;
    for (const SkipLine& l : read_skip_file(incomplete)) {
        if (!l.k) continue;
        left.insert(l.k);
        if (permanent_reason(l.reason)) perm.insert(l.k);
    }
    std::cerr << "[skipped] done: " << done << " k searched completely and removed, " << stopped
              << " stopped again, " << pairs_text(pairs, repeated) << ", " << left.size()
              << " k left in incomplete.txt\n";
    if (!perm.empty()) {
        std::cerr << "[skipped] " << perm.size() << " k cannot be finished (not retried):";
        int shown = 0;
        for (std::uint64_t k : perm) {
            if (++shown > 20) { std::cerr << " ..."; break; }
            std::cerr << ' ' << k;
        }
        std::cerr << '\n';
    }
    std::cout << "[pairs_found=" << pairs << "]\n";
    return 0;
}

} // namespace

int main(int argc, char* argv[]) {
    use_full_long_double_precision();
    AppConfig cfg;
    std::vector<std::string> positional;
    bool help = false;
    if (!parse_common_args(argc, argv, cfg, positional, help)) {
        usage(argv[0]);
        return 1;
    }
    if (help) { usage(argv[0]); return 0; }
    if (cfg.root.empty()) cfg.root = find_root(argv[0]);
    if (!load_config_file(cfg.root / "config.txt", cfg)) return 1;   // command-line values stay

    // positional arguments by mode
    std::uint64_t single_k = cfg.single_k;
    std::vector<std::uint64_t> resume;
    if (cfg.mode == "range") {
        if (positional.size() > 2) { usage(argv[0]); return 1; }
        if (!positional.empty()) {
            if (!parse_u64(positional[0], cfg.start_k) || cfg.start_k < 1) {
                std::cerr << "Invalid start_k: " << positional[0] << '\n';
                return 1;
            }
            cfg.start_given = true;
        }
        if (positional.size() == 2) {
            if (!parse_u64(positional[1], cfg.end_k)) {
                std::cerr << "Invalid end_k_exclusive: " << positional[1] << '\n';
                return 1;
            }
            cfg.end_given = true;
        }
    } else if (cfg.mode == "single") {
        if (positional.size() > 1 + MAX_POINT) { usage(argv[0]); return 1; }
        if (!positional.empty() && (!parse_u64(positional[0], single_k) || single_k < 1)) {
            std::cerr << "Invalid k: " << positional[0] << '\n';
            return 1;
        }
        for (std::size_t i = 1; i < positional.size(); ++i) {
            std::uint64_t v = 0;
            if (!parse_u64(positional[i], v)) {
                std::cerr << "Invalid resume value: " << positional[i] << '\n';
                return 1;
            }
            resume.push_back(v);
        }
        if (single_k == 0) {
            std::cerr << "mode single needs a k: set single_k in config.txt or give it on the command line\n";
            return 1;
        }
    } else if (!positional.empty()) {
        usage(argv[0]);
        return 1;
    }

    try {
        Session session;
        std::string err;
        if (!open_session(cfg, session, err)) {
            std::cerr << "[error] " << err << '\n';
            return 2;
        }
        if (!resume.empty() && resume.size() < 3u) {
            std::cerr << "[error] the resume point is k root q1 q2 [q3 ...]"
                      << "; copy the resume_with line of single_k_status.txt\n";
            return 1;
        }

        if (cfg.show_plan) {
            const std::uint64_t k = cfg.mode == "single" ? single_k : cfg.start_k;
            SearchK sk;
            if (!build_search_k(k, session.hash, sk)) {
                std::cout << "hash " << session.hash.text() << ", k=" << k
                          << ": nothing to search (no prime assignment fits, or k is already too abundant)\n";
                return 0;
            }
            std::cout << "hash " << session.hash.text() << ", k=" << k << ": general engine, "
                      << sk.roots.size() << " ordering(s)\n" << describe_plan(sk);
            return 0;
        }

        const std::string exe = fs::path(argv[0]).filename().string();
        if (cfg.mode == "single") return run_single(cfg, session, single_k, resume, exe);
        if (cfg.mode == "skipped") return run_skipped(cfg, session, exe);
        return run_range(cfg, session);
    } catch (const std::exception& ex) {
        std::cerr << "[error] " << ex.what() << '\n';
        return 2;
    }
}
