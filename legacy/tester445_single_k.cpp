// Build command:
// g++ -O3 -std=c++20 -pthread tester445_single_k.cpp -I"C:\msys64\tmp\primesieve\include" -I"C:\msys64\mingw64\include" -L"C:\msys64\tmp\primesieve\build" -L"C:\msys64\mingw64\lib" -lprimesieve -lgmpxx -lgmp -o tester445_single_k.exe
//
// Usage: ./tester445_single_k.exe <k> [P1_start]
//
//   <k>         required — the multiplier to search
//   [P1_start]  optional — resume from this P1 value (inclusive).
//               If the program crashes, pass the last "current_p1" value
//               from amicable_status.txt to pick up where you left off.
//               If omitted, the search starts from the beginning (P1=2).
//
// ═══════════════════════════════════════════════════════════════════════════
// THREADING MODEL
// ═══════════════════════════════════════════════════════════════════════════
//
// No BigInt ever crosses a thread boundary.  All per-P1 data is serialised
// into P1Work (strings + uint64_t + doubles) before any worker is launched.
// Workers reconstruct private BigInts from those plain values at startup.
//
// Pairs are written to stdout and the output file IMMEDIATELY when found,
// under a single output mutex.  There is no end-of-P1 merge step and no
// dedup set — nothing to lose if a thread crashes or returns early.
//
// primesieve generates P1 and P3 as uint64_t (always fits).
// P2, P4, P5 remain BigInt (can exceed uint64_t).
// ═══════════════════════════════════════════════════════════════════════════

#include <primesieve.hpp>
#include <gmpxx.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_set>
#include <utility>
#include <vector>

// ─── Configuration ────────────────────────────────────────────────────────────
static constexpr int  WORKERS           = 0;   // 0 = hardware_concurrency
static constexpr int  HEARTBEAT_SECONDS = 60;
static constexpr const char* OUTPUT_FILE = "results.txt";
static constexpr const char* STATUS_FILE = "amicable_status.txt";
static constexpr const char* SKIPPED_P1_FILE = "amicable_skipped_p1.txt";
static constexpr std::uint64_t SKIP_P1_IF_P3_MAX_EXCEEDS = 0; // 0 disables the skip.

// ─── Types ────────────────────────────────────────────────────────────────────
using BigInt = mpz_class;

// ─── GMP helpers ─────────────────────────────────────────────────────────────

static BigInt u64_to_bigint(std::uint64_t v) {
    BigInt r;
    mpz_import(r.get_mpz_t(), 1, 1, sizeof(v), 0, 0, &v);
    return r;
}

static std::uint64_t bigint_to_u64_capped(const BigInt& n) {
    if (n <= 0) return 0;
    if (n.get_d() > static_cast<double>(UINT64_MAX)) return UINT64_MAX;
    std::uint64_t val = 0;
    std::size_t   cnt = 0;
    mpz_export(&val, &cnt, 1, sizeof(val), 0, 0, n.get_mpz_t());
    return cnt > 0 ? val : 0;
}

static inline BigInt ceil_double_to_bigint(double x) {
    if (!std::isfinite(x)) return BigInt(0);
    BigInt r;
    mpz_set_d(r.get_mpz_t(), std::ceil(x));
    return r;
}

static inline bool divisible(const BigInt& a, const BigInt& b) {
    return mpz_divisible_p(a.get_mpz_t(), b.get_mpz_t()) != 0;
}

static inline bool is_probable_prime(const BigInt& n) {
    if (n < 2) return false;
    return mpz_probab_prime_p(n.get_mpz_t(), 25) > 0;
}

static gmp_randclass& thread_rng() {
    static thread_local gmp_randclass rng(gmp_randinit_default);
    static thread_local bool seeded = false;
    if (!seeded) {
        rng.seed(static_cast<unsigned long>(
            std::chrono::high_resolution_clock::now().time_since_epoch().count()));
        seeded = true;
    }
    return rng;
}

static BigInt pollard_rho(const BigInt& n) {
    if (n % 2 == 0) return BigInt(2);
    if (n % 3 == 0) return BigInt(3);
    auto& rng = thread_rng();
    while (true) {
        BigInt x = rng.get_z_range(n - 2) + 2;
        BigInt y = x;
        BigInt c = rng.get_z_range(n - 1) + 1;
        if (c >= n) c = 1;
        BigInt d = 1;
        while (d == 1) {
            x = (x*x + c) % n;
            y = (y*y + c) % n;
            y = (y*y + c) % n;
            BigInt diff = (x > y) ? (x - y) : (y - x);
            mpz_gcd(d.get_mpz_t(), diff.get_mpz_t(), n.get_mpz_t());
            if (d == n) break;
        }
        if (d > 1 && d < n) return d;
    }
}

static void factorize(BigInt n, std::map<BigInt,int>& f) {
    if (n <= 1) return;
    if (is_probable_prime(n)) { f[n]++; return; }
    BigInt d = pollard_rho(n);
    factorize(d, f);
    factorize(n / d, f);
}

static std::vector<BigInt> build_divisors(const std::map<BigInt,int>& f) {
    std::vector<BigInt> divs = {BigInt(1)};
    for (const auto& [p, e] : f) {
        const std::size_t sz = divs.size();
        BigInt pk = 1;
        for (int i = 0; i < e; ++i) {
            pk *= p;
            for (std::size_t j = 0; j < sz; ++j)
                divs.push_back(divs[j] * pk);
        }
    }
    std::sort(divs.begin(), divs.end());
    const std::size_t pos = divs.size();
    divs.reserve(pos * 2);
    for (std::size_t i = 0; i < pos; ++i)
        divs.push_back(-divs[i]);
    return divs;
}

static BigInt sigma1(std::uint64_t k) {
    BigInt n = u64_to_bigint(k);
    if (n <= 1) return BigInt(1);
    std::map<BigInt,int> f;
    factorize(n, f);
    BigInt total = 1;
    for (const auto& [p, e] : f) {
        BigInt term = 1, pk = 1;
        for (int i = 0; i < e; ++i) { pk *= p; term += pk; }
        total *= term;
    }
    return total;
}

static std::vector<std::pair<BigInt,int>> factorize_for_output(BigInt n) {
    std::vector<std::pair<BigInt,int>> terms;
    if (n <= 1) return terms;
    std::map<BigInt,int> f;
    factorize(n, f);
    for (auto& kv : f) terms.push_back(kv);
    return terms;
}

static std::string format_factorization(
    const std::vector<std::pair<BigInt,int>>& terms, const BigInt& orig)
{
    if (terms.empty()) return "1";
    BigInt residue = orig;
    std::string out;
    bool first = true;
    for (const auto& [p, e] : terms) {
        if (!first) out += "*";
        first = false;
        out += p.get_str();
        if (e > 1) out += "^" + std::to_string(e);
        BigInt pp = p;
        for (int i = 0; i < e; ++i)
            mpz_divexact(residue.get_mpz_t(), residue.get_mpz_t(), pp.get_mpz_t());
    }
    if (residue > 1) { if (!first) out += "*"; out += residue.get_str(); }
    return out;
}

struct SkippedP1Entry {
    std::uint64_t k  = 0;
    std::uint64_t p1 = 0;

    bool operator<(const SkippedP1Entry& other) const noexcept {
        return (k < other.k) || (k == other.k && p1 < other.p1);
    }
    bool operator==(const SkippedP1Entry& other) const noexcept {
        return k == other.k && p1 == other.p1;
    }
};

static std::vector<SkippedP1Entry> load_skipped_p1_entries(const char* path) {
    std::vector<SkippedP1Entry> entries;
    std::ifstream in(path);
    if (!in) return entries;

    std::string line;
    while (std::getline(in, line)) {
        if (line.empty()) continue;
        std::istringstream iss(line);
        SkippedP1Entry entry;
        if (iss >> entry.k >> entry.p1)
            entries.push_back(entry);
    }

    std::sort(entries.begin(), entries.end());
    entries.erase(std::unique(entries.begin(), entries.end()), entries.end());
    return entries;
}

static bool write_skipped_p1_entries(
    const char* path, const std::vector<SkippedP1Entry>& entries)
{
    std::ofstream out(path, std::ios::out | std::ios::trunc);
    if (!out) return false;

    for (const auto& entry : entries)
        out << entry.k << ' ' << entry.p1 << '\n';
    return true;
}

// ─── compute_bnd — pure double, no GMP, safe from any thread ─────────────────

static double compute_bnd(double A1d, double A2d, double P1d, double P3d) {
    const double disc =
        (A1d*A1d - A1d*A2d)*P1d*P1d*P1d
        - A1d*A2d*P1d
        + (A1d*A1d - 2.0*A1d*A2d)*P1d*P1d
        - ((A1d*A1d - A1d*A2d)*P1d*P1d - A1d*A2d
           + (A1d*A1d - 2.0*A1d*A2d)*P1d)*P3d*P3d
        + ((2.0*A1d*A1d - A1d*A2d)*P1d*P1d*P1d + A1d*A2d*P1d
           + (2.0*A1d*A1d - A1d*A2d)*P1d*P1d + A1d*A2d)*P3d;
    if (disc < 0.0) return -1.0;
    const double den = (A1d - A2d)*P1d
                     + ((2.0*A1d - A2d)*P1d + A1d - A2d)*P3d - A2d;
    if (den == 0.0) return -1.0;
    return -((A1d - A2d)*P1d + ((A1d - A2d)*P1d - A2d)*P3d - A2d
            - std::sqrt(disc)) / den;
}

// ─── P1Work — plain data only, zero BigInt ────────────────────────────────────

struct P1Work {
    std::string  A1_str, A2_str;
    std::uint64_t P1_u64 = 0;
    double        A1d = 0, A2d = 0, P1d = 0;
    std::string   a_coef_str, b_coef_str, c_coef_str;
    std::vector<std::pair<std::string,int>> extra_factors;
    std::vector<std::uint64_t> p3_vals;
};

// ─── Progress ────────────────────────────────────────────────────────────────

struct Progress {
    std::atomic<std::uint64_t> p1_done{0};
    std::atomic<std::size_t>   p3_done{0};
    std::atomic<std::size_t>   p3_total{0};

    std::string cur_p1;
    std::mutex  p1_mu;
    void set_p1(const std::string& s) { std::lock_guard<std::mutex> g(p1_mu); cur_p1 = s; }
    std::string get_p1()              { std::lock_guard<std::mutex> g(p1_mu); return cur_p1; }
};

// ─── OutputSink — immediate write, protected by mutex ────────────────────────

struct PairKeyHash {
    std::size_t operator()(const std::pair<std::string,std::string>& p) const noexcept {
        std::hash<std::string> h;
        std::size_t h1 = h(p.first), h2 = h(p.second);
        return h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
    }
};

struct OutputSink {
    std::uint64_t  k;
    std::ofstream& file;
    std::mutex     mu;
    std::uint64_t  pairs_found = 0;
    std::unordered_set<std::pair<std::string,std::string>, PairKeyHash> seen;

    void write_pair(const BigInt& n1, const BigInt& n2) {
        const BigInt& smaller = (n1 < n2) ? n1 : n2;
        const BigInt& larger  = (n1 < n2) ? n2 : n1;

        const std::string small_str = smaller.get_str();
        const std::string large_str = larger.get_str();

        {
            std::lock_guard<std::mutex> lk(mu);
            if (!seen.insert({small_str, large_str}).second) return;
            ++pairs_found;
        }

        const auto small_terms = factorize_for_output(smaller);
        const auto large_terms = factorize_for_output(larger);

        std::size_t i = 0, j = 0;
        int us = 0, ul = 0;
        while (i < small_terms.size() && j < large_terms.size()) {
            if      (small_terms[i].first == large_terms[j].first) { ++i; ++j; }
            else if (small_terms[i].first <  large_terms[j].first) { ++us; ++i; }
            else                                                    { ++ul; ++j; }
        }
        us += static_cast<int>(small_terms.size() - i);
        ul += static_cast<int>(large_terms.size() - j);

        const std::string small_facts = format_factorization(small_terms, smaller);
        const std::string large_facts = format_factorization(large_terms, larger);
        const std::string n1_str      = n1.get_str();
        const std::string n2_str      = n2.get_str();
        const std::string hdr         = std::to_string(us) + std::to_string(ul) + " Chesnut 2026";

        std::lock_guard<std::mutex> lk(mu);

        std::cout << k << ' ' << n1_str << ' ' << n2_str << '\n';
        std::cout.flush();

        file << hdr        << "\n";
        file << small_str  << "=" << small_facts << "\n";
        file << large_str  << "=" << large_facts << "\n\n";
        file.flush();
    }
};

struct SkippedP1Sink {
    const char* path;
    std::vector<SkippedP1Entry> entries;
    std::mutex mu;

    explicit SkippedP1Sink(const char* p)
        : path(p), entries(load_skipped_p1_entries(p)) {}

    void record(std::uint64_t k, std::uint64_t p1) {
        std::lock_guard<std::mutex> lk(mu);
        const SkippedP1Entry entry{k, p1};
        const auto it = std::lower_bound(entries.begin(), entries.end(), entry);
        if (it != entries.end() && *it == entry) return;

        entries.insert(it, entry);
        if (!write_skipped_p1_entries(path, entries))
            std::cerr << "[warn] Cannot update skipped P1 file: " << path << "\n";
    }
};

// ─── Worker ───────────────────────────────────────────────────────────────────

static void run_worker(
    const P1Work&           w,
    std::atomic<std::size_t>& p3_idx,
    Progress&               prog,
    OutputSink&             sink)
{
    BigInt A1, A2, P1, a_coef, b_coef, c_coef;
    mpz_set_str(A1.get_mpz_t(),     w.A1_str.c_str(),     10);
    mpz_set_str(A2.get_mpz_t(),     w.A2_str.c_str(),     10);
    mpz_import( P1.get_mpz_t(), 1, 1, sizeof(w.P1_u64), 0, 0, &w.P1_u64);
    mpz_set_str(a_coef.get_mpz_t(), w.a_coef_str.c_str(), 10);
    mpz_set_str(b_coef.get_mpz_t(), w.b_coef_str.c_str(), 10);
    mpz_set_str(c_coef.get_mpz_t(), w.c_coef_str.c_str(), 10);

    std::map<BigInt,int> extra;
    for (const auto& [ps, e] : w.extra_factors) {
        BigInt p;
        mpz_set_str(p.get_mpz_t(), ps.c_str(), 10);
        extra[std::move(p)] = e;
    }

    const double A1d = w.A1d, A2d = w.A2d, P1d = w.P1d;

    while (true) {
        const std::size_t idx = p3_idx.fetch_add(1, std::memory_order_relaxed);
        if (idx >= w.p3_vals.size()) break;

        const std::uint64_t p3_u64 = w.p3_vals[idx];
        BigInt P3;
        mpz_import(P3.get_mpz_t(), 1, 1, sizeof(p3_u64), 0, 0, &p3_u64);
        const double P3d = static_cast<double>(p3_u64);

        const double bnd = compute_bnd(A1d, A2d, P1d, P3d);

        const BigInt dP4 =
            (A1 - A2)*P1
            + ((BigInt(2)*A1 - A2)*P1 + A1 - A2)*P3
            - A2;
        if (dP4 == 0) { prog.p3_done.fetch_add(1, std::memory_order_relaxed); continue; }

        const BigInt val_ = a_coef * P3 * P3 + b_coef * P3 + c_coef;
        if (val_ == 0) { prog.p3_done.fetch_add(1, std::memory_order_relaxed); continue; }

        BigInt abs_val = val_;
        if (abs_val < 0) abs_val = -abs_val;

        std::map<BigInt,int> f = extra;
        factorize(abs_val, f);
        const auto all_divs = build_divisors(f);

        const BigInt num_base =
            -((A1 - A2)*P1 + ((A1 - A2)*P1 - A2)*P3 - A2);

        for (const BigInt& F : all_divs) {
            const BigInt nF = num_base + F;

            if (bnd >= 0.0) {
                const double p4a = nF.get_d() / dP4.get_d();
                if (p4a > bnd + 1.0) continue;
            }

            if (!divisible(nF, dP4)) continue;
            const BigInt P4 = nF / dP4;
            if (P4 <= 1) continue;
            if (!is_probable_prime(P4)) continue;
            if (divisible(A1, P4)) continue;

            const BigInt dP2 =
                (A1 - A2)*P1
                + ((A1 - A2)*P1 - A2)*P3
                + ((A1 - A2)*P1
                   + ((BigInt(2)*A1 - A2)*P1 + A1 - A2)*P3
                   - A2)*P4
                - A2;
            if (dP2 == 0) continue;

            const BigInt P2_num =
                (A1*P3*P3 + A1*P3)*P4*P4
                + A2*P1
                + (A2*P1 + A2)*P3
                + (A1*P3*P3 + A2*P1 - ((A1 - A2)*P1 - A2)*P3 + A2)*P4
                + A2;

            if (!divisible(P2_num, dP2)) continue;
            const BigInt P2 = P2_num / dP2;
            if (P2 <= 1) continue;
            if (!is_probable_prime(P2)) continue;
            if (divisible(A1, P2)) continue;

            const BigInt dP5 = (P3 + 1)*P4 + (P3 + 1);
            if (dP5 == 0) continue;

            const BigInt P5_num = (P1 + 1)*P2 - (P3 + 1)*P4 + (P1 - P3);
            if (!divisible(P5_num, dP5)) continue;
            const BigInt P5 = P5_num / dP5;
            if (P5 <= 1) continue;
            if (!is_probable_prime(P5)) continue;
            if (divisible(A1, P5)) continue;

            if (P1 == P2) continue;
            if (P3 == P4 || P3 == P5 || P4 == P5) continue;

            const BigInt n1 = A1 * P1 * P2;
            const BigInt n2 = A1 * P3 * P4 * P5;
            sink.write_pair(n1, n2);
        }

        prog.p3_done.fetch_add(1, std::memory_order_relaxed);
    }
}

// ─── Main solver ──────────────────────────────────────────────────────────────
//
// p1_resume: if non-zero, skip all P1 values strictly less than this.
//            The heartbeat writes "current_p1=X" to amicable_status.txt —
//            pass that X here to resume after a crash.

static void solve(std::uint64_t k, std::uint64_t p1_resume,
                  int num_workers, Progress& prog, OutputSink& sink,
                  SkippedP1Sink& skipped_p1_sink)
{
    const BigInt A1 = u64_to_bigint(k);
    const BigInt A2 = sigma1(k);

    if (BigInt(2)*A1 <= A2) return;

    const double A1d = A1.get_d();
    const double A2d = A2.get_d();

    const BigInt denom_p1 = BigInt(2)*A1 - A2;
    if (denom_p1 <= 0) return;

    BigInt p1max_big;
    mpz_cdiv_q(p1max_big.get_mpz_t(), A2.get_mpz_t(), denom_p1.get_mpz_t());
    if (p1max_big < 2) return;

    const std::uint64_t p1_max_u64 = bigint_to_u64_capped(p1max_big);
    if (p1_max_u64 < 2) return;

    if (p1_resume > 0)
        std::cerr << "[resume] Skipping P1 values below " << p1_resume << "\n";

    primesieve::iterator p1_it;
    std::uint64_t P1_u64;

    while ((P1_u64 = p1_it.next_prime()) <= p1_max_u64) {

        // ── Resume skip ──────────────────────────────────────────────────────
        if (p1_resume > 0 && P1_u64 < p1_resume) {
            prog.p1_done.fetch_add(1, std::memory_order_relaxed);
            continue;
        }

        if (k % P1_u64 == 0) continue;

        prog.set_p1(std::to_string(P1_u64));

        const double P1d = static_cast<double>(P1_u64);

        const double dP1_d = (2.0*A1d - A2d)*P1d + A1d - A2d;
        if (dP1_d == 0.0) continue;

        const double d0 =
            -A1d*A1d*P1d*P1d + A1d*A2d*P1d*P1d
            - A1d*A1d*P1d + 2.0*A1d*A2d*P1d + A1d*A2d;
        if (d0 < 0.0) continue;

        const double P3MM = -((A1d - A2d)*P1d - A2d - std::sqrt(d0)) / dP1_d;
        if (P3MM < 2.0) continue;

        const double bnd_at_P3MM = compute_bnd(A1d, A2d, P1d, P3MM);
        if (bnd_at_P3MM < 2.0) continue;

        const std::uint64_t p3_max_u64 =
            bigint_to_u64_capped(ceil_double_to_bigint(bnd_at_P3MM));
        if (p3_max_u64 < 2) continue;

        if (SKIP_P1_IF_P3_MAX_EXCEEDS > 0 && p3_max_u64 > SKIP_P1_IF_P3_MAX_EXCEEDS) {
            skipped_p1_sink.record(k, P1_u64);
            std::cerr << "[skip] k=" << k
                      << " P1=" << P1_u64
                      << " p3_max=" << p3_max_u64
                      << " limit=" << SKIP_P1_IF_P3_MAX_EXCEEDS << "\n";
            prog.p1_done.fetch_add(1, std::memory_order_relaxed);
            continue;
        }

        std::vector<std::uint64_t> p3_vals;
        {
            primesieve::iterator p3_it;
            std::uint64_t p3_u;
            while ((p3_u = p3_it.next_prime()) <= p3_max_u64)
                if (k % p3_u != 0)
                    p3_vals.push_back(p3_u);
        }

        if (p3_vals.empty()) {
            prog.p1_done.fetch_add(1, std::memory_order_relaxed);
            continue;
        }

        const BigInt P1 = u64_to_bigint(P1_u64);

        std::map<BigInt,int> extra_map;
        {
            BigInt val = A1 * (P1 + 1);
            factorize(val, extra_map);
        }

        const BigInt a_coef = (-A1*P1) + (A2*P1) + A2;
        const BigInt b_coef = BigInt(2)*A1*P1*P1 - A2*P1*P1 + A2;
        const BigInt c_coef = A1*P1*P1 - A2*P1*P1 - A2*P1;

        P1Work w;
        w.A1_str     = A1.get_str();
        w.A2_str     = A2.get_str();
        w.P1_u64     = P1_u64;
        w.A1d        = A1d;
        w.A2d        = A2d;
        w.P1d        = P1d;
        w.a_coef_str = a_coef.get_str();
        w.b_coef_str = b_coef.get_str();
        w.c_coef_str = c_coef.get_str();
        for (const auto& [p, e] : extra_map)
            w.extra_factors.push_back({p.get_str(), e});
        w.p3_vals = std::move(p3_vals);

        prog.p3_total.store(w.p3_vals.size(), std::memory_order_relaxed);
        prog.p3_done.store(0,                 std::memory_order_relaxed);

        std::atomic<std::size_t> p3_idx{0};
        std::vector<std::thread> threads;
        threads.reserve(static_cast<std::size_t>(num_workers));
        for (int t = 0; t < num_workers; ++t)
            threads.emplace_back(run_worker,
                std::cref(w),
                std::ref(p3_idx),
                std::ref(prog),
                std::ref(sink));
        for (auto& t : threads) t.join();

        prog.p1_done.fetch_add(1, std::memory_order_relaxed);
    }
}

// ─── main ─────────────────────────────────────────────────────────────────────

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <k> [P1_start]\n";
        std::cerr << "  P1_start  optional — resume from this P1 value (inclusive)\n";
        std::cerr << "            check amicable_status.txt for 'current_p1' after a crash\n";
        return 1;
    }

    std::uint64_t k = 0;
    {
        std::istringstream ss(argv[1]);
        if (!(ss >> k) || k < 1) {
            std::cerr << "Invalid k: " << argv[1] << "\n";
            return 1;
        }
    }

    // Optional P1 resume argument
    std::uint64_t p1_resume = 0;
    if (argc >= 3) {
        std::istringstream ss(argv[2]);
        if (!(ss >> p1_resume) || p1_resume < 2) {
            std::cerr << "Invalid P1_start: " << argv[2]
                      << "  (must be an integer >= 2)\n";
            return 1;
        }
    }

    int num_workers = WORKERS;
    if (num_workers <= 0) {
        num_workers = static_cast<int>(std::thread::hardware_concurrency());
        if (num_workers <= 0) num_workers = 4;
    }

    if (p1_resume > 0)
        std::cerr << "k=" << k << "  workers=" << num_workers
                  << "  P1_start=" << p1_resume << "\n";
    else
        std::cerr << "k=" << k << "  workers=" << num_workers << "\n";

    std::ofstream out(OUTPUT_FILE, std::ios::out | std::ios::app);
    if (!out) {
        std::cerr << "Cannot open output file: " << OUTPUT_FILE << "\n";
        return 1;
    }

    const auto t0 = std::chrono::steady_clock::now();
    Progress   prog;
    OutputSink sink{k, out};
    SkippedP1Sink skipped_p1_sink{SKIPPED_P1_FILE};
    std::atomic<bool> stop_monitor{false};

    std::thread monitor([&]() {
        int ticks = 0;
        while (!stop_monitor.load(std::memory_order_relaxed)) {
            std::this_thread::sleep_for(std::chrono::seconds(1));
            if (stop_monitor.load(std::memory_order_relaxed)) break;
            if (++ticks % HEARTBEAT_SECONDS != 0) continue;

            const auto elapsed =
                std::chrono::duration_cast<std::chrono::seconds>(
                    std::chrono::steady_clock::now() - t0).count();
            const std::size_t   p3d = prog.p3_done.load(std::memory_order_relaxed);
            const std::size_t   p3t = prog.p3_total.load(std::memory_order_relaxed);
            const std::uint64_t p1c = prog.p1_done.load(std::memory_order_relaxed);
            const std::uint64_t pf  = [&]{ std::lock_guard<std::mutex> g(sink.mu); return sink.pairs_found; }();
            const std::string   p1s = prog.get_p1();

            std::cerr << "[heartbeat] k=" << k
                      << "  P1=" << p1s
                      << "  P3=" << p3d << "/" << p3t
                      << "  P1_done=" << p1c
                      << "  pairs=" << pf
                      << "  elapsed=" << elapsed << "s\n";

            std::ofstream st(STATUS_FILE, std::ios::out | std::ios::trunc);
            st << "running\n"
               << "k="            << k          << "\n"
               << "p1_resume="    << p1_resume  << "\n"   // included for reference
               << "p1_completed=" << p1c        << "\n"
               << "current_p1="   << p1s        << "\n"   // <-- pass this to resume
               << "p3_progress="  << p3d << "/" << p3t << "\n"
               << "pairs_found="  << pf         << "\n"
               << "elapsed_sec="  << elapsed    << "\n";
        }
    });

    solve(k, p1_resume, num_workers, prog, sink, skipped_p1_sink);

    stop_monitor.store(true, std::memory_order_relaxed);
    monitor.join();

    const auto elapsed =
        std::chrono::duration_cast<std::chrono::seconds>(
            std::chrono::steady_clock::now() - t0).count();
    const std::uint64_t total = [&]{ std::lock_guard<std::mutex> g(sink.mu); return sink.pairs_found; }();
    {
        std::ofstream st(STATUS_FILE, std::ios::out | std::ios::trunc);
        st << "done\n"
           << "k="           << k     << "\n"
           << "pairs_found=" << total << "\n"
           << "elapsed_sec=" << elapsed << "\n";
    }
    std::cerr << "[done] k=" << k
              << "  pairs=" << total
              << "  elapsed=" << elapsed << "s\n";
    std::cout << "[pairs_found=" << total << "]\n";
    std::cout.flush();

    return 0;
}
