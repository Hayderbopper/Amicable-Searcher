// Build command:
// g++ -O3 -std=c++20 -pthread tester445_cpp_v2.cpp -I"C:\msys64\tmp\primesieve\include" -I"C:\msys64\mingw64\include" -L"C:\msys64\tmp\primesieve\build" -L"C:\msys64\mingw64\lib" -lprimesieve -lgmpxx -lgmp -o tester445_cpp_v2.exe
//
// Fully GMP version:
// - no __int128 / __uint128_t
// - no u64-only primality testing
// - no u64-only factorization
// - no u64-only divisor handling
// - mpz_nextprime used instead of primesieve iterators inside the solver

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <mutex>
#include <limits>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <thread>
#include <type_traits>
#include <unordered_set>
#include <utility>
#include <vector>

#include <gmpxx.h>

// ---------------------------------------------------------------------------
// Edit these directly.
// ---------------------------------------------------------------------------
static constexpr std::uint64_t START_K = 512ULL;
static constexpr std::uint64_t END_K   = START_K + 1ULL; // exclusive

static constexpr int  WORKERS          = 10;
static constexpr bool PRINT_K          = false;

static constexpr const char* OUTPUT_FILE  = "results.txt";
static constexpr const char* STATUS_FILE  = "amicable_status.txt";
static constexpr const char* SKIPPED_FILE = "amicable_skipped.txt";

static constexpr int  HEARTBEAT_SECONDS      = 1;
static constexpr int  MAX_SECONDS_PER_K      = 600;
static constexpr bool RETRY_FROM_SKIPPED_FILE = false;

static constexpr int TIMEOUT_CHECK_INTERVAL = 1024;

// ---------------------------------------------------------------------------
// Banned primes: k is REJECTED if divisible by ANY of these.
// ---------------------------------------------------------------------------
static constexpr bool USE_BANNED_K_PRIME_FILTER     = true;
static constexpr std::uint64_t BANNED_K_PRIMES[]     = {};
static constexpr std::size_t   BANNED_K_PRIMES_COUNT =
    sizeof(BANNED_K_PRIMES) / sizeof(BANNED_K_PRIMES[0]);

// ---------------------------------------------------------------------------
// Required primes: k is ACCEPTED only if divisible by ALL of these.
// ---------------------------------------------------------------------------
static constexpr bool USE_REQUIRED_K_PRIME_FILTER     = true;
static constexpr std::uint64_t REQUIRED_K_PRIMES[]     = {};
static constexpr std::size_t   REQUIRED_K_PRIMES_COUNT =
    sizeof(REQUIRED_K_PRIMES) / sizeof(REQUIRED_K_PRIMES[0]);

// ---------------------------------------------------------------------------

using BigInt = mpz_class;

// ---------------------------------------------------------------------------
// GMP helpers
// ---------------------------------------------------------------------------
static inline BigInt u64_to_bigint(std::uint64_t v) {
    BigInt r;
    mpz_import(r.get_mpz_t(), 1, 1, sizeof(v), 0, 0, &v);
    return r;
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

static inline BigInt next_prime_big(const BigInt& n) {
    BigInt r;
    mpz_nextprime(r.get_mpz_t(), n.get_mpz_t());
    return r;
}

static inline bool is_probable_prime_big(const BigInt& n) {
    if (n < 2) return false;
    return mpz_probab_prime_p(n.get_mpz_t(), 25) > 0;
}

static inline gmp_randclass& bigint_rng() {
    static thread_local gmp_randclass rng(gmp_randinit_default);
    static thread_local bool seeded = false;
    if (!seeded) {
        const auto seed_raw =
            static_cast<unsigned long long>(
                std::chrono::high_resolution_clock::now().time_since_epoch().count());
        rng.seed(static_cast<unsigned long>(seed_raw));
        seeded = true;
    }
    return rng;
}

static BigInt pollard_rho_big(const BigInt& n) {
    if (n % 2 == 0) return 2;
    if (n % 3 == 0) return 3;

    auto& rng = bigint_rng();

    while (true) {
        BigInt x = rng.get_z_range(n - 2) + 2;
        BigInt y = x;
        BigInt c = rng.get_z_range(n - 1) + 1;
        if (c >= n) c = 1;

        BigInt d = 1;
        while (d == 1) {
            x = (x * x + c) % n;
            y = (y * y + c) % n;
            y = (y * y + c) % n;

            BigInt diff = (x > y) ? (x - y) : (y - x);
            mpz_gcd(d.get_mpz_t(), diff.get_mpz_t(), n.get_mpz_t());

            if (d == n) break;
        }

        if (d > 1 && d < n) return d;
    }
}

static void factor_map_big(BigInt n, std::map<BigInt, int>& f) {
    if (n <= 1) return;

    if (is_probable_prime_big(n)) {
        f[n]++;
        return;
    }

    BigInt d = pollard_rho_big(n);
    factor_map_big(d, f);
    factor_map_big(n / d, f);
}

static std::vector<BigInt> build_divisors(const std::map<BigInt, int>& f) {
    std::vector<BigInt> divs = {1};
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
    const std::size_t pos_count = divs.size();
    divs.reserve(pos_count * 2);
    for (std::size_t i = 0; i < pos_count; ++i)
        divs.push_back(-divs[i]);
    return divs;
}

static BigInt sigma1_big(const BigInt& n) {
    if (n <= 1) return 1;

    std::map<BigInt, int> f;
    factor_map_big(n, f);

    BigInt total = 1;
    for (const auto& [p, e] : f) {
        BigInt term = 1;
        BigInt p_pow = 1;
        for (int i = 0; i < e; ++i) {
            p_pow *= p;
            term += p_pow;
        }
        total *= term;
    }
    return total;
}

static inline BigInt get_sigma(std::uint64_t k) {
    return sigma1_big(u64_to_bigint(k));
}

// ---------------------------------------------------------------------------
// k filter
// ---------------------------------------------------------------------------
static inline bool accept_k(std::uint64_t k) {
    if (USE_BANNED_K_PRIME_FILTER) {
        for (std::size_t i = 0; i < BANNED_K_PRIMES_COUNT; ++i) {
            const std::uint64_t p = BANNED_K_PRIMES[i];
            if (p > 1 && k % p == 0) return false;
        }
    }
    if (USE_REQUIRED_K_PRIME_FILTER) {
        for (std::size_t i = 0; i < REQUIRED_K_PRIMES_COUNT; ++i) {
            const std::uint64_t p = REQUIRED_K_PRIMES[i];
            if (p > 1 && k % p != 0) return false;
        }
    }
    return true;
}

// ---------------------------------------------------------------------------
// Load skipped k values from file for retry mode.
// ---------------------------------------------------------------------------
static std::vector<std::uint64_t> load_skipped_ks(const char* path) {
    std::vector<std::uint64_t> ks;
    std::ifstream in(path);
    if (!in) return ks;
    std::string line;
    while (std::getline(in, line)) {
        if (line.empty()) continue;
        std::istringstream iss(line);
        std::uint64_t k = 0;
        if (iss >> k) ks.push_back(k);
    }
    return ks;
}

// ---------------------------------------------------------------------------
// Factorisation helpers (output formatting only)
// ---------------------------------------------------------------------------
static std::vector<std::pair<BigInt, int>> factor_terms_bigint(BigInt n) {
    std::vector<std::pair<BigInt, int>> terms;
    if (n <= 1) return terms;

    std::map<BigInt, int> f;
    factor_map_big(n, f);
    for (const auto& kv : f) terms.push_back(kv);
    return terms;
}

static std::string terms_to_factorization(
    const std::vector<std::pair<BigInt, int>>& terms,
    const BigInt& original)
{
    if (terms.empty()) return "1";

    BigInt residue = original;
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

    if (residue > 1) {
        if (!first) out += "*";
        out += residue.get_str();
    }
    return out;
}

struct PairHash {
    std::size_t operator()(const std::pair<BigInt, BigInt>& p) const noexcept {
        std::hash<std::string> h;
        std::size_t h1 = h(p.first.get_str()), h2 = h(p.second.get_str());
        return h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
    }
};

struct SolveResult {
    std::vector<std::pair<BigInt, BigInt>> pairs;
    bool timed_out = false;
};

// ---------------------------------------------------------------------------
// solve_k — fully GMP arithmetic, primality, factorization, divisor walk.
//
// Seeks amicable pairs (k*P1*P2, k*P3*P4*P5).
// ---------------------------------------------------------------------------
static SolveResult solve_k(std::uint64_t k, int timeout_seconds) {
    const BigInt A1 = u64_to_bigint(k);
    const BigInt A2 = get_sigma(k);

    if (BigInt(2) * A1 <= A2) return {};

    std::unordered_set<std::pair<BigInt, BigInt>, PairHash> seen;
    SolveResult result;

    const auto deadline =
        std::chrono::steady_clock::now() + std::chrono::seconds(timeout_seconds);
    int timeout_ctr = 0;
    auto check_timeout = [&]() -> bool {
        if (result.timed_out) return true;
        if (++timeout_ctr % TIMEOUT_CHECK_INTERVAL != 0) return false;
        if (std::chrono::steady_clock::now() >= deadline) {
            result.timed_out = true;
            return true;
        }
        return false;
    };

    const double A1d = A1.get_d();
    const double A2d = A2.get_d();

    // P1 upper bound: P1 < A2 / (2*A1 - A2)
    const BigInt denom_p1 = BigInt(2) * A1 - A2;
    if (denom_p1 <= 0) return result;

    const double denom_p1_d = denom_p1.get_d();
    if (denom_p1_d == 0.0) return result;

    const BigInt P1_Max_b = ceil_double_to_bigint(A2d / denom_p1_d);
    if (P1_Max_b < 2) return result;

    // compute_bnd(P1d, P3d): P4 upper bound for given (P1, P3).
    auto compute_bnd = [&](double P1d, double P3d) -> double {
        double disc =
            (A1d*A1d - A1d*A2d)*P1d*P1d*P1d
            - A1d*A2d*P1d
            + (A1d*A1d - 2.0*A1d*A2d)*P1d*P1d
            - ((A1d*A1d - A1d*A2d)*P1d*P1d - A1d*A2d
               + (A1d*A1d - 2.0*A1d*A2d)*P1d)*P3d*P3d
            + ((2.0*A1d*A1d - A1d*A2d)*P1d*P1d*P1d + A1d*A2d*P1d
               + (2.0*A1d*A1d - A1d*A2d)*P1d*P1d + A1d*A2d)*P3d;
        if (disc < 0.0) return -1.0;
        double den = (A1d - A2d)*P1d
                   + ((2.0*A1d - A2d)*P1d + A1d - A2d)*P3d - A2d;
        if (den == 0.0) return -1.0;
        return -((A1d - A2d)*P1d + ((A1d - A2d)*P1d - A2d)*P3d - A2d
                - std::sqrt(disc)) / den;
    };

    BigInt P1 = 1;
    while (true) {
        if (check_timeout()) break;

        P1 = next_prime_big(P1);
        if (P1 >= P1_Max_b) break;

        if (divisible(A1, P1)) continue;

        const double P1d = P1.get_d();

        // dP1 denominator for P3MM
        const double dP1 = (2.0*A1d - A2d)*P1d + A1d - A2d;
        if (dP1 == 0.0) continue;

        // d0: discriminant for P3 bound at P4→∞
        const double d0 =
            -A1d*A1d*P1d*P1d + A1d*A2d*P1d*P1d
            - A1d*A1d*P1d + 2.0*A1d*A2d*P1d + A1d*A2d;
        if (d0 < 0.0) continue;

        // P3MM: asymptotic max P3 as P4→∞
        const double P3MM = -((A1d - A2d)*P1d - A2d - std::sqrt(d0)) / dP1;
        if (P3MM < 2.0) continue;

        // P3 loop ceiling = compute_bnd(P1, P3MM)
        const double bnd_at_P3MM = compute_bnd(P1d, P3MM);
        if (bnd_at_P3MM < 2.0) continue;

        const BigInt P3_loop_max_b = ceil_double_to_bigint(bnd_at_P3MM);

        // Extra factors from A1*(P1+1), merged into each factorisation for this P1.
        std::map<BigInt, int> extra;
        {
            BigInt val = A1 * (P1 + 1);
            factor_map_big(val, extra);
        }

        // Coefficients: abs_val = a_coef*P3^2 + b_coef*P3 + c_coef
        const BigInt a_coef = (-A1 * P1) + (A2 * P1) + A2;
        const BigInt b_coef = (BigInt(2) * A1 * P1 * P1) - (A2 * P1 * P1) + A2;
        const BigInt c_coef = (A1 * P1 * P1) - (A2 * P1 * P1) - (A2 * P1);

        BigInt P3 = 1;
        while (true) {
            if (check_timeout()) goto done_k;

            P3 = next_prime_big(P3);
            if (P3 > P3_loop_max_b) break;

            if (divisible(A1, P3)) continue;

            const double P3d = P3.get_d();

            // P4 upper bound for this (P1, P3)
            const double bnd = compute_bnd(P1d, P3d);

            const BigInt dP4 =
                (A1 - A2)*P1 + ((BigInt(2)*A1 - A2)*P1 + A1 - A2)*P3 - A2;
            if (dP4 == 0) continue;

            const BigInt val_ = a_coef * P3 * P3 + b_coef * P3 + c_coef;
            if (val_ == 0) continue;

            BigInt abs_val = val_;
            if (abs_val < 0) abs_val = -abs_val;

            std::map<BigInt, int> f = extra;
            factor_map_big(abs_val, f);
            const auto all_divs = build_divisors(f);

            const BigInt num_base =
                -((A1 - A2)*P1 + ((A1 - A2)*P1 - A2)*P3 - A2);

            for (const BigInt& F : all_divs) {
                if (check_timeout()) goto done_k;

                const BigInt nF = num_base + F;

                // Quick float bound check.
                if (bnd >= 0.0) {
                    double p4_approx = nF.get_d() / dP4.get_d();
                    if (p4_approx > bnd + 1.0) continue;
                }

                if (!divisible(nF, dP4)) continue;
                const BigInt P4 = nF / dP4;
                if (P4 <= 1) continue;

                if (!is_probable_prime_big(P4)) continue;
                if (divisible(A1, P4)) continue;

                // Compute P2
                const BigInt dP2 =
                    (A1 - A2)*P1
                    + ((A1 - A2)*P1 - A2)*P3
                    + ((A1 - A2)*P1 + ((BigInt(2)*A1 - A2)*P1 + A1 - A2)*P3 - A2)*P4
                    - A2;
                if (dP2 == 0) continue;

                const BigInt P2_num =
                    (A1*P3*P3 + A1*P3)*P4*P4
                    + A2*P1
                    + (A2*P1 + A2)*P3
                    + (A1*P3*P3 + A2*P1
                       - ((A1 - A2)*P1 - A2)*P3 + A2)*P4
                    + A2;

                if (!divisible(P2_num, dP2)) continue;
                const BigInt P2 = P2_num / dP2;
                if (P2 <= 1) continue;
                if (!is_probable_prime_big(P2)) continue;
                if (divisible(A1, P2)) continue;

                // Compute P5
                const BigInt dP5 = (P3 + 1)*P4 + (P3 + 1);
                if (dP5 == 0) continue;

                const BigInt P5_num =
                    (P1 + 1)*P2 - (P3 + 1)*P4 + (P1 - P3);

                if (!divisible(P5_num, dP5)) continue;
                const BigInt P5 = P5_num / dP5;
                if (P5 <= 1) continue;
                if (!is_probable_prime_big(P5)) continue;
                if (divisible(A1, P5)) continue;

                // All five primes must be pairwise distinct.
                if (P1 == P2) continue;
                if (P3 == P4 || P3 == P5 || P4 == P5) continue;

                const BigInt n1_b = A1 * P1 * P2;
                const BigInt n2_b = A1 * P3 * P4 * P5;
                const auto pair = std::make_pair(n1_b, n2_b);
                if (seen.insert(pair).second)
                    result.pairs.push_back(pair);
            }
        }
    }

done_k:
    return result;
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------
int main() {
    if (!RETRY_FROM_SKIPPED_FILE && END_K <= START_K) {
        std::cerr << "END_K must be greater than START_K\n"; return 1;
    }
    if (WORKERS < 1) { std::cerr << "WORKERS must be >= 1\n"; return 1; }

    for (std::size_t i = 0; i < BANNED_K_PRIMES_COUNT; ++i)
        for (std::size_t j = 0; j < REQUIRED_K_PRIMES_COUNT; ++j)
            if (BANNED_K_PRIMES[i] == REQUIRED_K_PRIMES[j] && BANNED_K_PRIMES[i] > 1) {
                std::cerr << "Error: prime " << BANNED_K_PRIMES[i]
                          << " is in both BANNED_K_PRIMES and REQUIRED_K_PRIMES.\n";
                return 1;
            }

    if (USE_BANNED_K_PRIME_FILTER && BANNED_K_PRIMES_COUNT > 0) {
        std::cerr << "Banned k primes:   {";
        for (std::size_t i = 0; i < BANNED_K_PRIMES_COUNT; ++i) {
            if (i) std::cerr << ", ";
            std::cerr << BANNED_K_PRIMES[i];
        }
        std::cerr << "}\n";
    }
    if (USE_REQUIRED_K_PRIME_FILTER && REQUIRED_K_PRIMES_COUNT > 0) {
        std::cerr << "Required k primes: {";
        for (std::size_t i = 0; i < REQUIRED_K_PRIMES_COUNT; ++i) {
            if (i) std::cerr << ", ";
            std::cerr << REQUIRED_K_PRIMES[i];
        }
        std::cerr << "}\n";
    }

    std::vector<std::uint64_t> retry_list;
    if (RETRY_FROM_SKIPPED_FILE) {
        auto loaded = load_skipped_ks(SKIPPED_FILE);
        for (std::uint64_t k : loaded)
            if (accept_k(k)) retry_list.push_back(k);
        std::cerr << "Retry mode: " << retry_list.size()
                  << " k values loaded from " << SKIPPED_FILE << "\n";
    }

    std::atomic<std::uint64_t> next_k{START_K};
    std::atomic<std::size_t>   next_retry_idx{0};
    std::atomic<std::uint64_t> done_k{0};
    std::atomic<std::uint64_t> skipped_k{0};
    std::atomic<std::uint64_t> rec_no{0};
    std::atomic<bool>          stop_monitor{false};

    std::vector<std::uint64_t> unresolved_skips;
    std::mutex out_mu;

    std::ofstream out(OUTPUT_FILE, std::ios::out | std::ios::app);
    if (!out) { std::cerr << "Failed opening output file: " << OUTPUT_FILE << "\n"; return 1; }

    std::vector<std::thread> threads;
    threads.reserve(static_cast<std::size_t>(WORKERS));
    const auto t0 = std::chrono::steady_clock::now();

    std::thread monitor([&]() {
        while (!stop_monitor.load(std::memory_order_relaxed)) {
            const auto elapsed =
                std::chrono::duration_cast<std::chrono::seconds>(
                    std::chrono::steady_clock::now() - t0).count();
            const std::uint64_t completed = done_k.load(std::memory_order_relaxed);
            {
                std::ofstream st(STATUS_FILE, std::ios::out | std::ios::trunc);
                st << "running\n"
                   << "completed_k=" << completed << "\n"
                   << "current_k="   << next_k.load(std::memory_order_relaxed) << "\n"
                   << "end_k="       << END_K << "\n"
                   << "elapsed_sec=" << elapsed << "\n"
                   << "records="     << rec_no.load(std::memory_order_relaxed) << "\n"
                   << "skipped_k="   << skipped_k.load(std::memory_order_relaxed) << "\n";
            }
            std::cerr << "[heartbeat] solved=" << completed
                      << " k~" << next_k.load(std::memory_order_relaxed)
                      << "/" << END_K
                      << " elapsed=" << elapsed << "s\n";
            std::this_thread::sleep_for(std::chrono::seconds(HEARTBEAT_SECONDS));
        }
    });

    for (int w = 0; w < WORKERS; ++w) {
        threads.emplace_back([&]() {
            while (true) {
                std::uint64_t k;

                if (RETRY_FROM_SKIPPED_FILE) {
                    const std::size_t idx = next_retry_idx.fetch_add(1);
                    if (idx >= retry_list.size()) break;
                    k = retry_list[idx];
                } else {
                    while (true) {
                        k = next_k.fetch_add(1);
                        if (k >= END_K) goto done;
                        if (accept_k(k)) break;
                    }
                }

                {
                    auto solve = solve_k(k, MAX_SECONDS_PER_K);

                    std::lock_guard<std::mutex> lock(out_mu);
                    done_k.fetch_add(1, std::memory_order_relaxed);

                    if (solve.timed_out) {
                        skipped_k.fetch_add(1, std::memory_order_relaxed);
                        unresolved_skips.push_back(k);
                        std::cerr << "[skip] k=" << k
                                  << " exceeded " << MAX_SECONDS_PER_K << "s\n";
                        std::ofstream skipped_append(SKIPPED_FILE, std::ios::out | std::ios::app);
                        if (skipped_append)
                            skipped_append << k << " timeout>" << MAX_SECONDS_PER_K << "s\n";
                    }

                    if (PRINT_K) std::cout << k << '\n';

                    for (const auto& [n1, n2] : solve.pairs) {
                        std::cout << k << ' ' << n1.get_str() << ' ' << n2.get_str() << '\n';

                        const BigInt smaller = (n1 < n2) ? n1 : n2;
                        const BigInt larger  = (n1 < n2) ? n2 : n1;
                        const auto small_terms = factor_terms_bigint(smaller);
                        const auto large_terms = factor_terms_bigint(larger);

                        std::size_t i = 0, j = 0;
                        int unique_small = 0, unique_large = 0;
                        while (i < small_terms.size() && j < large_terms.size()) {
                            if      (small_terms[i].first == large_terms[j].first) { ++i; ++j; }
                            else if (small_terms[i].first <  large_terms[j].first) { ++unique_small; ++i; }
                            else                                                    { ++unique_large; ++j; }
                        }
                        unique_small += static_cast<int>(small_terms.size() - i);
                        unique_large += static_cast<int>(large_terms.size() - j);

                        rec_no.fetch_add(1, std::memory_order_relaxed);
                        out << unique_small << unique_large << " Chesnut 2026\n";
                        out << smaller.get_str() << "=" << terms_to_factorization(small_terms, smaller) << "\n";
                        out << larger.get_str()  << "=" << terms_to_factorization(large_terms,  larger)  << "\n\n";
                        out.flush();
                    }
                }
                continue;
                done: break;
            }
        });
    }

    for (auto& t : threads) t.join();
    stop_monitor.store(true, std::memory_order_relaxed);
    monitor.join();

    {
        const auto elapsed =
            std::chrono::duration_cast<std::chrono::seconds>(
                std::chrono::steady_clock::now() - t0).count();
        std::ofstream st(STATUS_FILE, std::ios::out | std::ios::trunc);
        st << "done\n"
           << "completed_k=" << done_k.load()    << "\n"
           << "elapsed_sec=" << elapsed          << "\n"
           << "records="     << rec_no.load()    << "\n"
           << "skipped_k="   << skipped_k.load() << "\n";
        std::cerr << "[done] " << rec_no.load() << " records, "
                  << skipped_k.load() << " skipped, " << elapsed << "s\n";
    }

    if (!unresolved_skips.empty())
        std::cerr << "[warn] " << unresolved_skips.size()
                  << " items timed out. Run with RETRY_FROM_SKIPPED_FILE=true to retry.\n";

    return 0;
}