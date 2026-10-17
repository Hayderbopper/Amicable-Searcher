#include "general.h"

#include "divisors.h"
#include "external_factoring.h"
#include "introots.h"
#include "numeric_utils.h"

#include "prime_iterator.h"
#include <primesieve.hpp>

#include <algorithm>
#include <functional>
#include <cmath>
#include <cstdio>
#include <cstdint>
#include <climits>
#include <limits>
#include <memory>
#include <mutex>
#include <sstream>
#include <stdexcept>

namespace amicable {

namespace {

using u64 = std::uint64_t;

// prime ranges this short are scanned directly in the divisor tail
constexpr u64 SCAN_WINDOW = 1024;

#ifdef AMICABLE_STATS
struct Stats {
    std::atomic<u64> d3{0}, d3_scan{0}, d3_native{0}, d3_big{0}, d3_divs{0}, d3_mbits{0}, d3_absbits{0},
        d3_rbits{0}, d3_tbits{0}, prog{0}, prog_cand{0}, same{0}, mixed{0}, ranges{0}, children{0}, procs{0};
    ~Stats() {
        std::fprintf(stderr, "[stats] d3=%llu scan=%llu native=%llu big=%llu avg_divs=%.1f avg_mbits=%.1f avg_absbits=%.1f avg_Rbits=%.1f avg_Tcof_bits=%.1f prog=%llu cand=%llu same=%llu mixed=%llu\n",
            (unsigned long long)d3, (unsigned long long)d3_scan, (unsigned long long)d3_native, (unsigned long long)d3_big,
            d3 ? double(d3_divs) / double(d3_native + d3_big + 1) : 0.0,
            d3 ? double(d3_mbits) / double(d3_native + d3_big + 1) : 0.0,
            d3 ? double(d3_absbits) / double(d3_native + d3_big + 1) : 0.0,
            d3 ? double(d3_rbits) / double(d3_native + d3_big + 1) : 0.0,
            d3 ? double(d3_tbits) / double(d3_native + d3_big + 1) : 0.0,
            (unsigned long long)prog, (unsigned long long)prog_cand, (unsigned long long)same, (unsigned long long)mixed);
        std::fprintf(stderr, "[stats] ranges=%llu children=%llu process=%llu\n", (unsigned long long)ranges,
            (unsigned long long)children, (unsigned long long)procs);
    }
} g_stats;
#define STATADD(x, v) (g_stats.x += (v))
#else
#define STATADD(x, v) ((void)0)
#endif

// ---------------------------------------------------------------------------
// numeric helpers
// ---------------------------------------------------------------------------
[[nodiscard]] inline bool big_fits_u64(const BigInt& v) {
    return v >= 0 && mpz_sizeinbase(v.get_mpz_t(), 2) <= 64;
}

[[nodiscard]] inline u64 big_to_u64(const BigInt& v) { return bigint_to_u64(v); }

// v = w, reusing v's limbs (u64_to_bigint builds a new number; unsigned long is
// only 32 bits on Windows, hence the import for larger values)
inline void set_u64(BigInt& v, u64 w) {
    if (w <= ULONG_MAX) mpz_set_ui(v.get_mpz_t(), static_cast<unsigned long>(w));
    else mpz_import(v.get_mpz_t(), 1, -1, sizeof(w), 0, 0, &w);
}

// sign of v - w without building a BigInt for w
[[nodiscard]] inline int cmp_u64(const BigInt& v, u64 w) {
    if (mpz_sgn(v.get_mpz_t()) < 0) return -1;
    if (mpz_sizeinbase(v.get_mpz_t(), 2) > 64) return 1;
    const u64 x = big_to_u64(v);
    return (x < w) ? -1 : (x > w) ? 1 : 0;
}

// v = max(v, w)
inline void raise_to(BigInt& v, u64 w) {
    if (cmp_u64(v, w) < 0) v = u64_to_bigint(w);
}

[[nodiscard]] bool big_to_u128(const BigInt& v, u128& out) {
    if (v < 0 || mpz_sizeinbase(v.get_mpz_t(), 2) > 128) return false;
    std::uint64_t words[2] = {0, 0};
    std::size_t count = 0;
    mpz_export(words, &count, -1, sizeof(std::uint64_t), 0, 0, v.get_mpz_t());
    out = static_cast<u128>(words[0]) | (static_cast<u128>(words[1]) << 64);
    return true;
}

[[nodiscard]] BigInt from_u128(u128 v) {
    const std::uint64_t words[2] = {static_cast<std::uint64_t>(v), static_cast<std::uint64_t>(v >> 64)};
    BigInt out;
    mpz_import(out.get_mpz_t(), words[1] ? 2 : 1, -1, sizeof(std::uint64_t), 0, 0, words);
    return out;
}

[[nodiscard]] BigInt from_i128(i128 v) {
    if (v >= 0) return from_u128(static_cast<u128>(v));
    BigInt out = from_u128(static_cast<u128>(-v));
    return BigInt(-out);
}

[[nodiscard]] bool big_to_i128(const BigInt& v, i128& out) {
    if (mpz_sizeinbase(v.get_mpz_t(), 2) > 127) return false;
    std::uint64_t words[2] = {0, 0};
    std::size_t count = 0;
    mpz_export(words, &count, -1, sizeof(std::uint64_t), 0, 0, v.get_mpz_t());   // |v|
    const u128 m = static_cast<u128>(words[0]) | (static_cast<u128>(words[1]) << 64);
    out = (mpz_sgn(v.get_mpz_t()) < 0) ? -static_cast<i128>(m) : static_cast<i128>(m);
    return true;
}

// n.sx, n.px, n.sy, n.py as 128-bit integers, converted once per node;
// false when one of them does not fit
[[nodiscard]] bool node_nat(const Node& n, i128& A, i128& B, i128& C, i128& D) {
    if (n.nat_state < 0)
        n.nat_state = (big_to_i128(n.sx, n.nat[0]) && big_to_i128(n.px, n.nat[1]) &&
                       big_to_i128(n.sy, n.nat[2]) && big_to_i128(n.py, n.nat[3])) ? 1 : 0;
    if (n.nat_state == 0) return false;
    A = n.nat[0]; B = n.nat[1]; C = n.nat[2]; D = n.nat[3];
    return true;
}

[[nodiscard]] BigInt sigma_pow(const BigInt& p, int e) {
    BigInt s = 1, pw = 1;
    for (int i = 0; i < e; ++i) { pw *= p; s += pw; }
    return s;
}

[[nodiscard]] BigInt pow_big(const BigInt& b, int e) {
    BigInt r;
    mpz_pow_ui(r.get_mpz_t(), b.get_mpz_t(), static_cast<unsigned long>(e));
    return r;
}


[[nodiscard]] double big_d(const BigInt& v) {
    long e = 0;
    const double d = mpz_get_d_2exp(&e, v.get_mpz_t());
    return std::ldexp(d, static_cast<int>(e));
}

// a/b for positive BigInts without overflow (relative error < 3e-16)
[[nodiscard]] double ratio_d(const BigInt& a, const BigInt& b) {
    long ea = 0, eb = 0;
    const double da = mpz_get_d_2exp(&ea, a.get_mpz_t());
    const double db = mpz_get_d_2exp(&eb, b.get_mpz_t());
    return std::ldexp(da / db, static_cast<int>(ea - eb));
}

// floor of a non-negative long double
[[nodiscard]] BigInt ld_floor(long double v) {
    if (!(v > 0)) return 0;
    int e = 0;
    const long double m = std::frexp(v, &e);                 // v = m * 2^e, m in [0.5, 1)
    const auto mant = static_cast<std::uint64_t>(std::ldexp(m, 64));
    BigInt out = u64_to_bigint(mant);
    if (e >= 64) mpz_mul_2exp(out.get_mpz_t(), out.get_mpz_t(), static_cast<mp_bitcnt_t>(e - 64));
    else mpz_fdiv_q_2exp(out.get_mpz_t(), out.get_mpz_t(), static_cast<mp_bitcnt_t>(64 - e));
    return out;
}

[[nodiscard]] BigInt d_floor(double v) {
    return ld_floor(static_cast<long double>(v));
}

// Primality in the general engine: below 2^64 hurchalla's deterministic test
// (2-3 Miller-Rabin bases instead of the 7 of is_prime_u64; the same answer
// for every n), above 2^64 the GMP test of is_probable_prime.
[[nodiscard]] bool prime_test(const BigInt& n) {
    if (n < 2) return false;
    if (mpz_sizeinbase(n.get_mpz_t(), 2) <= 64) return is_prime_u64_fast(bigint_to_u64(n));
    return is_probable_prime(n);
}

[[nodiscard]] bool divides_k(const SearchK& sk, const BigInt& p) {
    if (p > sk.kb) return false;
    return mpz_divisible_p(sk.kb.get_mpz_t(), p.get_mpz_t()) != 0;
}

// ---------------------------------------------------------------------------
// factor lists
// ---------------------------------------------------------------------------
void fac_add(FacList& f, const BigInt& p, int e) {
    if (e == 0) return;
    for (auto& [q, x] : f)
        if (q == p) { x += e; return; }
    f.emplace_back(p, e);
}

void fac_merge(FacList& dst, const FacList& src, int sign = 1) {
    for (const auto& [p, e] : src) fac_add(dst, p, sign * e);
}

const std::vector<u64>& small_primes() {
    static const std::vector<u64> primes = [] {
        std::vector<u64> v;
        primesieve::generate_primes(u64{1} << 16, &v);
        return v;
    }();
    return primes;
}

void factor_u128_into(u128 n, FacList& out) {
    if (n <= 1) return;
    if (n <= std::numeric_limits<std::uint64_t>::max()) {
        U64FactorBuffer ub;
        factorize_runtime_u64(static_cast<std::uint64_t>(n), ub);
        for (std::size_t i = 0; i < ub.size; ++i) fac_add(out, u64_to_bigint(ub[i].prime), ub[i].exponent);
        return;
    }
    U128Factor buf[160];
    int cnt = 0;
    if (!factorize_runtime_u128(n, buf, cnt))
        throw std::runtime_error("128-bit factorisation could not be verified");
    for (int i = 0; i < cnt; ++i) fac_add(out, from_u128(buf[i].prime), buf[i].exponent);
}

// sigma(p^e) factorisations, cached per thread (the small primes recur in every k)
const FacList& cached_sigma_factors(const BigInt& p, int e) {
    static thread_local std::vector<std::pair<std::pair<u64, int>, FacList>> table(1 << 12);
    static thread_local FacList scratch;
    if (!big_fits_u64(p) || e > 60) {
        scratch.clear();
        factor_any(sigma_pow(p, e), scratch);
        return scratch;
    }
    const u64 pv = big_to_u64(p);
    const std::size_t h = static_cast<std::size_t>((pv * 0x9E3779B97F4A7C15ULL + static_cast<u64>(e)) >> 52);
    auto& slot = table[h];
    if (slot.first.first != pv || slot.first.second != e) {
        slot.first = {pv, e};
        slot.second.clear();
        factor_any(sigma_pow(p, e), slot.second);
    }
    return slot.second;
}

bool to_nat(const FacList& f, NatFactors& out) {
    out.clear();
    for (const auto& [p, e] : f) {
        u128 v;
        if (!big_to_u128(p, v)) return false;
        out.add(v, e);
    }
    return true;
}

// sigma(q^e) factored straight into 128-bit primes (false: too big, use FacList)
bool sigma_factors_nat(const BigInt& q, int e, NatFactors& out) {
    out.clear();
    if (!big_fits_u64(q)) return false;
    const u64 qv = big_to_u64(q);
    u128 sv = 0;
    if (e == 1) sv = static_cast<u128>(qv) + 1;
    else if (e == 2 && qv < (u64{1} << 62)) sv = static_cast<u128>(qv) * qv + qv + 1;
    else return false;
    if (sv <= std::numeric_limits<std::uint64_t>::max()) {
        U64FactorBuffer ub;
        factorize_runtime_u64(static_cast<std::uint64_t>(sv), ub);
        for (std::size_t i = 0; i < ub.size; ++i) out.add(ub[i].prime, ub[i].exponent);
        return true;
    }
    U128Factor buf[160];
    int cnt = 0;
    if (!factorize_runtime_u128(sv, buf, cnt)) return false;
    for (int i = 0; i < cnt; ++i) out.add(buf[i].prime, buf[i].exponent);
    return true;
}

void sigma_factors(const BigInt& p, int e, FacList& out) {
    factor_any(e == 1 ? BigInt(p + 1) : sigma_pow(p, e), out);
}

// ---------------------------------------------------------------------------
// interleavings
// ---------------------------------------------------------------------------
void interleave(const std::vector<int>& a, const std::vector<int>& b, std::size_t i, std::size_t j,
                std::vector<int>& cur, std::vector<std::vector<int>>& out) {
    if (i == a.size() && j == b.size()) { out.push_back(cur); return; }
    if (i < a.size()) { cur.push_back(a[i]); interleave(a, b, i + 1, j, cur, out); cur.pop_back(); }
    if (j < b.size()) { cur.push_back(b[j]); interleave(a, b, i, j + 1, cur, out); cur.pop_back(); }
}

std::string slot_name(const Config& cfg, int id) {
    const FreeSlot& s = cfg.slots[static_cast<std::size_t>(id)];
    return std::string(s.side == 0 ? "P" : "Q") + std::to_string(s.pos + 1);
}

// ---------------------------------------------------------------------------
// remaining slots / tail kind
// ---------------------------------------------------------------------------
enum class Tail { None, Done, SameSide, Mixed2, Divisor3, Progression };

struct Rem {
    int n = 0;
    int id[32];
    int side[32];
    int exp[32];
    int count[2] = {0, 0};
};

Rem remaining(const Node& n) {
    Rem r;
    const auto& order = n.root->shape->order;
    for (std::size_t i = static_cast<std::size_t>(n.depth); i < order.size(); ++i) {
        const FreeSlot& s = n.cfg->slots[static_cast<std::size_t>(order[i])];
        r.id[r.n] = order[i];
        r.side[r.n] = s.side;
        r.exp[r.n] = s.exp;
        ++r.count[s.side];
        ++r.n;
    }
    return r;
}

Tail tail_kind(const Rem& r) {
    if (r.n == 0) return Tail::Done;
    if (r.count[0] == 0 || r.count[1] == 0) return Tail::SameSide;
    if (r.n == 2) return (r.exp[0] >= 2 && r.exp[1] >= 2) ? Tail::None : Tail::Mixed2;
    if (r.n == 3 && r.side[1] != r.side[2] && r.exp[0] == 1 && r.exp[1] == 1 && r.exp[2] == 1)
        return Tail::Divisor3;
    if (r.count[r.side[0]] == 1 && r.exp[0] == 1) return Tail::Progression;
    return Tail::None;
}

// ---------------------------------------------------------------------------
// rigorous ranges for the next prime
//
//   x = sigma(N1)/N1,  y = sigma(N2)/N2  must satisfy (x-1)(y-1) = 1, x > 2, y < 2.
//   With the next prime q (slot exponent e on side s) and j0/j1 more primes
//   after it on each side, all > q:
//     upper:  x <= xm(q), y <= ym(q)  (later primes contribute < (q+1)/q each)
//             need xm > 2 and (xm-1)(ym-1) > 1          -> holds only up to some q
//     lower:  x >= xi(q), y >= yi(q)  (q's own factor only)
//             need yi < 2 and (xi-1)(yi-1) < 1          -> holds only from some q on
//   Both are monotone in q; tested exactly with integers.
// ---------------------------------------------------------------------------
struct BoundIn {
    const BigInt* sx;
    const BigInt* px;
    const BigInt* sy;
    const BigInt* py;
    int side, exp, j0, j1;
    double x0l = 0, y0l = 0;               // sx/px, sy/py (relative error < 3e-15)
    // remaining primes only known to be > fl[i] (not > q): each contributes
    // less than (fl+1)/fl on side fside[i]
    int nfl = 0;
    int fside[3] = {0, 0, 0};
    const BigInt* fl[3] = {nullptr, nullptr, nullptr};
    double fl_d[3] = {0, 0, 0};
    void add_float(int side_, const BigInt* L) {
        fside[nfl] = side_;
        fl[nfl] = L;
        fl_d[nfl] = mpz_get_d(L->get_mpz_t());
        ++nfl;
    }
    double float_factor(int side_) const {
        double f = 1.0;
        for (int i = 0; i < nfl; ++i)
            if (fside[i] == side_) f *= 1.0 + 1.0 / fl_d[i];
        return f;
    }
};

double h_ld(double q, int e) {
    double s = 1.0, t = 1.0;
    for (int i = 0; i < e; ++i) { t /= q; s += t; }
    return s;
}

double ipow_ld(double b, int e) {
    double r = 1.0;
    for (int i = 0; i < e; ++i) r *= b;
    return r;
}

// Filtered predicates: the double value decides when it is far from the
// threshold (its relative error is below 1e-15, the margin is 1e-13);
// otherwise the exact integer test below decides.
constexpr double FILTER_EPS = 1e-13;

// The exact tests below work in per-thread scratch numbers: the same integer
// arithmetic as with local temporaries, without a heap allocation per call
// (they run for every bisection step the double pre-screen cannot decide).
struct ExactScratch {
    BigInt XN, XD, YN, YD, sq, qe, t1, t2, t3;
};

ExactScratch& exact_scratch() {
    static thread_local ExactScratch s;
    return s;
}

// sq = sigma(q^e) = 1 + q + ... + q^e,  qe = q^e  (t: scratch)
void sigma_and_pow(const BigInt& q, int e, BigInt& sq, BigInt& qe) {
    mpz_set_ui(sq.get_mpz_t(), 1);
    mpz_set_ui(qe.get_mpz_t(), 1);
    for (int i = 0; i < e; ++i) {
        mpz_mul(qe.get_mpz_t(), qe.get_mpz_t(), q.get_mpz_t());
        mpz_add(sq.get_mpz_t(), sq.get_mpz_t(), qe.get_mpz_t());
    }
}

bool upper_ok_exact(const BoundIn& in, const BigInt& q) {
    ExactScratch& S = exact_scratch();
    BigInt &XN = S.XN, &XD = S.XD, &YN = S.YN, &YD = S.YD, &t1 = S.t1, &t2 = S.t2;
    XN = *in.sx; XD = *in.px; YN = *in.sy; YD = *in.py;
    sigma_and_pow(q, in.exp, S.sq, S.qe);
    if (in.side == 0) { XN *= S.sq; XD *= S.qe; } else { YN *= S.sq; YD *= S.qe; }
    if (in.j0 > 0 || in.j1 > 0) {
        mpz_add_ui(t1.get_mpz_t(), q.get_mpz_t(), 1);                          // (q+1)^j, q^j
        if (in.j0 > 0) {
            mpz_pow_ui(t2.get_mpz_t(), t1.get_mpz_t(), static_cast<unsigned long>(in.j0)); XN *= t2;
            mpz_pow_ui(t2.get_mpz_t(), q.get_mpz_t(), static_cast<unsigned long>(in.j0)); XD *= t2;
        }
        if (in.j1 > 0) {
            mpz_pow_ui(t2.get_mpz_t(), t1.get_mpz_t(), static_cast<unsigned long>(in.j1)); YN *= t2;
            mpz_pow_ui(t2.get_mpz_t(), q.get_mpz_t(), static_cast<unsigned long>(in.j1)); YD *= t2;
        }
    }
    for (int i = 0; i < in.nfl; ++i) {
        mpz_add_ui(t1.get_mpz_t(), in.fl[i]->get_mpz_t(), 1);
        if (in.fside[i] == 0) { XN *= t1; XD *= *in.fl[i]; }
        else { YN *= t1; YD *= *in.fl[i]; }
    }
    mpz_mul_2exp(t1.get_mpz_t(), XD.get_mpz_t(), 1);                         // XN <= 2 XD
    if (mpz_cmp(XN.get_mpz_t(), t1.get_mpz_t()) <= 0) return false;
    if (mpz_cmp(YN.get_mpz_t(), YD.get_mpz_t()) <= 0) return false;
    mpz_sub(t1.get_mpz_t(), XN.get_mpz_t(), XD.get_mpz_t());                 // (XN-XD)(YN-YD) > XD YD
    mpz_sub(t2.get_mpz_t(), YN.get_mpz_t(), YD.get_mpz_t());
    mpz_mul(t1.get_mpz_t(), t1.get_mpz_t(), t2.get_mpz_t());
    mpz_mul(S.t3.get_mpz_t(), XD.get_mpz_t(), YD.get_mpz_t());
    return mpz_cmp(t1.get_mpz_t(), S.t3.get_mpz_t()) > 0;
}

bool lower_ok_exact(const BoundIn& in, const BigInt& q) {
    ExactScratch& S = exact_scratch();
    BigInt &xn = S.XN, &xd = S.XD, &yn = S.YN, &yd = S.YD, &t1 = S.t1, &t2 = S.t2;
    xn = *in.sx; xd = *in.px; yn = *in.sy; yd = *in.py;
    sigma_and_pow(q, in.exp, S.sq, S.qe);
    if (in.side == 0) { xn *= S.sq; xd *= S.qe; } else { yn *= S.sq; yd *= S.qe; }
    mpz_mul_2exp(t1.get_mpz_t(), yd.get_mpz_t(), 1);                         // yn >= 2 yd
    if (mpz_cmp(yn.get_mpz_t(), t1.get_mpz_t()) >= 0) return false;
    mpz_sub(t1.get_mpz_t(), xn.get_mpz_t(), xd.get_mpz_t());                 // (xn-xd)(yn-yd) < xd yd
    mpz_sub(t2.get_mpz_t(), yn.get_mpz_t(), yd.get_mpz_t());
    mpz_mul(t1.get_mpz_t(), t1.get_mpz_t(), t2.get_mpz_t());
    mpz_mul(S.t3.get_mpz_t(), xd.get_mpz_t(), yd.get_mpz_t());
    return mpz_cmp(t1.get_mpz_t(), S.t3.get_mpz_t()) < 0;
}

// 1: true, 0: false, -1: too close to call in double
// A safe relative error margin for the double evaluations below: each one
// takes at most about 6 (e + j0 + j1 + floats + 3) rounding steps of 2^-53.
inline double filter_eps(int ops) {
    return std::max(FILTER_EPS, 16.0 * (ops + 3) * 0x1p-53);
}

int upper_filter(const BoundIn& in, double ql) {
    const double eps = filter_eps(in.exp + in.j0 + in.j1 + in.nfl);
    const double h = h_ld(ql, in.exp), B = 1.0 + 1.0 / ql;
    double Fx = 1.0, Fy = 1.0;
    for (int i = 0; i < in.nfl; ++i) (in.fside[i] == 0 ? Fx : Fy) *= 1.0 + 1.0 / in.fl_d[i];
    const double X = in.x0l * (in.side == 0 ? h : 1.0) * ipow_ld(B, in.j0) * Fx;
    const double Y = in.y0l * (in.side == 1 ? h : 1.0) * ipow_ld(B, in.j1) * Fy;
    if (X < 2.0 * (1.0 - eps)) return 0;
    if (X > 2.0 * (1.0 + eps)) {
        const double prod = (X - 1.0) * (Y - 1.0), err = 4.0 * eps * X * Y;
        if (prod > 1.0 + err) return 1;
        if (prod < 1.0 - err) return 0;
    }
    return -1;
}

int lower_filter(const BoundIn& in, double ql) {
    const double eps = filter_eps(in.exp);
    const double h = h_ld(ql, in.exp);
    const double X = in.x0l * (in.side == 0 ? h : 1.0);
    const double Y = in.y0l * (in.side == 1 ? h : 1.0);
    if (Y > 2.0 * (1.0 + eps)) return 0;
    if (Y < 2.0 * (1.0 - eps)) {
        const double prod = (X - 1.0) * (Y - 1.0), err = 4.0 * eps * X * Y;
        if (prod < 1.0 - err) return 1;
        if (prod > 1.0 + err) return 0;
    }
    return -1;
}

bool upper_ok(const BoundIn& in, const BigInt& q) {
    const int f = upper_filter(in, big_d(q));
    return f >= 0 ? f == 1 : upper_ok_exact(in, q);
}

bool lower_ok(const BoundIn& in, const BigInt& q) {
    const int f = lower_filter(in, big_d(q));
    return f >= 0 ? f == 1 : lower_ok_exact(in, q);
}

// the same for a 64-bit q (the double of a u64 is within 1.2e-16 relative)
// q as a BigInt in a per-thread number (unsigned long is 32 bits on Windows)
const BigInt& q_big(u64 q) {
    static thread_local BigInt b;
    if (q <= ULONG_MAX) mpz_set_ui(b.get_mpz_t(), static_cast<unsigned long>(q));
    else mpz_import(b.get_mpz_t(), 1, -1, sizeof(q), 0, 0, &q);
    return b;
}

bool upper_ok_q(const BoundIn& in, u64 q) {
    const int f = upper_filter(in, static_cast<double>(q));
    return f >= 0 ? f == 1 : upper_ok_exact(in, q_big(q));
}

bool lower_ok_q(const BoundIn& in, u64 q) {
    const int f = lower_filter(in, static_cast<double>(q));
    return f >= 0 ? f == 1 : lower_ok_exact(in, q_big(q));
}

struct BoundLd {
    double x0, y0;
    int side, exp, j0, j1;
    double fx = 1.0, fy = 1.0;             // the floating prime's factor
};

bool upper_ok_ld(const BoundLd& b, double q) {
    const double h = h_ld(q, b.exp), B = 1.0 + 1.0 / q;
    double X = b.x0 * (b.side == 0 ? h : 1.0) * ipow_ld(B, b.j0) * b.fx;
    double Y = b.y0 * (b.side == 1 ? h : 1.0) * ipow_ld(B, b.j1) * b.fy;
    return X > 2.0 && Y > 1.0 && (X - 1.0) * (Y - 1.0) > 1.0;
}

bool lower_ok_ld(const BoundLd& b, double q) {
    const double h = h_ld(q, b.exp);
    const double X = b.x0 * (b.side == 0 ? h : 1.0);
    const double Y = b.y0 * (b.side == 1 ? h : 1.0);
    return Y < 2.0 && (X - 1.0) * (Y - 1.0) < 1.0;
}

// ---- fast estimates of the bounds --------------------------------------------
// In t = 1/q every factor is a polynomial in t with non-negative coefficients,
// so X(t) - c, Y(t) - c and (X-1)(Y-1) - 1 are increasing and convex for t >= 0
// (X, Y >= 1).  Newton's method started right of a root (the linearisation at
// 0 lands there, by convexity) converges monotonically to it.  These are only
// estimates: the exact integer search that follows decides.
struct LdEval { double X, dX, Y, dY; };

void eval_xy(const BoundLd& b, double t, bool upper, LdEval& o) {
    double h = 1.0, dh = 0.0, tp = 1.0;
    for (int i = 1; i <= b.exp; ++i) { dh += i * tp; tp *= t; h += tp; }
    const double lh = dh / h;
    double X = b.x0, Y = b.y0, lx = 0.0, ly = 0.0;
    if (b.side == 0) { X *= h; lx += lh; } else { Y *= h; ly += lh; }
    if (upper) {
        const double B = 1.0 + t;
        X *= ipow_ld(B, b.j0) * b.fx;
        Y *= ipow_ld(B, b.j1) * b.fy;
        lx += b.j0 / B;
        ly += b.j1 / B;
    }
    o.X = X; o.Y = Y; o.dX = X * lx; o.dY = Y * ly;
}

// smallest t >= 0 with f(t) > 0 for an increasing convex f: 0 when f(0) > 0,
// +inf when f is constant and <= 0, NaN when undecidable here
template <class F>
double convex_root(F&& f, bool depends) {
    double v, dv;
    f(0.0, v, dv);
    if (v > 0.0) return 0.0;
    if (!depends) return std::numeric_limits<double>::infinity();
    if (!(dv > 0.0)) return std::numeric_limits<double>::quiet_NaN();
    double t = -v / dv;
    for (int it = 0; it < 100; ++it) {
        f(t, v, dv);
        if (!(dv > 0.0)) return std::numeric_limits<double>::quiet_NaN();
        const double step = v / dv;
        if (!(step > t * 1e-15)) break;
        t -= step;
    }
    return t;
}

// upper_ok_ld holds exactly for t > upper_root_t (q < 1/t)
double upper_root_t(const BoundLd& b) {
    LdEval e;
    const bool dx = b.side == 0 || b.j0 > 0, dy = b.side == 1 || b.j1 > 0;
    const double rx = convex_root([&](double t, double& v, double& dv) {
        eval_xy(b, t, true, e); v = e.X - 2.0; dv = e.dX; }, dx);
    const double ry = convex_root([&](double t, double& v, double& dv) {
        eval_xy(b, t, true, e); v = e.Y - 1.0; dv = e.dY; }, dy);
    const double rg = convex_root([&](double t, double& v, double& dv) {
        eval_xy(b, t, true, e);
        v = (e.X - 1.0) * (e.Y - 1.0) - 1.0;
        dv = e.dX * (e.Y - 1.0) + (e.X - 1.0) * e.dY; }, true);
    if (std::isnan(rx) || std::isnan(ry) || std::isnan(rg)) return std::numeric_limits<double>::quiet_NaN();
    return std::max(rx, std::max(ry, rg));
}

// lower_ok_ld holds exactly for t < lower_root_t (q > 1/t)
double lower_root_t(const BoundLd& b) {
    LdEval e;
    const double ry = convex_root([&](double t, double& v, double& dv) {
        eval_xy(b, t, false, e); v = e.Y - 2.0; dv = e.dY; }, b.side == 1);
    const double rg = convex_root([&](double t, double& v, double& dv) {
        eval_xy(b, t, false, e);
        v = (e.X - 1.0) * (e.Y - 1.0) - 1.0;
        dv = e.dX * (e.Y - 1.0) + (e.X - 1.0) * e.dY; }, true);
    if (std::isnan(ry) || std::isnan(rg)) return std::numeric_limits<double>::quiet_NaN();
    return std::min(ry, rg);
}

constexpr double REFINE_LIMIT = 1.8e19;

// exact largest q >= q0 with upper_ok (upper_ok(q0) is known to be true),
// starting from the estimate qe.  false: give up (the caller's general code runs).
bool refine_upper(const BoundIn& in, u64 q0, double qe, u64& out) {
    const double dlo = std::floor(qe * (1.0 - 1e-12)) - 2.0, dhi = std::ceil(qe * (1.0 + 1e-12)) + 2.0;
    if (!(dhi < REFINE_LIMIT)) return false;
    u64 lo = (dlo <= static_cast<double>(q0)) ? q0 : static_cast<u64>(dlo);   // want: true
    u64 hi = static_cast<u64>(dhi);                                             // want: false
    if (hi <= lo) hi = lo + 1;
    u64 step = hi - lo;
    for (int guard = 0; upper_ok_q(in, hi); ++guard) {
        if (guard > 70 || hi > (u64(1) << 62) || step > (u64(1) << 61)) return false;
        lo = hi;
        hi += step;
        step *= 2;
    }
    step = std::max<u64>(hi - lo, 1);
    while (lo > q0 && !upper_ok_q(in, lo)) {
        hi = lo;
        lo = (lo - q0 > step) ? lo - step : q0;
        step *= 2;
    }
    while (hi - lo > 1) {
        const u64 m = lo + (hi - lo) / 2;
        if (upper_ok_q(in, m)) lo = m; else hi = m;
    }
    out = lo;
    return true;
}

// exact smallest q > q0 with lower_ok (lower_ok(q0) is known to be false)
bool refine_lower(const BoundIn& in, u64 q0, double qe, u64& out) {
    const double dlo = std::floor(qe * (1.0 - 1e-12)) - 2.0, dhi = std::ceil(qe * (1.0 + 1e-12)) + 2.0;
    if (!(dhi < REFINE_LIMIT)) return false;
    u64 lo = (dlo <= static_cast<double>(q0)) ? q0 : static_cast<u64>(dlo);   // want: false
    u64 hi = static_cast<u64>(dhi);                                             // want: true
    if (hi <= lo) hi = lo + 1;
    u64 step = hi - lo;
    for (int guard = 0; !lower_ok_q(in, hi); ++guard) {
        if (guard > 70 || hi > (u64(1) << 62) || step > (u64(1) << 61)) return false;
        lo = hi;
        hi += step;
        step *= 2;
    }
    step = std::max<u64>(hi - lo, 1);
    while (lo > q0 && lower_ok_q(in, lo)) {
        hi = lo;
        lo = (lo - q0 > step) ? lo - step : q0;
        step *= 2;
    }
    while (hi - lo > 1) {
        const u64 m = lo + (hi - lo) / 2;
        if (lower_ok_q(in, m)) hi = m; else lo = m;
    }
    out = hi;
    return true;
}

const BigInt& bound_cap() {
    static const BigInt cap = [] { BigInt c = 1; mpz_mul_2exp(c.get_mpz_t(), c.get_mpz_t(), 400); return c; }();
    return cap;
}

// largest q >= qmin with upper_ok (false: none).  hi may be an overestimate by
// ~1e-9 relative, never an underestimate.
bool find_upper(const BoundIn& in, const BoundLd& bl, const BigInt& qmin, BigInt& hi, bool& unbounded) {
    unbounded = false;
    if (!upper_ok(in, qmin)) return false;
    if (big_fits_u64(qmin)) {
        const double t = upper_root_t(bl);
        u64 res;
        if (t > 0.0 && std::isfinite(t) && refine_upper(in, big_to_u64(qmin), 1.0 / t, res)) {
            hi = u64_to_bigint(res);
            return true;
        }
        if (t == 0.0 && upper_ok(in, bound_cap())) { unbounded = true; return true; }
    }
    double a = big_d(qmin), b = a * 2.0 + 16.0;
    while (upper_ok_ld(bl, b)) {
        a = b;
        b *= 2.0;
        if (b > 1e120) break;
    }
    if (b > 1e120) {
        if (upper_ok(in, bound_cap())) { unbounded = true; return true; }
        b = 1e121;
    }
    for (int it = 0; it < 300 && b - a > std::max(1.0, a * 1e-7); ++it) {
        const double m = a + (b - a) / 2.0;
        if (upper_ok_ld(bl, m)) a = m; else b = m;
    }
    BigInt c = d_floor(b * (1.0 + 1e-6)) + 4;
    if (c <= qmin) c = qmin + 1;
    if (!upper_ok(in, c)) { hi = c - 1; return true; }
    // the estimate was low: exact galloping + bisection
    BigInt t = c, step = c;
    while (true) {
        const BigInt nx = t + step;
        if (nx > bound_cap()) { unbounded = true; return true; }
        if (!upper_ok(in, nx)) break;
        t = nx;
        step *= 2;
    }
    BigInt f = t + step;
    while (f - t > 1) {
        const BigInt m = t + (f - t) / 2;
        if (upper_ok(in, m)) t = m; else f = m;
    }
    hi = t;
    return true;
}

// lower_ok in the limit q -> infinity (sigma(q^e)/q^e -> 1), exact:
//   y0 < 2  and  (x0-1)(y0-1) < 1.   lower_ok(q) for any q implies it.
bool lower_ok_limit(const BoundIn& in) {
    const BigInt &sx = *in.sx, &px = *in.px, &sy = *in.sy, &py = *in.py;
    if (!(sy < 2 * py)) return false;
    return (sx - px) * (sy - py) < px * py;
}

// smallest q >= qmin with lower_ok (false: none).  lo may be an underestimate.
// beyond = true: no q up to 2^400 works, but larger ones might (the caller
// reports the k as incomplete instead of treating the range as empty).
bool find_lower(const BoundIn& in, const BoundLd& bl, const BigInt& qmin, BigInt& lo, bool& beyond) {
    beyond = false;
    if (lower_ok(in, qmin)) { lo = qmin; return true; }
    if (big_fits_u64(qmin)) {
        const double t = lower_root_t(bl);
        u64 res;
        if (t > 0.0 && std::isfinite(t) && refine_lower(in, big_to_u64(qmin), 1.0 / t, res)) {
            lo = u64_to_bigint(res);
            return true;
        }
        // false up to 2^400: none at all unless the limit holds
        if (t == 0.0 && !lower_ok(in, bound_cap())) { beyond = lower_ok_limit(in); return false; }
    }
    double a = big_d(qmin), b = a * 2.0 + 16.0;
    while (!lower_ok_ld(bl, b)) {
        a = b;
        b *= 2.0;
        if (b > 1e120) break;
    }
    if (b > 1e120) {
        if (!lower_ok(in, bound_cap())) { beyond = lower_ok_limit(in); return false; }
        lo = qmin;                                   // give up on tightening: safe
        return true;
    }
    for (int it = 0; it < 300 && b - a > std::max(1.0, a * 1e-7); ++it) {
        const double m = a + (b - a) / 2.0;
        if (lower_ok_ld(bl, m)) b = m; else a = m;
    }
    BigInt c = d_floor(a * (1.0 - 1e-6));
    c -= 4;
    if (c <= qmin) c = qmin;
    if (c > qmin && !lower_ok(in, c)) {
        // the true minimum is above c.  Check that the estimate's "true" point
        // really is true (rounding can fake it when (x-1)(y-1) sits exactly at 1)
        BigInt bb = d_floor(b * (1.0 + 1e-6)) + 4;
        if (bb <= c) bb = c + 1;
        if (lower_ok(in, bb)) { lo = c + 1; return true; }
        BigInt t = bb, step = 1;                     // t is false: exact galloping
        while (true) {
            const BigInt nx = t + step;
            if (nx > bound_cap()) { beyond = lower_ok_limit(in); return false; }
            if (lower_ok(in, nx)) { c = nx; break; }
            t = nx;
            step *= 2;
        }
        while (c - t > 1) {
            const BigInt m = t + (c - t) / 2;
            if (lower_ok(in, m)) c = m; else t = m;
        }
        lo = c;
        return true;
    }
    if (c == qmin) {                                  // qmin is false (tested above)
        // exact search upward
        BigInt t = qmin, step = 1;
        while (true) {
            const BigInt nx = t + step;
            if (nx > bound_cap()) { beyond = lower_ok_limit(in); return false; }
            if (lower_ok(in, nx)) { c = nx; break; }
            t = nx;
            step *= 2;
        }
        // t false, c true
        while (c - t > 1) {
            const BigInt m = t + (c - t) / 2;
            if (lower_ok(in, m)) c = m; else t = m;
        }
        lo = c;
        return true;
    }
    // c is true although the estimate said false: bisect [qmin (false), c (true)]
    BigInt t = qmin;
    while (c - t > 1) {
        const BigInt m = t + (c - t) / 2;
        if (lower_ok(in, m)) c = m; else t = m;
    }
    lo = c;
    return true;
}

// split3 roots: lower limits of the tail primes u, w (the other member's two
// primes, free of the prefix): u >= its slot's lo, w > u and >= its slot's lo.
// Returned as L with "prime > L".
void split_floors(const Config& cfg, const RootShape& sh, BigInt& Lu, BigInt& Lw) {
    const std::size_t no = sh.order.size();
    const FreeSlot& fu = cfg.slots[static_cast<std::size_t>(sh.order[no - 3])];
    const FreeSlot& fw = cfg.slots[static_cast<std::size_t>(sh.order[no - 1])];
    const u64 lu = std::max<u64>(fu.lo, 2);
    const u64 lw = std::max<u64>(std::max<u64>(fw.lo, 2), lu + 1);
    Lu = u64_to_bigint(lu - 1);
    Lw = u64_to_bigint(lw - 1);
}

// float_id >= 0: that remaining prime is only known to be > the previous
// prime (a float3 or split3 tail), not > q; its contribution is bounded
// accordingly.  from_slot: the range starts at the slot's own lower limit,
// not above the previous prime (u of a split3 tail).
Range range_for(const Node& n, const Rem& r, int float_id = -1, bool from_slot = false) {
    STATADD(ranges, 1);
    Range out;
    // sigma(N1) = sigma(N2):  S0 sigma(rest of N1) = S1 sigma(rest of N2).  With a
    // single prime z (exponent 1) left in N1 and every prime left in N2 above
    // L, the i-th of those has sigma >= L+2+i, so  z + 1 >= S1 prod(L+2+i) / S0;
    // N1's abundancy x <= x0 (zmin+1)/zmin must still exceed 2 (exact test).
    if (float_id < 0 && !from_slot && !n.root->shape->split3 && r.count[0] == 1 && r.count[1] >= 1) {
        int zi = 0;
        while (r.side[zi] != 0) ++zi;
        if (r.exp[zi] == 1) {
            const BigInt L = (n.depth > 0) ? n.prime : BigInt(1);
            BigInt zmin = n.sy;
            for (int i = 0; i < r.count[1]; ++i) zmin *= L + 2 + i;
            mpz_cdiv_q(zmin.get_mpz_t(), zmin.get_mpz_t(), n.sx.get_mpz_t());
            zmin -= 1;
            if (zmin < L + 1) zmin = L + 1;
            if (!(n.sx * (zmin + 1) > 2 * n.px * zmin)) return out;
        }
    }
    const FreeSlot& slot = n.cfg->slots[static_cast<std::size_t>(r.id[0])];
    BoundIn in{&n.sx, &n.px, &n.sy, &n.py, slot.side, slot.exp,
               r.count[0] - (slot.side == 0 ? 1 : 0), r.count[1] - (slot.side == 1 ? 1 : 0)};
    in.x0l = ratio_d(n.sx, n.px);
    in.y0l = ratio_d(n.sy, n.py);
    BigInt Lf = (n.depth > 0) ? n.prime : BigInt(1);
    if (float_id >= 0) {
        const FreeSlot& vs = n.cfg->slots[static_cast<std::size_t>(float_id)];
        if (vs.lo > 2) raise_to(Lf, vs.lo - 1);
        (vs.side == 0 ? in.j0 : in.j1) -= 1;
        in.add_float(vs.side, &Lf);
    }
    // split3 prefix: u and w are only bounded by their own limits
    const RootShape& sh = *n.root->shape;
    BigInt Lu, Lw;
    if (sh.split3 && r.n > 3) {
        split_floors(*n.cfg, sh, Lu, Lw);
        const int os = n.cfg->slots[static_cast<std::size_t>(sh.order[sh.order.size() - 3])].side;
        (os == 0 ? in.j0 : in.j1) -= 2;
        in.add_float(os, &Lu);
        in.add_float(os, &Lw);
    }
    BoundLd bl{in.x0l, in.y0l, slot.side, slot.exp, in.j0, in.j1};
    bl.fx = in.float_factor(0);
    bl.fy = in.float_factor(1);
    BigInt qmin = (n.depth > 0 && !from_slot) ? BigInt(n.prime + 1) : BigInt(2);
    raise_to(qmin, slot.lo);
    if (qmin < 2) qmin = 2;

    // the lower end first: it is cheaper and settles most dead nodes.  The
    // upper test is monotone, so searching it from lo instead of qmin only
    // drops values below lo.
    BigInt lo;
    bool beyond = false;
    if (!find_lower(in, bl, qmin, lo, beyond)) {
        if (beyond && slot.hi == 0) {                    // a q above 2^400 is not excluded
            out.empty = false;
            out.unbounded = true;
            out.lo = bound_cap();
            out.hi = bound_cap();
        }
        return out;
    }
    if (slot.hi != 0 && cmp_u64(lo, slot.hi) > 0) return out;
    BigInt hi;
    bool unb = false;
    if (!find_upper(in, bl, lo, hi, unb)) return out;
    if (slot.hi != 0) {
        const BigInt sh = u64_to_bigint(slot.hi);
        if (unb || hi > sh) { hi = sh; unb = false; }
    }
    if (!unb && lo > hi) return out;
    out.empty = false;
    out.unbounded = unb;
    out.lo = lo;
    out.hi = hi;
    return out;
}

// ---------------------------------------------------------------------------
// output
// ---------------------------------------------------------------------------
using Solved = std::vector<std::pair<int, BigInt>>;

void emit(const Node& n, const Solved& solved, SearchCtx& ctx) {
    const Config& cfg = *n.cfg;
    const SearchK& sk = *n.sk;
    std::vector<BigInt> prime(cfg.slots.size());
    std::vector<char> have(cfg.slots.size(), 0);
    for (const Node* p = &n; p && p->depth > 0; p = p->parent) {
        const int id = p->slot;
        prime[static_cast<std::size_t>(id)] = p->prime;
        have[static_cast<std::size_t>(id)] = 1;
    }
    for (const auto& [id, q] : solved) {
        prime[static_cast<std::size_t>(id)] = q;
        have[static_cast<std::size_t>(id)] = 1;
    }
    // every slot filled, strictly increasing in the root's order
    const auto& order = n.root->shape->order;
    const std::size_t no = order.size();
    for (std::size_t i = 0; i < no; ++i) {
        const auto id = static_cast<std::size_t>(order[i]);
        if (!have[id] || prime[id] < 2) return;
        if (i == 0) continue;
        if (n.root->shape->split3 && i + 3 >= no) {
            // tail [u, v, w]: v above the prefix (its own member), u < w; u and w
            // are the other member's, unrelated to the prefix
            if (i == no - 2 && no > 3 && !(prime[static_cast<std::size_t>(order[no - 4])] < prime[id])) return;
            if (i == no - 1) {
                const BigInt& u = prime[static_cast<std::size_t>(order[no - 3])];
                const BigInt& v = prime[static_cast<std::size_t>(order[no - 2])];
                if (!(u < prime[id]) || v == u || v == prime[id]) return;
            }
            continue;
        }
        if (n.root->shape->float3 && i + 3 >= no) {
            // tail [u, v, w]: all three above the prefix, u < w, v differs from both
            if (no > 3 && !(prime[static_cast<std::size_t>(order[no - 4])] < prime[id])) return;
            if (i == no - 1) {
                const BigInt& u = prime[static_cast<std::size_t>(order[no - 3])];
                const BigInt& v = prime[static_cast<std::size_t>(order[no - 2])];
                if (!(u < prime[id]) || v == u || v == prime[id]) return;
            }
            continue;
        }
        if (n.root->shape->last2_free && i == no - 1) {
            // the last two may come in either order, but must differ and exceed the rest
            if (prime[static_cast<std::size_t>(order[i - 1])] == prime[id]) return;
            if (i >= 2 && !(prime[static_cast<std::size_t>(order[i - 2])] < prime[id])) return;
            continue;
        }
        if (!(prime[static_cast<std::size_t>(order[i - 1])] < prime[id])) return;
    }
    for (std::size_t id = 0; id < cfg.slots.size(); ++id) {
        const FreeSlot& s = cfg.slots[id];
        if (cmp_u64(prime[id], s.lo) < 0) return;
        if (s.hi != 0 && cmp_u64(prime[id], s.hi) > 0) return;
        if (divides_k(sk, prime[id])) return;
        if (!prime_test(prime[id])) return;
    }

    FacList f[2];
    for (int side = 0; side < 2; ++side) {
        for (const auto& [p, e] : sk.kf) f[side].emplace_back(u64_to_bigint(p), e);
        for (std::size_t pos = 0; pos < sk.hash->side[side].size(); ++pos) {
            const std::uint64_t bp = cfg.slot_prime[side][pos];
            if (bp != 0) fac_add(f[side], u64_to_bigint(bp), sk.hash->side[side][pos].exp);
        }
    }
    for (std::size_t id = 0; id < cfg.slots.size(); ++id)
        fac_add(f[cfg.slots[id].side], prime[id], cfg.slots[id].exp);

    FactorBuffer fb[2];
    BigInt N[2];
    for (int side = 0; side < 2; ++side) {
        std::sort(f[side].begin(), f[side].end(),
                  [](const auto& a, const auto& b) { return a.first < b.first; });
        N[side] = 1;
        for (const auto& [p, e] : f[side]) {
            fb[side].add(p, e);
            N[side] *= pow_big(p, e);
        }
    }
    if (!(N[0] < N[1])) return;
    const BigInt total = N[0] + N[1];
    if (sigma_from_factors(fb[0]) != total || sigma_from_factors(fb[1]) != total) return;
    BigInt gcd;
    mpz_gcd(gcd.get_mpz_t(), N[0].get_mpz_t(), N[1].get_mpz_t());
    if (gcd != sk.kb) return;                   // belongs to another k (cannot happen)
    ctx.sink->write_pair_with_factors(N[0], N[1], fb[0], fb[1]);
}

// sigma part of one side: s1f (or s2f) + sigma(p^e) of the chosen primes on that side
void collect_sig(const Node& n, int side, FacList& out) {
    if (n.cfg->s_nat_ok[side]) {
        out.clear();
        const NatFactors& sn = n.cfg->s_nat[side];
        for (std::size_t i = 0; i < sn.primes.size(); ++i) fac_add(out, from_u128(sn.primes[i]), sn.exps[i]);
    } else {
        out = (side == 0) ? n.cfg->s1f : n.cfg->s2f;
    }
    for (const Node* p = &n; p && p->depth > 0; p = p->parent) {
        const int id = p->slot;
        if (n.cfg->slots[static_cast<std::size_t>(id)].side != side) continue;
        if (!p->sig_done) {
            FacList tmp;                         // not computed in advance: do it now
            sigma_factors(p->prime, n.cfg->slots[static_cast<std::size_t>(id)].exp, tmp);
            fac_merge(out, tmp);
        } else if (p->sig_nat_ok) {
            for (std::size_t i = 0; i < p->sig_nat.primes.size(); ++i)
                fac_add(out, from_u128(p->sig_nat.primes[i]), p->sig_nat.exps[i]);
        } else {
            fac_merge(out, p->sig);
        }
    }
}

// collect_sig with 128-bit primes, added to (primes, exps) with sign +1 or -1.
// false: a prime does not fit 128 bits (the caller uses collect_sig instead).
bool collect_sig_nat(const Node& n, int side, int sign, std::vector<u128>& primes, std::vector<int>& exps) {
    if (!n.cfg->s_nat_ok[side]) return false;
    auto add = [&](u128 p, int e) {
        for (std::size_t i = 0; i < primes.size(); ++i)
            if (primes[i] == p) { exps[i] += sign * e; return; }
        primes.push_back(p);
        exps.push_back(sign * e);
    };
    const NatFactors& sn = n.cfg->s_nat[side];
    for (std::size_t i = 0; i < sn.primes.size(); ++i) add(sn.primes[i], sn.exps[i]);
    for (const Node* p = &n; p && p->depth > 0; p = p->parent) {
        const int id = p->slot;
        if (n.cfg->slots[static_cast<std::size_t>(id)].side != side) continue;
        if (!p->sig_done) {
            thread_local NatFactors tmp;
            if (!sigma_factors_nat(p->prime, n.cfg->slots[static_cast<std::size_t>(id)].exp, tmp)) return false;
            for (std::size_t i = 0; i < tmp.primes.size(); ++i) add(tmp.primes[i], tmp.exps[i]);
        } else if (p->sig_nat_ok) {
            for (std::size_t i = 0; i < p->sig_nat.primes.size(); ++i) add(p->sig_nat.primes[i], p->sig_nat.exps[i]);
        } else {
            return false;
        }
    }
    return true;
}

// v = w, reusing v's limbs
inline void set_u128(BigInt& v, u128 w) {
    const std::uint64_t words[2] = {static_cast<std::uint64_t>(w), static_cast<std::uint64_t>(w >> 64)};
    mpz_import(v.get_mpz_t(), words[1] ? 2 : 1, -1, sizeof(std::uint64_t), 0, 0, words);
}

// The factorisation of V for the SameSide tail that follows a Progression's u,
// without sigma(u): (sigma part of u's side) - (sigma part of the other side),
// taken at the Progression's node.  It is the same for every u of the tail.
struct SameBase {
    bool ok = false;
    std::vector<u128> primes;
    std::vector<int> exps;                       // signed
};

// ---------------------------------------------------------------------------
// Tail: every remaining prime on one side.  The other side is complete, so
// the product W of the remaining prime powers and their sigma V are known:
//    side 1:  W = (sx - px)/py,  V = sx/sy        side 0:  W = (sy - py)/px,  V = sy/sx
// ---------------------------------------------------------------------------
void solve_same(const Node& n, const Rem& r, int idx, const BigInt& W, const BigInt& V,
                FacList* Vf, const BigInt& L, Solved& solved, SearchCtx& ctx)
{
    const int T = r.n - idx;
    if (T == 1) {
        BigInt q;
        if (!exact_root(W, r.exp[idx], q) || q <= L) return;
        if (sigma_pow(q, r.exp[idx]) != V) return;
        solved.emplace_back(r.id[idx], q);
        emit(n, solved, ctx);
        solved.pop_back();
        return;
    }
    if (T == 2 && r.exp[idx] == 1 && r.exp[idx + 1] == 1) {
        // q1 + q2 = V - W - 1,  q1*q2 = W
        const BigInt S = V - W - 1;
        const BigInt disc = S * S - 4 * W;
        if (disc < 0) return;
        BigInt rt;
        if (!exact_root(disc, 2, rt)) return;
        BigInt t = S - rt;
        if (mpz_odd_p(t.get_mpz_t())) return;
        const BigInt q1 = t / 2, q2 = (S + rt) / 2;
        if (q1 <= L || !(q1 < q2)) return;
        solved.emplace_back(r.id[idx], q1);
        solved.emplace_back(r.id[idx + 1], q2);
        emit(n, solved, ctx);
        solved.pop_back();
        solved.pop_back();
        return;
    }
    if (!Vf) return;
    // smallest remaining prime q:  sigma(q^g) | V,  q^g | W,  q^(sum of exps) <= W
    const int g = r.exp[idx];
    int esum = 0;
    for (int i = idx; i < r.n; ++i) esum += r.exp[i];
    BigInt qmax;
    mpz_root(qmax.get_mpz_t(), W.get_mpz_t(), static_cast<unsigned long>(esum));
    if (qmax <= L) return;
    const BigInt dmin = sigma_pow(L + 1, g), dmax = sigma_pow(qmax, g);

    FacList vf;
    for (const auto& pe : *Vf) if (pe.second > 0) vf.push_back(pe);
    std::vector<int> ex(vf.size(), 0);
    BigInt d = 1;
    // recursive walk over the divisors of V in [dmin, dmax]
    struct Walker {
        const Node& n; const Rem& r; int idx, g; const BigInt& W; const BigInt& V;
        const BigInt& L; const BigInt& qmax; const BigInt& dmin; const BigInt& dmax;
        FacList& vf; std::vector<int>& ex; Solved& solved; SearchCtx& ctx;
        void go(std::size_t i, const BigInt& cur) {
            if (ctx.cancelled()) return;
            if (i == vf.size()) {
                if (cur < dmin) return;
                BigInt q;
                if (g == 1) q = cur - 1;
                else {
                    mpz_root(q.get_mpz_t(), cur.get_mpz_t(), static_cast<unsigned long>(g));
                    if (sigma_pow(q, g) != cur) return;
                }
                if (q <= L || q > qmax) return;
                const BigInt qg = pow_big(q, g);
                if (!mpz_divisible_p(W.get_mpz_t(), qg.get_mpz_t())) return;
                if (!prime_test(q)) return;
                FacList rest = vf;
                for (std::size_t j = 0; j < vf.size(); ++j) rest[j].second -= ex[j];
                solved.emplace_back(r.id[idx], q);
                solve_same(n, r, idx + 1, W / qg, V / cur, &rest, q, solved, ctx);
                solved.pop_back();
                return;
            }
            BigInt v = cur;
            for (int e = 0; e <= vf[i].second; ++e) {
                ex[i] = e;
                go(i + 1, v);
                if (e == vf[i].second) break;
                v *= vf[i].first;
                if (v > dmax) break;
            }
            ex[i] = 0;
        }
    } walker{n, r, idx, g, W, V, L, qmax, dmin, dmax, vf, ex, solved, ctx};
    walker.go(0, d);
}

// base: the tail follows a Progression's u (n is u's node, on the other side);
// V's factorisation is base + sigma(u) instead of two collect_sig walks.
void tail_same(const Node& n, const Rem& r, SearchCtx& ctx, const SameBase* base = nullptr)
{
    const int side = r.side[0];          // every remaining prime is on this side
    BigInt num, W, V;
    // the divisions are exact (just tested), so mpz_divexact gives the same quotients faster
    if (side == 1) {
        num = n.sx - n.px;
        if (num <= 0 || !mpz_divisible_p(num.get_mpz_t(), n.py.get_mpz_t())) return;
        if (!mpz_divisible_p(n.sx.get_mpz_t(), n.sy.get_mpz_t())) return;
        mpz_divexact(W.get_mpz_t(), num.get_mpz_t(), n.py.get_mpz_t());
        mpz_divexact(V.get_mpz_t(), n.sx.get_mpz_t(), n.sy.get_mpz_t());
    } else {
        num = n.sy - n.py;
        if (num <= 0 || !mpz_divisible_p(num.get_mpz_t(), n.px.get_mpz_t())) return;
        if (!mpz_divisible_p(n.sy.get_mpz_t(), n.sx.get_mpz_t())) return;
        mpz_divexact(W.get_mpz_t(), num.get_mpz_t(), n.px.get_mpz_t());
        mpz_divexact(V.get_mpz_t(), n.sy.get_mpz_t(), n.sx.get_mpz_t());
    }
    if (V <= W) return;
    const BigInt L = (n.depth > 0) ? n.prime : BigInt(1);
    Solved solved;
    const bool simple = r.n == 1 || (r.n == 2 && r.exp[0] == 1 && r.exp[1] == 1);
    if (simple) {
        solve_same(n, r, 0, W, V, nullptr, L, solved, ctx);
        return;
    }
    // factorisation of V = (sigma part of the complete side) / (sigma part of this side)
    if (base && base->ok) {
        // = base + sigma(u^e): the complete side is u's, and u's node is n
        thread_local std::vector<u128> vp;
        thread_local std::vector<int> ve;
        thread_local NatFactors su;
        thread_local FacList Vf;
        if (sigma_factors_nat(n.prime, n.cfg->slots[static_cast<std::size_t>(n.slot)].exp, su)) {
            vp = base->primes;
            ve = base->exps;
            for (std::size_t i = 0; i < su.primes.size(); ++i) {
                std::size_t j = 0;
                while (j < vp.size() && vp[j] != su.primes[i]) ++j;
                if (j == vp.size()) { vp.push_back(su.primes[i]); ve.push_back(0); }
                ve[j] += su.exps[i];
            }
            std::size_t m = 0;
            for (std::size_t i = 0; i < vp.size(); ++i) {
                if (ve[i] < 0) return;              // cannot happen when V is an integer
                if (ve[i] == 0) continue;
                if (m == Vf.size()) Vf.emplace_back();
                set_u128(Vf[m].first, vp[i]);       // reuses the entry's limbs
                Vf[m].second = ve[i];
                ++m;
            }
            for (std::size_t i = m; i < Vf.size(); ++i) Vf[i].second = 0;   // unused entries: solve_same skips them
            solve_same(n, r, 0, W, V, &Vf, L, solved, ctx);
            return;
        }
    }
    FacList num_f, den_f;
    collect_sig(n, 1 - side, num_f);
    collect_sig(n, side, den_f);
    fac_merge(num_f, den_f, -1);
    FacList Vf;
    for (const auto& pe : num_f) {
        if (pe.second < 0) return;              // cannot happen when V is an integer
        if (pe.second > 0) Vf.push_back(pe);
    }
    solve_same(n, r, 0, W, V, &Vf, L, solved, ctx);
}

// ---------------------------------------------------------------------------
// Tail: one prime left on each side (P on side 0, Q on side 1).
//    a*sigma(P^al) = c*sigma(Q^ga) = b*P^al + d*Q^ga    (a,b,c,d = sx,px,sy,py)
// al = ga = 1:  D = ad + bc - ac,  D(P+1) = c(b+d),  D(Q+1) = a(b+d).
// ga = 1:       (ac - ad) sigma(P^al) - bc P^al + cd = 0,  Q = a sigma(P^al)/c - 1
// al = 1:       (ac - bc) sigma(Q^ga) - ad Q^ga + ab = 0,  P = c sigma(Q^ga)/a - 1
// ---------------------------------------------------------------------------
void mixed_closed(const Node& n, const BigInt& a, const BigInt& b, const BigInt& c, const BigInt& d,
                  int pid, int qid, Solved& solved, SearchCtx& ctx)
{
    const BigInt D = a * d + b * c - a * c;
    if (D == 0) return;
    const BigInt bd = b + d;
    BigInt NP = c * bd, NQ = a * bd;
    if (!mpz_divisible_p(NP.get_mpz_t(), D.get_mpz_t()) || !mpz_divisible_p(NQ.get_mpz_t(), D.get_mpz_t()))
        return;
    const BigInt P = NP / D - 1, Q = NQ / D - 1;
    if (P < 2 || Q < 2) return;
    solved.emplace_back(pid, P);
    solved.emplace_back(qid, Q);
    emit(n, solved, ctx);
    solved.pop_back();
    solved.pop_back();
}

void tail_mixed2(const Node& n, const Rem& r, SearchCtx& ctx) {
    const int ip = (r.side[0] == 0) ? 0 : 1, iq = 1 - ip;
    const int al = r.exp[ip], ga = r.exp[iq];
    const BigInt &a = n.sx, &b = n.px, &c = n.sy, &d = n.py;
    Solved solved;
    if (al == 1 && ga == 1) {
        mixed_closed(n, a, b, c, d, r.id[ip], r.id[iq], solved, ctx);
        return;
    }
    const BigInt L = (n.depth > 0) ? BigInt(n.prime + 1) : BigInt(2);
    if (ga == 1) {
        std::vector<BigInt> co(static_cast<std::size_t>(al) + 1, a * c - a * d);
        co[static_cast<std::size_t>(al)] -= b * c;
        co[0] += c * d;
        for (const BigInt& P : integer_roots(co, L)) {
            const BigInt num = a * sigma_pow(P, al);
            if (!mpz_divisible_p(num.get_mpz_t(), c.get_mpz_t())) continue;
            const BigInt Q = num / c - 1;
            solved = {{r.id[ip], P}, {r.id[iq], Q}};
            emit(n, solved, ctx);
        }
    } else {
        std::vector<BigInt> co(static_cast<std::size_t>(ga) + 1, a * c - b * c);
        co[static_cast<std::size_t>(ga)] -= a * d;
        co[0] += a * b;
        for (const BigInt& Q : integer_roots(co, L)) {
            const BigInt num = c * sigma_pow(Q, ga);
            if (!mpz_divisible_p(num.get_mpz_t(), a.get_mpz_t())) continue;
            const BigInt P = num / a - 1;
            solved = {{r.id[ip], P}, {r.id[iq], Q}};
            emit(n, solved, ctx);
        }
    }
}

// state after adding prime u (exponent 1) on side su
inline void add_u(const BigInt& sx, const BigInt& px, const BigInt& sy, const BigInt& py, int su,
                  const BigInt& u, BigInt& a, BigInt& b, BigInt& c, BigInt& d) {
    if (su == 0) { a = sx * (u + 1); b = px * u; c = sy; d = py; }
    else { a = sx; b = px; c = sy * (u + 1); d = py * u; }
}

// odd primes below 2^24 as a bitmap (bit i of word w: number 2*(64w+i)+1)
constexpr u64 BITMAP_LIMIT = u64{1} << 24;
const std::vector<u64>& prime_bitmap() {
    static const std::vector<u64> bits = [] {
        std::vector<u64> b(BITMAP_LIMIT / 128 + 1, 0);
        std::vector<u64> ps;
        primesieve::generate_primes(3, BITMAP_LIMIT, &ps);
        for (u64 p : ps) { const u64 i = p / 2; b[i / 64] |= u64{1} << (i % 64); }
        return b;
    }();
    return bits;
}

// scan the primes of [lo, hi] (BigInt bounds) with fn(u)
template <typename Fn>
bool scan_primes(const SearchK& sk, const BigInt& lo, const BigInt& hi, SearchCtx& ctx, Fn&& fn) {
    if (hi < lo) return true;
    static const u64 max_stop = primesieve::get_max_stop();
    if (!big_fits_u64(hi) || big_to_u64(hi) > max_stop) { ctx.flag(INC_SCAN_LIMIT); return false; }
    const u64 l = big_to_u64(lo), h = big_to_u64(hi);
    if (h < BITMAP_LIMIT && h - l < 65536) {             // short and small: bitmap walk
        const auto& bits = prime_bitmap();
        if (l <= 2 && h >= 2 && sk.k % 2 != 0) fn(u64{2});
        for (u64 i = std::max<u64>(l, 3) / 2; 2 * i + 1 <= h; ++i) {
            if (!((bits[i / 64] >> (i % 64)) & 1)) continue;
            const u64 p = 2 * i + 1;
            if (p < l || sk.k % p == 0) continue;
            fn(p);
        }
        return true;
    }
    primesieve::iterator it(prime_iter_start(l), h);
    u64 p;
    std::uint64_t count = 0;
    while ((p = it.next_prime()) <= h) {
        if ((++count & 63) == 0 && ctx.cancelled()) return false;
        if (sk.k % p == 0) continue;
        fn(p);
    }
    return true;
}

// ---------------------------------------------------------------------------
// Tail: [u, v, w] with v, w on different sides, all exponent 1.
// For each u the last two are the closed form above with D = D(u) linear in u:
//    D(u) = d1*u + d0,  D(u) | R  (R independent of u):
//    u on side 1:  d0 = c0(b0-a0),  R = a0 * (a0 b0 d0 + c0 (b0-a0)(b0-d0))
//    u on side 0:  d0 = a0(d0-c0),  R = c0 * (b0 c0 d0 + a0 (d0-c0)(d0-b0))
//    d1 = a0 d0 + b0 c0 - a0 c0          (a0,b0,c0,d0 = sx,px,sy,py)
// (from D(Q+1) = a(b+d) resp. D(P+1) = c(b+d) reduced mod D(u)).  So u comes
// from the divisors F of R with F == d0 (mod d1).
// ---------------------------------------------------------------------------
// approximate largest q with upper_ok (long double only; a hint, never trusted)
double approx_upper(const BoundLd& bl, double a) {
    if (!upper_ok_ld(bl, a)) return a;
    {
        const double t = upper_root_t(bl);
        if (t == 0.0) return 1e300;
        if (t > 0.0 && std::isfinite(t)) return std::max(a, (1.0 / t) * (1.0 + 1e-9) + 1.0);
    }
    double b = a * 2.0 + 16.0;
    while (upper_ok_ld(bl, b)) {
        a = b;
        b *= 2.0;
        if (b > 1e120) return b;
    }
    for (int it = 0; it < 200 && b - a > std::max(4.0, a * 1e-4); ++it) {
        const double m = a + (b - a) / 2.0;
        if (upper_ok_ld(bl, m)) a = m; else b = m;
    }
    return b;
}

// ---- 128-bit helpers -------------------------------------------------------
inline bool imul(i128 a, i128 b, i128& o) { return !__builtin_mul_overflow(a, b, &o); }
inline bool iadd(i128 a, i128 b, i128& o) { return !__builtin_add_overflow(a, b, &o); }
inline bool isub(i128 a, i128 b, i128& o) { return !__builtin_sub_overflow(a, b, &o); }
inline u128 uabs(i128 v) { return v < 0 ? static_cast<u128>(-v) : static_cast<u128>(v); }

u64 gcd_binary_u64(u64 a, u64 b) {                      // a, b > 0
    const int shift = __builtin_ctzll(a | b);
    a >>= __builtin_ctzll(a);
    do {
        b >>= __builtin_ctzll(b);
        if (a > b) std::swap(a, b);
        b -= a;
    } while (b != 0);
    return a << shift;
}

u128 gcd_u128(u128 a, u128 b) {
    if (a == 0) return b;
    if (b == 0) return a;
    // mostly both fit in 64 bits, or one does: then 64-bit steps suffice
    if ((a >> 64) == 0 && (b >> 64) != 0) b %= a;
    else if ((b >> 64) == 0 && (a >> 64) != 0) a %= b;
    if (((a | b) >> 64) == 0) {
        if (a == 0) return b;
        if (b == 0) return a;
        return gcd_binary_u64(static_cast<u64>(a), static_cast<u64>(b));
    }
    auto ctz128 = [](u128 x) {
        const u64 lo = static_cast<u64>(x);
        return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll(static_cast<u64>(x >> 64));
    };
    const int shift = ctz128(a | b);
    a >>= ctz128(a);
    do {
        b >>= ctz128(b);
        if (a > b) std::swap(a, b);
        b -= a;
    } while (b != 0);
    return a << shift;
}

// R* factorisation from 128-bit g1 and t (see tail_divisor3)
bool rstar_native128(const Node& n, int side, u128 g1, u128 t, NatFactors& nf) {
    if (!n.cfg->s_nat_ok[side]) return false;
    nf = n.cfg->s_nat[side];
    for (const Node* p = &n; p && p->depth > 0; p = p->parent) {
        const int id = p->slot;
        if (n.cfg->slots[static_cast<std::size_t>(id)].side != side) continue;
        if (!p->sig_done) {
            thread_local NatFactors tmp;
            if (!sigma_factors_nat(p->prime, n.cfg->slots[static_cast<std::size_t>(id)].exp, tmp)) return false;
            for (std::size_t i = 0; i < tmp.primes.size(); ++i) nf.add(tmp.primes[i], tmp.exps[i]);
            continue;
        }
        if (!p->sig_nat_ok) return false;
        for (std::size_t i = 0; i < p->sig_nat.primes.size(); ++i) nf.add(p->sig_nat.primes[i], p->sig_nat.exps[i]);
    }
    for (std::size_t i = 0; i < nf.primes.size() && g1 > 1; ++i)
        while (nf.exps[i] > 0 && g1 % nf.primes[i] == 0) { g1 /= nf.primes[i]; --nf.exps[i]; }
    if (g1 != 1) return false;
    if (t != 0 && (t & 1) == 0) {
        bool two = false;
        for (std::uint64_t p : n.cfg->strip64) two = two || p == 2;
        if (two) {
            const u64 lo = static_cast<u64>(t);
            const int z = lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll(static_cast<u64>(t >> 64));
            t >>= z;
            nf.add(2, z);
        }
    }
    for (const Config::Div128& dv : n.cfg->strip_div) {
        u128 q = t * dv.inv;                             // exact quotient when p | t
        if (q > dv.lim) continue;
        int e = 0;
        do { t = q; ++e; q = t * dv.inv; } while (q <= dv.lim);
        nf.add(dv.p, e);
    }
    if (t > 1) {
        if (t <= std::numeric_limits<std::uint64_t>::max()) {
            U64FactorBuffer ub;
            factorize_runtime_u64(static_cast<std::uint64_t>(t), ub);
            for (std::size_t i = 0; i < ub.size; ++i) nf.add(ub[i].prime, ub[i].exponent);
        } else {
            U128Factor buf[160];
            int cnt = 0;
            if (!factorize_runtime_u128(t, buf, cnt)) return false;
            for (int i = 0; i < cnt; ++i) nf.add(buf[i].prime, buf[i].exponent);
        }
    }
    std::size_t w = 0;
    for (std::size_t i = 0; i < nf.primes.size(); ++i)
        if (nf.exps[i] > 0) { nf.primes[w] = nf.primes[i]; nf.exps[w] = nf.exps[i]; ++w; }
    nf.primes.resize(w);
    nf.exps.resize(w);
    return true;
}

// The divisor tail entirely in 128-bit arithmetic.  Returns false when some
// value does not fit (the caller then runs the BigInt version, which finds
// exactly the same candidates).
// est_width: estimated width of the u range (scan_hint != nullptr only).  When
// the number to factor needs the slow 128-bit path and the range is short,
// trying its primes is cheaper: then *scan_hint is set and nothing is done.
constexpr double BIG_T_SCAN_WINDOW = 4096.0;

bool divisor3_native(const Node& n, const Rem& r, const Range& rg, SearchCtx& ctx,
                     double est_width = 0.0, bool* scan_hint = nullptr) {
    i128 A, B, C, Dd;
    if (!node_nat(n, A, B, C, Dd)) return false;
    const int su = r.side[0];
    i128 t1, t2, t3, d1, dz, T;
    // d1 = A*Dd + B*C - A*C
    if (!imul(A, Dd, t1) || !imul(B, C, t2) || !imul(A, C, t3) || !iadd(t1, t2, d1) || !isub(d1, t3, d1)) return false;
    if (su == 1) {
        // dz = C*(B-A),  T = A*B*Dd + C*(B-A)*(B-Dd)
        i128 bma, bmd;
        if (!isub(B, A, bma) || !isub(B, Dd, bmd) || !imul(C, bma, dz)) return false;
        if (!imul(A, B, t1) || !imul(t1, Dd, t1) || !imul(dz, bmd, t2) || !iadd(t1, t2, T)) return false;
    } else {
        // dz = A*(Dd-C),  T = B*C*Dd + A*(Dd-C)*(Dd-B)
        i128 dmc, dmb;
        if (!isub(Dd, C, dmc) || !isub(Dd, B, dmb) || !imul(A, dmc, dz)) return false;
        if (!imul(B, C, t1) || !imul(t1, Dd, t1) || !imul(dz, dmb, t2) || !iadd(t1, t2, T)) return false;
    }
    if (d1 == 0 || T == 0) return false;
    const u128 g = gcd_u128(uabs(d1), uabs(dz));
    const i128 A0 = (su == 1) ? A : C;
    const u128 g1 = gcd_u128(g, uabs(A0));
    const u128 Tabs = uabs(T);
    if (Tabs % g != 0) return false;
    const u128 t = Tabs / g;
    const u128 a0g = uabs(A0) / g1;
    if (a0g != 0 && t > I128_MAX_U128 / a0g) return false;
    const u128 Rg = a0g * t;
    const i128 d1g = d1 / static_cast<i128>(g), dzg = dz / static_cast<i128>(g);
    const u128 m = uabs(d1g);
    if (m > std::numeric_limits<std::uint64_t>::max()) return false;

    i128 lo = 0, hi = 0;
    if (!big_to_i128(rg.lo, lo)) return false;
    if (!rg.unbounded && !big_to_i128(rg.hi, hi)) return false;
    i128 Flo, Fhi;
    u128 max_abs;
    if (rg.unbounded) {
        max_abs = Rg;
        Flo = -static_cast<i128>(Rg);
        Fhi = static_cast<i128>(Rg);
    } else {
        i128 f1, f2;
        if (!imul(d1g, lo, f1) || !iadd(f1, dzg, f1) || !imul(d1g, hi, f2) || !iadd(f2, dzg, f2)) return false;
        Flo = std::min(f1, f2);
        Fhi = std::max(f1, f2);
        max_abs = std::max(uabs(Flo), uabs(Fhi));
        if (max_abs > Rg) max_abs = Rg;
        if (Flo < -static_cast<i128>(max_abs)) Flo = -static_cast<i128>(max_abs);
        if (Fhi > static_cast<i128>(max_abs)) Fhi = static_cast<i128>(max_abs);
    }
    if (Flo > Fhi || max_abs < 1) return true;
    if (scan_hint && (t >> 64) != 0 && est_width <= 2.0 * BIG_T_SCAN_WINDOW) {
        *scan_hint = true;
        return true;
    }

    thread_local NatFactors nf;
    if (!rstar_native128(n, su == 1 ? 0 : 1, g1, t, nf)) return false;
    {
        std::size_t w = 0;
        for (std::size_t i = 0; i < nf.primes.size(); ++i)
            if (nf.primes[i] <= max_abs) { nf.primes[w] = nf.primes[i]; nf.exps[w] = nf.exps[i]; ++w; }
        nf.primes.resize(w);
        nf.exps.resize(w);
    }
    STATADD(d3_native, 1);
#ifdef AMICABLE_STATS
    { double nd = 1; for (int e : nf.exps) nd *= e + 1; STATADD(d3_divs, static_cast<u64>(nd)); }
#endif
    const auto mm = static_cast<std::uint64_t>(m);
    const auto tres = static_cast<std::uint64_t>(((dzg % static_cast<i128>(m)) + static_cast<i128>(m)) % static_cast<i128>(m));
    const int ip = (r.side[1] == 0) ? 1 : 2, iq = (ip == 1) ? 2 : 1;
    const int uid = r.id[0], pid = r.id[ip], qid = r.id[iq];
    const SearchK& sk = *n.sk;
    Solved solved;
    bool overflow = false;
    signed_divisors_mod(nf, max_abs, Flo, Fhi, mm, tres, [&](i128 F) {
        const i128 num = F - dzg;
        if (num % d1g != 0) return;
        const i128 u = num / d1g;
        if (u < lo || (!rg.unbounded && u > hi)) return;
        const u128 uu = static_cast<u128>(u);
        if (uu <= sk.k && sk.k % static_cast<u64>(uu) == 0) return;
        if (uu <= std::numeric_limits<std::uint64_t>::max()) {
            if (!is_prime_u64_fast(static_cast<u64>(uu))) return;
        } else if (!is_probable_prime(from_u128(uu))) return;
        // the last two from the closed form, natively when it fits
        i128 a = A, b = B, c = C, d = Dd;
        bool ok = true;
        if (su == 0) ok = imul(A, u + 1, a) && imul(B, u, b);
        else ok = imul(C, u + 1, c) && imul(Dd, u, d);
        i128 x1, x2, x3, D, bd, NP, NQ;
        ok = ok && imul(a, d, x1) && imul(b, c, x2) && imul(a, c, x3) && iadd(x1, x2, D) && isub(D, x3, D) &&
             iadd(b, d, bd) && imul(c, bd, NP) && imul(a, bd, NQ);
        if (!ok) {
            BigInt ab, bb, cb, db;
            add_u(n.sx, n.px, n.sy, n.py, su, from_u128(uu), ab, bb, cb, db);
            solved.assign(1, {uid, from_u128(uu)});
            mixed_closed(n, ab, bb, cb, db, pid, qid, solved, ctx);
            overflow = true;
            return;
        }
        if (D == 0 || NP % D != 0 || NQ % D != 0) return;
        const i128 P = NP / D - 1, Q = NQ / D - 1;
        if (P < 2 || Q < 2) return;
        solved.clear();
        solved.emplace_back(uid, from_u128(uu));
        solved.emplace_back(pid, from_i128(P));
        solved.emplace_back(qid, from_i128(Q));
        emit(n, solved, ctx);
    });
    (void)overflow;
    return true;
}

// try every prime u of [lo, hi] in the divisor tail (short ranges)
void divisor3_scan(const Node& n, const Rem& r, const Range& rg, SearchCtx& ctx) {
    const int su = r.side[0];
    const int ip = (r.side[1] == 0) ? 1 : 2, iq = (ip == 1) ? 2 : 1;
    const int uid = r.id[0], pid = r.id[ip], qid = r.id[iq];
    i128 A = 0, B = 0, C = 0, Dd = 0;
    const bool nat = node_nat(n, A, B, C, Dd);
    Solved solved;
    BigInt a, b, c, d;
    scan_primes(*n.sk, rg.lo, rg.hi, ctx, [&](u64 p) {
        if (nat) {
            const i128 u = static_cast<i128>(p);
            i128 aa = A, bb = B, cc = C, dd = Dd;
            bool ok = true;
            if (su == 0) ok = imul(A, u + 1, aa) && imul(B, u, bb);
            else ok = imul(C, u + 1, cc) && imul(Dd, u, dd);
            i128 x1, x2, x3, D, bd, NP, NQ;
            ok = ok && imul(aa, dd, x1) && imul(bb, cc, x2) && imul(aa, cc, x3) && iadd(x1, x2, D) &&
                 isub(D, x3, D) && iadd(bb, dd, bd) && imul(cc, bd, NP) && imul(aa, bd, NQ);
            if (ok) {
                if (D == 0 || NP % D != 0 || NQ % D != 0) return;
                const i128 P = NP / D - 1, Q = NQ / D - 1;
                if (P < 2 || Q < 2) return;
                solved.clear();
                solved.emplace_back(uid, u64_to_bigint(p));
                solved.emplace_back(pid, from_i128(P));
                solved.emplace_back(qid, from_i128(Q));
                emit(n, solved, ctx);
                return;
            }
        }
        const BigInt u = u64_to_bigint(p);
        add_u(n.sx, n.px, n.sy, n.py, su, u, a, b, c, d);
        solved.assign(1, {uid, u});
        mixed_closed(n, a, b, c, d, pid, qid, solved, ctx);
    });
}

void tail_progression(const Node& n, const Rem& r, SearchCtx& ctx);

// Upper cap for u in the divisor tail [u, v, w].  The prime on u's side among
// v, w (call it W) comes from the closed form:  W + 1 = num(u) / D(u),
// D(u) = d1 u + dz,  num = a (b + d u) (u on side 1) or c (b u + d) (side 0),
// all values positive.  A solution needs D(u) > 0 and W > u, so
//     f(u) = d1 u^2 + (dz - X) u - Y <= 0,   X, Y = a d, a b  (side 1)
//                                            X, Y = b c, c d  (side 0)
// (num >= (u+1) D >= u D).  f(0) = -Y < 0, so for d1 > 0 the valid u lie
// below the positive root of f; for d1 < 0, D(u) > 0 alone caps u.
// Exact (128-bit, checked); false: no u can work.  have = false: no cap
// (values too large, or d1 = 0): the other bounds still apply.
bool divisor3_cap(const Node& n, int su, BigInt& cap, bool& have) {
    have = false;
    i128 A, B, C, Dd, d1, dz, X, Y;
    {
        i128 t1, t2, t3;
        if (!node_nat(n, A, B, C, Dd)) return true;
        if (!imul(A, Dd, t1) || !imul(B, C, t2) || !imul(A, C, t3) || !iadd(t1, t2, d1) || !isub(d1, t3, d1))
            return true;
        if (su == 1) {
            i128 bma;
            if (!isub(B, A, bma) || !imul(C, bma, dz) || !imul(A, Dd, X) || !imul(A, B, Y)) return true;
        } else {
            i128 dmc;
            if (!isub(Dd, C, dmc) || !imul(A, dmc, dz) || !imul(B, C, X) || !imul(C, Dd, Y)) return true;
        }
    }
    if (d1 == 0) return true;
    if (d1 < 0) {                                        // D(u) > 0  <=>  u < dz / |d1|
        if (dz <= 0) return false;
        const i128 c = (dz - 1) / (-d1);
        if (c < 2) return false;
        cap = from_i128(c);
        have = true;
        return true;
    }
    i128 Bq;
    if (!isub(dz, X, Bq)) return true;
    // sign of f(u), exact
    auto sign_f = [&](u64 uu) -> int {
        const i128 u = static_cast<i128>(uu);
        i128 t, p, v;
        if (imul(d1, u, t) && iadd(t, Bq, t)) {
            if (!imul(t, u, p)) return t > 0 ? 1 : -1;          // |t u| >= 2^127 > Y > 0
            if (!isub(p, Y, v)) return p > 0 ? 1 : -1;
            return (v > 0) - (v < 0);
        }
        const BigInt ub = u64_to_bigint(uu);
        const BigInt fv = (from_i128(d1) * ub + from_i128(Bq)) * ub - from_i128(Y);
        return sgn(fv);
    };
    const double dd1 = static_cast<double>(d1), dB = static_cast<double>(Bq), dY = static_cast<double>(Y);
    const double sq = std::sqrt(dB * dB + 4.0 * dd1 * dY);
    const double r2 = (dB >= 0.0) ? (2.0 * dY) / (dB + sq) : (sq - dB) / (2.0 * dd1);
    if (!(r2 < 1.8e19)) return true;                     // beyond 64 bits: no cap
    u64 c = (r2 < 2.0) ? 2 : static_cast<u64>(r2);
    int steps = 0;
    while (sign_f(c + 1) <= 0) {
        ++c;
        if (++steps > 64) return true;
    }
    while (sign_f(c) > 0) {
        if (c <= 2) return false;                        // f > 0 from 2 on: no u
        --c;
        if (++steps > 128) return true;
    }
    cap = u64_to_bigint(c);
    have = true;
    return true;
}

void apply_cap(Range& rg, const BigInt& cap, bool have) {
    if (!have || rg.empty) return;
    if (rg.unbounded || rg.hi > cap) {
        rg.hi = cap;
        rg.unbounded = false;
    }
    if (rg.lo > rg.hi) rg.empty = true;
}

// The divisor tail.  On a float3 root the third remaining prime v (the only
// one of its side) may lie anywhere among u < w: the divisor condition and the
// closed form do not care where, so one call covers all three orderings.
// Only the range of u has to allow for it: there u >= previous+1 and no upper
// cut (the divisors bound it); the prune uses "every remaining prime > previous".
// Returns false only when called with a fixed u range and the problem is
// degenerate (no divisor condition); the caller then splits the orderings.
bool tail_divisor3(const Node& n, const Rem& r, SearchCtx& ctx, bool allow_float = true,
                   const Range* fixed = nullptr);

// sigma(N1) = sigma(N2) at a divisor-tail node reads  S_z (z+1) = S_o (a+1)(b+1)
// for the prime z that is alone on its side among the last three (a, b the
// other two; S_z, S_o the sigma products so far on z's and on their side).
// With a, b >= ulo and distinct,  z + 1 >= S_o (ulo+1)(ulo+2) / S_z.  When z is
// in N1, whose abundancy x must exceed 2, x <= x0 (zmin+1)/zmin must still
// exceed 2 (exact test).  false: no solution here.  zfloor (z > zfloor) is raised.
bool alone_filter(const Node& n, int zside, const BigInt& ulo, BigInt& zfloor) {
    if (zside != 0) return true;
    {   // the same in 128-bit arithmetic when everything fits
        constexpr i128 LIM = static_cast<i128>(1) << 120;
        i128 sx, px, sy, py, u, zf, a, b, c, zmin, l, r;
        if (node_nat(n, sx, px, sy, py) && big_to_i128(ulo, u) &&
            big_to_i128(zfloor, zf) && sx > 0 && u < LIM && zf < LIM && imul(sy, u + 1, a) && imul(a, u + 2, b) && b >= 0) {
            zmin = b / sx + (b % sx != 0) - 1;                 // ceil(b / sx) - 1
            if (zmin < zf + 1) zmin = zf + 1;
            if (imul(sx, zmin + 1, l) && imul(px, 2, c) && imul(c, zmin, r)) {
                if (!(l > r)) return false;
                zfloor = from_i128(zmin - 1);
                return true;
            }
        }
    }
    BigInt zmin = n.sy * (ulo + 1) * (ulo + 2);
    mpz_cdiv_q(zmin.get_mpz_t(), zmin.get_mpz_t(), n.sx.get_mpz_t());
    zmin -= 1;
    if (zmin < zfloor + 1) zmin = zfloor + 1;
    if (!(n.sx * (zmin + 1) > 2 * n.px * zmin)) return false;
    zfloor = zmin - 1;
    return true;
}

// split3 tail [u, v, w]: u < w the other member's primes, bounded only by their
// own limits (not by the prefix); v the last prime of the prefix's member.
// The divisor condition and the closed form do not depend on the order, so
// one search covers every interleaving.
void tail_divisor3_split(const Node& n, const Rem& r, SearchCtx& ctx) {
    STATADD(d3, 1);
    const FreeSlot& us = n.cfg->slots[static_cast<std::size_t>(r.id[0])];
    const FreeSlot& vs = n.cfg->slots[static_cast<std::size_t>(r.id[1])];
    const BigInt ulo = u64_to_bigint(std::max<u64>(us.lo, 2));
    BigInt L = (n.depth > 0) ? n.prime : BigInt(1);
    if (vs.lo > 2) raise_to(L, vs.lo - 1);
    if (!alone_filter(n, vs.side, ulo, L)) return;
    BoundIn in{&n.sx, &n.px, &n.sy, &n.py, us.side, us.exp,
               r.count[0] - (us.side == 0 ? 1 : 0), r.count[1] - (us.side == 1 ? 1 : 0)};
    in.x0l = ratio_d(n.sx, n.px);
    in.y0l = ratio_d(n.sy, n.py);
    (vs.side == 0 ? in.j0 : in.j1) -= 1;
    in.add_float(vs.side, &L);
    if (!upper_ok(in, ulo)) return;
    BigInt cap;
    bool have_cap = false;
    if (!divisor3_cap(n, us.side, cap, have_cap)) return;
    if (have_cap && cap < ulo) return;
    BoundLd bl{in.x0l, in.y0l, us.side, us.exp, in.j0, in.j1};
    bl.fx = in.float_factor(0);
    bl.fy = in.float_factor(1);
    double est = approx_upper(bl, big_d(ulo));
    if (have_cap) est = std::min(est, big_d(cap));
    Range rg;
    if (est - big_d(ulo) <= 2.0 * SCAN_WINDOW) {
        rg = range_for(n, r, r.id[1], true);
        apply_cap(rg, cap, have_cap);
        if (rg.empty) return;
        if (!rg.unbounded && rg.hi - rg.lo <= static_cast<unsigned long>(SCAN_WINDOW)) {
            STATADD(d3_scan, 1);
            divisor3_scan(n, r, rg, ctx);
            return;
        }
    } else {
        rg.empty = false;
        rg.lo = ulo;
        rg.unbounded = (us.hi == 0);
        if (us.hi) rg.hi = u64_to_bigint(us.hi);
        apply_cap(rg, cap, have_cap);
        if (rg.empty) return;
    }
    bool want_scan = false;
    if (divisor3_native(n, r, rg, ctx, est - big_d(ulo), &want_scan)) {
        if (!want_scan) return;
        Range ex = range_for(n, r, r.id[1], true);
        apply_cap(ex, cap, have_cap);
        if (ex.empty) return;
        if (!ex.unbounded && ex.hi - ex.lo <= static_cast<unsigned long>(BIG_T_SCAN_WINDOW)) {
            STATADD(d3_scan, 1);
            divisor3_scan(n, r, ex, ctx);
            return;
        }
        if (divisor3_native(n, r, ex, ctx)) return;
        rg = ex;
    }
    if (tail_divisor3(n, r, ctx, false, &rg)) return;         // BigInt divisor route
    // degenerate (no divisor condition): every prime of u's range is tried
    Range ex = range_for(n, r, r.id[1], true);
    apply_cap(ex, cap, have_cap);
    if (ex.empty) return;
    if (ex.unbounded) { ctx.flag(INC_UNBOUNDED); return; }
    STATADD(d3_scan, 1);
    divisor3_scan(n, r, ex, ctx);
}

bool tail_divisor3(const Node& n, const Rem& r, SearchCtx& ctx, bool allow_float,
                   const Range* fixed) {
    if (allow_float && n.root->shape->split3 &&
        static_cast<std::size_t>(n.depth) + 3 == n.root->shape->order.size()) {
        tail_divisor3_split(n, r, ctx);
        return true;
    }
    const bool floating = allow_float && n.root->shape->float3 &&
                          static_cast<std::size_t>(n.depth) + 3 == n.root->shape->order.size();
    if (floating) {
        const FreeSlot& us = n.cfg->slots[static_cast<std::size_t>(r.id[0])];
        const FreeSlot& vs = n.cfg->slots[static_cast<std::size_t>(r.id[1])];
        const BigInt L = (n.depth > 0) ? n.prime : BigInt(1);
        BigInt ulo = L + 1;
        raise_to(ulo, us.lo);
        BigInt vlo = L + 1;
        raise_to(vlo, vs.lo);
        {
            BigInt zf = L;                                // all three are > L
            if (!alone_filter(n, vs.side, L + 1, zf)) return true;
        }
        // Which orderings can still hold?  A: u < v (u is the next prime),
        // B: v < u (v is the next prime).  Both tests are rigorous.
        const double x0l = ratio_d(n.sx, n.px), y0l = ratio_d(n.sy, n.py);
        BoundIn inA{&n.sx, &n.px, &n.sy, &n.py, us.side, us.exp,
                    r.count[0] - (us.side == 0 ? 1 : 0), r.count[1] - (us.side == 1 ? 1 : 0)};
        inA.x0l = x0l; inA.y0l = y0l;
        BoundIn inB{&n.sx, &n.px, &n.sy, &n.py, vs.side, vs.exp,
                    r.count[0] - (vs.side == 0 ? 1 : 0), r.count[1] - (vs.side == 1 ? 1 : 0)};
        inB.x0l = x0l; inB.y0l = y0l;
        const bool caseA = upper_ok(inA, ulo);
        const bool caseB = upper_ok(inB, vlo);
        if (!caseA && !caseB) return true;
        if (!caseB) return tail_divisor3(n, r, ctx, false);       // only u < v: strict tail
        if (!caseA) {                                             // only v < u: congruence on v
            Rem rv;
            const int order3[3] = {1, 0, 2};
            for (int i : order3) {
                rv.id[rv.n] = r.id[i]; rv.side[rv.n] = r.side[i]; rv.exp[rv.n] = r.exp[i];
                ++rv.count[r.side[i]]; ++rv.n;
            }
            tail_progression(n, rv, ctx);
            return true;
        }
        // both possible: one divisor search covers every position of v.
        // u's range then only knows v > the previous prime.
        BoundIn in{&n.sx, &n.px, &n.sy, &n.py, us.side, us.exp,
                   r.count[0] - (us.side == 0 ? 1 : 0), r.count[1] - (us.side == 1 ? 1 : 0)};
        in.x0l = ratio_d(n.sx, n.px);
        in.y0l = ratio_d(n.sy, n.py);
        const int fs = r.side[1];                        // v = r.id[1]
        (fs == 0 ? in.j0 : in.j1) -= 1;
        in.add_float(fs, &L);
        if (!upper_ok(in, ulo)) return true;
        BigInt cap;
        bool have_cap = false;
        if (!divisor3_cap(n, r.side[0], cap, have_cap)) return true;
        if (have_cap && cap < ulo) return true;
        BoundLd bl{in.x0l, in.y0l, us.side, us.exp, in.j0, in.j1};
        bl.fx = in.float_factor(0);
        bl.fy = in.float_factor(1);
        double est = approx_upper(bl, big_d(ulo));
        if (have_cap) est = std::min(est, big_d(cap));
        Range rg;
        if (est - big_d(ulo) <= 2.0 * SCAN_WINDOW) {
            rg = range_for(n, r, r.id[1]);
            apply_cap(rg, cap, have_cap);
            if (rg.empty) return true;
            if (!rg.unbounded && rg.hi - rg.lo <= static_cast<unsigned long>(SCAN_WINDOW)) {
                STATADD(d3_scan, 1);
                divisor3_scan(n, r, rg, ctx);
                return true;
            }
        } else {
            rg.empty = false;
            rg.lo = ulo;
            rg.unbounded = (us.hi == 0);
            if (us.hi) rg.hi = u64_to_bigint(us.hi);
            apply_cap(rg, cap, have_cap);
            if (rg.empty) return true;
        }
        bool want_scan = false;
        if (divisor3_native(n, r, rg, ctx, est - big_d(ulo), &want_scan)) {
            if (!want_scan) return true;
            Range ex = range_for(n, r, r.id[1]);
            apply_cap(ex, cap, have_cap);
            if (ex.empty) return true;
            if (!ex.unbounded && ex.hi - ex.lo <= static_cast<unsigned long>(BIG_T_SCAN_WINDOW)) {
                STATADD(d3_scan, 1);
                divisor3_scan(n, r, ex, ctx);
                return true;
            }
            if (divisor3_native(n, r, ex, ctx)) return true;
            rg = ex;
        }
        if (tail_divisor3(n, r, ctx, false, &rg)) return true;   // BigInt divisor route
        // degenerate (no divisor condition): the two strict orderings
        tail_divisor3(n, r, ctx, false);                          // v > u
        Rem rv;                                                   // v < u: congruence on v
        const int order3[3] = {1, 0, 2};
        for (int i : order3) {
            rv.id[rv.n] = r.id[i]; rv.side[rv.n] = r.side[i]; rv.exp[rv.n] = r.exp[i];
            ++rv.count[r.side[i]]; ++rv.n;
        }
        tail_progression(n, rv, ctx);
        return true;
    }
    const int su = r.side[0];
    const int ip = (r.side[1] == 0) ? 1 : 2, iq = (ip == 1) ? 2 : 1;
    const int uid = r.id[0], pid = r.id[ip], qid = r.id[iq];
    const BigInt &a0 = n.sx, &b0 = n.px, &c0 = n.sy, &d0 = n.py;
    const FreeSlot& us = n.cfg->slots[static_cast<std::size_t>(uid)];
    STATADD(d3, 1);

    // u range.  Exactly: u >= ulo (previous prime + 1) and the rigorous upper
    // test at ulo.  The full exact range is only worked out when a cheap
    // estimate says it is short (then the primes are simply tried).
    Range rg;
    if (fixed) {
        rg = *fixed;
    } else {
        BigInt ulo = (n.depth > 0) ? BigInt(n.prime + 1) : BigInt(2);
        raise_to(ulo, us.lo);
        {
            // the prime alone on its side: v if u and w share a side, else w
            const int zi = (r.side[0] == r.side[2]) ? 1 : 2;
            BigInt zf = ulo;                              // it is above u
            if (!alone_filter(n, r.side[zi], ulo, zf)) return true;
        }
        BoundIn in{&n.sx, &n.px, &n.sy, &n.py, us.side, us.exp,
                   r.count[0] - (us.side == 0 ? 1 : 0), r.count[1] - (us.side == 1 ? 1 : 0)};
        in.x0l = ratio_d(n.sx, n.px);
        in.y0l = ratio_d(n.sy, n.py);
        if (!upper_ok(in, ulo)) return true;
        BigInt cap;
        bool have_cap = false;
        if (!divisor3_cap(n, su, cap, have_cap)) return true;
        if (have_cap && cap < ulo) return true;
        BoundLd bl{in.x0l, in.y0l, us.side, us.exp, in.j0, in.j1};
        double est = approx_upper(bl, big_d(ulo));
        if (have_cap) est = std::min(est, big_d(cap));
        if (est - big_d(ulo) <= 2.0 * SCAN_WINDOW) {
            rg = range_for(n, r);
            apply_cap(rg, cap, have_cap);
            if (rg.empty) return true;
            if (!rg.unbounded && rg.hi - rg.lo <= static_cast<unsigned long>(SCAN_WINDOW)) {
                STATADD(d3_scan, 1);
                divisor3_scan(n, r, rg, ctx);
                return true;
            }
        } else {
            rg.empty = false;
            rg.lo = ulo;
            rg.unbounded = (us.hi == 0);
            if (us.hi) rg.hi = u64_to_bigint(us.hi);
            apply_cap(rg, cap, have_cap);
            if (rg.empty) return true;
        }
        bool want_scan = false;
        if (divisor3_native(n, r, rg, ctx, est - big_d(ulo), &want_scan)) {
            if (!want_scan) return true;
            Range ex = range_for(n, r);
            apply_cap(ex, cap, have_cap);
            if (ex.empty) return true;
            if (!ex.unbounded && ex.hi - ex.lo <= static_cast<unsigned long>(BIG_T_SCAN_WINDOW)) {
                STATADD(d3_scan, 1);
                divisor3_scan(n, r, ex, ctx);
                return true;
            }
            if (divisor3_native(n, r, ex, ctx)) return true;
            rg = ex;
        }
    }

    const BigInt d1 = a0 * d0 + b0 * c0 - a0 * c0;
    BigInt dz, T;
    if (su == 1) {
        dz = c0 * (b0 - a0);
        T = a0 * b0 * d0 + c0 * (b0 - a0) * (b0 - d0);
    } else {
        dz = a0 * (d0 - c0);
        T = b0 * c0 * d0 + a0 * (d0 - c0) * (d0 - b0);
    }
    if (d1 == 0 || T == 0) {
        if (fixed) return false;
        // degenerate: no divisor condition, every prime of the (finite) range is tried
        rg = range_for(n, r);
        if (rg.empty) return true;
        if (rg.unbounded) { ctx.flag(INC_UNBOUNDED); return true; }
        STATADD(d3_scan, 1);
        divisor3_scan(n, r, rg, ctx);
        return true;
    }

    Solved solved;
    BigInt a, b, c, d;
    auto try_u = [&](const BigInt& u) {
        add_u(a0, b0, c0, d0, su, u, a, b, c, d);
        solved.clear();
        solved.emplace_back(uid, u);
        mixed_closed(n, a, b, c, d, pid, qid, solved, ctx);
    };

    // D(u) = g*D'(u) with g = gcd(d1, d0) its content.  From g*D' | A0*(b+d)
    // (A0 = a0 if u is on side 1, c0 if on side 0) and g1 = gcd(g, A0):
    //     D' | (A0/g1) * (b+d)
    // and reducing b+d mod D' (T = g * (d1' b0 - d0 d0') resp. g * (d1' d0 - b0 d0')):
    //     D' | R* = (A0/g1) * (T/g)
    BigInt g, g1;
    mpz_gcd(g.get_mpz_t(), d1.get_mpz_t(), dz.get_mpz_t());
    const int aside = (su == 1) ? 0 : 1;
    const BigInt& A0 = (su == 1) ? a0 : c0;
    mpz_gcd(g1.get_mpz_t(), g.get_mpz_t(), A0.get_mpz_t());
    BigInt t = abs(T);
    if (!mpz_divisible_p(t.get_mpz_t(), g.get_mpz_t())) return true;     // cannot happen
    t /= g;
    const BigInt Rg = (A0 / g1) * t;
    const BigInt d1g = d1 / g, dzg = dz / g;

    const BigInt absR = abs(Rg);
    BigInt Flo, Fhi, max_abs;
    if (rg.unbounded) {
        Flo = -absR; Fhi = absR; max_abs = absR;
    } else {
        Flo = d1g * rg.lo + dzg;
        Fhi = d1g * rg.hi + dzg;
        if (Flo > Fhi) std::swap(Flo, Fhi);
        max_abs = std::max(BigInt(abs(Flo)), BigInt(abs(Fhi)));
        if (max_abs > absR) max_abs = absR;
        if (Flo < -max_abs) Flo = -max_abs;
        if (Fhi > max_abs) Fhi = max_abs;
    }
    if (Flo > Fhi || max_abs < 1) return true;
    const BigInt m = abs(d1g);
    BigInt tres;
    mpz_fdiv_r(tres.get_mpz_t(), dzg.get_mpz_t(), m.get_mpz_t());

    BigInt u;
    auto from_F = [&](const BigInt& F) {
        u = F - dzg;
        if (!mpz_divisible_p(u.get_mpz_t(), d1g.get_mpz_t())) return;
        u /= d1g;
        if (u < rg.lo || (!rg.unbounded && u > rg.hi)) return;
        if (divides_k(*n.sk, u) || !prime_test(u)) return;
        try_u(u);
    };

    STATADD(d3_big, 1);
    FacList Rf;
    collect_sig(n, aside, Rf);                   // factorisation of A0
    {
        BigInt rest = g1;                         // A0 / g1
        for (auto& [p, e] : Rf)
            while (e > 0 && mpz_divisible_p(rest.get_mpz_t(), p.get_mpz_t())) { rest /= p; --e; }
        if (rest != 1) return true;               // cannot happen (g1 | A0)
    }
    auto strip_one = [&](const BigInt& p) {
        int e = 0;
        while (mpz_divisible_p(t.get_mpz_t(), p.get_mpz_t())) { t /= p; ++e; }
        if (e) fac_add(Rf, p, e);
    };
    for (std::uint64_t p : n.cfg->strip64) strip_one(u64_to_bigint(p));
    for (const BigInt& p : n.cfg->strip_big) strip_one(p);
    factor_any(t, Rf);
    FacList rel;
    for (const auto& pe : Rf) if (pe.second > 0 && pe.first <= max_abs) rel.push_back(pe);
    u128 mabs = 0;
    i128 flo = 0, fhi = 0;
    const bool native_range = big_fits_u64(m) && big_to_u128(max_abs, mabs) && mabs <= I128_MAX_U128 &&
                              big_to_i128(Flo, flo) && big_to_i128(Fhi, fhi);
    if (native_range) {
        NatFactors nf2;
        if (to_nat(rel, nf2)) {
            signed_divisors_mod(nf2, mabs, flo, fhi, big_to_u64(m), big_to_u64(tres),
                                [&](i128 F) { from_F(from_i128(F)); });
            return true;
        }
    }
    big_signed_divisors_mod(rel, max_abs, Flo, Fhi, m, tres, [&](const BigInt& F) { from_F(F); });
    return true;
}

// ---------------------------------------------------------------------------
// Tail: [u, rest...] with u the last prime of its side, the rest (2 or more)
// on the other side.  Once u is known the other side's product W and sigma V
// are fixed (see tail_same), and both must be integers:
//    u on side 0:  (sx-px) u + sx == 0 (mod py)   and   sy | sx (u+1)
//    u on side 1:  (sy-py) u + sy == 0 (mod px)   and   sx | sy (u+1)
// so u runs through one residue class mod M.
// ---------------------------------------------------------------------------
bool lin_congr(const BigInt& A, const BigInt& B, const BigInt& m, BigInt& r, BigInt& M) {
    // A u == B (mod m)
    BigInt g;
    mpz_gcd(g.get_mpz_t(), A.get_mpz_t(), m.get_mpz_t());
    BigInt Bm;
    mpz_fdiv_r(Bm.get_mpz_t(), B.get_mpz_t(), g.get_mpz_t());
    if (Bm != 0) return false;
    M = m / g;
    if (M == 1) { r = 0; return true; }
    BigInt Ag = A / g, Bg = B / g, inv;
    mpz_fdiv_r(Ag.get_mpz_t(), Ag.get_mpz_t(), M.get_mpz_t());
    if (!mpz_invert(inv.get_mpz_t(), Ag.get_mpz_t(), M.get_mpz_t())) return false;
    r = Bg * inv;
    mpz_fdiv_r(r.get_mpz_t(), r.get_mpz_t(), M.get_mpz_t());
    return true;
}

bool crt2(const BigInt& r1, const BigInt& m1, const BigInt& r2, const BigInt& m2, BigInt& r, BigInt& M) {
    // u == r1 (mod m1), u == r2 (mod m2)
    BigInt g;
    mpz_gcd(g.get_mpz_t(), m1.get_mpz_t(), m2.get_mpz_t());
    BigInt diff = r2 - r1, dm;
    mpz_fdiv_r(dm.get_mpz_t(), diff.get_mpz_t(), g.get_mpz_t());
    if (dm != 0) return false;
    const BigInt m2g = m2 / g;
    BigInt t = 0;
    if (m2g > 1) {
        BigInt m1r, inv;
        mpz_fdiv_r(m1r.get_mpz_t(), BigInt(m1 / g).get_mpz_t(), m2g.get_mpz_t());
        if (!mpz_invert(inv.get_mpz_t(), m1r.get_mpz_t(), m2g.get_mpz_t())) return false;
        t = (diff / g) * inv;
        mpz_fdiv_r(t.get_mpz_t(), t.get_mpz_t(), m2g.get_mpz_t());
    }
    M = m1 * m2g;
    r = r1 + m1 * t;
    mpz_fdiv_r(r.get_mpz_t(), r.get_mpz_t(), M.get_mpz_t());
    return true;
}

// The class of u in 64/128-bit arithmetic (the same steps as lin_congr and
// crt2).  -1: the values do not fit (use BigInt), 0: no u, 1: u == res (mod M).
inline bool small63(const BigInt& v, u64& out) {
    if (mpz_sgn(v.get_mpz_t()) <= 0 || mpz_sizeinbase(v.get_mpz_t(), 2) > 63) return false;
    out = big_to_u64(v);
    return true;
}

inline u64 gcd_u64(u64 a, u64 b) {
    while (b) { const u64 t = a % b; a = b; b = t; }
    return a;
}

// a^-1 mod m (m >= 2, gcd(a, m) = 1)
inline bool inv_mod_u64(u64 a, u64 m, u64& out) {
    i128 t = 0, nt = 1, rr = m, nr = a % m;
    while (nr != 0) {
        const i128 q = rr / nr;
        i128 tmp = t - q * nt; t = nt; nt = tmp;
        tmp = rr - q * nr; rr = nr; nr = tmp;
    }
    if (rr != 1) return false;
    if (t < 0) t += m;
    out = static_cast<u64>(t);
    return true;
}

int prog_class_native(const Node& n, int su, u128& res, u128& M) {
    u64 a, b, c, d;
    if (!small63(n.sx, a) || !small63(n.px, b) || !small63(n.sy, c) || !small63(n.py, d)) return -1;
    // su = 0: (a-b) u == -a (mod d), u == -1 (mod c/gcd(c,a));  su = 1: mirrored
    const u64 A = (su == 0) ? a - b : c - d;              // sigma(n) >= n
    const u64 Bv = (su == 0) ? a : c;
    const u64 m1 = (su == 0) ? d : b;
    const u64 m2 = (su == 0) ? c / gcd_u64(c, a) : a / gcd_u64(a, c);
    const u64 Am = A % m1, Bm = (m1 - Bv % m1) % m1;
    const u64 g = gcd_u64(Am, m1);                        // gcd(0, m1) = m1
    if (Bm % g != 0) return 0;
    const u64 M1 = m1 / g;
    u64 r1 = 0;
    if (M1 > 1) {
        u64 inv;
        if (!inv_mod_u64((Am / g) % M1, M1, inv)) return 0;
        r1 = static_cast<u64>(static_cast<u128>((Bm / g) % M1) * inv % M1);
    }
    const u64 r2 = (m2 == 1) ? 0 : m2 - 1;                // -1 mod m2
    const u64 g2 = gcd_u64(M1, m2);
    const i128 diff = static_cast<i128>(r2) - static_cast<i128>(r1);
    if (diff % static_cast<i128>(g2) != 0) return 0;
    const u64 m2g = m2 / g2;
    u64 t = 0;
    if (m2g > 1) {
        u64 inv;
        if (!inv_mod_u64((M1 / g2) % m2g, m2g, inv)) return 0;
        const i128 dg = diff / static_cast<i128>(g2);
        const u64 dgm = static_cast<u64>(((dg % static_cast<i128>(m2g)) + static_cast<i128>(m2g)) % static_cast<i128>(m2g));
        t = static_cast<u64>(static_cast<u128>(dgm) * inv % m2g);
    }
    M = static_cast<u128>(M1) * m2g;
    res = static_cast<u128>(r1) + static_cast<u128>(M1) * t;     // < M
    return 1;
}

// The Progression tail (§9.4) in two steps, so a long walk over u can be
// shared out in pieces: prog_plan finds u's residue class u == res (mod M) and
// its first and last candidates; prog_visit runs the tail for the class
// members in [lo, hi] only, in increasing order.  tail_progression is the two
// over the whole range.
struct ProgPlan {
    Rem rest;                                    // the primes after u (a SameSide tail)
    int uid = -1;                                // u's slot
    BigInt res, M, first, hi;                    // u == res (mod M), first <= u <= hi
};

// false: no u can work (or the k was flagged)
bool prog_plan(const Node& n, const Rem& r, SearchCtx& ctx, ProgPlan& p) {
    const int su = r.side[0];
    const FreeSlot& us = n.cfg->slots[static_cast<std::size_t>(r.id[0])];
    BigInt ulo = (n.depth > 0) ? BigInt(n.prime + 1) : BigInt(2);
    raise_to(ulo, us.lo);
    BoundIn in{&n.sx, &n.px, &n.sy, &n.py, us.side, us.exp,
               r.count[0] - (us.side == 0 ? 1 : 0), r.count[1] - (us.side == 1 ? 1 : 0)};
    in.x0l = ratio_d(n.sx, n.px);
    in.y0l = ratio_d(n.sy, n.py);
    if (!upper_ok(in, ulo)) return false;        // no u at all (monotone test)
    BigInt& res = p.res;
    BigInt& M = p.M;
    u128 res_n = 0, M_n = 0;
    const int cls = prog_class_native(n, su, res_n, M_n);
    if (cls == 0) return false;
    if (cls == 1) {
        res = from_u128(res_n);
        M = from_u128(M_n);
    } else {
        BigInt A, B, m1, m2;
        if (su == 0) {
            A = n.sx - n.px; B = -n.sx; m1 = n.py;
            BigInt g; mpz_gcd(g.get_mpz_t(), n.sy.get_mpz_t(), n.sx.get_mpz_t());
            m2 = n.sy / g;
        } else {
            A = n.sy - n.py; B = -n.sy; m1 = n.px;
            BigInt g; mpz_gcd(g.get_mpz_t(), n.sx.get_mpz_t(), n.sy.get_mpz_t());
            m2 = n.sx / g;
        }
        BigInt r1, M1;
        if (!lin_congr(A, B, m1, r1, M1)) return false;
        BigInt r2;
        mpz_fdiv_r(r2.get_mpz_t(), BigInt(-1).get_mpz_t(), m2.get_mpz_t());
        if (!crt2(r1, M1, r2, m2, res, M)) return false;
    }

    p.rest = Rem();
    for (int i = 1; i < r.n; ++i) {
        p.rest.id[p.rest.n] = r.id[i]; p.rest.side[p.rest.n] = r.side[i]; p.rest.exp[p.rest.n] = r.exp[i];
        ++p.rest.count[r.side[i]]; ++p.rest.n;
    }
    p.uid = r.id[0];

    // first u >= ulo in the class.  If even that one fails the (monotone)
    // upper test, no u of the class can work: done without the full range.
    BigInt& first = p.first;
    BigInt off;
    first = ulo;
    mpz_fdiv_r(off.get_mpz_t(), BigInt(res - ulo).get_mpz_t(), M.get_mpz_t());
    first += off;
    if (us.hi != 0 && cmp_u64(first, us.hi) > 0) return false;
    if (!upper_ok(in, first)) return false;
    const Range rg = range_for(n, r);
    if (rg.empty) return false;
    if (rg.unbounded) { ctx.flag(INC_UNBOUNDED); return false; }
    if (first < rg.lo) {
        mpz_fdiv_r(off.get_mpz_t(), BigInt(res - rg.lo).get_mpz_t(), M.get_mpz_t());
        first = rg.lo + off;
    }
    if (first > rg.hi) return false;
    p.hi = rg.hi;
    return true;
}

// the class members u of p in [lo, hi] (clipped to [p.first, p.hi])
void prog_visit(const Node& n, const ProgPlan& p, const BigInt& lo, const BigInt& hi, SearchCtx& ctx) {
    const BigInt& res = p.res;
    const BigInt& M = p.M;
    BigInt first = p.first;
    if (first < lo) {
        BigInt off;
        mpz_fdiv_r(off.get_mpz_t(), BigInt(res - lo).get_mpz_t(), M.get_mpz_t());
        first = lo + off;
    }
    const BigInt& last = (hi < p.hi) ? hi : p.hi;
    if (first > last) return;
    Node child;                                  // reused: make_child sets every field the tail reads
    // V's factorisation without sigma(u), once for all u (a SameSide tail that needs it)
    SameBase base;
    if (!(p.rest.n == 1 || (p.rest.n == 2 && p.rest.exp[0] == 1 && p.rest.exp[1] == 1))) {
        const int side = p.rest.side[0];        // the primes after u; u is on the other side
        base.ok = collect_sig_nat(n, 1 - side, +1, base.primes, base.exps) &&
                  collect_sig_nat(n, side, -1, base.primes, base.exps);
    }
    auto handle = [&](const BigInt& u) {
        STATADD(prog_cand, 1);
        // p.uid explicitly: on a float3 root this tail runs on [v, u, w],
        // not in the root's order [u, v, w]
        if (!make_child(n, u, child, p.uid)) return;
        tail_same(child, p.rest, ctx, &base);   // sigma(u) is added to the base
    };
    static const u64 max_stop = primesieve::get_max_stop();
    BigInt ub;
    if (M < 64 && big_fits_u64(last) && big_to_u64(last) <= max_stop) {
        const u64 Mu = big_to_u64(M), ru = big_to_u64(res);
        scan_primes(*n.sk, first, last, ctx, [&](u64 q) {
            if (Mu > 1 && q % Mu != ru) return;
            set_u64(ub, q);
            handle(ub);
        });
        return;
    }
    std::uint64_t count = 0;
    if (big_fits_u64(last) && big_fits_u64(M)) {
        // the same walk in 64-bit arithmetic (is_probable_prime is is_prime_u64 here)
        const u64 L = big_to_u64(last), Mu = big_to_u64(M);
        for (u64 u = big_to_u64(first);;) {
            if ((++count & 255) == 0 && ctx.cancelled()) return;
            if (u >= 2 && is_prime_u64_fast(u)) {
                set_u64(ub, u);
                handle(ub);
            }
            if (L - u < Mu) break;               // the next member would pass last
            u += Mu;
        }
        return;
    }
    for (BigInt u = first; u <= last; u += M) {
        if ((++count & 255) == 0 && ctx.cancelled()) return;
        if (u < 2 || !prime_test(u)) continue;
        handle(u);
    }
}

void tail_progression(const Node& n, const Rem& r, SearchCtx& ctx) {
    STATADD(prog, 1);
    ProgPlan p;
    if (!prog_plan(n, r, ctx, p)) return;
    prog_visit(n, p, p.first, p.hi, ctx);
}

// which sides' sigma(p^e) factorisations the root's tail will use
void set_root_needs(const Config& cfg, RootShape& rt) {
    rt.need_sig[0] = rt.need_sig[1] = false;
    const int no = static_cast<int>(rt.order.size());
    for (int start = 0; start <= no; ++start) {
        Rem s;
        for (int j = start; j < no; ++j) {
            const FreeSlot& fs = cfg.slots[static_cast<std::size_t>(rt.order[static_cast<std::size_t>(j)])];
            s.id[s.n] = rt.order[static_cast<std::size_t>(j)];
            s.side[s.n] = fs.side;
            s.exp[s.n] = fs.exp;
            ++s.count[fs.side];
            ++s.n;
        }
        const Tail t = tail_kind(s);
        if (t == Tail::None) continue;
        rt.tail_depth = start;
        rt.prog_tail = (t == Tail::Progression);
        if (t == Tail::SameSide) {
            const bool simple = s.n == 1 || (s.n == 2 && s.exp[0] == 1 && s.exp[1] == 1);
            if (!simple) rt.need_sig[0] = rt.need_sig[1] = true;
        } else if (t == Tail::Divisor3) {
            rt.need_sig[s.side[0] == 1 ? 0 : 1] = true;
        } else if (t == Tail::Progression) {
            const bool simple = (s.n - 1 == 2 && s.exp[1] == 1 && s.exp[2] == 1) || s.n - 1 == 1;
            if (!simple) rt.need_sig[0] = rt.need_sig[1] = true;
        }
        return;
    }
}

void run_tail(const Node& n, const Rem& r, Tail t, SearchCtx& ctx) {
    switch (t) {
    case Tail::Done: {
        if (n.sx == n.sy && n.sx == n.px + n.py) emit(n, {}, ctx);
        return;
    }
    case Tail::SameSide: tail_same(n, r, ctx); return;
    case Tail::Mixed2: tail_mixed2(n, r, ctx); return;
    case Tail::Divisor3: tail_divisor3(n, r, ctx); return;
    case Tail::Progression: tail_progression(n, r, ctx); return;
    case Tail::None: return;
    }
}

} // namespace

// ---------------------------------------------------------------------------
// public
// ---------------------------------------------------------------------------
void factor_any(const BigInt& n0, FacList& out) {
    if (n0 <= 1) return;
    u128 v;
    if (big_to_u128(n0, v)) { factor_u128_into(v, out); return; }
    BigInt n = n0;
    for (u64 p : small_primes()) {
        if (mpz_divisible_ui_p(n.get_mpz_t(), p)) {
            int e = 0;
            while (mpz_divisible_ui_p(n.get_mpz_t(), p)) {
                mpz_divexact_ui(n.get_mpz_t(), n.get_mpz_t(), p);
                ++e;
            }
            fac_add(out, u64_to_bigint(p), e);
            if (big_to_u128(n, v)) { factor_u128_into(v, out); return; }
        }
    }
    if (n == 1) return;
    if (mpz_probab_prime_p(n.get_mpz_t(), 30) > 0) { fac_add(out, n, 1); return; }
    std::vector<std::pair<BigInt, int>> fl;
    factorize_flint(n, fl);
    for (const auto& [p, e] : fl) fac_add(out, p, e);
}

namespace {

inline bool mul_u128_ok(u128& a, u128 b) {
    if (b != 0 && a > (~u128(0)) / b) return false;
    a *= b;
    return true;
}

// sigma(p^e) in 128 bits (false: does not fit)
inline bool sigma_u128(u64 p, int e, u128& out) {
    u128 s = 1, pw = 1;
    for (int i = 0; i < e; ++i) {
        if (!mul_u128_ok(pw, p)) return false;
        if (s > ~u128(0) - pw) return false;
        s += pw;
    }
    out = s;
    return true;
}

// sigma(p^e) as 128-bit primes, cached per thread (the small primes recur in
// every k).  false: sigma(p^e) does not fit 128 bits.
bool cached_sigma_nat(u64 p, int e, const NatFactors*& out) {
    struct Slot { u64 p = 0; int e = 0; bool ok = false; NatFactors f; };
    static thread_local std::vector<Slot> table(1 << 12);
    Slot& sl = table[static_cast<std::size_t>((p * 0x9E3779B97F4A7C15ULL + static_cast<u64>(e)) >> 52)];
    if (sl.p != p || sl.e != e) {
        sl.p = p;
        sl.e = e;
        sl.f.clear();
        u128 sv = 1, pw = 1;
        bool fits = true;
        for (int i = 0; i < e && fits; ++i) {
            if (pw > (~u128(0)) / p) { fits = false; break; }
            pw *= p;
            if (sv > ~u128(0) - pw) { fits = false; break; }
            sv += pw;
        }
        sl.ok = fits;
        if (fits) {
            // sigma(p^e) = (p^n - 1)/(p - 1) = prod over d | n, d > 1 of Phi_d(p)
            // (n = e + 1): the cyclotomic pieces are much smaller numbers to
            // factor (sigma(p^3) = (p+1)(p^2+1), for example)
            const int nn = e + 1;
            u128 phi[129];
            for (int d = 2; d <= nn && sl.ok; ++d) {
                if (nn % d != 0) continue;
                u128 a = 0, q = 1;                          // 1 + p + ... + p^(d-1) <= sv
                for (int i = 0; i < d; ++i) { a += q; if (i + 1 < d) q *= p; }
                for (int m = 2; m < d; ++m)
                    if (d % m == 0) a /= phi[m];            // exact
                phi[d] = a;
                if (a <= 1) continue;
                if (a <= std::numeric_limits<std::uint64_t>::max()) {
                    U64FactorBuffer ub;
                    factorize_runtime_u64(static_cast<std::uint64_t>(a), ub);
                    for (std::size_t i = 0; i < ub.size; ++i) sl.f.add(ub[i].prime, ub[i].exponent);
                } else {
                    U128Factor buf[160];
                    int cnt = 0;
                    if (!factorize_runtime_u128(a, buf, cnt)) sl.ok = false;
                    else for (int i = 0; i < cnt; ++i) sl.f.add(buf[i].prime, buf[i].exponent);
                }
            }
        }
    }
    out = &sl.f;
    return sl.ok;
}

void shape_key(const Config& cfg, bool allow_split, std::vector<int>& key) {
    key.clear();
    key.push_back(allow_split ? 1 : 0);
    for (const FreeSlot& f : cfg.slots) { key.push_back(f.side); key.push_back(f.exp); }
    key.push_back(-1);
    key.insert(key.end(), cfg.free_ids[0].begin(), cfg.free_ids[0].end());
    key.push_back(-2);
    key.insert(key.end(), cfg.free_ids[1].begin(), cfg.free_ids[1].end());
}

// One root for every interleaving: the smaller member's free primes are
// scanned and the larger member's two (exponent 1) are solved by the divisor
// tail wherever they lie.  Needs the larger member to have exactly two free
// primes, and the smaller member one or two with the last of exponent 1.
// The scanned prime P1 (when there are two) is then bounded by N1's abundancy
// alone, x0 (1+1/P1)... > 2, which is finite only when sigma(K1) < 2 K1; the
// caller checks that (allow_split).  Otherwise the interleavings are used.
bool split_shape(const Config& cfg) {
    const auto& f0 = cfg.free_ids[0];
    const auto& f1 = cfg.free_ids[1];
    return (f0.size() == 1 || f0.size() == 2) && f1.size() == 2 &&
           cfg.slots[static_cast<std::size_t>(f0.back())].exp == 1 &&
           cfg.slots[static_cast<std::size_t>(f1[0])].exp == 1 &&
           cfg.slots[static_cast<std::size_t>(f1[1])].exp == 1;
}

std::vector<RootShape> make_shapes(const Config& cfg, bool allow_split) {
    {
        const auto& f0 = cfg.free_ids[0];
        const auto& f1 = cfg.free_ids[1];
        if (allow_split && split_shape(cfg) &&
            cfg.slots[static_cast<std::size_t>(f0.back())].exp == 1 &&
            cfg.slots[static_cast<std::size_t>(f1[0])].exp == 1 &&
            cfg.slots[static_cast<std::size_t>(f1[1])].exp == 1) {
            RootShape rt;
            rt.order.assign(f0.begin(), f0.end() - 1);
            rt.order.push_back(f1[0]);
            rt.order.push_back(f0.back());
            rt.order.push_back(f1[1]);
            rt.split3 = true;
            set_root_needs(cfg, rt);
            return {rt};
        }
    }
    std::vector<std::vector<int>> orders;
    std::vector<int> cur;
    interleave(cfg.free_ids[0], cfg.free_ids[1], 0, 0, cur, orders);
    std::vector<RootShape> shapes;
    std::vector<std::vector<int>> seen_float;
    for (const auto& o : orders) {
        RootShape rt;
        rt.order = o;
        const std::size_t no = rt.order.size();
        // last three = one prime v of one side and u < w of the other, all
        // exponent 1: the divisor tail solves them whatever v's position, so
        // the three orderings become one root  prefix + [u, v, w]
        if (no >= 3) {
            const FreeSlot* t3[3];
            int c0 = 0;
            bool ones = true;
            for (int i = 0; i < 3; ++i) {
                t3[i] = &cfg.slots[static_cast<std::size_t>(o[no - 3 + static_cast<std::size_t>(i)])];
                c0 += (t3[i]->side == 0);
                ones = ones && t3[i]->exp == 1;
            }
            if (ones && (c0 == 1 || c0 == 2)) {
                const int vside = (c0 == 1) ? 0 : 1;
                int v = -1, uw[2], nb = 0;
                for (int i = 0; i < 3; ++i) {
                    const int id = o[no - 3 + static_cast<std::size_t>(i)];
                    if (t3[i]->side == vside) v = id; else uw[nb++] = id;
                }
                std::vector<int> canon(o.begin(), o.end() - 3);
                canon.push_back(uw[0]);
                canon.push_back(v);
                canon.push_back(uw[1]);
                if (std::find(seen_float.begin(), seen_float.end(), canon) != seen_float.end()) continue;
                seen_float.push_back(canon);
                rt.order = std::move(canon);
                rt.float3 = true;
                set_root_needs(cfg, rt);
                shapes.push_back(std::move(rt));
                continue;
            }
        }
        if (no >= 2) {
            // last two on different sides, not both exponent >= 2: the tail
            // solves them in either order, so keep one of the two orderings
            const FreeSlot& fa = cfg.slots[static_cast<std::size_t>(rt.order[no - 2])];
            const FreeSlot& fb = cfg.slots[static_cast<std::size_t>(rt.order[no - 1])];
            if (fa.side != fb.side && !(fa.exp >= 2 && fb.exp >= 2)) {
                if (fa.side == 1) continue;              // the twin with side 0 first is kept
                rt.last2_free = true;
            }
        }
        set_root_needs(cfg, rt);
        shapes.push_back(std::move(rt));
    }
    return shapes;
}

// shapes are built once per slot layout and never freed (a handful per run)
const std::vector<RootShape>& root_shapes(const Config& cfg, bool allow_split) {
    static std::mutex mu;
    static std::vector<std::pair<std::vector<int>, std::unique_ptr<std::vector<RootShape>>>> cache;
    thread_local std::vector<int> last_key;
    thread_local std::vector<int> key;
    thread_local const std::vector<RootShape>* last = nullptr;
    shape_key(cfg, allow_split, key);
    if (last && key == last_key) return *last;
    std::lock_guard<std::mutex> lock(mu);
    const std::vector<RootShape>* found = nullptr;
    for (const auto& [k, v] : cache)
        if (k == key) { found = v.get(); break; }
    if (!found) {
        cache.emplace_back(key, std::make_unique<std::vector<RootShape>>(make_shapes(cfg, allow_split)));
        found = cache.back().second.get();
    }
    last_key = key;
    last = found;
    return *found;
}

} // namespace

bool build_search_k(std::uint64_t k, const HashSpec& hash, SearchK& out) {
    out.k = k;
    out.kb = u64_to_bigint(k);
    out.hash = &hash;
    out.kf.clear();
    out.configs.clear();
    out.roots.clear();
    if (k > 1) {
        U64FactorBuffer ub;
        factorize_runtime_u64(k, ub);
        for (std::size_t i = 0; i < ub.size; ++i) {
            bool merged = false;
            for (auto& [p, e] : out.kf)
                if (p == ub[i].prime) { e += ub[i].exponent; merged = true; }
            if (!merged) out.kf.emplace_back(ub[i].prime, ub[i].exponent);
        }
        std::sort(out.kf.begin(), out.kf.end());
    }
    // sigma(K2)/K2 >= sigma(k)/k (K2 only raises exponents of primes of k):
    // an abundant k (sigma(k) >= 2k) has y >= 2 from the start, so no pairs
    {
        u128 sk = 1;
        bool fit = true;
        for (const auto& [p, e] : out.kf) {
            u128 sp = 0;
            fit = fit && sigma_u128(p, e, sp) && mul_u128_ok(sk, sp);
        }
        if (fit && sk >= 2 * static_cast<u128>(k)) return false;
    }

    // bound slots and their candidates (primes of k with the slot's multiplicity)
    struct BSlot { int side, pos, mult; };
    BSlot bslots[32];
    int nb = 0;
    for (int s = 0; s < 2; ++s)
        for (std::size_t p = 0; p < hash.side[s].size(); ++p)
            if (hash.side[s][p].mult > 0) bslots[nb++] = {s, static_cast<int>(p), hash.side[s][p].mult};
    u64 cand[32][16];                                     // a 64-bit k has at most 15 distinct primes
    int ncand[32];
    std::size_t combos = 1;
    for (int i = 0; i < nb; ++i) {
        ncand[i] = 0;
        for (const auto& [p, e] : out.kf)
            if (e == bslots[i].mult) cand[i][ncand[i]++] = p;
        if (ncand[i] == 0) return false;
        combos = std::min<std::size_t>(combos * static_cast<std::size_t>(ncand[i]), 64);
    }
    out.configs.reserve(combos);
    const std::size_t nside[2] = {hash.side[0].size(), hash.side[1].size()};
    const std::size_t nkf = out.kf.size();

    u64 pick[32] = {};
    u64 sp[2][32];
    auto add_config = [&]() {
        for (int s = 0; s < 2; ++s)
            for (std::size_t q = 0; q < nside[s]; ++q) sp[s][q] = 0;
        for (int i = 0; i < nb; ++i) sp[bslots[i].side][bslots[i].pos] = pick[i];
        // bound primes increase along each side
        for (int s = 0; s < 2; ++s) {
            u64 last = 0;
            for (std::size_t q = 0; q < nside[s]; ++q) {
                if (sp[s][q] == 0) continue;
                if (sp[s][q] <= last) return;
                last = sp[s][q];
            }
        }
        // every free slot needs room between its bound neighbours
        for (int s = 0; s < 2; ++s)
            for (std::size_t p = 0; p < nside[s]; ++p) {
                if (sp[s][p] != 0) continue;
                u64 lo = 2, hi = 0;
                for (std::size_t q = 0; q < p; ++q) if (sp[s][q]) lo = std::max<u64>(lo, sp[s][q] + 1);
                for (std::size_t q = nside[s]; q-- > p + 1;) if (sp[s][q]) hi = sp[s][q] - 1;
                if (hi != 0 && hi < lo) return;
            }

        // K1, K2 (A1 times the bound primes' extra powers) and their sigmas,
        // in 128 bits when they fit
        int pe[2][16];                                    // exponent of each prime of k in K1, K2
        u128 ku[2], su[2];
        bool fit[2];
        for (int s = 0; s < 2; ++s) {
            ku[s] = k;
            su[s] = 1;
            fit[s] = true;
            for (std::size_t i = 0; i < nkf; ++i) {
                const u64 p = out.kf[i].first;
                int e = out.kf[i].second;
                for (std::size_t q = 0; q < nside[s]; ++q)
                    if (sp[s][q] == p) {
                        for (int a = 0; a < hash.side[s][q].exp; ++a) fit[s] = fit[s] && mul_u128_ok(ku[s], p);
                        e += hash.side[s][q].exp;
                    }
                pe[s][i] = e;
                u128 sv = 0;
                fit[s] = fit[s] && sigma_u128(p, e, sv) && mul_u128_ok(su[s], sv);
            }
        }
        // x = sigma(N1)/N1 and y = sigma(N2)/N2 only grow with the free primes,
        // and a pair needs y < 2 and (x-1)(y-1) = 1: a configuration already
        // past either limit has no pairs (exact integer tests)
        if (fit[0] && fit[1]) {
            if (su[1] - ku[1] >= ku[1]) return;
            u128 l, r;
            if (!__builtin_mul_overflow(su[0] - ku[0], su[1] - ku[1], &l) &&
                !__builtin_mul_overflow(ku[0], ku[1], &r)) {
                if (l > r) return;
            } else {
                const BigInt K1 = from_u128(ku[0]), K2 = from_u128(ku[1]);
                const BigInt S1 = from_u128(su[0]), S2 = from_u128(su[1]);
                if ((S1 - K1) * (S2 - K2) > K1 * K2) return;
            }
        }

        out.configs.emplace_back();
        Config& cfg = out.configs.back();
        BigInt* K[2] = {&cfg.K1, &cfg.K2};
        BigInt* S[2] = {&cfg.s1, &cfg.s2};
        FacList* SF[2] = {&cfg.s1f, &cfg.s2f};
        for (int s = 0; s < 2; ++s) {
            if (fit[s]) {
                *K[s] = from_u128(ku[s]);
                *S[s] = from_u128(su[s]);
            } else {                                      // BigInt (rare)
                *K[s] = out.kb;
                *S[s] = 1;
                for (std::size_t i = 0; i < nkf; ++i) {
                    const BigInt pb = u64_to_bigint(out.kf[i].first);
                    *K[s] *= pow_big(pb, pe[s][i] - out.kf[i].second);
                    *S[s] *= sigma_pow(pb, pe[s][i]);
                }
            }
        }
        if (!(fit[0] && fit[1]) &&
            (cfg.s2 >= 2 * cfg.K2 || (cfg.s1 - cfg.K1) * (cfg.s2 - cfg.K2) > cfg.K1 * cfg.K2)) {
            out.configs.pop_back();
            return;
        }
        // slots
        for (int s = 0; s < 2; ++s) cfg.slot_prime[s].assign(sp[s], sp[s] + nside[s]);
        cfg.slots.reserve(nside[0] + nside[1]);
        for (int s = 0; s < 2; ++s) {
            for (std::size_t p = 0; p < nside[s]; ++p) {
                if (sp[s][p] != 0) continue;
                FreeSlot fs;
                fs.side = s;
                fs.pos = static_cast<int>(p);
                fs.exp = hash.side[s][p].exp;
                for (std::size_t q = 0; q < p; ++q) if (sp[s][q]) fs.lo = std::max<u64>(fs.lo, sp[s][q] + 1);
                for (std::size_t q = nside[s]; q-- > p + 1;) if (sp[s][q]) fs.hi = sp[s][q] - 1;
                cfg.free_ids[s].push_back(static_cast<int>(cfg.slots.size()));
                cfg.slots.push_back(fs);
            }
        }
        // sigma(K1), sigma(K2) as primes
        std::size_t nprimes = nkf;
        for (int s = 0; s < 2; ++s) {
            NatFactors& sn = cfg.s_nat[s];
            cfg.s_nat_ok[s] = true;
            sn.primes.reserve(4 * nkf);
            sn.exps.reserve(4 * nkf);
            for (std::size_t i = 0; i < nkf; ++i) {
                // merged at once: the cache entry may be reused by the next call
                const NatFactors* part = nullptr;
                if (!cached_sigma_nat(out.kf[i].first, pe[s][i], part)) { cfg.s_nat_ok[s] = false; break; }
                for (std::size_t j = 0; j < part->primes.size(); ++j) sn.add(part->primes[j], part->exps[j]);
            }
            if (cfg.s_nat_ok[s]) {                                // check: the primes give sigma(K) back
                if (fit[s]) {
                    u128 prod = 1;
                    bool ok = true;
                    for (std::size_t j = 0; j < sn.primes.size() && ok; ++j)
                        for (int e = 0; e < sn.exps[j] && ok; ++e) ok = mul_u128_ok(prod, sn.primes[j]);
                    if (!ok || prod != su[s]) cfg.s_nat_ok[s] = false;
                } else {
                    BigInt prod = 1;
                    for (std::size_t j = 0; j < sn.primes.size(); ++j)
                        prod *= pow_big(from_u128(sn.primes[j]), sn.exps[j]);
                    if (prod != *S[s]) cfg.s_nat_ok[s] = false;
                }
            }
            if (cfg.s_nat_ok[s]) {
                nprimes += sn.primes.size();
            } else {
                sn.clear();                                      // rare: sigma(p^e) above 128 bits
                for (std::size_t i = 0; i < nkf; ++i)
                    fac_merge(*SF[s], cached_sigma_factors(u64_to_bigint(out.kf[i].first), pe[s][i]));
                nprimes += SF[s]->size();
            }
        }
        // primes worth stripping before factoring: those of k, s1, s2
        cfg.strip64.reserve(nprimes);
        for (const auto& pk : out.kf) cfg.strip64.push_back(pk.first);
        for (int s = 0; s < 2; ++s) {
            if (cfg.s_nat_ok[s]) {
                for (u128 p : cfg.s_nat[s].primes) {
                    if (p <= std::numeric_limits<std::uint64_t>::max()) cfg.strip64.push_back(static_cast<u64>(p));
                    else cfg.strip_big.push_back(from_u128(p));
                }
            } else {
                for (const auto& [p, e] : *SF[s]) {
                    if (big_fits_u64(p)) cfg.strip64.push_back(big_to_u64(p));
                    else cfg.strip_big.push_back(p);
                }
            }
        }
        std::sort(cfg.strip64.begin(), cfg.strip64.end());
        cfg.strip64.erase(std::unique(cfg.strip64.begin(), cfg.strip64.end()), cfg.strip64.end());
        cfg.strip_div.reserve(cfg.strip64.size());
        for (u64 p : cfg.strip64) {
            if (p % 2 == 0) continue;
            u64 x = p;                                    // p^-1 mod 2^64 (Newton: 3 -> 96 bits)
            for (int i = 0; i < 5; ++i) x *= 2 - p * x;
            u128 y = x;                                   // one more step: mod 2^128
            y *= 2 - static_cast<u128>(p) * y;
            cfg.strip_div.push_back({p, y, ~u128(0) / p});
        }
    };
    auto rec = [&](auto&& self, int i) -> void {
        if (i == nb) { add_config(); return; }
        for (int c = 0; c < ncand[i]; ++c) {
            const u64 p = cand[i][c];
            bool used = false;
            for (int j = 0; j < i; ++j) used = used || pick[j] == p;
            if (used) continue;
            pick[i] = p;
            self(self, i + 1);
        }
    };
    rec(rec, 0);

    for (std::size_t ci = 0; ci < out.configs.size(); ++ci) {
        const Config& c = out.configs[ci];
        const bool allow_split = split_shape(c) && (c.free_ids[0].size() == 1 || c.s1 < 2 * c.K1);
        const std::vector<RootShape>& shapes = root_shapes(c, allow_split);
        out.roots.reserve(out.roots.size() + shapes.size());
        for (const RootShape& sh : shapes) out.roots.push_back({static_cast<int>(ci), &sh});
    }
    return !out.roots.empty();
}

void root_node(const SearchK& sk, int root, Node& out) {
    out = Node{};
    out.sk = &sk;
    out.root = &sk.roots[static_cast<std::size_t>(root)];
    out.cfg = &sk.configs[static_cast<std::size_t>(out.root->config)];
    out.depth = 0;
    out.sx = out.cfg->s1;
    out.px = out.cfg->K1;
    out.sy = out.cfg->s2;
    out.py = out.cfg->K2;
    out.nat_state = -1;
}

Step classify(const Node& n) {
    return tail_kind(remaining(n)) == Tail::None ? Step::Enumerate : Step::Tail;
}

Range next_range(const Node& n) {
    const Rem r = remaining(n);
    if (r.n == 0) return Range{};
    return range_for(n, r);
}

bool make_child(const Node& parent, const BigInt& q, Node& child, int slot) {
    STATADD(children, 1);
    const int id = (slot >= 0) ? slot : parent.root->shape->order[static_cast<std::size_t>(parent.depth)];
    const FreeSlot& s = parent.cfg->slots[static_cast<std::size_t>(id)];
    if (cmp_u64(q, s.lo) < 0) return false;
    if (s.hi != 0 && cmp_u64(q, s.hi) > 0) return false;
    if (parent.depth > 0 && q <= parent.prime) return false;
    if (divides_k(*parent.sk, q)) return false;
    child.sk = parent.sk;
    child.cfg = parent.cfg;
    child.root = parent.root;
    child.parent = &parent;
    child.depth = parent.depth + 1;
    child.slot = id;
    child.prime = q;
    child.sig.clear();
    child.sig_nat.clear();
    child.sig_nat_ok = false;
    // sigma(q^e) is factored up front only for a node with scanned levels below
    // it (all of them share it); a tail node factors it when it needs it
    child.sig_done = parent.root->shape->need_sig[s.side] && child.depth < parent.root->shape->tail_depth;
    if (child.sig_done) {
        child.sig_nat_ok = sigma_factors_nat(q, s.exp, child.sig_nat);
        if (!child.sig_nat_ok) sigma_factors(q, s.exp, child.sig);
    }
    BigInt* ms = (s.side == 0) ? &child.sx : &child.sy;
    BigInt* mp = (s.side == 0) ? &child.px : &child.py;
    child.sx = parent.sx;
    child.px = parent.px;
    child.sy = parent.sy;
    child.py = parent.py;
    child.nat_state = -1;
    // q^e and sigma(q^e); unsigned long is only 32 bits on Windows, so the
    // _ui fast path is taken only when the value fits it
    if (s.exp == 1 && mpz_fits_ulong_p(q.get_mpz_t()) && mpz_cmp_ui(q.get_mpz_t(), ULONG_MAX - 1) < 0) {
        const unsigned long qv = mpz_get_ui(q.get_mpz_t());
        mpz_mul_ui(ms->get_mpz_t(), ms->get_mpz_t(), qv + 1);
        mpz_mul_ui(mp->get_mpz_t(), mp->get_mpz_t(), qv);
    } else {
        *ms *= sigma_pow(q, s.exp);
        *mp *= pow_big(q, s.exp);
    }
    return true;
}

void scan_children(const Node& n, std::uint64_t lo, std::uint64_t hi, SearchCtx& ctx) {
    if (hi < lo) return;
    primesieve::iterator it(prime_iter_start(lo), hi);
    std::uint64_t q;
    Node child;
    BigInt qb;
    while ((q = it.next_prime()) <= hi) {
        if (ctx.cancelled()) return;
        if (n.sk->k % q == 0) continue;
        qb = u64_to_bigint(q);
        if (!make_child(n, qb, child)) continue;
        process(child, ctx);
    }
}

void process(const Node& n, SearchCtx& ctx) {
    STATADD(procs, 1);
    if (ctx.cancelled()) return;
    const Rem r = remaining(n);
    const Tail t = tail_kind(r);
    if (t != Tail::None) { run_tail(n, r, t, ctx); return; }
    const Range rg = range_for(n, r);
    if (rg.empty) return;
    if (rg.unbounded) { ctx.flag(INC_UNBOUNDED); return; }
    static const std::uint64_t max_stop = primesieve::get_max_stop();
    if (!big_fits_u64(rg.hi) || big_to_u64(rg.hi) > max_stop) { ctx.flag(INC_SCAN_LIMIT); return; }
    scan_children(n, big_to_u64(rg.lo), big_to_u64(rg.hi), ctx);
}

bool is_progression(const Node& n) {
    return tail_kind(remaining(n)) == Tail::Progression;
}

bool progression_range(const Node& n, SearchCtx& ctx, BigInt& first, BigInt& hi, BigInt& modulus,
                       ProgressionPlan* plan) {
    ProgPlan p;
    if (!prog_plan(n, remaining(n), ctx, p)) return false;
    first = p.first;
    hi = p.hi;
    modulus = p.M;
    if (plan) *plan = std::make_shared<const ProgPlan>(std::move(p));
    return true;
}

void progression_visit(const Node& n, std::uint64_t lo, std::uint64_t hi, SearchCtx& ctx,
                       const ProgressionPlan& plan) {
    if (plan) {                                  // the tail's own plan, made when it was split off
        prog_visit(n, *static_cast<const ProgPlan*>(plan.get()), u64_to_bigint(lo), u64_to_bigint(hi), ctx);
        return;
    }
    ProgPlan p;
    if (!prog_plan(n, remaining(n), ctx, p)) return;
    prog_visit(n, p, u64_to_bigint(lo), u64_to_bigint(hi), ctx);
}

void progression_tail(const Node& n, SearchCtx& ctx, const ProgressionSplit& split) {
    ProgPlan p;
    if (!prog_plan(n, remaining(n), ctx, p)) return;
    if (split) {
        const std::function<ProgressionPlan()> share = [&p]() -> ProgressionPlan {
            return std::make_shared<const ProgPlan>(p);
        };
        if (split(p.first, p.hi, p.M, share)) return;
    }
    prog_visit(n, p, p.first, p.hi, ctx);
}

namespace {

std::string config_label(const Config& cfg) {
    std::ostringstream lab;
    bool first = true;
    for (int s = 0; s < 2; ++s)
        for (std::size_t p = 0; p < cfg.slot_prime[s].size(); ++p)
            if (cfg.slot_prime[s][p]) {
                lab << (first ? "" : ",") << (s == 0 ? 'P' : 'Q') << (p + 1) << '=' << cfg.slot_prime[s][p];
                first = false;
            }
    return lab.str();
}

std::string root_label(const Config& cfg, const Root& root) {
    const RootShape& rt = *root.shape;
    std::string lab;
    const std::size_t no = rt.order.size();
    if (rt.split3) {                                  // e.g. "P1<P2, then {P3; Q1<Q2}"
        for (std::size_t i = 0; i + 3 < no; ++i) lab += (i == 0 ? "" : "<") + slot_name(cfg, rt.order[i]);
        lab += std::string(no > 3 ? ", then " : "") + "{" + slot_name(cfg, rt.order[no - 2]) + "; " +
               slot_name(cfg, rt.order[no - 3]) + "<" + slot_name(cfg, rt.order[no - 1]) + "}";
        return lab;
    }
    for (std::size_t i = 0; i < no; ++i) {
        const bool open = (rt.last2_free && i == no - 2) || (rt.float3 && i == no - 3);
        const bool close = (rt.last2_free || rt.float3) && i == no - 1;
        if (rt.float3 && i == no - 2) { lab += "," + slot_name(cfg, rt.order[i]); continue; }
        lab += (i == 0 ? "" : (close ? "," : "<")) + std::string(open ? "{" : "") +
               slot_name(cfg, rt.order[i]) + (close ? "}" : "");
    }
    return lab.empty() ? "(no free primes)" : lab;
}

} // namespace

std::string root_name(const SearchK& sk, int root) {
    const Root& rt = sk.roots[static_cast<std::size_t>(root)];
    const Config& cfg = sk.configs[static_cast<std::size_t>(rt.config)];
    std::string s = root_label(cfg, rt);
    const std::string c = config_label(cfg);
    if (!c.empty()) s += "  [" + c + "]";
    return s;
}

std::string describe_plan(const SearchK& sk) {
    std::ostringstream o;
    for (std::size_t i = 0; i < sk.roots.size(); ++i) {
        Node n;
        root_node(sk, static_cast<int>(i), n);
        Rem r = remaining(n);
        int scanned = 0;
        std::string tail = "none";
        for (int start = 0; start <= r.n; ++start) {
            Rem s;
            for (int j = start; j < r.n; ++j) {
                s.id[s.n] = r.id[j]; s.side[s.n] = r.side[j]; s.exp[s.n] = r.exp[j];
                ++s.count[r.side[j]]; ++s.n;
            }
            const Tail t = tail_kind(s);
            if (t == Tail::None) { ++scanned; continue; }
            switch (t) {
            case Tail::Done: tail = "check"; break;
            case Tail::SameSide: tail = "same-side solve"; break;
            case Tail::Mixed2: tail = "closed form"; break;
            case Tail::Divisor3: tail = "divisor"; break;
            case Tail::Progression: tail = "congruence"; break;
            default: break;
            }
            break;
        }
        o << "  root " << i << ": " << root_name(sk, static_cast<int>(i));
        o << "   scan " << scanned << " prime(s), then " << tail << '\n';
    }
    return o.str();
}

} // namespace amicable
