#ifndef AMICABLE_DIVISORS_H
#define AMICABLE_DIVISORS_H

// Divisor enumeration with a congruence filter:  all signed divisors F of a
// number R (given by its factorisation) with |F| <= max_abs, lo <= F <= hi and
// F == t (mod m).  Used by the "divisor" tail: F = D(u) must divide R and
// F == delta0 (mod delta1).
//
// Native path (everything below 2^127, m < 2^64): meet-in-the-middle on the
// residues mod m (the primes of R are split into two halves; one half goes
// into a hash table keyed by residue, the other half looks up the residue it
// needs).  Primes R shares with m are handled exactly (forced exponents + CRT).
// The residue products use 8-lane vector code (AVX-512 with -march=native).
// BigInt path: plain recursive walk, pruned by max_abs.

#include "factoring.h"

#include <algorithm>
#include <cstdint>
#include <utility>
#include <vector>

namespace amicable {

using u128 = unsigned __int128;
using i128 = __int128;

constexpr u128 I128_MAX_U128 = (u128(1) << 127) - 1;

[[nodiscard]] constexpr bool prod_fits(u128 a, u128 b) noexcept {
    return a == 0 || b <= I128_MAX_U128 / a;
}

// a*b <= limit (and a*b <= 2^127-1, as prod_fits); out = a*b when that fits.
// Same result as prod_fits + compare, without its 128-bit division (that
// division was the most frequent call in the divisor search).
[[nodiscard]] inline bool mul_le(u128 a, u128 b, u128 limit, u128& out) noexcept {
    u128 p;
    if (__builtin_mul_overflow(a, b, &p) || p > I128_MAX_U128) return false;
    out = p;
    return p <= limit;
}

struct NatFactors {
    std::vector<u128> primes;
    std::vector<int> exps;

    void clear() { primes.clear(); exps.clear(); }
    void add(u128 p, int e) {
        if (e <= 0) return;
        for (std::size_t i = 0; i < primes.size(); ++i)
            if (primes[i] == p) { exps[i] += e; return; }
        primes.push_back(p);
        exps.push_back(e);
    }
};

// x*y mod d with a floating-point quotient (d < 2^62) or u128 %
struct ModD {
    std::uint64_t d = 1;
    int kind = 0;               // 0: d < 2^52 (double), 1: d < 2^62 (long double), 2: u128 %
    double invd = 0.0;
    long double invdl = 0.0L;

    explicit ModD(std::uint64_t m) : d(m) {
        if (m < (std::uint64_t{1} << 52)) { kind = 0; invd = 1.0 / static_cast<double>(m); }
        else if (m < (std::uint64_t{1} << 62)) { kind = 1; invdl = 1.0L / static_cast<long double>(m); }
        else kind = 2;
    }

    [[nodiscard]] inline std::uint64_t mul(std::uint64_t a, std::uint64_t b) const noexcept {
        if (kind == 0) {
            const auto q = static_cast<std::uint64_t>(
                static_cast<double>(a) * static_cast<double>(b) * invd);
            auto r = static_cast<std::int64_t>(a * b - q * d);
            const auto sd = static_cast<std::int64_t>(d);
            while (r < 0) r += sd;
            while (r >= sd) r -= sd;
            return static_cast<std::uint64_t>(r);
        }
        if (kind == 1) {
            // the quotient estimate is only good to +-1 with a 64-bit long double
            // mantissa; a thread running the x87 unit at 53 bits (Windows' default
            // for new threads) or a 53-bit long double gets a far worse one.  The
            // remainder is therefore computed exactly and checked.
            const auto q = static_cast<std::uint64_t>(
                static_cast<long double>(a) * static_cast<long double>(b) * invdl);
            const u128 ab = static_cast<u128>(a) * b, qd = static_cast<u128>(q) * d;
            if (qd <= ab) {
                const u128 r = ab - qd;
                if (r < d) return static_cast<std::uint64_t>(r);
                if (r < 2 * static_cast<u128>(d)) return static_cast<std::uint64_t>(r - d);
            } else if (qd - ab <= d) {
                return static_cast<std::uint64_t>((d - (qd - ab)) % d);
            }
            return static_cast<std::uint64_t>(ab % d);
        }
        return static_cast<std::uint64_t>((static_cast<u128>(a) * b) % d);
    }
};

[[nodiscard]] std::uint64_t inv_mod_u64(std::uint64_t a, std::uint64_t m);
void mulmod_array(const ModD& md, std::uint64_t* a, std::uint64_t c, std::size_t n);

struct FreePrime {
    u128 p;
    std::uint64_t pres;     // p mod M
    std::uint64_t pinv;     // p^-1 mod M
    int emin, emax;
};

struct HalfList {
    std::vector<u128> val;
    std::vector<std::uint64_t> res;
    void clear() { val.clear(); res.clear(); }
    [[nodiscard]] std::size_t size() const { return val.size(); }
};

struct MitmScratch {
    HalfList da, db, tmp;
    std::vector<std::int32_t> table;
    std::vector<FreePrime> freep;
    std::vector<int> group;
    std::vector<std::size_t> order;
    std::vector<std::uint64_t> want[2];          // T[j] * a^-1 for the first half
    std::vector<std::uint64_t> pfx;              // prefix products (group_inverses)
};

MitmScratch& mitm_scratch();

// pinv = pres^-1 mod M for the free primes of group `which` (the only ones
// whose inverse is used), with one inversion for all of them (Montgomery's
// trick).  The inverse of the product is checked; if the check fails (a prime
// not coprime to M, which divisors_with_residue never passes) every prime is
// inverted on its own, as before.
void group_inverses(std::vector<FreePrime>& fp, const std::vector<int>& group, int which,
                    std::uint64_t M, const ModD& md, std::vector<std::uint64_t>& pfx);

void half_divisors(const std::vector<FreePrime>& fp, const std::vector<int>& group, int which,
                   bool inverse, std::uint64_t start, u128 limit, const ModD& md,
                   HalfList& out, HalfList& tmp);

// u == T[j] (mod M) for one of nt (1 or 2) targets, u = product over the free
// primes, u <= limit.  Calls fn(u, j).
template <typename Fn>
void mitm_solve(std::vector<FreePrime>& fp, std::uint64_t M, const std::uint64_t* T, int nt, u128 limit, Fn& fn)
{
    MitmScratch& S = mitm_scratch();
    const ModD md(M);
    for (FreePrime& f : fp) {
        f.pres = (f.p >> 64) == 0 ? static_cast<std::uint64_t>(f.p) % M : static_cast<std::uint64_t>(f.p % M);
        f.pinv = 0;
    }

    const std::size_t n = fp.size();
    S.group.assign(n, 0);
    S.order.resize(n);
    for (std::size_t i = 0; i < n; ++i) S.order[i] = i;
    std::sort(S.order.begin(), S.order.end(), [&](std::size_t x, std::size_t y) {
        return fp[x].emax - fp[x].emin > fp[y].emax - fp[y].emin;
    });
    double ca = 1.0, cb = 1.0;
    for (std::size_t i : S.order) {
        const double c = fp[i].emax - fp[i].emin + 1;
        if (ca <= cb) { S.group[i] = 0; ca *= c; } else { S.group[i] = 1; cb *= c; }
    }

    if (M > 1) group_inverses(fp, S.group, 0, M, md, S.pfx);

    // A side: a^-1 mod M;  B side: b mod M.  Match  b == T * a^-1.
    half_divisors(fp, S.group, 0, true, 1, limit, md, S.da, S.tmp);
    if (S.da.size() == 0) return;
    half_divisors(fp, S.group, 1, false, 1, limit, md, S.db, S.tmp);
    if (S.db.size() == 0) return;

    // the residue each a needs, T[j] * a^-1, for all a at once (vector code)
    const std::size_t na = S.da.size(), nb = S.db.size();
    for (int tj = 0; tj < nt; ++tj) {
        S.want[tj].assign(S.da.res.begin(), S.da.res.end());
        mulmod_array(md, S.want[tj].data(), T[tj] % M, na);
    }
    // A 4096-bit filter of the B residues: a residue whose bit is clear is not
    // among them, so its lookup is skipped (almost every lookup finds nothing).
    // It only skips lookups that cannot match: every match is still visited.
    std::uint64_t filt[64] = {};
    auto fbit = [](std::uint64_t key) { return static_cast<unsigned>((key * 0x9E3779B97F4A7C15ULL) >> 52); };
    for (std::size_t j = 0; j < nb; ++j) {
        const unsigned b = fbit(S.db.res[j]);
        filt[b >> 6] |= std::uint64_t{1} << (b & 63);
    }
    auto maybe = [&](std::uint64_t key) {
        const unsigned b = fbit(key);
        return ((filt[b >> 6] >> (b & 63)) & 1) != 0;
    };
    if (nb <= 64) {
        // short B side: a lookup that passes the filter scans it directly
        for (std::size_t i = 0; i < na; ++i) {
            for (int tj = 0; tj < nt; ++tj) {
                const std::uint64_t want = S.want[tj][i];
                if (!maybe(want)) continue;
                for (std::size_t j = 0; j < nb; ++j) {
                    if (S.db.res[j] != want) continue;
                    u128 u;
                    if (!mul_le(S.da.val[i], S.db.val[j], limit, u)) continue;
                    fn(u, tj);
                }
            }
        }
        return;
    }
    std::size_t tsize = 16;
    while (tsize < 2 * nb) tsize <<= 1;
    const std::size_t mask = tsize - 1;
    S.table.assign(tsize, -1);
    auto slot_of = [&](std::uint64_t key) {
        return static_cast<std::size_t>((key * 0x9E3779B97F4A7C15ULL) >> 29) & mask;
    };
    for (std::size_t j = 0; j < nb; ++j) {
        std::size_t h = slot_of(S.db.res[j]);
        while (S.table[h] >= 0) h = (h + 1) & mask;
        S.table[h] = static_cast<std::int32_t>(j);
    }
    for (std::size_t i = 0; i < na; ++i) {
        for (int tj = 0; tj < nt; ++tj) {
            const std::uint64_t want = S.want[tj][i];
            if (!maybe(want)) continue;
            std::size_t h = slot_of(want);
            while (S.table[h] >= 0) {
                const auto j = static_cast<std::size_t>(S.table[h]);
                h = (h + 1) & mask;
                if (S.db.res[j] != want) continue;
                u128 u;
                if (!mul_le(S.da.val[i], S.db.val[j], limit, u)) continue;
                fn(u, tj);
            }
        }
    }
}

// Divisors v of R with v == t[j] (mod d) (nt = 1 or 2 targets; with 2 they
// must be t and -t), v <= max_abs (MITM).  fn(v, j).
// Returns false when the congruence is too weak to be worth it (caller walks).
template <typename Fn>
bool divisors_with_residue(const NatFactors& f, std::uint64_t d, u128 max_abs,
                           const std::uint64_t* t, int nt, Fn& fn)
{
    const std::size_t n = f.primes.size();
    if (n == 0 || n > 256 || d < 2) return false;
    double ndiv = 1;
    for (int e : f.exps) ndiv *= e + 1;
    if (ndiv < 96) return false;                    // tiny: a plain walk is cheaper

    std::uint64_t d2 = d;
    MitmScratch& S = mitm_scratch();
    S.freep.clear();
    u128 fixed = 1;
    std::uint64_t crt_mod[64], crt_qm[64], crt_ps[64];
    std::uint64_t crt_res[2][64];
    std::size_t ncrt = 0;

    for (std::size_t i = 0; i < n; ++i) {
        const u128 p = f.primes[i];
        int m = 0;
        std::uint64_t qm = 1;
        if (p <= d2) {
            const auto p64 = static_cast<std::uint64_t>(p);
            while (d2 % p64 == 0) { d2 /= p64; ++m; qm *= p64; }
        }
        if (m == 0) {
            S.freep.push_back({p, 0, 0, 0, f.exps[i]});
            continue;
        }
        const auto p64 = static_cast<std::uint64_t>(p);
        const std::uint64_t tr = t[0] % qm;
        if (tr == 0) {
            if (f.exps[i] < m) return true;             // no solution for any target
            S.freep.push_back({p, 0, 0, m, f.exps[i]});
            continue;
        }
        int sv = 0;
        std::uint64_t x = tr, ps = 1;
        while (x % p64 == 0) { x /= p64; ++sv; ps *= p64; }
        if (sv > f.exps[i]) return true;
        if (!mul_le(fixed, ps, max_abs, fixed)) return true;
        if (ncrt >= 64) return false;
        crt_mod[ncrt] = qm / ps;
        crt_qm[ncrt] = qm;
        crt_ps[ncrt] = ps;
        ++ncrt;
    }
    // v = fixed * u and  v/ps == t/ps (mod qm/ps)  for each piece, so
    // u == (t/ps) * (fixed/ps)^-1  (mod qm/ps)      (fixed/ps is prime to p)
    for (std::size_t c = 0; c < ncrt; ++c) {
        const std::uint64_t mod = crt_mod[c];
        for (int tj = 0; tj < nt; ++tj) {
            if (mod == 1) { crt_res[tj][c] = 0; continue; }
            const std::uint64_t base = (t[tj] % crt_qm[c] / crt_ps[c]) % mod;
            const auto other = static_cast<std::uint64_t>((fixed / crt_ps[c]) % mod);
            crt_res[tj][c] = static_cast<std::uint64_t>(
                (static_cast<u128>(base) * inv_mod_u64(other, mod)) % mod);
        }
    }

    std::uint64_t T[2] = {0, 0};
    std::uint64_t M = d2;
    const std::uint64_t finv = (d2 > 1) ? inv_mod_u64(static_cast<std::uint64_t>(fixed % d2), d2) : 0;
    for (int tj = 0; tj < nt; ++tj) {
        std::uint64_t Mt = d2, Tt = (d2 > 1) ? ModD(d2).mul(t[tj] % d2, finv) : 0;
        for (std::size_t c = 0; c < ncrt; ++c) {
            const std::uint64_t mi = crt_mod[c], ri = crt_res[tj][c];
            const std::uint64_t Mmod = Mt % mi;
            const std::uint64_t Tmod = Tt % mi;
            const std::uint64_t diff = (ri + mi - Tmod) % mi;
            const std::uint64_t kk = (mi == 1) ? 0
                : static_cast<std::uint64_t>((static_cast<u128>(diff) * inv_mod_u64(Mmod, mi)) % mi);
            Tt = static_cast<std::uint64_t>(static_cast<u128>(Tt) + static_cast<u128>(Mt) * kk);
            Mt *= mi;
        }
        T[tj] = Tt;
        M = Mt;
    }
    if (M < 64) return false;

    const u128 limit = max_abs / fixed;
    auto emit = [&](u128 u, int tj) { fn(fixed * u, tj); };
    mitm_solve(S.freep, M, T, nt, limit, emit);
    return true;
}

// plain walk over all divisors v <= max_abs
template <typename Fn>
void walk_divisors(const NatFactors& f, std::size_t idx, u128 cur, u128 max_abs, Fn& fn) {
    if (idx == f.primes.size()) { fn(cur); return; }
    const u128 p = f.primes[idx];
    u128 v = cur;
    for (int e = 0; e <= f.exps[idx]; ++e) {
        walk_divisors(f, idx + 1, v, max_abs, fn);
        if (e == f.exps[idx]) break;
        if (!mul_le(v, p, max_abs, v)) break;
    }
}

// walk over all divisors v <= max_abs carrying v mod m; fn(v, j) when v == want[j]
template <typename Fn>
void walk_residues(const NatFactors& f, const std::vector<std::uint64_t>& pres, std::size_t idx,
                   u128 cur, std::uint64_t res, u128 max_abs, const ModD& md,
                   const std::uint64_t* want, int nt, Fn& fn) {
    if (idx == f.primes.size()) {
        for (int j = 0; j < nt; ++j) if (res == want[j]) fn(cur, j);
        return;
    }
    const u128 p = f.primes[idx];
    u128 v = cur;
    std::uint64_t r = res;
    for (int e = 0; e <= f.exps[idx]; ++e) {
        walk_residues(f, pres, idx + 1, v, r, max_abs, md, want, nt, fn);
        if (e == f.exps[idx]) break;
        if (!mul_le(v, p, max_abs, v)) break;
        r = md.mul(r, pres[idx]);
    }
}

// Signed divisors F of R:  |F| <= max_abs, lo <= F <= hi, F == t (mod m).
template <typename Fn>
void signed_divisors_mod(const NatFactors& f, u128 max_abs, i128 lo, i128 hi,
                         std::uint64_t m, std::uint64_t t, Fn&& fn)
{
    // v = |F|:  +v == t  or  -v == t  (mod m)
    std::uint64_t want[2];
    int sign[2];
    int nt = 0;
    if (hi >= 1) { want[nt] = (m <= 1) ? 0 : t % m; sign[nt] = 1; ++nt; }
    if (lo <= -1) { want[nt] = (m <= 1) ? 0 : (m - t % m) % m; sign[nt] = -1; ++nt; }
    if (nt == 0) return;
    auto take = [&](u128 v, int j) {
        const i128 F = (sign[j] > 0) ? static_cast<i128>(v) : -static_cast<i128>(v);
        if (F < lo || F > hi) return;
        fn(F);
    };
    if (m >= 2) {
        // with both signs the targets are t and -t, as divisors_with_residue needs
        if (divisors_with_residue(f, m, max_abs, want, nt, take)) return;
        const ModD md(m);
        std::vector<std::uint64_t> pres(f.primes.size());
        for (std::size_t i = 0; i < f.primes.size(); ++i)
            pres[i] = static_cast<std::uint64_t>(f.primes[i] % m);
        walk_residues(f, pres, 0, u128(1), 1 % m, max_abs, md, want, nt, take);
    } else {
        auto all = [&](u128 v) { for (int j = 0; j < nt; ++j) take(v, j); };
        walk_divisors(f, 0, u128(1), max_abs, all);
    }
}

// BigInt version: plain walk
using BigFacList = std::vector<std::pair<BigInt, int>>;

template <typename Fn>
void walk_big(const BigFacList& f, std::size_t idx, const BigInt& cur, const BigInt& max_abs, Fn& fn) {
    if (idx == f.size()) { fn(cur); return; }
    BigInt v = cur;
    for (int e = 0; e <= f[idx].second; ++e) {
        walk_big(f, idx + 1, v, max_abs, fn);
        if (e == f[idx].second) break;
        v *= f[idx].first;
        if (v > max_abs) break;
    }
}

template <typename Fn>
void big_signed_divisors_mod(const BigFacList& f, const BigInt& max_abs, const BigInt& lo,
                             const BigInt& hi, const BigInt& m, const BigInt& t, Fn&& fn)
{
    BigInt F, r;
    auto check = [&](const BigInt& v) {
        for (int sign = 1; sign >= -1; sign -= 2) {
            F = (sign > 0) ? v : BigInt(-v);
            if (F < lo || F > hi) continue;
            if (m > 1) {
                r = F - t;
                if (!mpz_divisible_p(r.get_mpz_t(), m.get_mpz_t())) continue;
            }
            fn(F);
        }
    };
    walk_big(f, 0, BigInt(1), max_abs, check);
}

} // namespace amicable

#endif
