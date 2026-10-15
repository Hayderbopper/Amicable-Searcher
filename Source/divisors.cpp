#include "divisors.h"

namespace amicable {

std::uint64_t inv_mod_u64(std::uint64_t a, std::uint64_t m) {
    // a coprime to m, m > 1
    if (m < (std::uint64_t{1} << 63)) {
        std::int64_t t = 0, nt = 1;
        auto r = static_cast<std::int64_t>(m);
        auto nr = static_cast<std::int64_t>(a % m);
        while (nr != 0) {
            const std::int64_t q = r / nr;
            std::int64_t tmp = t - q * nt; t = nt; nt = tmp;
            tmp = r - q * nr; r = nr; nr = tmp;
        }
        if (t < 0) t += static_cast<std::int64_t>(m);
        return static_cast<std::uint64_t>(t);
    }
    i128 t = 0, new_t = 1;
    i128 r = m, new_r = a % m;
    while (new_r != 0) {
        const i128 q = r / new_r;
        i128 tmp = t - q * new_t; t = new_t; new_t = tmp;
        tmp = r - q * new_r; r = new_r; new_r = tmp;
    }
    if (t < 0) t += m;
    return static_cast<std::uint64_t>(t);
}

// ---------------------------------------------------------------------------
// out[i] = in[i] * c mod d for a whole array.  For d < 2^52 this is written
// with 8-lane vectors (GCC vector extensions): with -march=native on an
// AVX-512 CPU it becomes zmm code, eight residues per instruction.
// ---------------------------------------------------------------------------
#if defined(__GNUC__)
typedef std::uint64_t v8u __attribute__((vector_size(64)));
typedef std::int64_t v8i __attribute__((vector_size(64)));
typedef double v8d __attribute__((vector_size(64)));
#define AMICABLE_HAVE_VEC 1
#endif

void mulmod_array(const ModD& md, std::uint64_t* a, std::uint64_t c, std::size_t n) {
    std::size_t i = 0;
#ifdef AMICABLE_HAVE_VEC
    if (md.kind == 0) {
        const v8u dv = (v8u){} + md.d;
        const v8i sd = (v8i){} + static_cast<std::int64_t>(md.d);
        const v8u cv = (v8u){} + c;
        const v8d scale = (v8d){} + static_cast<double>(c) * md.invd;
        for (; i + 8 <= n; i += 8) {
            v8u x;
            __builtin_memcpy(&x, a + i, sizeof x);
            const v8d xd = __builtin_convertvector(x, v8d);
            const v8u q = __builtin_convertvector(xd * scale, v8u);
            v8i r = reinterpret_cast<v8i>(x * cv - q * dv);
            r += (r < 0) & sd;
            r += (r < 0) & sd;
            r -= (r >= sd) & sd;
            r -= (r >= sd) & sd;
            __builtin_memcpy(a + i, &r, sizeof r);
        }
    }
#endif
    for (; i < n; ++i) a[i] = md.mul(a[i], c);
}

MitmScratch& mitm_scratch() {
    static thread_local MitmScratch s;
    return s;
}

void group_inverses(std::vector<FreePrime>& fp, const std::vector<int>& group, int which,
                    std::uint64_t M, const ModD& md, std::vector<std::uint64_t>& pfx) {
    pfx.clear();
    std::uint64_t acc = 1 % M;
    for (std::size_t i = 0; i < fp.size(); ++i) {
        if (group[i] != which) continue;
        acc = md.mul(acc, fp[i].pres);
        pfx.push_back(acc);                        // pres of the group's first primes, multiplied
    }
    if (pfx.empty()) return;
    std::uint64_t inv = inv_mod_u64(acc, M);
    if (md.mul(inv, acc) != 1 % M) {               // not invertible: one prime at a time, as before
        for (std::size_t i = 0; i < fp.size(); ++i)
            if (group[i] == which) fp[i].pinv = inv_mod_u64(fp[i].pres, M);
        return;
    }
    std::size_t k = pfx.size();
    for (std::size_t i = fp.size(); i-- > 0;) {
        if (group[i] != which) continue;
        --k;                                       // inv = (pres of the group's first k+1 primes)^-1
        fp[i].pinv = (k == 0) ? inv : md.mul(inv, pfx[k - 1]);
        inv = md.mul(inv, fp[i].pres);
    }
}

void half_divisors(const std::vector<FreePrime>& fp, const std::vector<int>& group, int which,
                   bool inverse, std::uint64_t start, u128 limit, const ModD& md,
                   HalfList& out, HalfList& tmp)
{
    out.clear();
    out.val.push_back(1);
    out.res.push_back(start % md.d);
    for (std::size_t i = 0; i < fp.size(); ++i) {
        if (group[i] != which) continue;
        const FreePrime& f = fp[i];
        const std::uint64_t step = inverse ? f.pinv : f.pres;
        u128 pe = 1;
        std::uint64_t pe_res = 1 % md.d;
        bool ok = true;
        for (int e = 0; e < f.emin; ++e) {
            if (!mul_le(pe, f.p, limit, pe)) { ok = false; break; }
            pe_res = md.mul(pe_res, step);
        }
        tmp.clear();
        if (ok) {
            const std::size_t base_n = out.size();
            for (int e = f.emin; e <= f.emax; ++e) {
                const std::size_t first = tmp.size();
                for (std::size_t j = 0; j < base_n; ++j) {
                    u128 v;
                    if (!mul_le(out.val[j], pe, limit, v)) continue;
                    tmp.val.push_back(v);
                    tmp.res.push_back(out.res[j]);
                }
                if (tmp.size() == first) break;
                mulmod_array(md, tmp.res.data() + first, pe_res, tmp.size() - first);
                if (e == f.emax || !mul_le(pe, f.p, limit, pe)) break;
                pe_res = md.mul(pe_res, step);
            }
        }
        std::swap(out, tmp);
        if (out.size() == 0) return;
    }
}

} // namespace amicable
