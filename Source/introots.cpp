#include "introots.h"

#include <algorithm>

namespace amicable {

namespace {

void trim(std::vector<BigInt>& c) {
    while (!c.empty() && c.back() == 0) c.pop_back();
}

int sgn(const BigInt& v) { return mpz_sgn(v.get_mpz_t()); }

BigInt floor_div(const BigInt& a, const BigInt& b) {
    BigInt q;
    mpz_fdiv_q(q.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return q;
}

// unit brackets [m, m+1] covering every real root of c (c trimmed, deg >= 1)
std::vector<BigInt> brackets(const std::vector<BigInt>& c) {
    const std::size_t n = c.size() - 1;
    if (n == 0) return {};
    if (n == 1) return {floor_div(BigInt(-c[0]), c[1])};

    std::vector<BigInt> d(n);
    for (std::size_t i = 1; i <= n; ++i) d[i - 1] = c[i] * static_cast<unsigned long>(i);
    trim(d);
    std::vector<BigInt> crit = (d.size() >= 2) ? brackets(d) : std::vector<BigInt>{};
    std::sort(crit.begin(), crit.end());

    // Cauchy bound: every root has |x| <= 1 + max|c_i| / |c_n|
    BigInt mx = 0;
    for (std::size_t i = 0; i < n; ++i) mx = std::max(mx, BigInt(abs(c[i])));
    BigInt B;
    mpz_cdiv_q(B.get_mpz_t(), mx.get_mpz_t(), BigInt(abs(c[n])).get_mpz_t());
    B += 2;

    // merge the critical brackets into disjoint integer intervals
    std::vector<std::pair<BigInt, BigInt>> iv;
    for (const BigInt& m : crit) {
        if (m + 1 < -B || m > B) continue;
        if (!iv.empty() && m <= iv.back().second) iv.back().second = std::max(iv.back().second, BigInt(m + 1));
        else iv.emplace_back(m, m + 1);
    }

    std::vector<BigInt> out;
    auto monotone_piece = [&](const BigInt& a, const BigInt& b) {
        if (a > b) return;
        const BigInt fa = horner(c, a), fb = horner(c, b);
        const int sa = sgn(fa), sb = sgn(fb);
        if (sa == 0) out.push_back(a);
        if (sb == 0) out.push_back(b);
        if (sa == 0 || sb == 0 || sa == sb) return;
        BigInt lo = a, hi = b, mid;
        while (hi - lo > 1) {
            mid = lo + (hi - lo) / 2;
            if (sgn(horner(c, mid)) == sa) lo = mid;
            else hi = mid;
        }
        out.push_back(lo);
    };
    BigInt cur = -B;
    for (const auto& [s, e] : iv) {
        monotone_piece(cur, s);
        for (BigInt m = s; m < e; ++m) out.push_back(m);   // short: at most deg units
        cur = e;
    }
    monotone_piece(cur, B);
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
    return out;
}

} // namespace

BigInt horner(const std::vector<BigInt>& c, const BigInt& x) {
    if (c.empty()) return 0;
    BigInt acc = c.back();
    for (std::size_t i = c.size() - 1; i-- > 0;) {
        acc *= x;
        acc += c[i];
    }
    return acc;
}

std::vector<BigInt> integer_roots(std::vector<BigInt> c, const BigInt& lo) {
    trim(c);
    std::vector<BigInt> roots;
    if (c.size() < 2) return roots;
    for (const BigInt& m : brackets(c)) {
        for (int k = 0; k < 2; ++k) {
            const BigInt x = m + k;
            if (x >= lo && horner(c, x) == 0) roots.push_back(x);
        }
    }
    std::sort(roots.begin(), roots.end());
    roots.erase(std::unique(roots.begin(), roots.end()), roots.end());
    return roots;
}

bool exact_root(const BigInt& n, int k, BigInt& r) {
    if (n < 0) return false;
    if (k == 1) { r = n; return true; }
    if (k == 2) {
        // squares: GMP's exact test rejects almost every non-square with a few
        // residues, far cheaper than computing the root first
        if (!mpz_perfect_square_p(n.get_mpz_t())) return false;
        mpz_sqrt(r.get_mpz_t(), n.get_mpz_t());
        return true;
    }
    return mpz_root(r.get_mpz_t(), n.get_mpz_t(), static_cast<unsigned long>(k)) != 0;
}

} // namespace amicable
