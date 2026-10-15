#include "external_factoring.h"

#ifndef AMICABLE_USE_FLINT
#error "AmicableNumbers2 is now built in the FLINT-enabled profile. Build with -DAMICABLE_USE_FLINT and link -lflint -lmpfr."
#endif

// hurchalla first: some FLINT versions #define names hurchalla uses
#include <hurchalla/factoring/factorize.h>
#include <hurchalla/factoring/is_prime.h>
#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>

#include <algorithm>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

namespace amicable {
namespace {

using u128 = unsigned __int128;

[[nodiscard]] bool factorize_hurchalla_u64_flat(std::uint64_t n, U64FactorBuffer& out) {
    out.clear();
    if (n <= 1) return true;

    try {
        unsigned int count = 0;
        auto factors = hurchalla::factorize<std::uint64_t>(n, count, true);
        if (count > out.terms.size()) {
            out.clear();
            return false;
        }

        // the factors must multiply back to n (overflow = wrong factors)
        std::uint64_t product = 1;
        for (unsigned int i = 0; i < count; ++i)
            if (__builtin_mul_overflow(product, factors[i], &product)) { out.clear(); return false; }
        if (product != n) { out.clear(); return false; }

        for (unsigned int i = 0; i < count; ++i)
            out.terms[out.size++] = {factors[i], 1};
        return true;
    } catch (const std::exception& ex) {
        out.clear();
        throw std::runtime_error(
            std::string("hurchalla::factorize<u64> failed: ") + ex.what());
    } catch (...) {
        out.clear();
        throw std::runtime_error("hurchalla::factorize<u64> failed");
    }
}

} // namespace

void configure_external_factoring() {
    // The solver already parallelizes over P3. Keep any linked FLINT code from
    // trying to nest its own worker pool if a fallback/debug path calls it.
    flint_set_num_threads(1);
}

void factorize_flint(const BigInt& n, std::vector<std::pair<BigInt, int>>& out) {
    if (n <= 1) return;
    fmpz_t f;
    fmpz_init(f);
    fmpz_set_mpz(f, n.get_mpz_t());
    fmpz_factor_t fac;
    fmpz_factor_init(fac);
    fmpz_factor(fac, f);
    BigInt product = 1;
    if (fac->sign < 0) product = -1;
    for (slong i = 0; i < fac->num; ++i) {
        BigInt p;
        fmpz_get_mpz(p.get_mpz_t(), fac->p + i);
        BigInt pe;
        mpz_pow_ui(pe.get_mpz_t(), p.get_mpz_t(), static_cast<unsigned long>(fac->exp[i]));
        product *= pe;
        if (mpz_sizeinbase(p.get_mpz_t(), 2) > 64 && mpz_probab_prime_p(p.get_mpz_t(), 25) == 0)
            throw std::runtime_error("FLINT returned a composite factor of " + n.get_str());
        out.emplace_back(p, static_cast<int>(fac->exp[i]));
    }
    fmpz_factor_clear(fac);
    fmpz_clear(f);
    // the factors must multiply back to n
    if (product != n)
        throw std::runtime_error("FLINT factorization of " + n.get_str() + " could not be verified");
}

bool factorize_runtime_u128_parts(std::uint64_t lo, std::uint64_t hi, U128FactorParts* out, int& count) {
    const u128 n = (static_cast<u128>(hi) << 64) | lo;
    count = 0;
    if (n <= 1) return true;
    unsigned int num = 0;
    auto factors = hurchalla::factorize<u128>(n, num, true);
    u128 product = 1;
    for (unsigned int i = 0; i < num; ++i)
        if (__builtin_mul_overflow(product, factors[i], &product)) return false;
    if (product != n) return false;
    // above 2^64 hurchalla's primality test is Miller-Rabin with fixed bases,
    // not a proof: confirm each such factor with GMP's BPSW + Miller-Rabin
    for (unsigned int i = 0; i < num; ++i) {
        if ((factors[i] >> 64) == 0) continue;
        const std::uint64_t w[2] = {static_cast<std::uint64_t>(factors[i]), static_cast<std::uint64_t>(factors[i] >> 64)};
        mpz_class p;
        mpz_import(p.get_mpz_t(), 2, -1, sizeof(std::uint64_t), 0, 0, w);
        if (mpz_probab_prime_p(p.get_mpz_t(), 25) == 0) return false;
    }
    std::sort(factors.begin(), factors.begin() + num);
    for (unsigned int i = 0; i < num;) {
        const u128 prime = factors[i++];
        int exponent = 1;
        while (i < num && factors[i] == prime) { ++exponent; ++i; }
        out[count++] = {static_cast<std::uint64_t>(prime), static_cast<std::uint64_t>(prime >> 64), exponent};
    }
    return true;
}


bool is_prime_u64_fast(std::uint64_t n) {
    return n >= 2 && hurchalla::is_prime<std::uint64_t>(n);
}

void factorize_runtime_u64(std::uint64_t n, U64FactorBuffer& out) {
    if (factorize_hurchalla_u64_flat(n, out)) return;

    out.clear();
    throw std::runtime_error(
        "hurchalla::factorize<u64> did not produce a verified factorization");
}

} // namespace amicable
