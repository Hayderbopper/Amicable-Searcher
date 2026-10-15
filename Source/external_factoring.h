#ifndef AMICABLE_EXTERNAL_FACTORING_H
#define AMICABLE_EXTERNAL_FACTORING_H

#include "factoring.h"

#include <cstdint>
#include <utility>
#include <vector>

namespace amicable {

void configure_external_factoring();
void factorize_runtime_u64(std::uint64_t n, U64FactorBuffer& out);

// n prime?  hurchalla's test: trial division, then Miller-Rabin with bases
// proven for every n < 2^64 (the test hurchalla's factorize uses).  Exact.
[[nodiscard]] bool is_prime_u64_fast(std::uint64_t n);

// 64..128-bit values straight through hurchalla (no GMP round trip).
// out gets (prime, exponent) pairs; returns false if not verified.
struct U128Factor { unsigned __int128 prime; int exponent; };
// This file's functions take and return no __int128 by value or inside a
// struct, so external_factoring.cpp may be compiled by another compiler than
// the rest (build.sh CXX_FACTORING, build.ps1 -ClangFactoring): GCC and clang
// do not agree on how an __int128 argument is passed in every position (on
// x86-64 Linux when one register is left, and on Windows).  The 128-bit route
// therefore crosses as two 64-bit halves.
struct U128FactorParts { std::uint64_t lo, hi; int exponent; };
[[nodiscard]] bool factorize_runtime_u128_parts(std::uint64_t lo, std::uint64_t hi, U128FactorParts* out,
                                                int& count);
[[nodiscard]] inline bool factorize_runtime_u128(unsigned __int128 n, U128Factor* out, int& count) {
    U128FactorParts parts[128];                  // a number below 2^128 has fewer than 128 prime factors
    if (!factorize_runtime_u128_parts(static_cast<std::uint64_t>(n), static_cast<std::uint64_t>(n >> 64),
                                      parts, count))
        return false;
    for (int i = 0; i < count; ++i)
        out[i] = {(static_cast<unsigned __int128>(parts[i].hi) << 64) | parts[i].lo, parts[i].exponent};
    return true;
}

// any size through FLINT's fmpz_factor (trial division, rho, ECM, quadratic
// sieve); appends (prime, exponent) pairs.  n >= 1.
void factorize_flint(const BigInt& n, std::vector<std::pair<BigInt, int>>& out);

} // namespace amicable

#endif
