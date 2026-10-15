#ifndef AMICABLE_NUMERIC_UTILS_H
#define AMICABLE_NUMERIC_UTILS_H

#include "factoring.h"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace amicable {

BigInt u64_to_bigint(std::uint64_t value);
std::uint64_t bigint_to_u64(const BigInt& value);
bool bigint_fits_u64(const BigInt& value);
std::string format_factorization(const FactorBuffer& factors);
// sech.me/ap pair type: <primes only in smaller><primes only in larger>,
// prefixed with X for an irregular pair: a shared prime with different exponents,
// or a prime of one member only with exponent > 1 (any hash slot other than (1,0)).
// Both factor lists must be sorted by prime.  e.g. 220/284 -> "21", 1184/1210 -> "X12"
std::string sech_type(const FactorBuffer& smaller, const FactorBuffer& larger);
BigInt sigma_from_factors(const FactorBuffer& factors);

} // namespace amicable

#endif
