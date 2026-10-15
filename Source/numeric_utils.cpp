#include "numeric_utils.h"

#include <algorithm>
#include <cmath>
#include <limits>

namespace amicable {

BigInt u64_to_bigint(std::uint64_t value) {
    if constexpr (sizeof(unsigned long) >= sizeof(std::uint64_t)) {
        return BigInt(static_cast<unsigned long>(value));      // LP64: one limb, no import
    } else {
        BigInt out;                                              // LLP64 (Windows): unsigned long is 32 bits
        mpz_import(out.get_mpz_t(), 1, 1, sizeof(value), 0, 0, &value);
        return out;
    }
}

std::uint64_t bigint_to_u64(const BigInt& value) {
    if constexpr (sizeof(unsigned long) >= sizeof(std::uint64_t)) {
        return static_cast<std::uint64_t>(mpz_get_ui(value.get_mpz_t()));
    } else {
        std::uint64_t out = 0;
        mpz_export(&out, nullptr, 1, sizeof(out), 0, 0, value.get_mpz_t());
        return out;
    }
}

bool bigint_fits_u64(const BigInt& value) {
    static const BigInt U64_MAX = u64_to_bigint(std::numeric_limits<std::uint64_t>::max());
    return value >= 0 && value <= U64_MAX;
}

std::string format_factorization(const FactorBuffer& factors) {
    if (factors.empty()) return "1";

    std::string out;
    for (std::size_t i = 0; i < factors.size(); ++i) {
        if (i != 0) out += '*';
        out += factors[i].prime.get_str();
        if (factors[i].exponent > 1)
            out += '^' + std::to_string(factors[i].exponent);
    }
    return out;
}

std::string sech_type(const FactorBuffer& smaller, const FactorBuffer& larger) {
    std::size_t i = 0;
    std::size_t j = 0;
    int small_only = 0;
    int large_only = 0;
    bool irregular = false;
    while (i < smaller.size() && j < larger.size()) {
        if (smaller[i].prime == larger[j].prime) {
            if (smaller[i].exponent != larger[j].exponent) irregular = true;
            ++i;
            ++j;
        } else if (smaller[i].prime < larger[j].prime) {
            if (smaller[i].exponent > 1) irregular = true;
            ++small_only;
            ++i;
        } else {
            if (larger[j].exponent > 1) irregular = true;
            ++large_only;
            ++j;
        }
    }
    for (; i < smaller.size(); ++i, ++small_only)
        if (smaller[i].exponent > 1) irregular = true;
    for (; j < larger.size(); ++j, ++large_only)
        if (larger[j].exponent > 1) irregular = true;
    return (irregular ? std::string("X") : std::string())
         + std::to_string(small_only) + std::to_string(large_only);
}

BigInt sigma_from_factors(const FactorBuffer& factors) {
    BigInt total = 1;
    for (std::size_t i = 0; i < factors.size(); ++i) {
        BigInt term = 1;
        BigInt power = 1;
        for (int e = 0; e < factors[i].exponent; ++e) {
            power *= factors[i].prime;
            term += power;
        }
        total *= term;
    }
    return total;
}

} // namespace amicable
