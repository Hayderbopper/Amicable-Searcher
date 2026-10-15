#include "factoring.h"

#include <algorithm>
#include <bit>
#include <cstdint>
#include <stdexcept>
#include <utility>

namespace amicable {
namespace {

using u128 = __uint128_t;

#if defined(__GNUC__) || defined(__clang__)
#define FORCE_INLINE inline __attribute__((always_inline))
#elif defined(_MSC_VER)
#define FORCE_INLINE __forceinline
#else
#define FORCE_INLINE inline
#endif

FORCE_INLINE void set_mpz_from_u64(mpz_t dst, std::uint64_t value) noexcept {
    if constexpr (sizeof(unsigned long) >= sizeof(std::uint64_t)) {
        mpz_set_ui(dst, static_cast<unsigned long>(value));
    } else {
        mpz_import(dst, 1, 1, sizeof(value), 0, 0, &value);
    }
}

std::uint64_t bigint_to_u64(const BigInt& value) {
    std::uint64_t out = 0;
    mpz_export(&out, nullptr, 1, sizeof(out), 0, 0, value.get_mpz_t());
    return out;
}


struct Montgomery64 {
    std::uint64_t mod = 1;
    std::uint64_t inv = 0; // -mod^{-1} modulo 2^64
    std::uint64_t r2 = 0;  // R^2 modulo mod
    std::uint64_t one = 0; // 1 in Montgomery space

    explicit Montgomery64(std::uint64_t m) : mod(m) {
        std::uint64_t x = 1;
        for (int i = 0; i < 6; ++i)
            x *= 2 - mod * x;
        inv = ~x + 1;

        const u128 r = (u128(1) << 64) % mod;
        r2 = static_cast<std::uint64_t>((r * r) % mod);
        one = to_mont(1);
    }

    [[nodiscard]] std::uint64_t reduce(u128 value) const noexcept {
        const std::uint64_t q =
            static_cast<std::uint64_t>(value) * inv;
        const u128 qn = static_cast<u128>(q) * mod;
        const std::uint64_t carry =
            (static_cast<std::uint64_t>(value) + static_cast<std::uint64_t>(qn))
            < static_cast<std::uint64_t>(value);
        u128 out = (value >> 64) + (qn >> 64) + carry;
        if (out >= mod) out -= mod;
        return static_cast<std::uint64_t>(out);
    }

    [[nodiscard]] std::uint64_t mul(
        std::uint64_t lhs,
        std::uint64_t rhs) const noexcept
    {
        return reduce(static_cast<u128>(lhs) * rhs);
    }

    [[nodiscard]] std::uint64_t to_mont(std::uint64_t value) const noexcept {
        return mul(value % mod, r2);
    }

    [[nodiscard]] std::uint64_t from_mont(std::uint64_t value) const noexcept {
        return reduce(value);
    }

    [[nodiscard]] std::uint64_t add(
        std::uint64_t lhs,
        std::uint64_t rhs) const noexcept
    {
        std::uint64_t out = lhs + rhs;
        if (out < lhs || out >= mod) out -= mod;
        return out;
    }
};

FORCE_INLINE std::uint64_t pow_montgomery(
    std::uint64_t base,
    std::uint64_t exponent,
    const Montgomery64& mont) noexcept
{
    std::uint64_t result = mont.one;
    while (exponent != 0) {
        if (exponent & 1U) result = mont.mul(result, base);
        base = mont.mul(base, base);
        exponent >>= 1U;
    }
    return result;
}

} // namespace

FactorBuffer::FactorBuffer(const FactorBuffer& other) {
    for (std::size_t i = 0; i < other.size_; ++i)
        new (&data()[i]) FactorTerm(other.data()[i]);
    size_ = other.size_;
}

FactorBuffer& FactorBuffer::operator=(const FactorBuffer& other) {
    if (this == &other) return *this;
    clear();
    for (std::size_t i = 0; i < other.size_; ++i)
        new (&data()[i]) FactorTerm(other.data()[i]);
    size_ = other.size_;
    return *this;
}

FactorBuffer::FactorBuffer(FactorBuffer&& other) {
    for (std::size_t i = 0; i < other.size_; ++i)
        new (&data()[i]) FactorTerm(std::move(other.data()[i]));
    size_ = other.size_;
    other.clear();
}

FactorBuffer& FactorBuffer::operator=(FactorBuffer&& other) {
    if (this == &other) return *this;
    clear();
    for (std::size_t i = 0; i < other.size_; ++i)
        new (&data()[i]) FactorTerm(std::move(other.data()[i]));
    size_ = other.size_;
    other.clear();
    return *this;
}

FactorBuffer::~FactorBuffer() {
    clear();
}

bool FactorBuffer::empty() const noexcept {
    return size_ == 0;
}

std::size_t FactorBuffer::size() const noexcept {
    return size_;
}

FactorTerm& FactorBuffer::operator[](std::size_t index) noexcept {
    return data()[index];
}

const FactorTerm& FactorBuffer::operator[](std::size_t index) const noexcept {
    return data()[index];
}

void FactorBuffer::clear() noexcept {
    for (std::size_t i = 0; i < size_; ++i)
        data()[i].~FactorTerm();
    size_ = 0;
}

void FactorBuffer::add(const BigInt& prime, int exponent) {
    if (exponent <= 0) return;

    for (std::size_t i = 0; i < size_; ++i) {
        if (data()[i].prime == prime) {
            data()[i].exponent += exponent;
            return;
        }
    }

    if (size_ >= FACTOR_CAPACITY)
        throw std::runtime_error("FactorBuffer capacity exceeded");

    new (&data()[size_]) FactorTerm{prime, exponent};
    ++size_;
}

void FactorBuffer::add_u64(std::uint64_t prime, int exponent) {
    if (exponent <= 0) return;

    for (std::size_t i = 0; i < size_; ++i) {
        if (mpz_sizeinbase(data()[i].prime.get_mpz_t(), 2) <= 64 &&
            bigint_to_u64(data()[i].prime) == prime) {
            data()[i].exponent += exponent;
            return;
        }
    }

    if (size_ >= FACTOR_CAPACITY)
        throw std::runtime_error("FactorBuffer capacity exceeded");

    new (&data()[size_]) FactorTerm{};
    set_mpz_from_u64(data()[size_].prime.get_mpz_t(), prime);
    data()[size_].exponent = exponent;
    ++size_;
}

void FactorBuffer::merge_from(const FactorBuffer& other) {
    for (std::size_t i = 0; i < other.size_; ++i)
        add(other.data()[i].prime, other.data()[i].exponent);
}

void FactorBuffer::sort_by_prime() {
    std::sort(
        data(),
        data() + static_cast<std::ptrdiff_t>(size_),
        [](const FactorTerm& lhs, const FactorTerm& rhs) {
            return lhs.prime < rhs.prime;
        });
}

FactorTerm* FactorBuffer::data() noexcept {
    return reinterpret_cast<FactorTerm*>(storage_.data());
}

const FactorTerm* FactorBuffer::data() const noexcept {
    return reinterpret_cast<const FactorTerm*>(storage_.data());
}

bool is_prime_u64(std::uint64_t n) noexcept {
    if (n < 2) return false;

    static constexpr std::uint64_t small_primes[] = {
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37
    };
    for (std::uint64_t prime : small_primes) {
        if (n == prime) return true;
        if (n % prime == 0) return false;
    }

    const unsigned shifts = std::countr_zero(n - 1);
    const std::uint64_t d = (n - 1) >> shifts;
    const Montgomery64 mont(n);

    static constexpr std::uint64_t bases[] = {
        2ULL, 325ULL, 9375ULL, 28178ULL, 450775ULL, 9780504ULL, 1795265022ULL
    };

    for (std::uint64_t base : bases) {
        if (base % n == 0) continue;

        std::uint64_t x_m =
            pow_montgomery(mont.to_mont(base % n), d, mont);
        std::uint64_t x = mont.from_mont(x_m);
        if (x == 1 || x == n - 1) continue;

        bool witness = true;
        for (unsigned r = 1; r < shifts; ++r) {
            x_m = mont.mul(x_m, x_m);
            x = mont.from_mont(x_m);
            if (x == n - 1) {
                witness = false;
                break;
            }
        }
        if (witness) return false;
    }

    return true;
}

bool is_probable_prime(const BigInt& n) {
    if (n < 2) return false;
    if (mpz_sizeinbase(n.get_mpz_t(), 2) <= 64)
        return is_prime_u64(bigint_to_u64(n));
    return mpz_probab_prime_p(n.get_mpz_t(), 25) > 0;
}

} // namespace amicable
