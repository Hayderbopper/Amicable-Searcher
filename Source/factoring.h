#ifndef AMICABLE_FACTORING_H
#define AMICABLE_FACTORING_H

#include <array>
#include <cstddef>
#include <cstdint>
#include <new>
#include <type_traits>

#include <gmpxx.h>

namespace amicable {

using BigInt = mpz_class;

static constexpr std::size_t FACTOR_CAPACITY = 256;

struct FactorTerm {
    BigInt prime;
    int exponent = 0;
};

// left uninitialised on purpose: only the first `size` terms are ever read,
// and zeroing 4 KB per buffer showed up in profiles (one buffer per factorisation)
struct U64FactorTerm {
    std::uint64_t prime;
    int exponent;
};

struct U64FactorBuffer {
    std::array<U64FactorTerm, FACTOR_CAPACITY> terms;
    std::size_t size = 0;

    [[nodiscard]] bool empty() const noexcept { return size == 0; }
    void clear() noexcept { size = 0; }

    [[nodiscard]] U64FactorTerm& operator[](std::size_t index) noexcept {
        return terms[index];
    }

    [[nodiscard]] const U64FactorTerm& operator[](std::size_t index) const noexcept {
        return terms[index];
    }
};

class FactorBuffer {
public:
    FactorBuffer() = default;
    FactorBuffer(const FactorBuffer& other);
    FactorBuffer& operator=(const FactorBuffer& other);
    FactorBuffer(FactorBuffer&& other);
    FactorBuffer& operator=(FactorBuffer&& other);
    ~FactorBuffer();

    [[nodiscard]] bool empty() const noexcept;
    [[nodiscard]] std::size_t size() const noexcept;

    [[nodiscard]] FactorTerm& operator[](std::size_t index) noexcept;
    [[nodiscard]] const FactorTerm& operator[](std::size_t index) const noexcept;

    void clear() noexcept;
    void add(const BigInt& prime, int exponent = 1);
    void add_u64(std::uint64_t prime, int exponent = 1);
    void merge_from(const FactorBuffer& other);
    void sort_by_prime();

private:
    using Storage = std::aligned_storage_t<sizeof(FactorTerm), alignof(FactorTerm)>;

    [[nodiscard]] FactorTerm* data() noexcept;
    [[nodiscard]] const FactorTerm* data() const noexcept;

    std::array<Storage, FACTOR_CAPACITY> storage_;
    std::size_t size_ = 0;
};

[[nodiscard]] bool is_prime_u64(std::uint64_t n) noexcept;
[[nodiscard]] bool is_probable_prime(const BigInt& n);

} // namespace amicable

#endif
