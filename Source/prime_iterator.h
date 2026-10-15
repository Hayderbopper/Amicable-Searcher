#pragma once
// Where a primesieve::iterator starts.
//
// After primesieve::iterator it(start, stop_hint), next_prime() returns the
// primes >= start from primesieve 11 on, but only the primes > start in
// versions 7 to 10 (Ubuntu 22.04 ships 7.8).  Every search loop here needs
// all primes >= start, so iterators are built as
//     primesieve::iterator it(prime_iter_start(start), stop_hint);
// and check_prime_iterator() verifies the convention against the library
// actually loaded, once at start-up.

#include <primesieve.hpp>

#include <cstdint>
#include <stdexcept>
#include <string>

namespace amicable {

[[nodiscard]] constexpr std::uint64_t prime_iter_start(std::uint64_t start) noexcept {
#if defined(PRIMESIEVE_VERSION_MAJOR) && PRIMESIEVE_VERSION_MAJOR >= 11
    return start;
#else
    return start > 0 ? start - 1 : 0;
#endif
}

// Throws if next_prime() after prime_iter_start(s) is not the first prime >= s.
inline void check_prime_iterator() {
    struct Case { std::uint64_t start, first; };
    static constexpr Case cases[] = {{0, 2}, {2, 2}, {3, 3}, {4, 5}, {1000003, 1000003}, {1000004, 1000033}};
    for (const Case& c : cases) {
        primesieve::iterator it(prime_iter_start(c.start), c.start + 100);
        const std::uint64_t p = it.next_prime();
        if (p != c.first)
            throw std::runtime_error("primesieve " + primesieve::primesieve_version()
                + ": iterator started at " + std::to_string(c.start) + " returned "
                + std::to_string(p) + " instead of " + std::to_string(c.first)
                + " (prime_iterator.h does not match this library version)");
    }
}

} // namespace amicable
