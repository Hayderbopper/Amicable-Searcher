#ifndef AMICABLE_HASH_SPEC_H
#define AMICABLE_HASH_SPEC_H

// A hash describes the shape of an amicable pair (N1 < N2) around its common
// part A1 = gcd(N1, N2):
//
//     [(a1,b1),...,(am,bm)] _ [(c1,d1),...,(cn,dn)]
//
//     N1 = A1 * P1^a1 * ... * Pm^am     (the smaller member)
//     N2 = A1 * Q1^c1 * ... * Qn^cn     (the larger member)
//
// with P1 < P2 < ... < Pm and Q1 < Q2 < ... < Qn, and Pi dividing A1 exactly
// bi times (bi = 0: Pi does not divide A1), Qj dividing A1 exactly dj times.
// So a prime with exponent e1 in N1 and e2 in N2 is listed on the side where
// it is bigger, as (|e1-e2|, min(e1,e2)); primes with e1 == e2 are in A1.
// Every amicable pair has exactly one hash and one A1.

#include <string>
#include <vector>

namespace amicable {

struct HashSlot {
    int exp = 1;      // a (or c): extra exponent on this side
    int mult = 0;     // b (or d): exact exponent of the prime in A1
};

struct HashSpec {
    std::vector<HashSlot> side[2];   // [0] = smaller member N1, [1] = larger member N2

    [[nodiscard]] std::string text() const;      // "[(1,0),(1,0)] _ [(1,0),(1,0),(1,0)]"
    [[nodiscard]] std::string folder() const;    // "((1,0),(1,0)) _ ((1,0),(1,0),(1,0))"
};

// Accepts "[(1,0),(1,0)] _ [(1,0),(1,0),(1,0)]", "((1,0),(1,0)) _ ((1,0),(1,0),(1,0))",
// "[(1,0),(1,0)] [(1,0),(1,0),(1,0)]", "(1,0),(1,0) | (1,0),(1,0),(1,0)" ...
[[nodiscard]] bool parse_hash_spec(const std::string& text, HashSpec& out, std::string& error);

} // namespace amicable

#endif
