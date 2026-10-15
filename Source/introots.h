#ifndef AMICABLE_INTROOTS_H
#define AMICABLE_INTROOTS_H

// Exact integer roots of integer polynomials (no floating point):
// every real root is bracketed in a unit interval [m, m+1] by recursion on
// the derivative and integer bisection on the monotone pieces, then the
// bracket ends are tested exactly.

#include "factoring.h"

#include <vector>

namespace amicable {

// c[i] = coefficient of x^i.  Returns every integer root r >= lo, ascending.
[[nodiscard]] std::vector<BigInt> integer_roots(std::vector<BigInt> c, const BigInt& lo);

[[nodiscard]] BigInt horner(const std::vector<BigInt>& c, const BigInt& x);

// exact k-th root: true and r = n^(1/k) when n is a perfect k-th power (n >= 0)
[[nodiscard]] bool exact_root(const BigInt& n, int k, BigInt& r);

} // namespace amicable

#endif
