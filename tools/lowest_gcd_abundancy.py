"""Find amicable pairs in results/all_pairs.txt whose shared gcd has the lowest abundancy index.

Abundancy index of g is sigma(g)/g. The gcd is built from the given prime
factorizations (min exponent of each shared prime), so no factoring is needed.

Usage: python tools/lowest_gcd_abundancy.py [file] [top_n]
       (file defaults to results/all_pairs.txt next to this folder)
"""
import os
import re
import sys
from fractions import Fraction

LINE = re.compile(r"^(\d+)=([\d^*]+)$")


def parse_factors(text):
    factors = {}
    for term in text.split("*"):
        p, _, e = term.partition("^")
        factors[int(p)] = int(e) if e else 1
    return factors


def read_pairs(path):
    """Yield ((a, a_factors), (b, b_factors)) from consecutive factorization lines."""
    pending = []
    with open(path) as f:
        for line in f:
            m = LINE.match(line.strip())
            if not m:
                continue
            pending.append((int(m.group(1)), parse_factors(m.group(2))))
            if len(pending) == 2:
                yield pending[0], pending[1]
                pending = []


def gcd_factors(fa, fb):
    return {p: min(e, fb[p]) for p, e in fa.items() if p in fb}


def abundancy(factors):
    result = Fraction(1)
    for p, e in factors.items():
        result *= Fraction(p ** (e + 1) - 1, p ** e * (p - 1))
    return result


def fmt_factors(factors):
    if not factors:
        return "1"
    return "*".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(factors.items()))


def main():
    default = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results", "all_pairs.txt")
    path = sys.argv[1] if len(sys.argv) > 1 else default
    top_n = int(sys.argv[2]) if len(sys.argv) > 2 else 20

    results = []
    for (a, fa), (b, fb) in read_pairs(path):
        g = gcd_factors(fa, fb)
        results.append((abundancy(g), g, a, b))

    results.sort(key=lambda r: (r[0], r[2]))

    # keep only the smallest pair for each distinct gcd
    seen = set()
    unique = []
    for r in results:
        key = tuple(sorted(r[1].items()))
        if key not in seen:
            seen.add(key)
            unique.append(r)
    results = unique

    print(f"{len(results)} distinct gcds; showing {min(top_n, len(results))} lowest gcd abundancy index\n")
    for idx, g, a, b in results[:top_n]:
        print(f"abundancy(gcd) = {idx} (~{float(idx):.6f})")
        print(f"  gcd = {fmt_factors(g)}")
        print(f"  {a}\n  {b}\n")


if __name__ == "__main__":
    main()
