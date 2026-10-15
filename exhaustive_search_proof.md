# Why Amicable-Searcher never misses a pair: a proof

This document proves that the search engine of Amicable-Searcher
(formerly `General_Hash_Search`, the "general engine") is **exhaustive**. For every `k` in the requested
range, it writes every amicable pair with the requested hash and
`gcd(N1, N2) = k`, unless it lists that `k` in `incomplete.txt`.

It is written for a reader who knows undergraduate number theory (divisors,
congruences, the Chinese remainder theorem) and basic algorithm analysis
(loops, recursion, invariants, monotone predicates and binary search). Every
claim is tied to the function in `Source/general.cpp` or `Source/engine.cpp`
that implements it (Appendix A has the full map).

The proof is a long chain of small lemmas. The idea behind it is simple:

> Take any pair the program is supposed to find. Follow the path through the
> search that *that pair* would take. Show that at every step, the program's
> loop bounds contain the pair's next prime and no filter rejects it. Then the
> pair reaches the final check, passes it, and is written.

---

## Contents

1. [Definitions](#1-definitions)
2. [What is assumed about the computer](#2-what-is-assumed-about-the-computer)
3. [Three basic facts](#3-three-basic-facts)
4. [The shape of the search](#4-the-shape-of-the-search)
5. [Level 1: the loop over k](#5-level-1-the-loop-over-k)
6. [Level 2: the primes of k (configurations)](#6-level-2-the-primes-of-k-configurations)
7. [Level 3: the order of the free primes (roots)](#7-level-3-the-order-of-the-free-primes-roots)
8. [Level 4: scanning one prime](#8-level-4-scanning-one-prime)
9. [Level 5: the last primes are solved, not scanned (tails)](#9-level-5-the-last-primes-are-solved-not-scanned-tails)
10. [Level 6: the final check](#10-level-6-the-final-check)
11. [Proof of the Main Theorem](#11-proof-of-the-main-theorem)
12. [Termination, and what "incomplete" means](#12-termination-and-what-incomplete-means)
13. [Resuming a stopped run](#13-resuming-a-stopped-run)
14. [Limits of this proof, and the tests that back it](#14-limits-of-this-proof-and-the-tests-that-back-it)
- [Appendix A: lemma → code](#appendix-a-lemma--code)
- [Appendix B: the floating-point margin](#appendix-b-the-floating-point-margin)
- [Appendix C: defects found while checking the code](#appendix-c-defects-found-while-checking-the-code)

---

## 1. Definitions

### 1.1 Divisor sums

For a positive integer `n`, `σ(n)` is the sum of the positive divisors of `n`.
Two facts are used constantly:

* **Multiplicativity.** If `gcd(m, n) = 1`, then `σ(mn) = σ(m)·σ(n)`.
* **Prime powers.** `σ(p^e) = 1 + p + p² + … + p^e`.

The **abundancy** of `n` is `h(n) = σ(n)/n`. It is also multiplicative.

### 1.2 Amicable pairs

An **amicable pair** is `(N1, N2)` with `0 < N1 < N2` and

```
σ(N1) = σ(N2) = N1 + N2.                                   (AP)
```

`N1` is the *smaller member* (side 0) and `N2` the *larger member* (side 1).

### 1.3 The hash and k

Let `A1 = k = gcd(N1, N2)`. For each prime `p`, let `α = v_p(N1)` and
`β = v_p(N2)` be its exponents in the two members.

* If `α = β`, then `p` only belongs to `k`, and it has no slot in the hash.
* If `α > β`, then `p` has a **slot** `(α − β, β)` on side 0.
* If `β > α`, then `p` has a slot `(β − α, α)` on side 1.

A slot `(e, b)` therefore means two things. On its own side the prime has `e`
more powers than on the other side. It divides `k` exactly `b` times. The
slots of each side are listed in increasing order of their primes. The
**hash** is the pair of lists, written

```
[(e1,b1), (e2,b2), …] _ [(c1,d1), (c2,d2), …]
```

A slot with `b = 0` is **free**: its prime does not divide `k`, and it divides
only one member. A slot with `b > 0` is **bound**: its prime is a prime of `k`
with `v_p(k) = b`.

Every amicable pair has exactly one hash and exactly one `k`.

### 1.4 The statement

Fix a hash `H` and a range of k values `[k_start, k_end)`. These are the
**search limits**; the program places no other limit on any prime. Let

```
T(H, k) = { (N1, N2) : (N1, N2) is an amicable pair, its hash is H, gcd(N1, N2) = k }.
```

> **Main Theorem.** Run `multi_k_searcher` with hash `H`, in any mode (`range` over k values, `single` for one k, `skipped`
> for the k values of `incomplete.txt`). Let `k` be a value it finished and
> did not list in `incomplete.txt`. Then every pair of `T(H, k)` has been
> written to that mode's results file (or was already in it). Modes `range`
> and `skipped` write `multi_k_results.txt`, and mode `single` writes
> `single_k_results.txt`. Every pair written is an amicable pair with hash
> `H` and `gcd = k`.
>
> A `k` is listed in `incomplete.txt` only when
>
> * a timeout was set and reached, or
> * some prime's proven range could not be capped below `2^400`, or it lies
>   beyond `2^64`, where primesieve cannot scan it.
>
> In every case the reason is written next to the `k`.

The theorem is conditional on the assumptions of Section 2. These are about
the libraries and the hardware, not about the mathematics.

---

## 2. What is assumed about the computer

| | assumption |
|---|---|
| **A1** | Integer arithmetic is exact. Big integers use GMP. Every 128-bit operation in the code is overflow-checked (`__builtin_*_overflow`), and on overflow the code falls back to GMP. Where a floating-point quotient speeds up a modular product (`ModD` in `divisors.h`), the remainder is checked in exact 128-bit arithmetic and recomputed if the estimate was off, so the result never depends on floating-point precision (Appendix C, item 12). |
| **A2** | `primesieve::iterator(prime_iter_start(lo), hi)` returns exactly the primes of `[lo, hi]` in increasing order, for `hi ≤ primesieve::get_max_stop()` (about 1.8·10¹⁹). `prime_iter_start` absorbs a convention that changed between primesieve versions, and every run checks it at start-up (Appendix C, item 4). Each prime loop ends by asking for one prime past `hi`. With primesieve 11 and later, that call throws when `hi ≥ 18,446,744,073,709,551,557`, the largest prime below `2^64`. The throw is a fatal error (A6): the program stops with a message, and the k stays unfinished, so nothing is skipped. |
| **A3** | The factorization routines return the true prime factorization: hurchalla below `2^128`, and FLINT above it after trial division by the primes below `2^16`. The product of the factors is multiplied back out and compared with the number on every factoring route: hurchalla's 64-bit route (`factorize_runtime_u64`, which most numbers take), its 128-bit route (`factorize_runtime_u128`), FLINT's route (`factorize_flint`), and the assembled `σ(K)` (Lemma 6.4). A mismatch is a fatal error (A6). It is not checked on the `σ(p^e)` fallback (`cached_sigma_factors`), whose pieces come from those routes. That the factors are prime is assumed. Below `2^64` this is proven, because hurchalla uses deterministic Miller–Rabin bases. A factor above `2^64`, from hurchalla's 128-bit route or from FLINT, must also pass GMP's `mpz_probab_prime_p` (BPSW plus Miller–Rabin rounds), as must a cofactor above `2^128` that is taken as prime without factoring. These are probable-prime tests. A composite could in principle pass one, but no such number is known, and it would have to pass hurchalla's or FLINT's test as well. |
| **A4** | A primality test never calls a prime composite. Miller–Rabin and BPSW have this property: a "composite" answer is always correct. Below `2^64` the general engine tests its candidates (`prime_test`, `is_prime_u64_fast`) with hurchalla's `is_prime`: trial division, then Miller–Rabin with bases proven for every `n < 2^64`, the same test hurchalla's factorization relies on in A3. Its answer is exact there; it was compared with the 7-base Miller–Rabin test (`is_prime_u64`) and GMP's BPSW on 56 million numbers (every `n < 2·10^7`, random ones of every size, the 2 million below `2^64`, and pseudoprime-shaped composites) with no difference. Above `2^64` `mpz_probab_prime_p` is used, as before. |
| **A5** | Floating point is IEEE-754 binary64 with round-to-nearest. On x86-64, `double` arithmetic runs in SSE2 registers, so there is no x87 double rounding. Builds with `-march=native` may fuse `a·b + c` into one multiply-add, which drops a rounding; Appendix B's bound covers both. GMP's conversion of an integer to `double` truncates, with relative error below `2^-52`. `long double` appears only in estimates that are checked exactly afterwards. Every thread sets the x87 unit to 64-bit precision (`fpu.h`), so those estimates are the same on Windows as on Linux. |
| **A6** | Each work item handed to a thread is executed. Work stops early only by the timeout mechanism, which marks the k as incomplete, or by a fatal error. A fatal error stops the program with an error message, and every k it cut short stays unfinished in the state file, including a k that was cut short in another thread (Appendix C, item 6). Failing to record a k in `incomplete.txt` is itself a fatal error (Appendix C, item 7). So is failing to read the file before rewriting it (Appendix C, item 13). |

**Completeness uses only A1–A6.** A probable-prime test that wrongly accepted
a composite (the opposite of A4) could only create a *wrong* candidate. The
final check would then most likely reject it; it could never cause a miss.

---

## 3. Three basic facts

**Lemma 3.1 (abundancy identity).** For an amicable pair, let
`x = σ(N1)/N1` and `y = σ(N2)/N2`. Then

```
(x − 1)(y − 1) = 1,     x > 2,     1 < y < 2.
```

*Proof.* By (AP), `x = (N1 + N2)/N1 = 1 + N2/N1` and `y = 1 + N1/N2`, so
`(x − 1)(y − 1) = (N2/N1)(N1/N2) = 1`. Since `N1 < N2`, `x − 1 > 1`, so
`x > 2` and `y − 1 = 1/(x − 1) < 1`. Finally `y > 1` because `N1 > 0`. ∎

**Lemma 3.2 (one prime power).** For a prime `p` and `e ≥ 1`,

```
1 < h(p^e) = σ(p^e)/p^e = 1 + 1/p + … + 1/p^e < p/(p − 1).
```

If `p > L` for an integer `L ≥ 1`, then `h(p^e) < (L + 1)/L`.
The upper bound holds for every `e ≥ 0`. Also, for `e ≥ 1`, `h(p^e)` strictly
decreases as `p` grows.

*Proof.* The sum is a truncated geometric series with ratio `1/p`, so it is
below the full series `p/(p − 1)`. If `p ≥ L + 1`, then
`p/(p − 1) = 1 + 1/(p − 1) ≤ 1 + 1/L`. Each term `p^-i` decreases in `p`. ∎

**Lemma 3.3 (decomposition).** Let `(N1, N2) ∈ T(H, k)`. Define:

* `K1 = k · ∏ (bound side-0 slot primes)^e`, and `K2` likewise for side 1;
* `X = ∏ P^e` over the free side-0 slots, and `Y = ∏ Q^c` over the free
  side-1 slots.

Then `N1 = K1·X`, `N2 = K2·Y`, `gcd(K1, X) = gcd(K2, Y) = 1`, and

```
σ(K1)·σ(X) = σ(K2)·σ(Y) = K1·X + K2·Y.                     (E)
```

*Proof.* By the definition of the hash, a prime of `k` that has no slot
appears with exponent `v_p(k)` in both members. A bound slot `(e, b)` on
side 0 has `v_p(N1) = b + e` and `v_p(N2) = b = v_p(k)`. A free slot's prime
divides only its own member and not `k`. Collecting exponents gives
`N1 = K1·X` and `N2 = K2·Y`. Free primes do not divide `k` or any bound prime,
so the gcds are 1, and (E) is (AP) rewritten using multiplicativity. ∎

### Partial states

During the search, some free primes are already chosen. Let `X0` and `Y0` be
the products of the chosen prime powers of each side. The program stores
four integers:

```
a = σ(K1)σ(X0) = σ(K1·X0),   b = K1·X0,   c = σ(K2)σ(Y0) = σ(K2·Y0),   d = K2·Y0
```

These are `sx, px, sy, py` in the code. The partial abundancies are
`x0 = a/b` and `y0 = c/d`. If `X_rem` and `Y_rem` are the products of the
remaining prime powers, multiplicativity gives

```
x = x0 · h(X_rem),        y = y0 · h(Y_rem).                (P)
```

**Corollary 3.4 (abundancy only grows).** `x ≥ x0` and `y ≥ y0`. The
inequality is strict exactly when a prime remains on that side.

---

## 4. The shape of the search

The search for one `k` is a tree with six levels:

```
k ──► configuration (which primes of k fill the bound slots)
        ──► root (in which order the free primes are taken)
              ──► scanned primes, one level each (a loop over a proven range)
                    ──► tail: the last 2–3 primes solved exactly (no loop over primes)
                          ──► final check, then output
```

**The witness path.** Fix a pair `π ∈ T(H, k)`. At each level we name the
branch that `π` itself belongs to: its configuration, a root whose rules it
satisfies, and its own primes at each scanned level. We then show that the
program actually visits this branch. The visit ends in the tail producing the
rest of `π`'s primes and the final check accepting `π`. This is an induction
on depth; Section 11 assembles it.

To *visit* a branch the program must do two things:

1. The branch value lies within the loop bounds.
2. No condition between loop iterations (a filter, an early exit or a
   rejection) discards it.

The lemmas below check both, at every level.

---

## 5. Level 1: the loop over k

*Code: `Engine::worker`, `Engine::run_k`, `Engine::k_done` (`engine.cpp`).*

Each worker takes the next `k` from a shared atomic counter
(`next_k.fetch_add(1)`), starting at `k_start` and stopping at `k_end`. An
atomic increment gives each value to exactly one worker, so **every k of the
range is processed exactly once**.

For each `k`, `run_k` calls `build_search_k` (Level 2) and then `generate`,
which loops over all roots (Level 3).

A `k` is *finished* when its generator and every piece of work it created
have returned (a reference count, `pending`), and none of it was cut short
by a fatal error. If the k timed out or raised a "bound not finite" or
"beyond 2^64" flag, it is written to `incomplete.txt` with the reason.

Two cases do not count as finished, and the frontier does not move past
them:
* the generator stopped early because another `k` hit a fatal error (such
  a `k` counts as failed; Appendix C, item 6);
* the `k`'s line could not be written to `incomplete.txt` (item 7).

The state file stores the **frontier**: the smallest `k` that is not yet
finished. Every `k` below it is finished. A restart without `start_k` resumes
at the frontier, so no `k` is skipped across restarts.

---

## 6. Level 2: the primes of k (configurations)

*Code: `build_search_k`.*

### 6.1 The enumeration

The program factors `k` exactly, using a deterministic 64-bit routine (A3).
For each bound slot with multiplicity `b`, the candidates are the primes `p`
of `k` with `v_p(k) = b`. The recursion `rec` tries every assignment of
distinct candidate primes to the bound slots. It keeps those where the bound
primes increase along each side, and where every free slot still has room
between its bound neighbours.

**Lemma 6.1.** Let `π ∈ T(H, k)`. The assignment `φ_π` of `π`'s bound primes
to the bound slots is one of the configurations built.

*Proof.* By §1.3, each bound slot's prime has `v_p(k) = b`, so it is a
candidate. Distinct slots hold distinct primes. The slots of a side are
listed in increasing order of their primes, so the bound primes increase
along the side. A free slot between two bound slots holds a prime strictly
between them, so it has room. The recursion tries every injective assignment
from the candidate lists, so it reaches `φ_π`. ∎

For each configuration, every free slot gets static limits: `lo` is one more
than the nearest bound prime before it on its side (or 2), and `hi` is one
less than the nearest bound prime after it (or "none"). By sortedness, `π`'s
free primes satisfy their slots' limits.

### 6.2 Exact early exits

Three tests can discard work before any prime is scanned. All three are exact
integer comparisons.

**Lemma 6.2 (abundant k).** If `σ(k) ≥ 2k`, then `T(H, k) = ∅`.

*Proof.* `K2 = k · ∏ q^c` only raises exponents of primes that already divide
`k`. For each such prime, `h(q^{m+c}) > h(q^m)` (Lemma 3.2 applied to more
terms), and `h` is multiplicative. So `σ(K2)/K2 ≥ σ(k)/k ≥ 2`. By
Corollary 3.4, `y ≥ σ(K2)/K2 ≥ 2`, which contradicts Lemma 3.1. ∎

**Lemma 6.3 (dead configuration).** A configuration with `σ(K2) ≥ 2·K2`, or
with `(σ(K1) − K1)(σ(K2) − K2) > K1·K2`, has no pair.

*Proof.* The first gives `y ≥ y0 ≥ 2`. The second says `(x0 − 1)(y0 − 1) > 1`.
Since `x ≥ x0` and `y ≥ y0`, we get `(x − 1)(y − 1) > 1`. Both contradict
Lemma 3.1. ∎

**Lemma 6.4 (the σ(K) factorizations are checked).** The factorization of
`σ(K1)` and `σ(K2)` is used later to factor the divisor-step number. It is
assembled from cached factorizations of `σ(p^e)`, each built from the
cyclotomic pieces `Φ_d(p)` with `d | e + 1`. This works because
`σ(p^e) = (p^{e+1} − 1)/(p − 1) = ∏_{d | e+1, d > 1} Φ_d(p)`. After assembly,
the program multiplies the factorization back out and compares it with
`σ(K)` (in 128 bits, or with big integers when `σ(K)` is larger). If they
differ, it discards the result and factors each `σ(p^e)` again with the
general routine (A3). So the factorization used later is always that of
`σ(K)` itself.

---

## 7. Level 3: the order of the free primes (roots)

*Code: `make_shapes`, `split_shape`, `root_shapes`.*

The free primes of a pair are all distinct: each divides only one member, and
none divides `k`. Sorting them by size gives a single list. Restricted to one
side, this list is that side's slots in order. So the sorted list is an
**interleaving** of the two sides' slot lists.

A **root** is a list of the free slots (`order`), together with a set of
order rules. It visits the slots in its listed order. Each root type has its
own rules:

| root type | rules a pair must satisfy |
|---|---|
| **strict** | the primes increase along `order` |
| **last-two-free** | as strict, except the last two slots (one per side) may come in either order; both exceed everything before them |
| **float3** | `order = prefix + [u, v, w]`. The prefix increases. `u, v, w` all exceed the last prefix prime. `u < w` (same side). `v` (the other side) may lie anywhere among them |
| **split3** | `order = [P_1, …, P_{m−1}] + [u, v, w]`, where the `P_i` and `v` are the smaller member's free primes in increasing order and `u < w` are the larger member's two. No rule relates the two members |

**How the roots are built.** If the configuration qualifies for split3 (see
below), that single root is used. Otherwise, all interleavings are generated
(`interleave`), and each is turned into a root:

1. If its last three slots all have exponent 1 and both sides occur among
   them, it becomes a **float3** root. Interleavings that give the same
   `prefix + [u, v, w]` are merged into one.
2. Otherwise, if its last two slots are on different sides and not both of
   exponent ≥ 2, the two orderings of those slots are merged. The one with
   side 0 first is kept as a **last-two-free** root.
3. Otherwise it is a **strict** root.

**split3 qualifies when:**

* the larger member has exactly two free slots, both of exponent 1;
* the smaller member has one or two free slots, the last of exponent 1;
* with two, also `σ(K1) < 2·K1`. This guarantees a finite range for `P_1`;
  see §8.3.

**Lemma 7.1 (coverage).** Let `π` be a pair whose configuration is `φ_π`.
Some root of `φ_π` has rules that `π` satisfies.

*Proof.* Let `o_π` be the interleaving given by `π`'s sorted free primes.

* *split3 was used.* There is only one root. Its rules only ask each member's
  free primes to increase, which they do.
* *Otherwise.* `o_π` was generated, and step 1, 2 or 3 turned it into a root
  `ρ`.
  * **Step 1.** `ρ = prefix(o_π) + [u, v, w]`. The prefix of `o_π` is `π`'s
    smallest free primes in order. The last three exceed them. `u < w`
    because they are on the same side in their slot order. `v` may be
    anywhere. So `π` satisfies the float3 rules.
  * **Step 2, `o_π` kept.** `π` satisfies the rules of `ρ = o_π`, since they
    are weaker than strict.
  * **Step 2, `o_π` skipped.** Its twin, the same list with the last two
    swapped, is also an interleaving with the same last three slots, so it
    fell into step 2 too and was kept. `π` satisfies the twin's rules: the
    prefix is the same, both last primes exceed it, and they differ.
  * **Step 3.** `ρ = o_π` and `π` is strictly increasing along it. ∎

The rules of each root are enforced at the end, by the final check (§10). The
search itself only relies on them to prove its bounds.

---

## 8. Level 4: scanning one prime

*Code: `range_for`, `find_lower`, `find_upper`, `refine_lower`,
`refine_upper`, `upper_ok`, `lower_ok`, `scan_children`, `make_child`,
`process`, and the first two levels in `Engine::generate`.*

### 8.1 The node invariant

A **node** at depth `t` of root `ρ` stores the primes chosen for the first `t`
slots of `ρ.order`, and the four integers `a, b, c, d` of §3 for them. The
root node has `t = 0` and `a = σ(K1)`, `b = K1`, `c = σ(K2)`, `d = K2`.

`make_child(n, q)` creates the child for prime `q`:

* it multiplies `σ(q^e)` into `a` (or `c`) and `q^e` into `b` (or `d`);
* it records which slot `q` fills;
* it rejects `q` only if `q < slot.lo`, `q > slot.hi`, `q ≤ ` the previous
  prime, or `q | k`.

**Lemma 8.1.** Let `n` be a node on `π`'s witness path, and let `q*` be
`π`'s prime for the next slot. Then `make_child(n, q*)` succeeds and yields
the next node on the witness path.

*Proof.* `q*` lies within its slot's limits (§6.1). It exceeds the previous
prime on the path: for strict, last-two-free and float3 roots this is the
root's order rule; for a split3 prefix the previous prime is the previous
smaller-member prime. It does not divide `k`, since it is free. ∎

### 8.2 The two tests

Let the next slot have side `s` and exponent `e`, and let `q` be a candidate
for it. The primes still to come after `q` fall into two kinds:

* **ordered** ones: known to be `> q`. There are `j0` of them on side 0 and
  `j1` on side 1.
* **floating** ones: known only to be `> L_i` for a fixed integer `L_i`. This
  is the case in split3 prefixes and in the float3/split3 tails.

Let `H_e(q) = σ(q^e)/q^e`. The **upper test** `U(q)` uses

```
X⁺(q) = x0 · [H_e(q) if s = 0] · ((q+1)/q)^{j0} · ∏_{floating, side 0} (L_i+1)/L_i
Y⁺(q) = y0 · [H_e(q) if s = 1] · ((q+1)/q)^{j1} · ∏_{floating, side 1} (L_i+1)/L_i

U(q)  :⇔  X⁺ > 2  and  Y⁺ > 1  and  (X⁺ − 1)(Y⁺ − 1) > 1
```

The **lower test** `L(q)` uses only `q`'s own factor:

```
X⁻(q) = x0 · [H_e(q) if s = 0],      Y⁻(q) = y0 · [H_e(q) if s = 1]

L(q)  :⇔  Y⁻ < 2  and  (X⁻ − 1)(Y⁻ − 1) < 1
```

**Lemma 8.2 (the true prime passes both).** Suppose a node is on `π`'s
witness path, with at least one prime of `π` remaining after the next one.
Suppose every remaining prime of `π` satisfies its stated lower limit (`> q*`
or `> L_i`). Then `π`'s next prime `q*` satisfies `U(q*)` and `L(q*)`.

*Proof.* By (P) and Lemma 3.2, each remaining prime power contributes a factor
`h > 1` that is strictly below its bound `(q*+1)/q*` or `(L_i+1)/L_i`. So
`X⁺(q*) ≥ x` and `Y⁺(q*) ≥ y`. The inequality is strict on any side where a
prime remains after `q*`, and at least one side has one.

* `X⁺ ≥ x > 2` and `Y⁺ ≥ y > 1`, by Lemma 3.1.
* For the product, suppose the remaining prime is on side 0. Then
  `X⁺ − 1 > x − 1 > 0` and `Y⁺ − 1 ≥ y − 1 > 0`, so
  `(X⁺−1)(Y⁺−1) > (x−1)(y−1) = 1`. Side 1 is symmetric. So `U(q*)` holds.
* For `L`: `X⁻ ≤ x` and `Y⁻ ≤ y` with the same strictness, all factors `≥ 1`.
  So `Y⁻ ≤ y < 2`, and `(X⁻−1)(Y⁻−1) < (x−1)(y−1) = 1`. So `L(q*)` holds. ∎

**Lemma 8.3 (monotone).** `U` is monotone non-increasing in `q`: once false,
it stays false. `L` is monotone non-decreasing: once true, it stays true.

*Proof.* `H_e(q)` and `(q+1)/q` decrease as `q` grows (Lemma 3.2), and the
floating factors do not depend on `q`. So `X⁺, Y⁺, X⁻, Y⁻` are non-increasing
in `q`. The condition `U` is monotone increasing in `(X⁺, Y⁺)`, and `L` is
monotone decreasing in `(X⁻, Y⁻)`. ∎

So the set of `q ≥ q_min` passing both tests is an interval `[lo*, hi*]`, and
Lemma 8.2 puts `q*` inside it.

### 8.3 Computing the interval

`range_for` computes `lo` and `hi` with `[lo*, hi*] ⊆ [lo, hi]`. It never
returns an interval that misses a point of `[lo*, hi*]`.

**Where the scan starts, `q_min`.** It is one more than the previous prime
(on that side, for a split3 prefix), raised to `slot.lo`. `q*` is at least
this by Lemma 8.1.

**Exact predicates.** `upper_ok(q)` and `lower_ok(q)` decide `U(q)` and
`L(q)` *exactly*. A floating-point pre-screen decides only when its value is
far from the threshold, using a margin `ε ≥ 10⁻¹³` that is several times the
worst rounding error (Lemma B.1, Appendix B). Otherwise the predicate is
evaluated in exact integer arithmetic (`upper_ok_exact`, `lower_ok_exact`),
with every fraction cleared:

```
U:  X_N > 2·X_D,   Y_N > Y_D,   (X_N − X_D)(Y_N − Y_D) > X_D·Y_D
```

where `X⁺ = X_N/X_D` and `Y⁺ = Y_N/Y_D` are products of integers (A1). So
`upper_ok` ≡ `U` and `lower_ok` ≡ `L` as functions.

**Lemma 8.4 (exact boundary search).** Let `P` be a monotone predicate on
the integers, decided exactly. Suppose `P(lo)` is true and `P(hi)` is false.
Then the bisection loop

```
while hi − lo > 1:  m = ⌊(lo+hi)/2⌋;  if P(m): lo = m else hi = m
```

ends with `lo` = the largest value where `P` holds.

*Proof.* The loop keeps the invariant "`P(lo)` true, `P(hi)` false", and
`hi − lo` strictly decreases, so it terminates with `hi = lo + 1`. By
monotonicity, the boundary lies between them. ∎

**Lower end (`find_lower`).**

1. If `L(q_min)` holds, then `lo = q_min`.
2. Otherwise, a Newton step proposes an estimate. It is used only as a
   starting point. `refine_lower` *verifies* a false point and a true point
   with the exact predicate, moving outward by doubling steps until it has
   them, and then runs Lemma 8.4. The result is exactly the smallest `q`
   with `L(q)`.
3. If the estimate cannot be confirmed within 64 bits, a slower exact
   galloping search, followed by bisection, does the same with big integers.

If `L` is still false at `q = 2^400`, monotonicity says that every
`q ≤ 2^400` fails. The program then evaluates `L` *in the limit*
`q → ∞`, where `H_e → 1`, exactly:

```
L(∞)  :⇔  y0 < 2  and  (x0 − 1)(y0 − 1) < 1          (lower_ok_limit)
```

Since `X⁻ ≥ x0` and `Y⁻ ≥ y0`, `L(q)` for any `q` implies `L(∞)`.

* If `L(∞)` is false, no `q` works at all, and the range is empty. This is
  correct.
* If `L(∞)` is true, a `q > 2^400` is not excluded. The range is reported as
  unbounded, and the caller marks the `k` incomplete. Nothing is silently
  dropped. (This case was handled incorrectly before this proof was
  written; see Appendix C.)

**Upper end (`find_upper`).** Search starts from `lo`. If `U(lo)` is false,
there is no `q ≥ lo` with `U`, by Lemma 8.3. Otherwise the same scheme runs:
estimate, verify both ends exactly, bisect. The result is exactly `hi*`.

The slow fallback uses a value `c` with `U(c)` exactly false and returns
`hi = c − 1`. This can only be larger than `hi*`, which is safe. If no false
point is found below `2^400`, the range is reported as unbounded and the `k`
becomes incomplete.

Finally `hi` is cut to `slot.hi`, which `q*` respects (§6.1).

**Why split3 needs `σ(K1) < 2·K1`.** At a split3 prefix node, the larger
member's two primes float with small lower limits. `Y⁺` may then stay large
as `q → ∞`, and only `X⁺ > 2` can bound `q`. When the smaller member has two
free primes, the scanned `P_1` has `X⁺(q) = x0 · H_e(q) · (q+1)/q → x0` as
`q → ∞`. This drops below 2 for large `q` exactly when `x0 < 2`, that is,
`σ(K1) < 2K1`. Under that condition, `hi*` is finite and found as above.
When the condition fails, the program does not use split3; the interleavings
give finite ranges in the usual way.

### 8.4 An extra exact filter

*Code: the first block of `range_for`.*

**Lemma 8.5.** At a node of a non-split3 root, suppose exactly one prime `z`
of exponent 1 remains in the smaller member, and all `r ≥ 1` primes remaining
in the larger member exceed `L` (the previous prime). Then a pair can exist
below this node only if

```
a·(z_min + 1) > 2·b·z_min,    where   z_min = max( ⌈c·∏_{i=0}^{r−1}(L+2+i) / a⌉ − 1,  L + 1 ).
```

*Proof.* By (E), `a·(z + 1) = c·σ(Y_rem)`. The remaining larger-member primes
are distinct and exceed `L`, so the `i`-th smallest is at least `L + 1 + i`,
and its `σ` is at least `L + 2 + i`. Hence `z + 1 ≥ c·∏(L+2+i)/a`, so
`z ≥ z_min`. Then `x = (a/b)·(z+1)/z ≤ (a/b)·(z_min+1)/z_min`, because
`(z+1)/z` decreases in `z`. Lemma 3.1 requires `x > 2`. ∎

When the inequality fails, `range_for` returns an empty range for the whole
subtree, and this is correct.

### 8.5 The loop over the interval

`process` (and `Engine::generate` for the first two levels) does the
following:

* If the range is empty, return. This is correct by the lemmas above.
* If it is unbounded, flag the `k` incomplete.
* If `hi` is beyond primesieve's limit, flag the `k` incomplete.
* Otherwise call `scan_children(lo, hi)`. It iterates **every prime in
  `[lo, hi]`** (A2), skips only primes dividing `k`, calls `make_child`, and
  recurses with `process`.

**Lemma 8.6.** If a node on `π`'s witness path is not a tail node, the
program visits the next node on the witness path.

*Proof.* By Lemmas 8.2–8.5, `q* ∈ [lo, hi]` and the range is not discarded.
`q*` is prime and does not divide `k`, so `scan_children` reaches it, and
`make_child` accepts it (Lemma 8.1). ∎

The engine splits one scanned level into blocks
`[lo + i·w, min(hi, lo + (i+1)·w − 1)]` for `i = 0, …, ⌊(hi − lo)/w⌋`. In
mode range that is the second scanned level. In modes single and skipped it
is the last one, and the generator walks the levels above it in the same
order as `process` (§13). Short ranges are handed out whole, in batches.
The blocks partition `[lo, hi]`, and each block is scanned exactly once, so
the argument is unchanged.

**Why no level can skip.** The only ways to move to the next iteration
without recursing are:

* the prime divides `k` (it cannot be a free prime);
* `make_child` rejects it (impossible for `q*`, Lemma 8.1);
* cancellation, which only happens on timeout, and the timeout marks the `k`
  incomplete.

---

## 9. Level 5: the last primes are solved, not scanned (tails)

*Code: `tail_kind`, `run_tail` and the `tail_*` functions.*

At each node, `tail_kind` looks at the remaining slots `r`. It hands them to
an exact solver ("tail") as soon as one applies; otherwise the next prime is
scanned. The tails are:

| tail | when | solved by |
|---|---|---|
| Done | nothing remains | direct check of (AP) |
| SameSide | all remaining slots on one side | §9.2 |
| Mixed2 | two remain, one per side, not both exponent ≥ 2 | §9.3 |
| Divisor3 | three remain, all exponent 1, the last two on different sides | §9.5 |
| Progression | the first remaining is the last of its side, exponent 1 | §9.4 |

For each tail we prove: **if the node is on `π`'s witness path, the tail
reaches the final check with `π`'s remaining primes.** Throughout, `a, b, c,
d` are the node's values.

### 9.1 Done

If no free slot remains, then `N1 = b` and `N2 = d`. The pair is `π` exactly
when `a = c = b + d`. The code tests exactly this and emits. ∎

### 9.2 SameSide (one member is complete)

Say every remaining slot is on side 1, so the smaller member is complete:
`σ(N1) = a` and `N1 = b`. Let `W = Y_rem` and `V = σ(W)`. Since `W` is
coprime to `d`, (E) reads `a = c·V = b + d·W`. So

```
W = (a − b)/d,     V = a/c      (both must be integers).
```

The code returns only if a division is not exact, or `V ≤ W`. Both are
impossible for `π`, since `V = σ(W) > W` when `W > 1`. Side 0 is symmetric.

`solve_same` then recovers the remaining primes `q_1 < … < q_T` (all `> L`,
the previous prime) from `W` and `V`:

* **`T = 1`:** `W = q^e`. The exact integer `e`-th root gives `q`; the code
  checks `σ(q^e) = V` and `q > L`.
* **`T = 2`, both exponents 1:** `q_1 + q_2 = V − W − 1` and `q_1·q_2 = W`.
  These are the two roots of `z² − Sz + W`, recovered exactly by an integer
  square root. The code checks `q_1 > L` and `q_1 < q_2`.
* **Otherwise:** the smallest remaining prime `q` satisfies
  * `σ(q^g)` divides `V`, where `g` is its exponent;
  * `σ(q^g) ≥ σ((L+1)^g)`;
  * `q^{Σ e_i} ≤ W`, since every remaining prime is `≥ q`, so
    `σ(q^g) ≤ σ(q_max^g)` with `q_max = ⌊W^{1/Σe_i}⌋`.

  The walker visits **every divisor of `V` up to that maximum**. It stops
  increasing an exponent only once the partial product exceeds the maximum,
  and any extension would exceed it too. For each divisor it recovers `q`
  exactly, then recurses on `W/q^g`, `V/σ(q^g)` and the leftover
  factorization, with `L = q`. The factorization of `V` is that of `a`
  divided by that of `c` (Lemma 6.4 and A3). After a Progression's `u`
  (§9.4) it is assembled as the part that does not depend on `u` (made once
  for the tail, from the same σ factorizations) plus that of `σ(u)`: by
  multiplicativity the same primes with the same exponents. ∎

### 9.3 Mixed2 (one prime left on each side)

Let `P` (side 0, exponent `α`) and `Q` (side 1, exponent `γ`) remain. The
equations are `a·σ(P^α) = c·σ(Q^γ) = b·P^α + d·Q^γ`.

* **`α = γ = 1`.** Write `S` for the common value. Then `P = S/a − 1` and
  `Q = S/c − 1`, and `S = b(S/a − 1) + d(S/c − 1)` gives
  `S·(ad + bc − ac) = ac(b + d)`. With `D = ad + bc − ac`:

  ```
  D·(P + 1) = c·(b + d),        D·(Q + 1) = a·(b + d).
  ```

  `D ≠ 0` for a solution, since `S` is finite. So `P` and `Q` are uniquely
  determined, and `mixed_closed` computes them exactly.
* **`γ = 1`, `α ≥ 2`.** Eliminating `Q = a·σ(P^α)/c − 1` gives the
  polynomial equation `(ac − ad)·σ(P^α) − bc·P^α + cd = 0` in `P`. Its
  integer roots `≥ L` are all found by `integer_roots` (Lemma 9.1). Then `Q`
  follows exactly.
* **`α = 1`, `γ ≥ 2`.** The same, with the roles exchanged.
* **Both `≥ 2`.** `tail_kind` does not use Mixed2; the next prime is scanned
  (§8) and the last one is a SameSide tail.

Under a last-two-free root, the two primes may come in either order. The
closed form does not depend on their order, and the final check accepts
either.

**Lemma 9.1 (`integer_roots`).** For an integer polynomial `f` of degree
`n ≥ 1`, the routine returns every integer root `≥ lo`.

*Proof.* All real roots satisfy `|x| ≤ B` (Cauchy's bound).
* The critical points of `f` lie in unit intervals obtained recursively from
  `f'`. Every integer in those intervals is tested.
* Between consecutive critical intervals, `f` is monotone, so it has at most
  one root there. A sign change is located to a unit interval by exact
  bisection; a zero at an endpoint is recorded.
* Each candidate `m` and `m + 1` from a unit interval is tested exactly
  (`horner(f, x) = 0`).

So no integer root is missed. ∎

### 9.4 Progression (the last prime of one side)

Let `u` (exponent 1, side `s_u`) be the last remaining prime of its side,
with the rest (two or more) on the other side. Take `s_u = 0`. After adding
`u`, the smaller member is complete, so §9.2 requires

```
d | (a − b)·u + a        and        c | a·(u + 1).
```

The first is a linear congruence `A·u ≡ B (mod d)`. It is solvable exactly
when `gcd(A, d) | B`, and then `u` lies in one class modulo `d/gcd`
(`lin_congr`). The second says `u ≡ −1 (mod c/gcd(a, c))`. The two classes
combine by the Chinese remainder theorem (`crt2`) into one class `u ≡ ρ
(mod M)`, or no class at all. A 64-bit version computes the same class when
the numbers fit; it was checked against the big-integer version on more than
200,000 cases. `s_u = 1` is symmetric.

The code then works as follows:

* If no class exists, return. `π` cannot have reached this point, so this
  is correct.
* Let `first` be the smallest member of the class `≥ u_lo`. If `U(first)`
  fails, return. `u* ≥ first` and `U(u*)` holds (Lemma 8.2), so `U(first)`
  holds by monotonicity; this exit is never taken on the witness path.
* Compute `u`'s exact range (§8.3), and visit **every** member of the class
  in it. There are two ways to do this:
  * when `M < 64` and the range ends below `2^64`, the primes in the range
    are sieved and filtered by class;
  * otherwise, the class members are stepped through with big integers and
    tested for primality (A4).

  The second way also takes a range that ends beyond `2^64`, which cannot
  be sieved. This is the one place where such a range is walked rather than
  flagged. The walk is finite, so Section 12 holds. But with `M < 64` and a
  wide range it can take practically forever. Only a time limit ends it,
  and the time limit then lists the k.
* For each `u`, call `make_child` with `u`'s slot named explicitly, then the
  SameSide tail of §9.2.

In code the tail is two steps: `prog_plan` finds the class, `first` and the
range, and `prog_visit` visits the members in an interval. In modes single
and skipped, a range that ends below `2^64` may be handed out in pieces, one
interval each (§13). The plan depends only on the node, so it is made once,
by the thread that splits the tail off, and every piece uses that one plan
(`ProgressionPlan`); the pieces partition the range, so together they visit
exactly the members above.

`u*` is in the class, in the range and prime, so it is visited, and §9.2
finishes the pair. ∎

### 9.5 Divisor3 (three primes left)

Let `u, v, w` remain, all of exponent 1, with `v` and `w` on different sides.
Call the one on side 0 `P` and the one on side 1 `Q`.

**The divisor condition.** Take `u` on side 1 (side 0 is symmetric). After
adding `u`, the values are `a' = a`, `b' = b`, `c' = c(u+1)`, `d' = d·u`. By
§9.3,

```
D(u) := a·d·u + b·c·(u+1) − a·c·(u+1) = δ1·u + δ0,
        δ1 = ad + bc − ac,   δ0 = c(b − a),

D(u)·(Q + 1) = a·(b + d·u).
```

So `D(u)` divides `a·(b + d·u)`. Two reductions make the right side
independent of `u`:

* **Content.** Let `g = gcd(δ1, δ0)` and `D = g·D'`, where `D'(u) = δ1'u + δ0'`
  is primitive. Let `g1 = gcd(g, a)`. Since `g·D'` divides `a·(b + d·u)`,
  dividing both by `g1` gives `(g/g1)·D' | (a/g1)·(b + d·u)`, so
  `D' | (a/g1)·(b + d·u)`.
* **Remove `u`.** `δ1'·(b + d·u) = d·D'(u) + (δ1'·b − d·δ0')`, so
  `δ1'·(b + d·u) ≡ T/g (mod D')`, where `T = δ1·b − d·δ0`. Hence

  ```
  D'(u)  divides  R* := (a/g1) · (T/g),       a number that does not depend on u.
  ```

Expanding, `T = abd + c(b − a)(b − d)`. For `u` on side 0, the same argument
gives `δ0 = a(d − c)`, `T = bcd + a(d − c)(d − b)` and `R* = (c/g1)(T/g)`.
The code computes exactly these.

**Generic case (`δ1 ≠ 0`, `T ≠ 0`).**

1. If `u` ranges over `[u_lo, u_hi]`, then `F = D'(u)` lies between
   `D'(u_lo)` and `D'(u_hi)`, satisfies `|F| ≤ |R*|`, divides `R*`, and
   `F ≡ δ0' (mod |δ1'|)`.
2. The program factors `R*`. The factorization of `a/g1` comes from `σ(K1)`
   and the chosen primes' `σ(p^e)`; the cofactor `T/g` is factored after
   removing the known primes (A3).
3. It enumerates **every** signed divisor `F` of `R*` with these three
   properties: in the interval, `|F| ≤` the bound, and in the residue class.
   * Either all divisors are walked (`walk_residues`, `walk_big`), which is
     plainly complete;
   * or a meet-in-the-middle residue search is used (`divisors_with_residue`).
     It splits the primes into two halves and matches residues through a hash
     table. Primes dividing the modulus are handled first: their exponent in
     `F` is forced by the residue (a CRT argument). A lookup is skipped only
     when a 4096-bit filter of the second half's residues shows that no
     residue there equals the one looked up, so no match is skipped. The
     inverses modulo the modulus are computed together (one inversion and
     products); the inverse of their product is checked, and if the check
     fails each is inverted on its own. It was tested against brute force on
     20,000 random cases, 688,216 divisors, with no difference, and the
     current version against the earlier one and brute force on 500,000
     cases, 59,354,812 divisors, with no difference.
4. Each `F` gives `u = (F − δ0')/δ1'` when the division is exact. `u` is kept
   if it is in range, prime and coprime to `k`. Then `P` and `Q` follow from
   §9.3.

`π`'s `u*` produces `F = D'(u*)` with all three properties, so it is found.
When values exceed 128 bits, the same computation runs in GMP (the
"BigInt route"), with the same candidate set.

**Degenerate case (`δ1 = 0` or `T = 0`).** There is no divisor condition. The
code then tries **every prime** `u` of `u`'s proven range (or flags the `k`
incomplete if that range is unbounded), and solves `P` and `Q` by §9.3 for
each.

**Scanning instead of factoring.** When `u`'s range is short (at most 1024
numbers, or 4096 when `R*` would need the slow 128-bit factoring), the code
computes the exact range (§8.3) and tries every prime in it directly
(`divisor3_scan`). That is trivially complete.

**The range of `u`.** `u_lo` is one more than the previous prime (raised to
`slot.lo`), or, in split3, just `slot.lo`. The upper end is the smallest of
three bounds:

* the proven range of §8.3, with the remaining primes' limits stated for
  each case below;
* `slot.hi`;
* the cap of Lemma 9.2.

None of them excludes `u*`.

**Lemma 9.2 (cap on u).** Let `W` be the other remaining prime on `u`'s side.
In every Divisor3 variant, `W > u` (by the root's rules). Write
`num(u) = X·u + Y` for the right side `a(b + du)` (or `c(bu + d)` when `u` is
on side 0), with `X, Y > 0`. Then every solution satisfies

```
f(u) := δ1·u² + (δ0 − X)·u − Y = u·D(u) − num(u) < 0.
```

*Proof.* `num > 0`, and `W + 1 = num/D(u)` is positive, so `D(u) > 0`. From
`W ≥ u + 1`: `num = (W + 1)·D ≥ (u + 2)·D > u·D`. ∎

Since `f(0) = −Y < 0`, the consequences depend on the sign of `δ1`:

* **`δ1 > 0`.** `f` is a convex parabola, and the valid `u` lie below its
  positive root. The code estimates the root in floating point, then corrects
  the estimate with the exact sign of `f`. It returns `c` with `f(c + 1) > 0`
  (so `f > 0` for all larger `u`), or "no cap" if 64 correction steps do not
  suffice.
* **`δ1 < 0`.** `D(u) > 0` forces `u ≤ ⌊(δ0 − 1)/(−δ1)⌋`, and no `u` exists
  if `δ0 ≤ 0`.
* **`δ1 = 0`.** No cap.

Every case is exact, and every exit ("no u") is justified by the lemma.

**Lemma 9.3 (the σ-equation filter).** Among `u, v, w`, let `z` be the prime
alone on its side, and suppose `z` is in the smaller member. Let the other two
be at least `u_lo` and distinct. By (E),
`a(z + 1) = c·(p+1)(p'+1) ≥ c·(u_lo+1)(u_lo+2)`. As in Lemma 8.5,
`x ≤ (a/b)(z_min+1)/z_min`, so a pair needs this to exceed 2. The test is
exact, and `z_min − 1` becomes a valid lower limit for `z`.

#### The three Divisor3 variants

**(i) Strict root.** All three exceed the previous prime, and `u` is the
smallest. The range of `u` treats `v` and `w` as `> u`, which is valid. The
filter of Lemma 9.3 applies with `u_lo`. Then the generic case runs, or the
degenerate case.

**(ii) float3 root.** `u < w` and `v` are all above `L`, the last prefix
prime. Either `u` or `v` is the smallest of the three.

* Test A is `U` for "`u` is next" (with `v, w > u`) at `u_lo`. Test B is `U`
  for "`v` is next" (with `u, w > v`) at `v_lo`. By Lemmas 8.2 and 8.3, if a
  pair with `u` smallest exists, test A holds; if a pair with `v` smallest
  exists, test B holds.
* **Neither A nor B:** there is no pair; return.
* **Only A:** every pair has `u` smallest. Run (i).
* **Only B:** every pair has `v < u < w`. `v` is then the only prime of its
  side among the three, and comes first, so this is a Progression tail on
  the list `[v, u, w]` (§9.4). The child node is created for `v`'s slot,
  named explicitly. (Before this proof was written it was created for the
  wrong slot; see Appendix C.)
* **Both:** one divisor search covers every position of `v`. The divisor
  condition and the closed form do not depend on the order. The range of `u`
  treats `w` as `> u` and `v` as floating, only `> L`. In the degenerate
  case, both (i) (`u` smallest) and the Progression on `[v, u, w]` (`v`
  smallest) are run, which covers both possibilities.

**(iii) split3 root.** `u < w` are the larger member's two primes, bounded
only by their slots. `v` exceeds the last prefix prime `L`.

* `u_lo = max(slot.lo, 2)`.
* `v` floats above `L`, raised by Lemma 9.3.
* `w` is ordered `> u`.
* The degenerate case tries every prime of `u`'s range, or flags the `k`.

In every variant, `π`'s `u*` lies in the range searched and satisfies every
filter, and `π`'s `v*` and `w*` come out of §9.3. ∎

---

## 10. Level 6: the final check

*Code: `emit`.*

Before writing a candidate, `emit` performs these checks:

1. **Root rules.** Every free slot has a value. The values satisfy the
   root's order rules (strict, last-two-free, float3 or split3, as in §7) and
   their slots' `lo`/`hi`. No free prime divides `k`, and each passes the
   primality test.
2. **Rebuild.** It rebuilds `N1` and `N2` from `k`, the bound primes and the
   free primes, with full factorizations.
3. **Pair check.** `N1 < N2`, `σ(N1) = σ(N2) = N1 + N2` (computed from the
   factorizations), and `gcd(N1, N2) = k`.

**Soundness.** Anything written passes step 3, so it is an amicable pair with
`gcd = k`. Its slots match `H`, so its hash is `H`.

**Completeness at this step.** `π` passes every check:

* step 1: by Lemma 7.1, the slot limits, the fact that free primes don't
  divide `k`, and A4;
* steps 2–3: `π` is an amicable pair in `T(H, k)`.

The results file removes duplicates, so a pair found through two roots is
written once.

---

## 11. Proof of the Main Theorem

Let `k` be finished and not listed as incomplete, and let `π ∈ T(H, k)`.

1. `k` was processed (Section 5).
2. If `σ(k) ≥ 2k`, then `T(H, k) = ∅` (Lemma 6.2), and there is nothing to
   prove. Otherwise the configuration `φ_π` was built (Lemma 6.1) and was not
   discarded (Lemma 6.3).
3. Some root `ρ` of `φ_π` has rules that `π` satisfies (Lemma 7.1).
   `generate` loops over every root.
4. **Induction on depth.** Let `n_t` be the node of `ρ` holding `π`'s first
   `t` free primes in `ρ`'s order. `n_0` is the root node. If `n_t` is not a
   tail node, Lemma 8.6 shows the program visits `n_{t+1}`. The depth is
   bounded by the number of free slots (at most 16), so the induction reaches
   a tail node `n_τ`.
5. The tail at `n_τ` reaches the final check with all of `π`'s remaining
   primes (§9.1–§9.5).
6. The final check accepts `π` and writes it (Section 10).

The only steps that could stop this chain are:

* a range that could not be capped below `2^400`;
* a range beyond primesieve's limit;
* a timeout.

Each of these marks `k` incomplete, and `k` was assumed not to be. ∎

---

## 12. Termination, and what "incomplete" means

Every loop runs over a finite set, or reports why it cannot:

* configurations: injective maps into the finite set of primes of `k`;
* roots: interleavings of at most 16 slots;
* scanned ranges: finite `[lo, hi]`, or flagged "bound_not_finite"
  (unbounded, or a lower end beyond `2^400`) or "range_beyond_2^64". The
  exception is the class walk of a Progression tail (§9.4). It walks a
  finite range beyond `2^64` with big integers instead of flagging it;
* tails: closed forms, integer roots of a nonzero polynomial, divisors of a
  nonzero integer, residue classes inside a finite range, and primes inside
  a finite range;
* recursion depth: at most the number of free slots.

So the program finishes every `k` after finitely many steps. That number may
be astronomically large for nearly perfect `k` or many-prime hashes; this is
what the optional time limits (`timeout_seconds` in mode range,
`single_timeout_seconds` in modes single and skipped) are for. A time limit
always records the `k` in `incomplete.txt`. If the line cannot be written
(another program keeps the file locked for more than ten seconds), the
program stops with an error and does not count the `k` as done.

A flag (`bound_not_finite`, `range_beyond_2^64`) is a property of `k`
itself: no retry with the same engine can remove it. A flag raised at any
point of a search therefore marks the `k` permanently incomplete. This holds
even when the time limit fired too, and even if the flag was raised in a
branch that finished before the stop. Such a `k` gets no resume point
(Appendix C, item 5).

In mode `skipped`, a `k` is deleted from `incomplete.txt` only after a search
of it ended with no time limit reached and no flag raised. That is the same
condition under which mode `range` would never have listed it. Its lines are
deleted under the file lock, after re-reading the file, so a line another run
is adding at the same moment is not lost. A file that exists but cannot be
opened is never read as empty. The program waits up to ten seconds for it
and then stops with an error, leaving the file as it was. Otherwise the
rewrite would replace every line with nothing (Appendix C, item 13). A `k`
stopped again by the time limit keeps a line, now with its resume point. A `k` with a flag keeps a
line that names the flag and has no resume point, and later skipped runs
leave it alone.

---

## 13. Resuming a stopped run

* **Mode range.** The state file holds the frontier of Section 5, so a
  restart repeats no work below it and skips nothing. The file is one
  number, rewritten in place (emptied, then written). A kill or power cut
  during the rewrite leaves the first digits of the number or an empty
  file. The first digits form a smaller number, so the restart begins
  earlier. An empty file makes the run start at `start_k` from config.txt,
  as if no state had been saved.
* **Modes single and skipped.** A point is a sequence
  `X = (root, q1, q2, …)`: a root, then one value for each level in that
  root's order. Points are compared lexicographically. A point claims that
  every leaf of the search lying before it is finished, except the leaves
  inside its own subtree.
  * A leaf `L` lies before `X` when `L < X` and `X` does not begin with
    `L`.
  * A missing entry means the start of its level, so `(r, q1)` is the start
    of `q1`'s subtree.
  * For a Progression tail (§9.4), the tail's `u` counts as one more level:
    §9.4 visits the members of `u`'s class in increasing order, each with a
    tail of its own.

  *How the work is split.* One thread, the generator, walks each root's
  levels in increasing order down to the *job depth*, the last scanned
  level. For each node there it queues one piece:
  * a *sweep*: the node's children in `[lo, hi]`, cut into blocks of
    consecutive values;
  * a *batch*: up to 32 consecutive short nodes, each run whole.

  The blocks of a piece are taken in increasing order.

  A Progression tail is planned by the thread that runs it, inside a block
  or a batch item (`run_prog_node`), never by the generator. When the range
  of its `u` is long, that thread does not walk it. It splits it off as a
  piece of its own, a *Progression sweep*: the members of the class in
  `[first, hi]`, in blocks.
  * The new piece is registered before the block or item that split it off
    counts as finished.
  * It is queued in search order among the other split-off pieces, ahead of
    every block not yet taken. It comes from a block taken from the front,
    so it lies before all of those.

  A block of a Progression sweep visits the class members in its interval
  (`progression_visit`). The class, the range and the work per member are
  those of the whole tail: its plan is made once, when the tail is planned,
  and every block uses it. The blocks
  partition `[first, hi]`. So the blocks together visit exactly the members
  §9.4 visits, and splitting changes nothing there.

  Mode range splits each `k` the same way, down to the same job depth, so
  idle threads join a `k` that runs much longer than the others. Two things
  differ there: a Progression tail is always run whole by the thread that
  plans it (no Progression sweeps), and no point is kept, since there each
  `k` is the unit of resuming. Either way the pieces of a node partition
  its children, so every node the search visits is visited exactly once.

  *The point.* It is the smallest of these:
  * the generator's point: the node it is at, extended by the child it is
    handling, or by the first child of a batch it is still filling;
  * for each queued piece not yet finished, split-off pieces included: the
    piece's node, extended by the start of its first unfinished block (a
    sweep) or by its first unfinished child (a batch).

  Every leaf before this point is finished, for three reasons:
  * The generator handles children in increasing order. Every child it has
    passed is finished, belongs to a queued piece, or sits in the batch it
    is filling, and that batch is covered by its point. A piece is
    registered before the generator moves past it.
  * Within a piece, every block before the first unfinished one is
    finished, apart from work split off from it. That work is a registered
    piece of its own, registered before the block counted as finished.
  * Each piece's entry is at most any of its unfinished work.

  The generator's point and the list of pieces are each read under their
  own lock, the generator's point first. By then, any piece the generator
  has moved past is registered, or already finished. No point is read
  half-updated. Appendix C, item 8 concerned an earlier version that
  published the point in two separate stores.

  *The restart.* Given `X`:
  * the generator skips the roots before `X[0]`;
  * at each level, for the node whose values so far equal `X`'s, it starts
    the children at the next entry of `X`;
  * a node on `X` at the job depth becomes a sweep that starts there, never
    a batch;
  * when `X` enters a Progression tail (it names a `u`), the generator
    plans that one tail itself and starts its `u` exactly at `X`'s entry,
    and the tail's parent's other children start after it.

  Off that path nothing is skipped. Each child skipped on the path has a
  smaller value than `X`'s entry, so its whole subtree lies before `X` and
  is finished. Every other leaf is searched again.

  Points saved by the earlier version have three entries `(root, q1, q2)`
  and keep their meaning under the rule for missing entries. A point whose
  root does not exist is ignored, and the `k` is searched from the start.
  Some work may be repeated, which is harmless because output is
  deduplicated: a pair already in the results file is not written again. A
  pair counts as already written only when both of its lines are in the
  file. A pair whose second line was lost to a kill or a power cut is
  written again in full (Appendix C, item 10).

  The same point is used in three ways. It is passed by hand (the
  `resume_with=` line). It is taken from `single_k_status.txt` when the
  program is started again on the same `k`. The file must name the same
  mode, the same hash, the same engine and that `k`, and its state must be
  `running` or `timeout`. Otherwise the `k` starts from the beginning.
  Finally, mode skipped takes it from the `resume=general:root,q1,q2[,…]` field
  of the `k`'s line in `incomplete.txt`, which only mode skipped writes,
  when a time limit stopped it.

  The mode has to match because modes single and skipped write different
  results files (`single_k_results.txt` and `multi_k_results.txt`). The
  pairs found before a point are in the file of the mode that made it. A
  point made by the other mode would leave them out of this mode's file
  (Appendix C, item 9). Mode single resumes only from its own status file.

  The state `incomplete` (a flag was raised, Section 12) has no resume
  point, so a flagged `k` is never continued from a point. Without this
  rule, a restart could skip a flagged branch before the point and then
  report the `k` as complete.

  The status file is rewritten about once a second, so a run that is
  killed leaves a point at most about a second old. Everything before that
  point was finished already when it was written, so the restart still
  skips nothing.

  The rewrite happens in place: the file is emptied, then written. A kill or
  power cut during a rewrite leaves only the first part of the new
  contents. The fields a restart reads are written in a fixed order, and
  nothing a restart reads comes after them:
  `resume_root`, `resume_q1`, `resume_q2`, then `resume_deeper`, which
  holds the entries from `q3` on, comma-separated. So a cut has one of
  three effects:
  * it drops one of the first three lines, and the `k` starts from the
    beginning;
  * it drops entries from the end of the point, which then means the start
    of that level, an earlier point;
  * it cuts the last number short, which makes it smaller and moves the
    point earlier.

  Either way nothing is skipped.

---

## 14. Limits of this proof, and the tests that back it

**What is not covered.**

* The correctness of GMP, primesieve, FLINT and hurchalla, and of the
  hardware (A1–A6).
* The primality of factors above `2^64`, which rests on BPSW-type tests (A3).
* Logic proofs do not catch typing mistakes. The tests below are the second
  line of defence.

**Tests that exercise these arguments.** All were run on the final version.

| test | what it checks | result |
|---|---|---|
| every amicable pair below 10⁹ (564 pairs, 89 hashes), exhaustive single-k runs | Main Theorem, end to end | all 267 (hash, k) groups that finish within 30 s found every pair |
| the same 564 pairs, guided: each pair's own witness path is walked | Lemmas 8.2–8.6 at every scanned level (1,387 levels), and every tail | 564 / 564 |
| the same, with every float3 tail forced through both of its sub-cases (§9.5 (ii)) | the "only B" path and its Progression on `[v, u, w]` | 564 / 564 (the code before the Appendix C, item 1 fix lost 45) |
| sech's AP23 list: all 28,503 pairs with k < 2^64, guided, with the scan limit applied as the program applies it | the same lemmas on large numbers | 28,500 found. The other 3 (k = 9,007,199,254,740,992, 36,033,534,233,673,728 and 2,305,845,198,573,273,088) lie on a branch whose scanned range ends beyond `2^64`. The program lists those k as `range_beyond_2^64` (§12) instead of finding the pairs, which the Main Theorem allows. 0 failures. (An earlier count of 28,486 / 28,486, for k < 2^63, came from a harness that ignored the scan limit.) |
| AP23, k < 8192, exhaustive | Main Theorem | all 591 pairs, no others |
| this engine against `Multi_K_Auto_Cached`'s independent algebra (the former `--engine special`, since removed), many ranges | independent cross-check | identical pairs |
| meet-in-the-middle divisor search against brute force | §9.5 step 3 | 20,000 cases, no difference; the current version (filter, batched inverses) against the earlier one and brute force: 500,000 cases, 59,354,812 divisors, no difference |
| σ(p^e) through cyclotomic pieces against direct computation | Lemma 6.4 | no difference |
| type 23, k ≤ 3000, stopped and restarted: time limits then mode skipped, repeated 1 s limits, `kill -9` inside a `k`, range and skipped running at once (both engines of that version) | §12–13 | results identical to the reference, no pair twice, `incomplete.txt` empty at the end |
| a flag forced early in a `k`, then a time limit, then a restart (test build) | §12–13, Appendix C item 5 | the `k` stays listed with its flag |
| a fatal error forced in one `k` while another runs (test build) | A6 | the other `k` is not counted as finished |
| `ModD` against exact 128-bit `%` with the x87 unit at 53 bits | A1 | 0 of 20,000 wrong (17,114 before Appendix C item 12) |
| `incomplete.txt` held with no sharing by another program while a `k` is removed (Windows build under Wine) | §12, Appendix C item 13 | 4 s hold: the other lines are kept (before: file emptied); 14 s hold: stops with an error, file untouched |
| deep resume points, test build: every finished piece and every point logged; tiny blocks, a point every 2 ms, a slowed generator; types 23, 33, 43, 32, 22, and 31 and 41 with a whole-root Progression; 5,709 Progression tails split off (`tests/check_resume_trace.py`) | §13 | over 31,000 points against up to 450,000 pieces: 0 points claim unfinished work; engines broken on purpose are caught (a point one block ahead: 1,612 violations; a point that ignores a batch being filled: 44,301; a split-off tail not registered: 67,022 to 2,293,252) |
| the second review's end-to-end check: restarts from points sampled during a run (up to 5 entries deep), types 23, 43, 33, 32; and the status file cut at every length | §13 | 53 restarts: every pair found before the point or by the restart; 321 cuts: no later point |
| a `k` searched in pieces until done, stopped by 2–5 s time limits or by `kill -9` at random moments: types 23 (k = 4096, 8192), 43 (k = 68, 124), 32 (k = 4096) | §13 | every one ends with exactly the pairs of one uninterrupted run, none written twice |

---

## Appendix A: lemma → code

| section | function(s) in `general.cpp` (or `engine.cpp`) |
|---|---|
| §5 | `Engine::worker`, `run_k`, `k_done`, `generate` (`engine.cpp`) |
| §6.1 | `build_search_k` (`rec`, `add_config`) |
| §6.2 | the start of `build_search_k`; the checks in `add_config` |
| Lemma 6.4 | `cached_sigma_nat`; the product check in `add_config` |
| §7 | `make_shapes`, `split_shape`, `interleave`, `root_shapes` |
| §8.1 | `root_node`, `make_child` |
| §8.2–8.3 | `range_for`, `upper_ok(_exact)`, `lower_ok(_exact)`, `upper_filter`, `lower_filter`, `find_upper`, `find_lower`, `refine_upper`, `refine_lower`, `lower_ok_limit` |
| §8.4 | the first block of `range_for` |
| §8.5 | `process`, `scan_children`; `Engine::generate`, `expand`, `run_block`, `run_item` (`engine.cpp`) |
| §9.1–9.4 | `run_tail`, `tail_same`, `solve_same`, `tail_mixed2`, `mixed_closed`, `integer_roots` (`introots.cpp`), `tail_progression`, `prog_plan`, `prog_visit`, `lin_congr`, `crt2`, `prog_class_native` |
| §9.5 | `tail_divisor3`, `tail_divisor3_split`, `divisor3_native`, `rstar_native128`, `divisor3_scan`, `divisor3_cap`, `alone_filter`, `signed_divisors_mod`, `divisors_with_residue`, `ModD` (`divisors.h`) |
| §10 | `emit` |
| §12 | `Engine::k_done`, `append_incomplete` (`engine.cpp`); `search_one_k`, `permanent_reason`, `run_skipped` (`multi_k_main.cpp`); `read_skip_file`, `append_skip_line`, `edit_skip_file` (`skip_file.cpp`) |
| §13 | `Engine::status`, `generate`, `expand`, `split_progression`, `push_job`, `run_item`, `run_block`, `finish_block`, `set_gen` (`engine.cpp`); `progression_range`, `progression_visit` (`general.cpp`); `status_resume`, `run_single`, `run_skipped` (`multi_k_main.cpp`); `pairs_in_file` (`types.cpp`) |

---

## Appendix B: the floating-point margin

The pre-screen in `upper_filter` and `lower_filter` computes `X⁺, Y⁺` (or
`X⁻, Y⁻`) in double precision. It decides only when the result is clear by a
margin.

**Lemma B.1.** Let `u = 2^-53` be the unit roundoff. Suppose the next slot has
exponent `e`, there are `j = j0 + j1` ordered remaining primes and `f`
floating ones. Then the computed `X̂ = X⁺(1 + θ)` with `|θ| ≤ δ`, where
`δ := 5(e + j + f + 2)u + O(u²)`. The same holds for `Ŷ`.

*Proof sketch* (standard error analysis: each operation adds a relative error
of at most `u`, and a GMP conversion at most `2u`; GMP truncates, so a
conversion lies in `[x(1 − 2u), x]`):

| quantity | relative error at most |
|---|---|
| `x0 = a/b`: two truncating conversions and one division | `5u` |
| `q` as a double | `2u` |
| `H_e(q) = Σ_{i=0}^{e} q^{-i}`: term `i` comes from `i` divisions by `q`; then `e` additions of positive terms | `3iu` per term; `4eu` in total |
| `(1 + 1/q)^j` | `5ju` |
| each floating factor `1 + 1/L_i` (conversion, division, addition, multiplication) | `5u` |
| final products | `3u` |

Summing gives `δ`. ∎

*Underflow.* "Relative error at most `u`" holds only for results in the
normal range. Every sum, difference and product here is 0 or between
`2^-110` and `2^410`, but the divisions `t /= q` in `h_ld` reach `q^-e`,
which underflows (for example `q` near `2^400` and `e ≥ 3`). There a rounding
has an absolute error of at most `2^-1075` instead. It adds at most
`3e·2^-1075` to a sum `s ≥ 1`, which is far below one more factor `u`.

The code uses the margin `ε = max(10⁻¹³, 16·(e + j + f + 3)·u)`, so
`ε ≥ 3δ`.

* **Threshold tests.** If `X̂ < 2(1 − ε)`, then
  `X⁺ ≤ X̂/(1 − δ) < 2(1 − ε)/(1 − δ) < 2`. If `X̂ > 2(1 + ε)`, then
  `X⁺ > 2`. The same holds for `Ŷ` against 1 or 2.
* **Product test.** `x0, y0 ≥ 1` (they are abundancies) and every other
  factor is `≥ 1`, so `X⁺, Y⁺ ≥ 1` and `|X⁺ − 1| ≤ X⁺`, `|Y⁺ − 1| ≤ Y⁺`.
  The computed `p̂ ≈ (X̂ − 1)(Ŷ − 1)` then differs from the true
  product by at most about `(2δ + 2δ)·X⁺Y⁺ < 4ε·X̂Ŷ`. That is the `err`
  the code subtracts or adds before comparing with 1.

The thresholds `2(1 ± ε)` and `1 ± err` are rounded too, once each; that adds
`u` to each condition, which the margin covers.

*Checked in Lean* (`lean/AmicableProof/FP.lean`). Counting a
truncating conversion as three roundings, every evaluation of `X` (or `Y`) is
within `N = 5e + 6j + 6f + 11` roundings of `X⁺`, so `|X̂ − X⁺| ≤ D·X⁺` with
`D = 2Nu`. With `n = e + j + f ≤ 10^8` and `ε ≥ 16(n + 3)u`, the conditions the
argument needs, `ε ≥ D + 2u` and `4ε(1 − D)²(1 − u)³ ≥ D(2 + D) + 4u(1 + D)² + u`,
hold (`ε ≥ 3δ` above is their first-order form). Each use of `X̂` and `Ŷ` may
come from a different evaluation, which covers any fused multiply-add.

So whenever the pre-screen decides, its answer equals the exact test. In
every other case the exact integer test decides. The margin grows with the
hash's exponents, so this holds for every hash the program accepts (at most
16 primes, exponents at most 1000).

---

## Appendix C: defects found while checking the code

Checking each step against the code found three places where the code did
not match the argument (items 1–3). Building on Linux later found a fourth,
in how a library was called (item 4).

An independent review then checked both versions, Windows and Linux,
against this proof. It found no error in Sections 3–11. It did find two
kinds of problems elsewhere:
* nine defects in the code around the search (items 5–13; the review's IDs
  are given with each):
  * seven in how runs are stopped, resumed and recorded;
  * two in Windows platform details;
* ten statements in the proof's other sections that were wrong or missing
  (the review's P1–P10, listed at the end of this appendix).

Each defect was reproduced before it was fixed. C5 needed a test hook to
widen its race window. Every reproduction passes on the fixed code.

All thirteen defects are fixed in the delivered sources. All ten statements
are corrected, and the proof above describes the fixed code. All tests in
Section 14 were re-run after the fixes.

1. **Wrong slot in one Progression case** (§9.5 (ii), "only B").
   `tail_progression` created its child node for the *root's* next slot
   (`u`), while in this case the prime being placed is `v`. A pair reaching
   this case would be lost.
   * The case needs a float3 tail in which `u` cannot be the smallest prime
     while `v` can. That only happens when the two slots have different
     lower limits, through a bound prime between them.
   * No test pair reached it in normal runs. Forcing every float3 tail
     through this path, the old code lost 45 of the 564 test pairs; the
     fixed code finds all 564.
   * Fix: every node now records its slot, and `make_child` takes the slot
     explicitly.
2. **Lower end beyond 2^400** (§8.3). When the lower test was still false at
   `2^400`, the range was treated as empty. Correct handling depends on the
   limit `L(∞)`. Now the range is empty only if `L(∞)` fails; otherwise the
   `k` is marked incomplete. This needs primes above 10¹²⁰, so it never
   arises in practice, but the guarantee must hold without that caveat.
3. **Fixed floating-point margin** (Appendix B). The margin was a fixed
   `10⁻¹³`. For exponents in the hundreds (accepted, if unusual), the
   rounding error of the pre-screen could exceed it. The margin now scales
   with the number of operations, as above.
4. **Where a prime scan starts** (assumption A2). After
   `primesieve::iterator it(lo, hi)`, primesieve 11 and later return the
   primes `≥ lo`, but versions 7 to 10 return only the primes `> lo`. With an
   older library, a prime equal to the computed lower end `lo` was skipped.
   Lower ends are often primes themselves, so this does happen.
   * Found by the Linux self-test on Ubuntu 22.04, which ships primesieve
     7.8. The general engine missed pairs there (for example 2 of the 4
     X22 pairs with k ≤ 300,000).
   * The Windows build uses primesieve 11 or later, so it was never
     affected. Its results stand.
   * Fix: every iterator is built at `prime_iter_start(lo)`. This is `lo` for
     primesieve 11+ and `lo − 1` for older versions, so both return exactly
     the primes `≥ lo`. `check_prime_iterator()` tests the convention
     against the loaded library each time a program starts, and refuses to
     run if it does not hold.
5. **A flag lost at a time limit** (Sections 12–13, modes single and
   skipped; review: C1). The status reported only the flags of the branch running when
   the time limit fired. Suppose `range_beyond_2^64` was raised in a branch
   that ended before the stop. The `k` was then saved as an ordinary
   timeout, with a resume point after that branch. The next run started
   after the flagged branch and reported the `k` as complete.
   * Reproduced: `k = 4096` with the flag forced in an early branch. The old
     code printed "[done] … (removed from incomplete.txt)". The fixed code
     keeps "4096 range_beyond_2^64".
   * Fix: the engine keeps every flag seen during the `k`
     (`EngineStatus::flags`). Any flag makes the `k` permanent, with state
     `incomplete` and no resume point.
6. **A fatal error in another k** (A6, mode range; review: C2). When a fatal error in
   one `k` stopped the program, other `k` values running at the same time
   were cut short. One whose remaining work had not yet been handed out
   could still be counted as finished, which moved the state file's
   frontier past it.
   * Reproduced: an error forced in `k = 527873` while `k = 527872` was
     running. The old state file read 527873; the fixed one reads 527872.
   * Fix: `run_k` marks its `k` failed when the program is stopping.
7. **Failed writes to `incomplete.txt`** (Section 12; review: C3). A `k` was counted as
   done after its line was "written", even when the write had failed. That
   happens when another program (an editor, a virus scanner, a sync client)
   holds the file open on Windows. The `k` was then neither searched nor
   listed.
   * Reproduced under Wine, with a second program holding the file.
   * Fix: the write is retried for up to 10 s and then raises an error. The
     error stops the program, and the `k` is not counted as done.
8. **Resume point taken between two stores** (Section 13; review: C5). On moving to a
   new root, the generator stored the new root and only then reset its
   first-prime position. A status written in between paired the new root
   with the old root's first prime. That point lay after first primes of
   the new root that had not even been generated, and a restart would have
   skipped them.
   * The window is a few nanoseconds once per root, so a run is unlikely to
     have hit it by chance.
   * Reproduced with a test hook that pauses 5 s between the two stores. A
     kill at the status point `(1, 16127, 0)` made the restart report the `k`
     complete with 0 of its 72 pairs. With the fix, the first status in root
     1 is `(1, 0, 0)`, and the restart finds all 72.
   * Fix: the position is reset first, so the worst case is
     `(old root, 0)`, which lies before the true point.
9. **Status file from the other mode** (Section 13; review: C4). Modes single and
   skipped share `single_k_status.txt` but write different results files.
   A point made by one mode could be used by the other, so the pairs before
   it ended up only in the other mode's file. Mode single also wrote its
   point into `incomplete.txt`, where mode skipped would use it the same
   way.
   * Reproduced: mode single on `k = 4096` with an 8 s limit, then mode
     skipped. `incomplete.txt` ended empty, and `multi_k_results.txt` held 64
     of the 72 pairs. With the fix, mode skipped starts the `k` from the
     beginning and writes all 72.
   * Fix: the status file's `mode` must match. Mode single no longer writes
     `resume=` into `incomplete.txt`; its own resume point stays in the
     status file.
10. **A half-written pair counted as written** (Section 13; review: C6). Deduplication
    read the results file and counted a pair as present when its first line
    was there. A run killed between the two lines of a pair left only the
    first. Every later run then refused to write the pair again, so it
    stayed half missing.
    * Reproduced: `single_k_results.txt` was cut after the first line of the
      `k = 611,488` pair. The rerun left it cut. With the fix, the pair is
      written in full.
    * Fix: a pair counts as present only when both lines are in the file.
11. **`unsigned long` is 32 bits on Windows** (A3, the former specialized
    engine only, since removed; review: X2). `FactorBuffer::add_u64` compared a 64-bit prime with
    `mpz_cmp_ui`, whose argument is an `unsigned long`. On Windows the
    prime was cut to its low 32 bits.
    * Two different primes that agree modulo `2^32` could be merged into
      one, for example `3` and `21,474,836,483 = 3 + 5·2^32`. That gives a
      wrong factorization and, with it, a wrong divisor list.
    * Only the specialized engine and the former `Multi_K_Auto_Cached`
      build their factor lists this way. The general engine compares big
      integers (`fac_add`). Linux has 64-bit `unsigned long` and was never
      affected.
    * It needs two primes of one factored number to agree in 32 bits, about
      one chance in 10⁹ per factorization.
    * Reproduced in a Windows build: adding 3 and then 21,474,836,483 gave
      `3^2`. The fixed code gives `3 · 21,474,836,483`.
    * Fix: the full 64-bit value is compared. All other `mpz_*_ui` calls
      were checked: they pass values below `2^16` or are guarded by
      `mpz_fits_ulong_p`.
12. **x87 precision on Windows** (A1; review: X1). `ModD`, used by the meet-in-the-middle
    divisor search of §9.5 for moduli between `2^52` and `2^62`, estimated
    a quotient in `long double` and corrected it by at most one step. That
    is correct only with the x87 unit's full 64-bit mantissa.
    * Windows starts new threads at 53 bits. MinGW's "posix" thread model
      (winpthreads) resets this to 64 bits in every thread, but the "win32"
      thread model does not.
    * Reproduced in a win32-model build: 17,114 of 20,000 products modulo
      `d ≈ 2^62` were wrong in a worker thread. The fixed code gets 0 wrong.
    * The build that produced the existing Windows results (MSYS2 GCC with
      libwinpthread) uses the posix model, so it was not affected.
    * Fix: the remainder is now checked in exact 128-bit arithmetic and
      recomputed with `%` whenever the estimate is off, so the result no
      longer depends on the precision.
    * Every engine thread, and the main thread, also sets the x87 unit to
      64 bits at start (`fpu.h`), whichever thread model a compiler uses.
13. **`incomplete.txt` erased while another program holds it** (Section 12,
    Windows, modes single and skipped; review: C7). `read_skip_file` could
    not tell a file it could not open from a missing one, and returned no
    lines. Each rewrite then went wrong:
    * `edit_skip_file` applied its edit to that empty list.
    * `replace_file` retried until the other program let go, then replaced
      `incomplete.txt` with the result.
    * Every other listed `k` was gone, and mode skipped reported "0 k left".

    More about the defect:
    * It needs another program to open `incomplete.txt` without read
      sharing, for less than ten seconds, just as mode single or skipped
      rewrites it after a `k`.
    * Mode range only appends to the file and was not affected. Linux has no
      share modes, so a read there cannot fail this way.
    * It was in the original code. The review found it on its second pass.
    * Reproduced under Wine with five listed `k` and a 4 s exclusive hold.
      Removing one `k` left an empty file. The fixed code waits for the hold
      to end and keeps the other four. A 14 s hold now stops with "cannot
      read …" after ten seconds and leaves the file untouched.
    * Fix: a file that exists but cannot be opened is retried for ten
      seconds, then raises an error. A missing file still reads as empty,
      and a read error part-way through also raises an error.

**Corrections to the text.** The review also listed ten statements outside
the mathematics of Sections 3–11 that were wrong or missing. All are
corrected above.

| review | where | what was wrong | corrected in |
|---|---|---|---|
| P1 | §12, §13 | the deletion rule and auto-resume ignored a flag raised before a stop, the mode, and a torn read of the generator's position | §12, §13; items 5, 8, 9 |
| P2 | §5, A6 | a fatal error left only the failing `k` unfinished | A6; item 6 |
| P3 | A3 | it said the product of every factorization is checked, and called hurchalla's 128-bit test BPSW-type | A3 now names the routes that check the product and those that do not, and the primality test used on each |
| P4 | A5 | it left out two things: x87 precision in worker threads, and that doubles use SSE2 (no x87 double rounding) | A1, A5; item 12 |
| P5 | A2 | the extra `next_prime()` call past `hi` throws when `hi` is within the last primes below `2^64` | A2 |
| P6 | §9.5 | an unnecessary coprimality step in the content reduction | §9.5, direct divisibility |
| P7 | §9.4, §12 | a Progression class walk beyond `2^64` is walked, not flagged | §9.4, §12 |
| P8 | §14 | the AP23 guided count included 3 pairs whose path crosses a range beyond `2^64` | §14 |
| P9 | §1.4 | "the results file" is two files, one per mode | §1.4 |
| P10 | §13 | the status and state files are rewritten in place | §13: a cut write can only move the point earlier |
