/-
  §2 of exhaustive_search_proof.md: what is assumed about the computer, as explicit
  hypothesis structures over an abstract interface `Impl` to the program's primitives.
  Nothing here is an `axiom`: a theorem that needs an assumption takes it as an argument.

  A5 (floating point) is used in `FP.lean` in its per-operation form: every theorem there
  takes the rounding errors `η` with `|η| ≤ u`, the underflow terms `ζ` with `|ζ| ≤ λ`, and
  the truncating conversions (`A 3 d x`) as hypotheses; `A5` below bundles the same model for
  the operations themselves, so that a model of the code built from `Impl` meets FP's
  hypotheses.
-/
import AmicableProof.FP
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Sort

namespace Amicable

/-- The primitives of the program that the proof treats as black boxes. -/
structure Impl where
  /-- `ModD` (`divisors.h`) and the other modular products: `a·b mod m`. -/
  mulMod : ℕ → ℕ → ℕ → ℕ
  /-- integer `r`-th root, rounded down (`introots.cpp`). -/
  iroot : ℕ → ℕ → ℕ
  /-- `primesieve::iterator(prime_iter_start(lo), hi)`: `none` = the call throws (fatal). -/
  primesIn : ℕ → ℕ → Option (List ℕ)
  /-- primesieve's `get_max_stop()`. -/
  maxStop : ℕ
  /-- the factorization routines (hurchalla, FLINT): list of `(p, v_p(n))`. -/
  factor : ℕ → List (ℕ × ℕ)
  /-- `prime_test` / `is_prime_u64_fast` / `mpz_probab_prime_p`. -/
  isPrime : ℕ → Bool
  /-- binary64 operations on exactly-represented values (rationals). -/
  fadd : ℚ → ℚ → ℚ
  fsub : ℚ → ℚ → ℚ
  fmul : ℚ → ℚ → ℚ
  fdiv : ℚ → ℚ → ℚ
  /-- GMP's `mpz_get_d` (truncating) on a positive integer. -/
  toDouble : ℕ → ℚ

/-- **A1.** Integer arithmetic is exact (GMP; 128-bit with overflow checks and GMP fallback;
`ModD`'s floating quotient corrected exactly). -/
structure A1 (I : Impl) : Prop where
  mulMod_exact : ∀ a b m, 0 < m → I.mulMod a b m = a * b % m
  iroot_exact : ∀ n r, 0 < r → I.iroot n r ^ r ≤ n ∧ n < (I.iroot n r + 1) ^ r

/-- **A2.** For `hi ≤ maxStop` the iterator yields exactly the primes of `[lo, hi]` in
increasing order; beyond it, the program stops with a fatal error (A6). -/
structure A2 (I : Impl) : Prop where
  exact : ∀ lo hi, hi ≤ I.maxStop →
    I.primesIn lo hi = some ((List.range' lo (hi + 1 - lo)).filter Nat.Prime)
  fatal : ∀ lo hi, I.maxStop < hi → I.primesIn lo hi = none

/-- **A3.** The factorization routines return the true factorization, primes increasing. -/
structure A3 (I : Impl) : Prop where
  primes : ∀ n, 0 < n → (I.factor n).map Prod.fst = n.primeFactors.sort
  exps : ∀ n, 0 < n → ∀ pe ∈ I.factor n, pe.2 = n.factorization pe.1

/-- **A4.** A primality test never calls a prime composite, and below `2⁶⁴` it is exact. -/
structure A4 (I : Impl) : Prop where
  no_false_composite : ∀ p, p.Prime → I.isPrime p = true
  exact_u64 : ∀ n, n < 2 ^ 64 → (I.isPrime n = true ↔ n.Prime)

/-- A result that is neither subnormal nor overflowing (`x = 0` is exact anyway). -/
def InNormalRange (x : ℚ) : Prop := x = 0 ∨ ((1 : ℚ) / 2 ^ 1022 ≤ |x| ∧ |x| < 2 ^ 1024)

open FP in
/-- **A5.** binary64, round to nearest: each operation returns the exact result times
`(1+η)`, `|η| ≤ u`, plus (for a quotient in the subnormal range) an absolute error `ζ`,
`|ζ| ≤ 2⁻¹⁰⁷⁵`; a sum, difference or product is only claimed in the normal range (in the
pre-screen every one is 0 or of magnitude between 2⁻¹¹⁰ and 2⁴¹⁰); rounding never changes the sign of a nonnegative result; GMP's conversion
truncates (`x(1-2u) ≤ d ≤ x`).  A fused multiply-add is the case of a product with `η = 0`
(see `FP.lean`). -/
structure A5 (I : Impl) : Prop where
  add : ∀ x y, InNormalRange (x + y) → ∃ η, |η| ≤ u ∧ I.fadd x y = (x + y) * (1 + η)
  sub : ∀ x y, InNormalRange (x - y) → ∃ η, |η| ≤ u ∧ I.fsub x y = (x - y) * (1 + η)
  mul : ∀ x y, InNormalRange (x * y) → ∃ η, |η| ≤ u ∧ I.fmul x y = x * y * (1 + η)
  div : ∀ x y, y ≠ 0 → |x / y| < 2 ^ 1024 →
    ∃ η ζ, |η| ≤ u ∧ |ζ| ≤ lam ∧ I.fdiv x y = x / y * (1 + η) + ζ
  div_nonneg : ∀ x y, 0 ≤ x → 0 < y → 0 ≤ I.fdiv x y
  conv : ∀ n : ℕ, 0 < n → (n : ℚ) * (1 - 2 * u) ≤ I.toDouble n ∧ I.toDouble n ≤ n

/-- **A6.** Every work item handed to a thread is executed; work stops early only by the
time limit (which marks the `k` incomplete) or by a fatal error (which stops the program and
leaves every `k` it cut short unfinished).  It is a property of the scheduler, so it is stated
about a run: the set of executed items equals the set of queued items unless the run was
stopped. -/
structure A6 (Item : Type) (queued executed : Set Item) (stopped : Prop) : Prop where
  all_run : ¬ stopped → queued ⊆ executed

end Amicable
