/-
  §1 of exhaustive_search_proof.md: divisor sums, amicable pairs, the hash and k,
  and the set T(H, k).  Everything is built from Mathlib's standard notions:
  `ArithmeticFunction.sigma 1` (σ(n) = Σ_{d ∣ n} d), `Nat.factorization`
  (the exponent v_p(n) of each prime), `Nat.primeFactors` and `Nat.gcd`.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Finset.Sort

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Amicable

/-- §1.2.  An amicable pair `(N1, N2)` with `N1 < N2`:  σ(N1) = σ(N2) = N1 + N2.
`0 < N1` is not an extra condition (σ 1 0 = 0 ≠ 0 + N2 when N2 > 0), but it is
stated so that the definition reads as in the proof. -/
def IsAmicablePair (N1 N2 : ℕ) : Prop :=
  0 < N1 ∧ N1 < N2 ∧ σ 1 N1 = N1 + N2 ∧ σ 1 N2 = N1 + N2

/-- §1.3.  A slot `(e, b)`: on its own side the prime has `e` more powers than on
the other side, and it divides `k` exactly `b` times. -/
structure Slot where
  e : ℕ
  b : ℕ
  deriving DecidableEq, Repr

/-- A hash: the slots of the smaller member (side 0) and of the larger member
(side 1), each list in increasing order of its primes. -/
abbrev Hash := List Slot × List Slot

/-- The primes with a strictly larger exponent in `M` than in `N`, increasing. -/
noncomputable def slotPrimes (M N : ℕ) : List ℕ :=
  (M.primeFactors.filter fun p => N.factorization p < M.factorization p).sort

/-- The slots of `M`'s side against the other member `N`: for each prime with
`v_p(M) > v_p(N)`, in increasing order, the slot `(v_p(M) − v_p(N), v_p(N))`. -/
noncomputable def slotsOf (M N : ℕ) : List Slot :=
  (slotPrimes M N).map fun p => ⟨M.factorization p - N.factorization p, N.factorization p⟩

/-- §1.3.  The hash of the pair `(N1, N2)`. -/
noncomputable def hashOf (N1 N2 : ℕ) : Hash := (slotsOf N1 N2, slotsOf N2 N1)

/-- §1.4.  `T(H, k)`: the amicable pairs with hash `H` and `gcd(N1, N2) = k`. -/
def T (H : Hash) (k : ℕ) : Set (ℕ × ℕ) :=
  {π | IsAmicablePair π.1 π.2 ∧ hashOf π.1 π.2 = H ∧ Nat.gcd π.1 π.2 = k}

/-- §1.3, "every amicable pair has exactly one hash and exactly one k": the sets
`T(H, k)` for different `(H, k)` are disjoint, and every amicable pair lies in one. -/
theorem T_partition {N1 N2 : ℕ} (h : IsAmicablePair N1 N2) :
    (N1, N2) ∈ T (hashOf N1 N2) (Nat.gcd N1 N2) ∧
    ∀ H k, (N1, N2) ∈ T H k → H = hashOf N1 N2 ∧ k = Nat.gcd N1 N2 := by
  refine ⟨⟨h, rfl, rfl⟩, fun H k hm => ⟨hm.2.1.symm, hm.2.2.symm⟩⟩

end Amicable
