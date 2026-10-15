/-
  Sanity checks for §1: the definitions give the hashes, k values and pairs that
  the README lists.  If `hashOf`, `IsAmicablePair` or `T` were defined wrongly
  (for example so that every set `T(H, k)` were empty), these would fail.
-/
import AmicableProof.Defs
import Mathlib.Tactic.Simproc.Factors
import Mathlib.Tactic.Simproc.Divisors
import Mathlib.Tactic.NormNum

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Amicable

theorem factorization_eq_count (n p : ℕ) : n.factorization p = n.primeFactorsList.count p :=
  Nat.primeFactorsList_count_eq.symm

/-- 220 = 2²·5·11 and 284 = 2²·71: hash `[(1,0),(1,0)] _ [(1,0)]`, k = 4. -/
theorem sanity_220_284 :
    (220, 284) ∈ T ([⟨1, 0⟩, ⟨1, 0⟩], [⟨1, 0⟩]) 4 := by
  refine ⟨⟨by norm_num, by norm_num, ?_, ?_⟩, ?_, by norm_num⟩
  · rw [sigma_one_apply]; simp only [Nat.divisors_ofNat]; decide
  · rw [sigma_one_apply]; simp only [Nat.divisors_ofNat]; decide
  · simp only [hashOf, slotsOf, slotPrimes, factorization_eq_count, Nat.primeFactors,
      Nat.primeFactorsList_ofNat]
    have h1 : ({x ∈ [2, 2, 5, 11].toFinset | List.count x [2, 2, 71] < List.count x [2, 2, 5, 11]} :
        Finset ℕ) = {5, 11} := by decide
    have h2 : ({x ∈ [2, 2, 71].toFinset | List.count x [2, 2, 5, 11] < List.count x [2, 2, 71]} :
        Finset ℕ) = {71} := by decide
    have h3 : (({5, 11} : Finset ℕ).sort fun a b => a ≤ b) = [5, 11] := by
      rw [Finset.sort_insert (s := {11}) (a := 5) (fun a b => a ≤ b) (by decide) (by decide),
        Finset.sort_singleton]
    rw [h1, h2, h3, Finset.sort_singleton]
    decide

/-- 1184 = 2⁵·37 and 1210 = 2·5·11²: hash `[(4,1),(1,0)] _ [(1,0),(2,0)]`, k = 2
(a bound slot: 2 divides k once and has 4 more powers in N1). -/
theorem sanity_1184_1210 :
    (1184, 1210) ∈ T ([⟨4, 1⟩, ⟨1, 0⟩], [⟨1, 0⟩, ⟨2, 0⟩]) 2 := by
  refine ⟨⟨by norm_num, by norm_num, ?_, ?_⟩, ?_, by norm_num⟩
  · rw [sigma_one_apply]; simp only [Nat.divisors_ofNat]; decide
  · rw [sigma_one_apply]; simp only [Nat.divisors_ofNat]; decide
  · simp only [hashOf, slotsOf, slotPrimes, factorization_eq_count, Nat.primeFactors,
      Nat.primeFactorsList_ofNat]
    have h1 : ({x ∈ [2, 2, 2, 2, 2, 37].toFinset | List.count x [2, 5, 11, 11] <
        List.count x [2, 2, 2, 2, 2, 37]} : Finset ℕ) = {2, 37} := by decide
    have h2 : ({x ∈ [2, 5, 11, 11].toFinset | List.count x [2, 2, 2, 2, 2, 37] <
        List.count x [2, 5, 11, 11]} : Finset ℕ) = {5, 11} := by decide
    have h3 : (({2, 37} : Finset ℕ).sort fun a b => a ≤ b) = [2, 37] := by
      rw [Finset.sort_insert (s := {37}) (a := 2) (fun a b => a ≤ b) (by decide) (by decide),
        Finset.sort_singleton]
    have h4 : (({5, 11} : Finset ℕ).sort fun a b => a ≤ b) = [5, 11] := by
      rw [Finset.sort_insert (s := {11}) (a := 5) (fun a b => a ≤ b) (by decide) (by decide),
        Finset.sort_singleton]
    rw [h1, h2, h3, h4]
    decide

/-- 6232 = 2³·19·41 and 6368 = 2⁵·199: hash `[(1,0),(1,0)] _ [(2,3),(1,0)]`, k = 8
(the shared prime 2 sits on the larger side with multiplicity 3). -/
theorem sanity_6232_6368 :
    (6232, 6368) ∈ T ([⟨1, 0⟩, ⟨1, 0⟩], [⟨2, 3⟩, ⟨1, 0⟩]) 8 := by
  refine ⟨⟨by norm_num, by norm_num, ?_, ?_⟩, ?_, by norm_num⟩
  · rw [sigma_one_apply]; simp only [Nat.divisors_ofNat]; decide
  · rw [sigma_one_apply]; simp only [Nat.divisors_ofNat]; decide
  · simp only [hashOf, slotsOf, slotPrimes, factorization_eq_count, Nat.primeFactors,
      Nat.primeFactorsList_ofNat]
    have h1 : ({x ∈ [2, 2, 2, 19, 41].toFinset | List.count x [2, 2, 2, 2, 2, 199] <
        List.count x [2, 2, 2, 19, 41]} : Finset ℕ) = {19, 41} := by decide
    have h2 : ({x ∈ [2, 2, 2, 2, 2, 199].toFinset | List.count x [2, 2, 2, 19, 41] <
        List.count x [2, 2, 2, 2, 2, 199]} : Finset ℕ) = {2, 199} := by decide
    have h3 : (({19, 41} : Finset ℕ).sort fun a b => a ≤ b) = [19, 41] := by
      rw [Finset.sort_insert (s := {41}) (a := 19) (fun a b => a ≤ b) (by decide) (by decide),
        Finset.sort_singleton]
    have h4 : (({2, 199} : Finset ℕ).sort fun a b => a ≤ b) = [2, 199] := by
      rw [Finset.sort_insert (s := {199}) (a := 2) (fun a b => a ≤ b) (by decide) (by decide),
        Finset.sort_singleton]
    rw [h1, h2, h3, h4]
    decide

/-- A non-pair is in no `T(H, k)`: 220 and 285 fail σ(N1) = N1 + N2. -/
theorem sanity_not_pair (H : Hash) (k : ℕ) : (220, 285) ∉ T H k := by
  rintro ⟨⟨-, -, h, -⟩, -⟩
  rw [sigma_one_apply] at h; simp only [Nat.divisors_ofNat] at h; revert h; decide

end Amicable
