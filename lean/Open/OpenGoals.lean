/-
  The lemma statements this file used to list as open (6.2, 6.3, 8.3) are now proved in the
  library (`AmicableProof/Search.lean`); the theorems at the end check that the library's
  statements are exactly these.  This file is outside the library (it is not imported by
  `AmicableProof.lean`); `check.sh` checks that it elaborates.
  What remains open is the model of the search and the Main Theorem: see `Open/README.md`.
-/
import AmicableProof

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Amicable.Open

/-- Lemma 6.2 (abundant k): if `σ(k) ≥ 2k` then `T(H, k)` is empty. -/
def lemma_6_2 : Prop :=
  ∀ (H : Hash) (k : ℕ), 0 < k → 2 * k ≤ σ 1 k → T H k = ∅

/-- Lemma 6.3 (dead configuration), contrapositive form: the configuration of an amicable
pair has `σ(K2) < 2·K2` and `(σ(K1) − K1)(σ(K2) − K2) ≤ K1·K2`. -/
def lemma_6_3 : Prop :=
  ∀ N1 N2 : ℕ, IsAmicablePair N1 N2 →
    let k := Nat.gcd N1 N2
    let K1 := k * boundPart N1 N2
    let K2 := k * boundPart N2 N1
    σ 1 K2 < 2 * K2 ∧ (σ 1 K1 - K1) * (σ 1 K2 - K2) ≤ K1 * K2

open FP in
/-- Lemma 8.3 (monotone): `U` is non-increasing and `L` non-decreasing in `q`. -/
def lemma_8_3 : Prop :=
  ∀ (x0 y0 q q' : ℚ) (e j0 j1 : ℕ) (side0 : Bool) (Lx Ly : List ℚ),
    1 ≤ x0 → 1 ≤ y0 → 2 ≤ q → q ≤ q' → 1 ≤ e → (∀ L ∈ Lx ++ Ly, 0 < L) →
    (Utest (Xexact x0 q' e j0 side0 Lx) (Xexact y0 q' e j1 (!side0) Ly) →
      Utest (Xexact x0 q e j0 side0 Lx) (Xexact y0 q e j1 (!side0) Ly)) ∧
    (Ltest (Xexact x0 q e 0 side0 []) (Xexact y0 q e 0 (!side0) []) →
      Ltest (Xexact x0 q' e 0 side0 []) (Xexact y0 q' e 0 (!side0) []))

/- The Main Theorem itself is stated in the library as `Amicable.MainTheorem Run`
   (AmicableProof/MainStatement.lean).  Open: build the model `Run` of the engine (M2) and
   prove `MainTheorem Run` (M3). -/

/-! The three statements above, closed by the library. -/

theorem lemma_6_2_holds : lemma_6_2 := fun H k hk hab => Amicable.lemma_6_2 H k hk hab

theorem lemma_6_3_holds : lemma_6_3 := fun _ _ h => Amicable.lemma_6_3 h

theorem lemma_8_3_holds : lemma_8_3 := fun x0 y0 q q' e j0 j1 side0 Lx Ly hx0 hy0 hq hqq he hL =>
  Amicable.FP.lemma_8_3 x0 y0 q q' e j0 j1 side0 Lx Ly hx0 hy0 hq hqq he hL

end Amicable.Open
