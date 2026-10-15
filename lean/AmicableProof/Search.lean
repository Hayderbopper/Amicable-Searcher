/-
  The mathematical lemmas of §6, §8 and §9 of exhaustive_search_proof.md that do not need a
  model of the program: the early exits of §6.2, the monotonicity of the tests (Lemma 8.3),
  the bisection (Lemma 8.4), and the algebra the tails solve exactly (§9.2, §9.3, §9.5,
  Lemma 9.2).  What is still open is the model of the search itself (`Open/README.md`).
-/
import AmicableProof.Basic
import AmicableProof.FP
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.LinearCombination

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Amicable

/-! ### Abundancy of a divisor -/

/-- `h(n) = σ(n)/n = Σ_{d ∣ n} 1/d`. -/
theorem abund_eq_sum_inv {n : ℕ} (hn : 0 < n) :
    abund n = ∑ d ∈ n.divisors, (1 / (d : ℚ)) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold abund
  rw [sigma_one_apply, ← Nat.sum_div_divisors n (fun d => d)]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdn hd0]
  field_simp

/-- A divisor is at most as abundant as the number: `d ∣ n ⇒ h(d) ≤ h(n)`
(the inequality behind Corollary 3.4, for any divisor). -/
theorem abund_le_of_dvd {d n : ℕ} (hn : 0 < n) (hd : d ∣ n) : abund d ≤ abund n := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  rw [abund_eq_sum_inv hd0, abund_eq_sum_inv hn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hn.ne' hd)
    fun _ _ _ => by positivity

/-! ### §6.2 Exact early exits -/

/-- **Lemma 6.2 (abundant k).** If `σ(k) ≥ 2k`, then `T(H, k)` is empty. -/
theorem lemma_6_2 (H : Hash) (k : ℕ) (hk : 0 < k) (hab : 2 * k ≤ σ 1 k) : T H k = ∅ := by
  ext ⟨N1, N2⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hp, -, hg⟩
  have hN2 : 0 < N2 := hp.1.trans hp.2.1
  have hle := abund_le_of_dvd hN2 (hg ▸ Nat.gcd_dvd_right N1 N2)
  have h2 : (2 : ℚ) ≤ abund k := by
    unfold abund
    rw [le_div_iff₀ (by exact_mod_cast hk)]
    exact_mod_cast hab
  linarith [(abundancy_identity hp).2.2.2]

/-- **Lemma 6.3 (dead configuration)**, in the form the code uses: for an amicable pair,
`σ(K2) < 2·K2` and `(σ(K1) − K1)(σ(K2) − K2) ≤ K1·K2`.  A configuration that fails either
test holds no pair. -/
theorem lemma_6_3 {N1 N2 : ℕ} (h : IsAmicablePair N1 N2) :
    let k := Nat.gcd N1 N2
    let K1 := k * boundPart N1 N2
    let K2 := k * boundPart N2 N1
    σ 1 K2 < 2 * K2 ∧ (σ 1 K1 - K1) * (σ 1 K2 - K2) ≤ K1 * K2 := by
  intro k K1 K2
  obtain ⟨e1, e2, -⟩ := decomposition h
  have hN1 : 0 < N1 := h.1
  have hN2 : 0 < N2 := h.1.trans h.2.1
  have hd1 : K1 ∣ N1 := ⟨_, e1⟩
  have hd2 : K2 ∣ N2 := ⟨_, e2⟩
  have hK1 : 0 < K1 := Nat.pos_of_dvd_of_pos hd1 hN1
  have hK2 : 0 < K2 := Nat.pos_of_dvd_of_pos hd2 hN2
  have l1 := abund_le_of_dvd hN1 hd1
  have l2 := abund_le_of_dvd hN2 hd2
  have g1 := one_le_abund hK1
  have g2 := one_le_abund hK2
  obtain ⟨hxy, -, -, hy2⟩ := abundancy_identity h
  have hK1q : (0 : ℚ) < K1 := by exact_mod_cast hK1
  have hK2q : (0 : ℚ) < K2 := by exact_mod_cast hK2
  have s1 : (σ 1 K1 : ℚ) = abund K1 * K1 := by unfold abund; field_simp
  have s2 : (σ 1 K2 : ℚ) = abund K2 * K2 := by unfold abund; field_simp
  constructor
  · have : (σ 1 K2 : ℚ) < 2 * K2 := by rw [s2]; nlinarith
    exact_mod_cast this
  · have p : (abund K1 - 1) * (abund K2 - 1) ≤ (abund N1 - 1) * (abund N2 - 1) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hq : ((σ 1 K1 - K1 : ℕ) : ℚ) * ((σ 1 K2 - K2 : ℕ) : ℚ) ≤ (K1 : ℚ) * K2 := by
      rw [Nat.cast_sub (sigma_one_ge_self K1), Nat.cast_sub (sigma_one_ge_self K2), s1, s2]
      have e : (abund K1 * K1 - K1) * (abund K2 * K2 - K2) =
          (abund K1 - 1) * (abund K2 - 1) * (K1 * K2) := by ring
      rw [e]
      have hKK : (0 : ℚ) < K1 * K2 := mul_pos hK1q hK2q
      nlinarith
    exact_mod_cast hq

/-! ### Lemma 8.3: the tests are monotone in `q` -/

namespace FP

theorem Hq_anti {q q' : ℚ} (hq : 0 < q) (hqq : q ≤ q') (e : ℕ) : Hq q' e ≤ Hq q e := by
  unfold Hq
  have hq' : 0 < q' := hq.trans_le hqq
  refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (one_div_pos.mpr hq').le ?_ i
  exact one_div_le_one_div_of_le hq hqq

/-- `X⁺` and `X⁻` do not increase when `q` grows. -/
theorem Xexact_anti {x0 q q' : ℚ} {e j : ℕ} {hs : Bool} {Ls : List ℚ} (hx0 : 0 ≤ x0)
    (hq : 0 < q) (hqq : q ≤ q') (hL : ∀ L ∈ Ls, 0 < L) :
    Xexact x0 q' e j hs Ls ≤ Xexact x0 q e j hs Ls := by
  have hq' : 0 < q' := hq.trans_le hqq
  unfold Xexact
  have hF : 0 ≤ (Ls.map fun L => 1 + 1 / L).prod := zero_le_one.trans (floatProd_ge_one hL)
  have hH : (if hs then Hq q' e else 1) ≤ (if hs then Hq q e else 1) := by
    cases hs
    · simp
    · simpa using Hq_anti hq hqq e
  have hH0 : 0 ≤ (if hs then Hq q' e else 1) := by
    cases hs
    · simp
    · simpa using zero_le_one.trans (one_le_Hq hq' e)
  have hp' : 0 < 1 / q' := one_div_pos.mpr hq'
  have hB : (1 + 1 / q') ^ j ≤ (1 + 1 / q) ^ j :=
    pow_le_pow_left₀ (by linarith) (by linarith [one_div_le_one_div_of_le hq hqq]) j
  have h1 : x0 * (if hs then Hq q' e else 1) ≤ x0 * (if hs then Hq q e else 1) :=
    mul_le_mul_of_nonneg_left hH hx0
  have h2 : x0 * (if hs then Hq q' e else 1) * (1 + 1 / q') ^ j ≤
      x0 * (if hs then Hq q e else 1) * (1 + 1 / q) ^ j :=
    mul_le_mul h1 hB (pow_nonneg (by linarith) j) (by
      have : 0 ≤ (if hs then Hq q e else 1) := by
        cases hs
        · simp
        · simpa using zero_le_one.trans (one_le_Hq hq e)
      positivity)
  exact mul_le_mul_of_nonneg_right h2 hF

/-- **Lemma 8.3 (monotone).** `U` is non-increasing and `L` non-decreasing in `q`: if `U`
holds at `q' ≥ q` it holds at `q`, and if `L` holds at `q` it holds at `q' ≥ q`. -/
theorem lemma_8_3 (x0 y0 q q' : ℚ) (e j0 j1 : ℕ) (side0 : Bool) (Lx Ly : List ℚ)
    (hx0 : 1 ≤ x0) (hy0 : 1 ≤ y0) (hq : 2 ≤ q) (hqq : q ≤ q') (_he : 1 ≤ e)
    (hL : ∀ L ∈ Lx ++ Ly, 0 < L) :
    (Utest (Xexact x0 q' e j0 side0 Lx) (Xexact y0 q' e j1 (!side0) Ly) →
      Utest (Xexact x0 q e j0 side0 Lx) (Xexact y0 q e j1 (!side0) Ly)) ∧
    (Ltest (Xexact x0 q e 0 side0 []) (Xexact y0 q e 0 (!side0) []) →
      Ltest (Xexact x0 q' e 0 side0 []) (Xexact y0 q' e 0 (!side0) [])) := by
  have hq0 : 0 < q := by linarith
  have hq0' : 0 < q' := by linarith
  have hLx : ∀ L ∈ Lx, 0 < L := fun L h => hL L (List.mem_append_left _ h)
  have hLy : ∀ L ∈ Ly, 0 < L := fun L h => hL L (List.mem_append_right _ h)
  have hnil : ∀ L ∈ ([] : List ℚ), 0 < L := by simp
  constructor
  · rintro ⟨u1, u2, u3⟩
    have ax := Xexact_anti (e := e) (j := j0) (hs := side0) (zero_le_one.trans hx0) hq0 hqq hLx
    have ay := Xexact_anti (e := e) (j := j1) (hs := !side0) (zero_le_one.trans hy0) hq0 hqq hLy
    have ox := one_le_Xexact (e := e) (j := j0) (hs := side0) hx0 hq0' hLx
    have oy := one_le_Xexact (e := e) (j := j1) (hs := !side0) hy0 hq0' hLy
    refine ⟨by linarith, by linarith, ?_⟩
    have := mul_le_mul (sub_le_sub_right ax 1) (sub_le_sub_right ay 1) (by linarith)
      (by linarith)
    linarith
  · rintro ⟨l1, l2⟩
    have ax := Xexact_anti (e := e) (j := 0) (hs := side0) (zero_le_one.trans hx0) hq0 hqq hnil
    have ay := Xexact_anti (e := e) (j := 0) (hs := !side0) (zero_le_one.trans hy0) hq0 hqq hnil
    have ox := one_le_Xexact (e := e) (j := 0) (hs := side0) hx0 hq0' hnil
    have oy := one_le_Xexact (e := e) (j := 0) (hs := !side0) hy0 hq0' hnil
    refine ⟨by linarith, ?_⟩
    have := mul_le_mul (sub_le_sub_right ax 1) (sub_le_sub_right ay 1) (by linarith)
      (by linarith)
    linarith

end FP

/-! ### Lemma 8.4: exact boundary search -/

/-- The bisection loop of §8.3: `while hi − lo > 1: m = ⌊(lo+hi)/2⌋; if P(m) lo = m else hi = m`. -/
def bisect (P : ℤ → Bool) (lo hi : ℤ) : ℤ :=
  if h : 1 < hi - lo then
    let m := (lo + hi) / 2
    if P m then bisect P m hi else bisect P lo m
  else lo
termination_by (hi - lo).toNat
decreasing_by all_goals omega

/-- The loop keeps "`P(lo)` true, `P(hi)` false" and ends with `hi = lo + 1`. -/
theorem bisect_spec (P : ℤ → Bool) :
    ∀ lo hi, lo < hi → P lo = true → P hi = false →
      P (bisect P lo hi) = true ∧ P (bisect P lo hi + 1) = false := by
  intro lo hi
  induction h : (hi - lo).toNat using Nat.strong_induction_on generalizing lo hi with
  | _ n ih =>
    intro hlt hlo hhi
    rw [bisect]
    by_cases h1 : 1 < hi - lo
    · simp only [h1, ↓reduceDIte]
      by_cases hm : P ((lo + hi) / 2) = true
      · simp only [hm, ite_true]
        exact ih _ (by omega) _ _ rfl (by omega) hm hhi
      · simp only [hm]
        exact ih _ (by omega) _ _ rfl (by omega) hlo (by simpa using hm)
    · simp only [h1, ↓reduceDIte]
      have : hi = lo + 1 := by omega
      subst this
      exact ⟨hlo, hhi⟩

/-- **Lemma 8.4 (exact boundary search).** For `P` monotone (true, then false) with `P(lo)`
true and `P(hi)` false, the loop ends with the largest value where `P` holds: `P x` holds
exactly for `x ≤ bisect P lo hi`. -/
theorem lemma_8_4 (P : ℤ → Bool) (hmono : ∀ x y, x ≤ y → P y = true → P x = true)
    (lo hi : ℤ) (hlt : lo < hi) (hlo : P lo = true) (hhi : P hi = false) :
    ∀ x, P x = true ↔ x ≤ bisect P lo hi := by
  obtain ⟨h1, h2⟩ := bisect_spec P lo hi hlt hlo hhi
  intro x
  constructor
  · intro hx
    by_contra hc
    have := hmono (bisect P lo hi + 1) x (by omega) hx
    rw [h2] at this
    exact Bool.false_ne_true this
  · intro hx
    exact hmono x _ hx h1

/-! ### §9.2 SameSide -/

/-- **SameSide.** With `σ(N1) = a`, `N1 = b` and the remaining part `W` of side 1, (E) is
`a = c·V = b + d·W`; so `d ∣ a − b`, `c ∣ a`, `W = (a − b)/d`, `V = a/c`. -/
theorem sameSide {a b c d V W : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) (h1 : a = c * V)
    (h2 : a = b + d * W) : W = (a - b) / d ∧ V = a / c := by
  constructor
  · rw [h2, add_sub_cancel_left, Int.mul_ediv_cancel_left _ hd]
  · rw [h1, Int.mul_ediv_cancel_left _ hc]

/-- **SameSide, `T = 2`, both exponents 1.** `W = q1·q2` and `V = σ(W) = (q1+1)(q2+1)` give
`q1 + q2 = V − W − 1`, so `q1, q2` are the roots of `z² − (V − W − 1)z + W`. -/
theorem sameSide_two {q1 q2 V W : ℤ} (hW : W = q1 * q2) (hV : V = (q1 + 1) * (q2 + 1)) :
    q1 + q2 = V - W - 1 ∧ ∀ z, z ^ 2 - (V - W - 1) * z + W = (z - q1) * (z - q2) := by
  subst hW hV
  exact ⟨by ring, fun z => by ring⟩

/-! ### §9.3 Mixed2 -/

/-- **Mixed2, `α = γ = 1`.** From `a(P+1) = c(Q+1) = bP + dQ`, with `D = ad + bc − ac`:
`D(P+1) = c(b+d)` and `D(Q+1) = a(b+d)`.  When `a, c > 0` and `b + d ≠ 0`, `D ≠ 0`, so
`P` and `Q` are determined. -/
theorem mixed2 {a b c d P Q : ℤ} (ha : a ≠ 0) (hc : c ≠ 0)
    (h1 : a * (P + 1) = c * (Q + 1)) (h2 : c * (Q + 1) = b * P + d * Q) :
    (a * d + b * c - a * c) * (P + 1) = c * (b + d) ∧
      (a * d + b * c - a * c) * (Q + 1) = a * (b + d) := by
  have e1 : a * ((a * d + b * c - a * c) * (P + 1) - c * (b + d)) = 0 := by
    linear_combination (a * d - a * c) * h1 - a * c * h2
  have e2 : c * ((a * d + b * c - a * c) * (Q + 1) - a * (b + d)) = 0 := by
    linear_combination (-(c * b)) * h1 - a * c * h2
  exact ⟨by linarith [(mul_eq_zero.mp e1).resolve_left ha],
    by linarith [(mul_eq_zero.mp e2).resolve_left hc]⟩

theorem mixed2_D_ne_zero {a b c d P : ℤ} (hc : c ≠ 0) (hbd : b + d ≠ 0)
    (h : (a * d + b * c - a * c) * (P + 1) = c * (b + d)) : a * d + b * c - a * c ≠ 0 := by
  intro h0
  rw [h0, zero_mul] at h
  exact mul_ne_zero hc hbd h.symm

/-! ### §9.5 Divisor3 -/

/-- `D(u) = δ1·u + δ0` and the expansion of `T`. -/
theorem divisor3_D (a b c d u : ℤ) :
    a * d * u + b * c * (u + 1) - a * c * (u + 1) =
      (a * d + b * c - a * c) * u + c * (b - a) ∧
    (a * d + b * c - a * c) * b - d * (c * (b - a)) = a * b * d + c * (b - a) * (b - d) :=
  ⟨by ring, by ring⟩

/-- **The divisor condition of Divisor3** (`u` on side 1).  Let `δ1 = ad + bc − ac`,
`δ0 = c(b − a)`, `T = δ1·b − d·δ0`.  If `D(u)·(Q+1) = a·(b + d·u)`, `g ≠ 0` divides `δ1` and
`δ0` (the code takes `g = gcd(δ1, δ0)`) and `g1 ≠ 0` divides `g` and `a` (the code takes
`g1 = gcd(g, a)`), then `D'(u) = (δ1/g)·u + δ0/g` divides `R* = (a/g1)·(T/g)`, a number that
does not depend on `u`. -/
theorem divisor3_dvd {a b c d u Q g g1 : ℤ}
    (hE : (a * d * u + b * c * (u + 1) - a * c * (u + 1)) * (Q + 1) = a * (b + d * u))
    (hg0 : g ≠ 0) (hgd1 : g ∣ a * d + b * c - a * c) (hgd0 : g ∣ c * (b - a))
    (hg10 : g1 ≠ 0) (hg1g : g1 ∣ g) (hg1a : g1 ∣ a) :
    ((a * d + b * c - a * c) / g * u + c * (b - a) / g) ∣
      (a / g1) * (((a * d + b * c - a * c) * b - d * (c * (b - a))) / g) := by
  obtain ⟨δ1', hδ1⟩ := hgd1
  obtain ⟨δ0', hδ0⟩ := hgd0
  obtain ⟨g', hg'⟩ := hg1g
  obtain ⟨a', ha'⟩ := hg1a
  have qT : ((a * d + b * c - a * c) * b - d * (c * (b - a))) = g * (δ1' * b - d * δ0') := by
    rw [hδ1, hδ0]; ring
  rw [qT, hδ1, hδ0, Int.mul_ediv_cancel_left _ hg0, Int.mul_ediv_cancel_left _ hg0,
    Int.mul_ediv_cancel_left _ hg0]
  have hDu : a * d * u + b * c * (u + 1) - a * c * (u + 1) = g * (δ1' * u + δ0') := by
    rw [(divisor3_D a b c d u).1, hδ1, hδ0]; ring
  rw [hDu, hg'] at hE
  rw [ha'] at hE ⊢
  rw [Int.mul_ediv_cancel_left _ hg10]
  have hE' : g' * (δ1' * u + δ0') * (Q + 1) = a' * (b + d * u) := by
    have : g1 * (g' * (δ1' * u + δ0') * (Q + 1)) = g1 * (a' * (b + d * u)) := by
      linear_combination hE
    exact mul_left_cancel₀ hg10 this
  have hdiv : (δ1' * u + δ0') ∣ a' * (b + d * u) := ⟨g' * (Q + 1), by linear_combination -hE'⟩
  -- δ1'(b + du) = d·D' + (δ1'b − dδ0')
  have key : a' * (δ1' * b - d * δ0') =
      δ1' * (a' * (b + d * u)) - (δ1' * u + δ0') * (a' * d) := by ring
  rw [key]
  exact dvd_sub (dvd_mul_of_dvd_right hdiv _) (dvd_mul_right _ _)

/-- **Lemma 9.2 (cap on u).** If `num = (W+1)·D` with `num > 0`, `u ≥ 0` and `W ≥ u + 1`, then
`D > 0` and `u·D − num < 0`. -/
theorem lemma_9_2 {u W D num : ℤ} (hu : 0 ≤ u) (hW : u + 1 ≤ W) (hnum : 0 < num)
    (hE : num = (W + 1) * D) : 0 < D ∧ u * D - num < 0 := by
  have hW1 : 0 < W + 1 := by omega
  have hD : 0 < D := by
    rcases lt_trichotomy D 0 with h | h | h
    · nlinarith
    · subst h; simp at hE; omega
    · exact h
  exact ⟨hD, by nlinarith⟩

end Amicable
