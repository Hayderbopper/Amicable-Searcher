/-
  Appendix B of exhaustive_search_proof.md: the floating-point pre-screen.

  Rounding model (assumption A5, made explicit):
  * an IEEE-754 binary64 operation with round-to-nearest returns `x·(1+η)` with `|η| ≤ u = 2⁻⁵³`
    when the result is in the normal range, and `x·(1+η) + ζ` with `|ζ| ≤ 2⁻¹⁰⁷⁵` in general
    (gradual underflow).  Only the divisions `t /= q` in `h_ld` can underflow (their quotients
    reach `q⁻ᵉ`, e.g. `2⁻⁴⁰⁰⁰⁰⁰`); every other intermediate value lies in `[2⁻⁴⁰¹, 2⁴⁰¹]`;
  * GMP's conversions (`mpz_get_d`, `mpz_get_d_2exp`) truncate: the result `d` of `x > 0`
    satisfies `x·(1-2u) ≤ d ≤ x`; `ldexp` by an in-range exponent is exact;
  * a fused multiply-add computes `a·b+c` with one rounding: this is the model with the
    product's `η = 0`, so every statement below (which quantifies over all `|η| ≤ u`) covers it.
    Every *use* of a computed value is allowed its own rounding history (`X`, `Xp`, `Xe`, …),
    which covers contraction of any `a·b ± c` the compiler chooses to fuse.

  All rounding errors are rational (a double and an exact rational give a rational `η`), so the
  model is over `ℚ` without loss of generality.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace Amicable.FP

/-- Unit roundoff of binary64 with round-to-nearest. -/
irreducible_def u : ℚ := 1 / 2 ^ 53

/-- Largest absolute error of a rounding in the subnormal range (half the smallest
subnormal). -/
irreducible_def lam : ℚ := 1 / 2 ^ 1075

theorem u_pos : 0 < u := by rw [u_def]; norm_num
theorem u_le : u ≤ 1 / 10 ^ 15 := by rw [u_def]; norm_num
theorem lam_pos : 0 < lam := by rw [lam_def]; positivity
theorem lam_le : lam * 2 ^ 1000 ≤ u := by
  rw [lam_def, u_def]
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- `c = 1 - u`. -/
def c : ℚ := 1 - u

theorem c_pos : 0 < c := by unfold c; linarith [u_le]
theorem c_le_one : c ≤ 1 := by unfold c; linarith [u_pos]
theorem cpow_pos (n : ℕ) : 0 < c ^ n := pow_pos c_pos n
theorem cpow_le_one (n : ℕ) : c ^ n ≤ 1 := pow_le_one₀ c_pos.le c_le_one
theorem cpow_anti {m n : ℕ} (h : m ≤ n) : c ^ n ≤ c ^ m :=
  pow_le_pow_of_le_one c_pos.le c_le_one h

/-- Bernoulli: `(1-u)^n ≥ 1 - n·u`. -/
theorem cpow_ge (n : ℕ) : 1 - n * u ≤ c ^ n := by
  have := one_add_mul_le_pow (a := -u) (by linarith [u_le]) n
  rw [← sub_eq_add_neg] at this
  unfold c
  linarith [show (n : ℚ) * -u = -(n * u) by ring]

theorem bound_of_abs {η : ℚ} (h : |η| ≤ u) : c ≤ 1 + η ∧ (1 + η) * c ≤ 1 := by
  rw [abs_le] at h
  unfold c
  have hu := u_pos
  have hu2 := u_le
  constructor
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show (0 : ℚ) ≤ 1 - u by linarith), sq_nonneg u]

/-! ### Approximation with `n` rounding factors -/

/-- `A n xh x`: the computed value `xh` equals the exact `x ≥ 0` up to `n` rounding factors:
`x·(1-u)ⁿ ≤ xh` and `xh·(1-u)ⁿ ≤ x`. -/
def A (n : ℕ) (xh x : ℚ) : Prop := x * c ^ n ≤ xh ∧ xh * c ^ n ≤ x

theorem A_exact {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : A n x x :=
  ⟨mul_le_of_le_one_right hx (cpow_le_one n), mul_le_of_le_one_right hx (cpow_le_one n)⟩

theorem A_nonneg {n : ℕ} {xh x : ℚ} (hx : 0 ≤ x) (h : A n xh x) : 0 ≤ xh :=
  le_trans (mul_nonneg hx (cpow_pos n).le) h.1

theorem A_pos {n : ℕ} {xh x : ℚ} (hx : 0 < x) (h : A n xh x) : 0 < xh :=
  lt_of_lt_of_le (mul_pos hx (cpow_pos n)) h.1

theorem A_mono {m n : ℕ} {xh x : ℚ} (hx : 0 ≤ x) (hmn : m ≤ n) (h : A m xh x) : A n xh x := by
  have hxh := A_nonneg hx h
  exact ⟨le_trans (mul_le_mul_of_nonneg_left (cpow_anti hmn) hx) h.1,
    le_trans (mul_le_mul_of_nonneg_left (cpow_anti hmn) hxh) h.2⟩

/-- One rounding of a computed value adds one factor. -/
theorem A_round {n : ℕ} {xh x η : ℚ} (hx : 0 ≤ x) (h : A n xh x) (hη : |η| ≤ u) :
    A (n + 1) (xh * (1 + η)) x := by
  have hxh := A_nonneg hx h
  obtain ⟨h1, h2⟩ := bound_of_abs hη
  have hc := c_pos
  constructor
  · calc x * c ^ (n + 1) = (x * c ^ n) * c := by ring
      _ ≤ xh * (1 + η) := mul_le_mul h.1 h1 hc.le hxh
  · calc xh * (1 + η) * c ^ (n + 1) = (xh * c ^ n) * ((1 + η) * c) := by ring
      _ ≤ x * 1 := mul_le_mul h.2 h2 (by nlinarith [cpow_pos n]) hx
      _ = x := mul_one x

theorem A_mul {m n : ℕ} {xh x yh y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h1 : A m xh x)
    (h2 : A n yh y) : A (m + n) (xh * yh) (x * y) := by
  have hxh := A_nonneg hx h1
  have hyh := A_nonneg hy h2
  constructor
  · calc x * y * c ^ (m + n) = (x * c ^ m) * (y * c ^ n) := by ring
      _ ≤ xh * yh := mul_le_mul h1.1 h2.1 (mul_nonneg hy (cpow_pos n).le) hxh
  · calc xh * yh * c ^ (m + n) = (xh * c ^ m) * (yh * c ^ n) := by ring
      _ ≤ x * y := mul_le_mul h1.2 h2.2 (mul_nonneg hyh (cpow_pos n).le) hx

theorem A_inv {n : ℕ} {xh x : ℚ} (hx : 0 < x) (h : A n xh x) : A n (1 / xh) (1 / x) := by
  have hxh := A_pos hx h
  have hc := cpow_pos n
  constructor
  · rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hx hxh, one_mul]
    linarith [h.2]
  · rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hxh hx, one_mul]
    linarith [h.1]

theorem A_add {n : ℕ} {xh x yh y : ℚ} (h1 : A n xh x) (h2 : A n yh y) :
    A n (xh + yh) (x + y) :=
  ⟨by linarith [h1.1, h2.1, add_mul x y (c ^ n)], by linarith [h1.2, h2.2, add_mul xh yh (c ^ n)]⟩

/-- A truncating conversion (`mpz_get_d`): `x(1-2u) ≤ d ≤ x` gives three factors. -/
theorem A_trunc {xh x : ℚ} (hx : 0 ≤ x) (h1 : x * (1 - 2 * u) ≤ xh) (h2 : xh ≤ x) :
    A 3 xh x := by
  have hc3 : c ^ 3 ≤ 1 - 2 * u := by
    have hu := u_pos
    have hu2 := u_le
    have e3 : c ^ 3 = 1 - 3 * u + 3 * u ^ 2 - u ^ 3 := by unfold c; ring
    rw [e3]
    nlinarith [mul_le_mul_of_nonneg_left hu2 hu.le, pow_pos hu 3]
  have hxh : 0 ≤ xh := le_trans (mul_nonneg hx (by linarith [u_le])) h1
  exact ⟨le_trans (mul_le_mul_of_nonneg_left hc3 hx) h1,
    le_trans (mul_le_of_le_one_right hxh (cpow_le_one 3)) h2⟩

/-- From `A n` to an absolute bound: `|xh - x| ≤ D·x` with `D = (1-u)⁻ⁿ - 1 ≤ 2nu`. -/
theorem A_abs {n : ℕ} {xh x : ℚ} (hx : 0 ≤ x) (h : A n xh x) (hn : n * u ≤ 1 / 2) :
    |xh - x| ≤ 2 * n * u * x := by
  have hb := cpow_ge n
  have hc := cpow_pos n
  have hc1 := cpow_le_one n
  have hxh := A_nonneg hx h
  rw [abs_le]
  constructor
  · nlinarith [h.1]
  · -- xh ≤ x / c^n ≤ x (1 + 2nu)
    have h1 : xh * (1 - n * u) ≤ xh * c ^ n := mul_le_mul_of_nonneg_left hb hxh
    have h2 : xh * c ^ n ≤ x := h.2
    have hnu : 0 ≤ (n : ℚ) * u := mul_nonneg (Nat.cast_nonneg n) u_pos.le
    have h3 : xh ≤ 2 * x := by nlinarith
    have h4 : (n * u) * xh ≤ (n * u) * (2 * x) := mul_le_mul_of_nonneg_left h3 hnu
    nlinarith

/-! ### Conversions and `1.0 + 1.0/d` -/

/-- `ratio_d(a, b)`: two truncating conversions, one division (and an exact `ldexp`). -/
theorem ratio_d_A {a b da db η : ℚ} (ha : 0 ≤ a) (hb : 0 < b) (hda : A 3 da a) (hdb : A 3 db b)
    (hη : |η| ≤ u) : A 7 (da / db * (1 + η)) (a / b) := by
  have h := A_mul ha (by positivity) hda (A_inv hb hdb)
  rw [mul_one_div, mul_one_div] at h
  exact A_round (div_nonneg ha hb.le) h hη

/-- `1.0 + 1.0 / d` for a computed `d` (three factors from `d`, one from the division, one
from the addition). -/
def onePlusInv (d η1 η2 : ℚ) : ℚ := (1 + 1 / d * (1 + η1)) * (1 + η2)

theorem onePlusInv_A {x d η1 η2 : ℚ} (hx : 0 < x) (hd : A 3 d x) (h1 : |η1| ≤ u)
    (h2 : |η2| ≤ u) : A 5 (onePlusInv d η1 η2) (1 + 1 / x) := by
  have hi := A_round (by positivity) (A_inv hx hd) h1
  have hs := A_add (A_exact zero_le_one 4) hi
  exact A_round (by positivity) hs h2

/-! ### Products computed one factor at a time (`ipow_ld`, the floating factors) -/

/-- `r = acc; for each (f, η): r *= f` (each product rounded). -/
def prodL : ℚ → List (ℚ × ℚ) → ℚ
  | acc, [] => acc
  | acc, (f, η) :: rest => prodL (acc * f * (1 + η)) rest

theorem prodL_A {n : ℕ} :
    ∀ {l : List (ℚ × ℚ)} {F : List ℚ},
      List.Forall₂ (fun p Fi => A n p.1 Fi ∧ |p.2| ≤ u ∧ 0 ≤ Fi) l F →
      ∀ {m : ℕ} {acch acc : ℚ}, 0 ≤ acc → A m acch acc →
        A (m + (n + 1) * l.length) (prodL acch l) (acc * F.prod) := by
  intro l F hl
  induction hl with
  | nil =>
    intro m acch acc _ h
    simpa [prodL] using h
  | @cons p Fi l F hp _ ih =>
    intro m acch acc hacc h
    obtain ⟨f, η⟩ := p
    obtain ⟨hA, hη, hF⟩ := hp
    have h1 := A_round (mul_nonneg hacc hF) (A_mul hacc hF h hA) hη
    have h2 := ih (mul_nonneg hacc hF) h1
    have hidx : m + (n + 1) * ((f, η) :: l).length = m + n + 1 + (n + 1) * l.length := by
      simp only [List.length_cons]; ring
    rw [hidx, List.prod_cons, ← mul_assoc]
    exact h2

theorem prodL_one_A {n : ℕ} {l : List (ℚ × ℚ)} {F : List ℚ}
    (hl : List.Forall₂ (fun p Fi => A n p.1 Fi ∧ |p.2| ≤ u ∧ 0 ≤ Fi) l F) :
    A ((n + 1) * l.length) (prodL 1 l) F.prod := by
  have := prodL_A hl zero_le_one (A_exact zero_le_one 0)
  simpa using this

/-! ### `h_ld(q, e)`: `s = 1; t = 1; repeat e times { t /= q; s += t; }` -/

/-- The terms `t`; the division may underflow (absolute error `ζ`). -/
def hT (qh : ℚ) (η ζ : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | i + 1 => hT qh η ζ i / qh * (1 + η i) + ζ i

/-- The partial sums `s`. -/
def hS (qh : ℚ) (η ζ η' : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | i + 1 => (hS qh η ζ η' i + hT qh η ζ (i + 1)) * (1 + η' i)

/-- `H_e(q) = 1 + 1/q + … + 1/qᵉ`. -/
def Hq (q : ℚ) (e : ℕ) : ℚ := ∑ i ∈ range (e + 1), (1 / q) ^ i

theorem Hq_succ (q : ℚ) (i : ℕ) : Hq q (i + 1) = Hq q i + (1 / q) ^ (i + 1) := by
  unfold Hq; rw [Finset.sum_range_succ]

theorem one_le_Hq {q : ℚ} (hq : 0 < q) (e : ℕ) : 1 ≤ Hq q e := by
  unfold Hq
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have : 0 ≤ ∑ i ∈ range e, (1 / q) ^ (i + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith

theorem cpow_split4 (i : ℕ) : c ^ (4 * (i + 1)) = c ^ (4 * i) * c ^ 4 := by
  rw [show 4 * (i + 1) = 4 * i + 4 by ring, pow_add]

/-- Bounds on the terms `t_i` of `h_ld`: `rⁱc⁴ⁱ - 3λ ≤ t_i` and `t_i c⁴ⁱ ≤ rⁱ + 3λc⁴ⁱ`. -/
theorem hT_bounds {q qh : ℚ} {η ζ : ℕ → ℚ} (hq : 2 ≤ q) (hqh : A 3 qh q)
    (hη : ∀ i, |η i| ≤ u) (hζ : ∀ i, |ζ i| ≤ lam) (hTnn : ∀ i, 0 ≤ hT qh η ζ i) :
    ∀ i, (1 / q) ^ i * c ^ (4 * i) - 3 * lam ≤ hT qh η ζ i ∧
      hT qh η ζ i * c ^ (4 * i) ≤ (1 / q) ^ i + 3 * lam * c ^ (4 * i) := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < 1 / q := by positivity
  have hr2 : 1 / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
  have hrh := A_inv hq0 hqh
  have hrh0 : 0 < 1 / qh := A_pos hr0 hrh
  have hc := c_pos
  have hc4 : 3 / 4 ≤ c ^ 4 := by
    have := cpow_ge 4; have := u_le; push_cast at *; linarith
  have hc4le := cpow_le_one 4
  have hlam := lam_pos
  intro i
  induction i with
  | zero =>
    simp only [hT, pow_zero, mul_zero, mul_one]
    constructor <;> linarith
  | succ i ih =>
    set r := 1 / q with hr
    set t := hT qh η ζ i with ht_def
    have ht : 0 ≤ t := hTnn i
    obtain ⟨hb1, hb2⟩ := bound_of_abs (hη i)
    have hz := abs_le.mp (hζ i)
    have hstep : hT qh η ζ (i + 1) = t * (1 / qh) * (1 + η i) + ζ i := by
      simp only [hT, ht_def]; ring
    have hci := cpow_pos (4 * i)
    rw [hstep, cpow_split4, pow_succ]
    constructor
    · -- lower bound
      have l1 : t * (r * c ^ 3) * c ≤ t * (1 / qh) * (1 + η i) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrh.1 ht) hb1 hc.le
          (mul_nonneg ht hrh0.le)
      have l2 : (r ^ i * c ^ (4 * i) - 3 * lam) * (r * c ^ 4) ≤ t * (r * c ^ 4) :=
        mul_le_mul_of_nonneg_right ih.1 (by positivity)
      have l3 : r * c ^ 4 ≤ 1 / 2 := by
        calc r * c ^ 4 ≤ (1 / 2) * 1 := mul_le_mul hr2 hc4le (cpow_pos 4).le (by norm_num)
          _ = 1 / 2 := by ring
      have l4 : 3 * lam * (r * c ^ 4) ≤ 3 * lam * (1 / 2) :=
        mul_le_mul_of_nonneg_left l3 (by linarith)
      have e1 : t * (r * c ^ 3) * c = t * (r * c ^ 4) := by ring
      have e2 : (r ^ i * c ^ (4 * i) - 3 * lam) * (r * c ^ 4) =
          r ^ i * r * (c ^ (4 * i) * c ^ 4) - 3 * lam * (r * c ^ 4) := by ring
      linarith
    · -- upper bound
      have u1 : (t * (1 / qh) * (1 + η i)) * (c ^ (4 * i) * c ^ 4) ≤ t * c ^ (4 * i) * r := by
        have e : (t * (1 / qh) * (1 + η i)) * (c ^ (4 * i) * c ^ 4) =
            (t * c ^ (4 * i)) * ((1 / qh) * c ^ 3) * ((1 + η i) * c) := by ring
        rw [e]
        have hp : 0 ≤ t * c ^ (4 * i) := mul_nonneg ht hci.le
        calc (t * c ^ (4 * i)) * ((1 / qh) * c ^ 3) * ((1 + η i) * c)
            ≤ (t * c ^ (4 * i)) * r * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hrh.2 hp) hb2
                (mul_nonneg (by linarith) hc.le) (mul_nonneg hp hr0.le)
          _ = t * c ^ (4 * i) * r := mul_one _
      have u2 : t * c ^ (4 * i) * r ≤ (r ^ i + 3 * lam * c ^ (4 * i)) * r :=
        mul_le_mul_of_nonneg_right ih.2 hr0.le
      have u3 : ζ i * (c ^ (4 * i) * c ^ 4) ≤ lam * (c ^ (4 * i) * c ^ 4) :=
        mul_le_mul_of_nonneg_right hz.2 (mul_nonneg hci.le (cpow_pos 4).le)
      have u4 : lam * c ^ (4 * i) * (3 * r) ≤ lam * c ^ (4 * i) * (2 * c ^ 4) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hlam.le hci.le)
      have e1 : (t * (1 / qh) * (1 + η i) + ζ i) * (c ^ (4 * i) * c ^ 4) =
          (t * (1 / qh) * (1 + η i)) * (c ^ (4 * i) * c ^ 4) + ζ i * (c ^ (4 * i) * c ^ 4) := by
        ring
      rw [e1]
      nlinarith

/-- Error bounds for `h_ld`.  Hypotheses: `q ≥ 2`, `q̂` within three factors of `q`, every
rounding error bounded, rounding preserves the sign of a nonnegative quotient (`hTnn`),
and `e ≤ 10⁹` (the program accepts exponents up to 1000).  Conclusion: `5e + 1` factors. -/
theorem hS_A {q qh : ℚ} {η ζ η' : ℕ → ℚ} {e : ℕ} (hq : 2 ≤ q) (hqh : A 3 qh q)
    (hη : ∀ i, |η i| ≤ u) (hζ : ∀ i, |ζ i| ≤ lam) (hη' : ∀ i, |η' i| ≤ u)
    (hTnn : ∀ i, 0 ≤ hT qh η ζ i) (he : e ≤ 10 ^ 9) :
    A (5 * e + 1) (hS qh η ζ η' e) (Hq q e) := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < 1 / q := by positivity
  have hc := c_pos
  have hc1 := c_le_one
  have hlam := lam_pos
  have hTb := hT_bounds hq hqh hη hζ hTnn
  -- the sums: H_i c^(5i) - 3 i λ ≤ s_i,  s_i c^(5i) ≤ H_i + 3 i λ,  0 ≤ s_i
  have hS_bd : ∀ i, Hq q i * c ^ (5 * i) - 3 * i * lam ≤ hS qh η ζ η' i ∧
      hS qh η ζ η' i * c ^ (5 * i) ≤ Hq q i + 3 * i * lam ∧ 0 ≤ hS qh η ζ η' i := by
    intro i
    induction i with
    | zero => simp only [hS, Hq, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero,
        mul_zero, mul_one, Nat.cast_zero, zero_mul, sub_zero, add_zero]; norm_num
    | succ i ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      set S := hS qh η ζ η' i with hS_def
      set T := hT qh η ζ (i + 1) with hT_def
      set H := Hq q i with hH_def
      have hT0 : 0 ≤ T := hTnn (i + 1)
      obtain ⟨ht1, ht2⟩ := hTb (i + 1)
      obtain ⟨hb1, hb2⟩ := bound_of_abs (hη' i)
      have hST : 0 ≤ S + T := add_nonneg ih3 hT0
      have hstep : hS qh η ζ η' (i + 1) = (S + T) * (1 + η' i) := rfl
      have hH1 : 1 ≤ H := one_le_Hq hq0 i
      have p1 : c ^ (5 * (i + 1)) ≤ c ^ (5 * i + 1) := cpow_anti (by omega)
      have p2 : c ^ (5 * (i + 1)) ≤ c ^ (4 * (i + 1) + 1) := cpow_anti (by omega)
      have p3 : c ^ (5 * i + 4) ≤ c ^ (5 * i) := cpow_anti (by omega)
      have p4 : c ^ (5 * i + 4) ≤ c ^ (4 * (i + 1)) := cpow_anti (by omega)
      have e1 : c ^ (5 * i + 1) = c ^ (5 * i) * c := pow_succ c (5 * i)
      have e2 : c ^ (4 * (i + 1) + 1) = c ^ (4 * (i + 1)) * c := pow_succ c _
      have e3 : c ^ (5 * (i + 1)) = c ^ (5 * i + 4) * c := by
        rw [← pow_succ, show 5 * i + 4 + 1 = 5 * (i + 1) by ring]
      have hrp := pow_pos hr0 (i + 1)
      have hc5 := cpow_pos (5 * i)
      have hc54 := cpow_pos (5 * i + 4)
      have hc4 := cpow_pos (4 * (i + 1))
      rw [Hq_succ, ← hH_def, hstep]
      push_cast
      refine ⟨?_, ?_, mul_nonneg hST (by linarith)⟩
      · -- lower: (S + T)(1+η') ≥ (S + T) c
        have l1 : (S + T) * c ≤ (S + T) * (1 + η' i) := mul_le_mul_of_nonneg_left hb1 hST
        have l2 : (H * c ^ (5 * i) - 3 * i * lam) * c ≤ S * c :=
          mul_le_mul_of_nonneg_right ih1 hc.le
        have l3 : ((1 / q) ^ (i + 1) * c ^ (4 * (i + 1)) - 3 * lam) * c ≤ T * c :=
          mul_le_mul_of_nonneg_right ht1 hc.le
        have l4 : H * c ^ (5 * (i + 1)) ≤ H * (c ^ (5 * i) * c) := by
          rw [← e1]; exact mul_le_mul_of_nonneg_left p1 (by linarith)
        have l5 : (1 / q) ^ (i + 1) * c ^ (5 * (i + 1)) ≤
            (1 / q) ^ (i + 1) * (c ^ (4 * (i + 1)) * c) := by
          rw [← e2]; exact mul_le_mul_of_nonneg_left p2 hrp.le
        have l6 : (3 * (i : ℚ) * lam + 3 * lam) * c ≤ 3 * (i : ℚ) * lam + 3 * lam :=
          mul_le_of_le_one_right (by positivity) hc1
        nlinarith
      · -- upper: (S + T)(1+η') c^(5(i+1)) ≤ (S + T) c^(5i+4)
        have u1 : (S + T) * (1 + η' i) * c ^ (5 * (i + 1)) ≤ (S + T) * c ^ (5 * i + 4) := by
          rw [e3]
          have e : (S + T) * (1 + η' i) * (c ^ (5 * i + 4) * c) =
              ((S + T) * c ^ (5 * i + 4)) * ((1 + η' i) * c) := by ring
          rw [e]
          exact mul_le_of_le_one_right (mul_nonneg hST hc54.le) hb2
        have u2 : S * c ^ (5 * i + 4) ≤ S * c ^ (5 * i) := mul_le_mul_of_nonneg_left p3 ih3
        have u3 : T * c ^ (5 * i + 4) ≤ T * c ^ (4 * (i + 1)) := mul_le_mul_of_nonneg_left p4 hT0
        have u4 : 3 * lam * c ^ (4 * (i + 1)) ≤ 3 * lam :=
          mul_le_of_le_one_right (by linarith) (cpow_le_one _)
        nlinarith
  -- conclusion
  obtain ⟨s1, s2, s3⟩ := hS_bd e
  set S := hS qh η ζ η' e
  set H := Hq q e
  have hH : 1 ≤ H := one_le_Hq hq0 e
  have hu := u_pos
  have hcu : c = 1 - u := rfl
  have he' : (e : ℚ) ≤ 10 ^ 9 := by exact_mod_cast he
  have hc5e : 1 / 2 ≤ c ^ (5 * e) := by
    have h1 := cpow_ge (5 * e)
    have h2 := u_le
    push_cast at h1
    have h3 : 5 * (e : ℚ) * u ≤ 5 * 10 ^ 9 * (1 / 10 ^ 15) :=
      mul_le_mul (by linarith) h2 hu.le (by norm_num)
    linarith
  have hlam3 : 3 * (e : ℚ) * lam ≤ u / 2 := by
    have hl := lam_le
    have h2 : (2 : ℚ) ^ 40 ≤ 2 ^ 1000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h3 : (6 * 10 ^ 9 : ℚ) ≤ 2 ^ 40 := by norm_num
    have h4 : 3 * (e : ℚ) * lam ≤ 3 * 10 ^ 9 * lam :=
      mul_le_mul_of_nonneg_right (by linarith) hlam.le
    have h5 : 6 * 10 ^ 9 * lam ≤ lam * 2 ^ 1000 := by
      rw [mul_comm lam]
      exact mul_le_mul_of_nonneg_right (h3.trans h2) hlam.le
    calc 3 * (e : ℚ) * lam ≤ 3 * 10 ^ 9 * lam := h4
      _ = (6 * 10 ^ 9 * lam) / 2 := by ring
      _ ≤ (lam * 2 ^ 1000) / 2 := by gcongr
      _ ≤ u / 2 := by gcongr
  have hc5 := cpow_pos (5 * e)
  constructor
  · -- H c^(5e+1) ≤ S
    have e1 : H * c ^ (5 * e + 1) = H * c ^ (5 * e) - H * c ^ (5 * e) * u := by
      rw [pow_succ, hcu]; ring
    have h1 : 1 / 2 * u ≤ H * c ^ (5 * e) * u :=
      mul_le_mul_of_nonneg_right (by nlinarith) hu.le
    rw [e1]
    linarith
  · -- S c^(5e+1) ≤ H
    have e1 : S * c ^ (5 * e + 1) = S * c ^ (5 * e) * c := by rw [pow_succ, mul_assoc]
    have h1 : S * c ^ (5 * e) * c ≤ (H + 3 * e * lam) * c :=
      mul_le_mul_of_nonneg_right s2 hc.le
    have h2 : (H + 3 * e * lam) * c = H + 3 * e * lam - H * u - 3 * e * lam * u := by
      rw [hcu]; ring
    have h3 : u ≤ H * u := le_mul_of_one_le_left hu.le hH
    have h4 : 0 ≤ 3 * (e : ℚ) * lam * u := by positivity
    rw [e1]
    linarith

/-! ### The values `X`, `Y` the filters compute -/

/-- `ipow_ld(b, k)`: `r = 1; repeat k times r *= b` (each product rounded). -/
def ipowC (Bh : ℚ) (ηp : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => ipowC Bh ηp k * Bh * (1 + ηp k)

theorem ipowC_A {Bh B : ℚ} {ηp : ℕ → ℚ} (hB : 0 ≤ B) (hBh : A 5 Bh B)
    (hηp : ∀ k, |ηp k| ≤ u) : ∀ k, A (6 * k) (ipowC Bh ηp k) (B ^ k)
  | 0 => by simpa [ipowC] using A_exact zero_le_one 0
  | k + 1 => by
    have := A_round (by positivity)
      (A_mul (pow_nonneg hB k) hB (ipowC_A hB hBh hηp k) hBh) (hηp k)
    rw [show 6 * (k + 1) = 6 * k + 5 + 1 by ring, pow_succ]
    exact this

/-- The exact `X⁺` (§8.2) `= x0 · [H_e(q)] · ((q+1)/q)^j · ∏ (L+1)/L`; with `j = 0` and no
floating primes it is `X⁻`. -/
def Xexact (x0 q : ℚ) (e j : ℕ) (hs : Bool) (Ls : List ℚ) : ℚ :=
  x0 * (if hs then Hq q e else 1) * (1 + 1 / q) ^ j * (Ls.map fun L => 1 + 1 / L).prod

/-- One evaluation in double precision of
`X = x0l * (side == s ? h_ld(ql, e) : 1.0) * ipow_ld(1.0 + 1.0/ql, j) * F` (`upper_filter`),
`F` the product of `1.0 + 1.0/fl_d[i]` over this side's floating primes, with all its rounding
errors (`x0l = ratio_d(sx, px)`, `ql` the conversion of `q`, `d` that of `L`). -/
def IsXEval (x0 q : ℚ) (e j : ℕ) (hs : Bool) (Ls : List ℚ) (Xh : ℚ) : Prop :=
  ∃ (x0l ql : ℚ) (η ζ η' ηp : ℕ → ℚ) (ηb1 ηb2 : ℚ) (lF : List (ℚ × ℚ)) (η1 η2 η3 : ℚ),
    A 7 x0l x0 ∧ A 3 ql q ∧
    (∀ i, |η i| ≤ u) ∧ (∀ i, |ζ i| ≤ lam) ∧ (∀ i, |η' i| ≤ u) ∧ (∀ i, 0 ≤ hT ql η ζ i) ∧
    |ηb1| ≤ u ∧ |ηb2| ≤ u ∧ (∀ k, |ηp k| ≤ u) ∧
    List.Forall₂ (fun p L => ∃ d δ1 δ2, A 3 d L ∧ |δ1| ≤ u ∧ |δ2| ≤ u ∧
      p.1 = onePlusInv d δ1 δ2 ∧ |p.2| ≤ u) lF Ls ∧
    |η1| ≤ u ∧ |η2| ≤ u ∧ |η3| ≤ u ∧
    Xh = x0l * (if hs then hS ql η ζ η' e else 1) * (1 + η1) *
      ipowC (onePlusInv ql ηb1 ηb2) ηp j * (1 + η2) * prodL 1 lF * (1 + η3)

/-- `lower_filter`'s `X = x0l * (side == s ? h : 1.0)` is the instance `j = 0`, no floating
primes, `η2 = η3 = 0`. -/
theorem isXEval_lower {x0 q x0l ql η1 : ℚ} {e : ℕ} {hs : Bool} {η ζ η' : ℕ → ℚ}
    (hx0l : A 7 x0l x0) (hql : A 3 ql q) (hη : ∀ i, |η i| ≤ u) (hζ : ∀ i, |ζ i| ≤ lam)
    (hη' : ∀ i, |η' i| ≤ u) (hTnn : ∀ i, 0 ≤ hT ql η ζ i) (h1 : |η1| ≤ u) :
    IsXEval x0 q e 0 hs [] (x0l * (if hs then hS ql η ζ η' e else 1) * (1 + η1)) := by
  have hu := u_pos
  refine ⟨x0l, ql, η, ζ, η', fun _ => 0, 0, 0, [], η1, 0, 0, hx0l, hql, hη, hζ, hη', hTnn,
    by simp; linarith, by simp; linarith, fun _ => by simp; linarith, List.Forall₂.nil, h1,
    by simp; linarith, by simp; linarith, ?_⟩
  simp [ipowC, prodL]

theorem forall2_floats {lF : List (ℚ × ℚ)} {Ls : List ℚ}
    (hF : List.Forall₂ (fun p L => ∃ d δ1 δ2, A 3 d L ∧ |δ1| ≤ u ∧ |δ2| ≤ u ∧
      p.1 = onePlusInv d δ1 δ2 ∧ |p.2| ≤ u) lF Ls) (hL : ∀ L ∈ Ls, 0 < L) :
    List.Forall₂ (fun p Fi => A 5 p.1 Fi ∧ |p.2| ≤ u ∧ 0 ≤ Fi) lF
      (Ls.map fun L => 1 + 1 / L) := by
  induction hF with
  | nil => exact List.Forall₂.nil
  | @cons p L lF Ls hp _ ih =>
    obtain ⟨d, δ1, δ2, hd, h1, h2, hp1, hp2⟩ := hp
    have hL0 : 0 < L := hL L (List.mem_cons_self ..)
    refine List.Forall₂.cons ⟨?_, hp2, by positivity⟩
      (ih fun L' h' => hL L' (List.mem_cons_of_mem _ h'))
    rw [hp1]; exact onePlusInv_A hL0 hd h1 h2

theorem floatProd_ge_one {Ls : List ℚ} (hL : ∀ L ∈ Ls, 0 < L) :
    1 ≤ (Ls.map fun L => 1 + 1 / L).prod := by
  induction Ls with
  | nil => simp
  | cons L Ls ih =>
    simp only [List.map_cons, List.prod_cons]
    have hL0 : 0 < L := hL L (List.mem_cons_self ..)
    have h1 : 1 ≤ 1 + 1 / L := by
      have := one_div_pos.mpr hL0
      linarith
    exact one_le_mul_of_one_le_of_one_le h1 (ih fun L' h => hL L' (List.mem_cons_of_mem _ h))

theorem Xexact_nonneg {x0 q : ℚ} {e j : ℕ} {hs : Bool} {Ls : List ℚ} (hx0 : 0 ≤ x0)
    (hq : 0 < q) (hL : ∀ L ∈ Ls, 0 < L) : 0 ≤ Xexact x0 q e j hs Ls := by
  unfold Xexact
  have hH : 0 ≤ (if hs then Hq q e else 1) := by
    cases hs
    · simp
    · simpa using (zero_le_one.trans (one_le_Hq hq e))
  have hF : 0 ≤ (Ls.map fun L => 1 + 1 / L).prod := zero_le_one.trans (floatProd_ge_one hL)
  have : 0 ≤ (1 + 1 / q) ^ j := by positivity
  positivity

theorem one_le_Xexact {x0 q : ℚ} {e j : ℕ} {hs : Bool} {Ls : List ℚ} (hx0 : 1 ≤ x0)
    (hq : 0 < q) (hL : ∀ L ∈ Ls, 0 < L) : 1 ≤ Xexact x0 q e j hs Ls := by
  unfold Xexact
  have hH : 1 ≤ (if hs then Hq q e else 1) := by
    cases hs
    · simp
    · simpa using one_le_Hq hq e
  have hq' : 0 < 1 / q := by positivity
  have hB : 1 ≤ (1 + 1 / q) ^ j := one_le_pow₀ (by linarith)
  have hF : 1 ≤ (Ls.map fun L => 1 + 1 / L).prod := floatProd_ge_one hL
  have h1 : 1 ≤ x0 * (if hs then Hq q e else 1) := one_le_mul_of_one_le_of_one_le hx0 hH
  have h2 := one_le_mul_of_one_le_of_one_le h1 hB
  exact one_le_mul_of_one_le_of_one_le h2 hF

/-- **Lemma B.1 (error of `X`).** An evaluation of `X` is within
`N = 5e + 6j + 6f + 11` rounding factors of the exact `X⁺`. -/
theorem IsXEval.approx {x0 q : ℚ} {e j : ℕ} {hs : Bool} {Ls : List ℚ} {Xh : ℚ}
    (hx0 : 0 ≤ x0) (hq : 2 ≤ q) (hL : ∀ L ∈ Ls, 0 < L) (he : e ≤ 10 ^ 9)
    (h : IsXEval x0 q e j hs Ls Xh) :
    A (5 * e + 6 * j + 6 * Ls.length + 11) Xh (Xexact x0 q e j hs Ls) := by
  obtain ⟨x0l, ql, η, ζ, η', ηp, ηb1, ηb2, lF, η1, η2, η3, hx0l, hql, hη, hζ, hη', hTnn,
    hb1, hb2, hηp, hF, h1, h2, h3, rfl⟩ := h
  have hq0 : 0 < q := by linarith
  have hHnn : 0 ≤ (if hs then Hq q e else 1) := by
    cases hs
    · simp
    · simpa using (zero_le_one.trans (one_le_Hq hq0 e))
  have hH : A (5 * e + 1) (if hs then hS ql η ζ η' e else 1) (if hs then Hq q e else 1) := by
    cases hs
    · simpa using A_exact zero_le_one (5 * e + 1)
    · simpa using hS_A hq hql hη hζ hη' hTnn he
  have hBnn : 0 ≤ 1 + 1 / q := by positivity
  have t1 := A_round (mul_nonneg hx0 hHnn) (A_mul hx0 hHnn hx0l hH) h1
  have hP := ipowC_A hBnn (onePlusInv_A hq0 hql hb1 hb2) hηp j
  have t2 := A_round (mul_nonneg (mul_nonneg hx0 hHnn) (pow_nonneg hBnn j))
    (A_mul (mul_nonneg hx0 hHnn) (pow_nonneg hBnn j) t1 hP) h2
  have hF' := forall2_floats hF hL
  have hlen : lF.length = Ls.length := hF.length_eq
  have hFnn : 0 ≤ (Ls.map fun L => 1 + 1 / L).prod := zero_le_one.trans (floatProd_ge_one hL)
  have t3 := A_round (mul_nonneg (mul_nonneg (mul_nonneg hx0 hHnn) (pow_nonneg hBnn j)) hFnn)
    (A_mul (mul_nonneg (mul_nonneg hx0 hHnn) (pow_nonneg hBnn j)) hFnn t2 (prodL_one_A hF')) h3
  rw [hlen] at t3
  have hidx : 7 + (5 * e + 1) + 1 + 6 * j + 1 + (5 + 1) * Ls.length + 1 =
      5 * e + 6 * j + 6 * Ls.length + 11 := by ring
  rw [hidx] at t3
  exact t3

/-! ### The decisions -/

/-- §8.2: the upper test `U` and the lower test `L` on exact values. -/
def Utest (X Y : ℚ) : Prop := 2 < X ∧ 1 < Y ∧ 1 < (X - 1) * (Y - 1)
def Ltest (X Y : ℚ) : Prop := Y < 2 ∧ (X - 1) * (Y - 1) < 1

theorem abs_le_of_A {N : ℕ} {xh x : ℚ} (hx : 0 ≤ x) (h : A N xh x) (hN : N * u ≤ 1 / 2) :
    x * (1 - 2 * N * u) ≤ xh ∧ xh ≤ x * (1 + 2 * N * u) := by
  have := abs_le.mp (A_abs hx h hN)
  constructor <;> nlinarith

/-- A computed value below `2(1-ε)` (threshold computed as `2.0*(1.0-eps)`) means the exact one
is below 2. -/
theorem below_two {Xh Xt D ε η : ℚ} (hlo : Xt * (1 - D) ≤ Xh) (hD : 0 ≤ D) (hD1 : D ≤ 1)
    (hη : |η| ≤ u) (hε : D + u ≤ ε) (hε1 : ε ≤ 1) (h : Xh < 2 * ((1 - ε) * (1 + η))) :
    Xt < 2 := by
  have hη' := (abs_le.mp hη).2
  have hu := u_pos
  by_contra hX
  push Not at hX
  have h1 : 2 * (1 - D) ≤ Xt * (1 - D) := mul_le_mul_of_nonneg_right hX (by linarith)
  have h2 : (1 - ε) * (1 + η) ≤ (1 - ε) * (1 + u) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : (1 - ε) * (1 + u) = 1 + u - ε - ε * u := by ring
  have h4 : 0 ≤ ε * u := mul_nonneg (by linarith) hu.le
  linarith

/-- A computed value above `2(1+ε)` means the exact one is above 2. -/
theorem above_two {Xh Xt D ε η : ℚ} (hhi : Xh ≤ Xt * (1 + D)) (hD : 0 ≤ D)
    (hη : |η| ≤ u) (hε : D + 2 * u ≤ ε) (hε1 : ε ≤ 1) (h : 2 * ((1 + ε) * (1 + η)) < Xh) :
    2 < Xt := by
  have hη' := (abs_le.mp hη).1
  have hu := u_pos
  by_contra hX
  push Not at hX
  have h1 : Xt * (1 + D) ≤ 2 * (1 + D) := mul_le_mul_of_nonneg_right hX (by linarith)
  have h2 : (1 + ε) * (1 - u) ≤ (1 + ε) * (1 + η) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : (1 + ε) * (1 - u) = 1 + ε - u - ε * u := by ring
  have h4 : ε * u ≤ u := mul_le_of_le_one_left hu.le hε1
  linarith

/-- The error of `prod = (X - 1.0) * (Y - 1.0)`. -/
theorem prod_err {Xt Yt Xp Yp D η1 η2 η3 : ℚ} (hX1 : 1 ≤ Xt) (hY1 : 1 ≤ Yt)
    (hXp : |Xp - Xt| ≤ D * Xt) (hYp : |Yp - Yt| ≤ D * Yt) (hD : 0 ≤ D)
    (h1 : |η1| ≤ u) (h2 : |η2| ≤ u) (h3 : |η3| ≤ u) :
    |(Xp - 1) * (1 + η1) * ((Yp - 1) * (1 + η2)) * (1 + η3) - (Xt - 1) * (Yt - 1)| ≤
      (D * (2 + D) + 4 * u * (1 + D) ^ 2) * (Xt * Yt) := by
  set a := Xt - 1
  set b := Yt - 1
  set ah := Xp - 1
  set bh := Yp - 1
  have ha0 : 0 ≤ a := by simp only [a]; linarith
  have hb0 : 0 ≤ b := by simp only [b]; linarith
  have haX : a ≤ Xt := by simp only [a]; linarith
  have hbY : b ≤ Yt := by simp only [b]; linarith
  have hda : |ah - a| ≤ D * Xt := by simpa [ah, a] using hXp
  have hdb : |bh - b| ≤ D * Yt := by simpa [bh, b] using hYp
  have hX0 : 0 ≤ Xt := by linarith
  have hY0 : 0 ≤ Yt := by linarith
  -- |ah bh - a b| ≤ D(2+D) Xt Yt
  have k1 : |ah * bh - a * b| ≤ D * (2 + D) * (Xt * Yt) := by
    have e : ah * bh - a * b = (ah - a) * (bh - b) + (ah - a) * b + a * (bh - b) := by ring
    rw [e]
    have t1 : |(ah - a) * (bh - b)| ≤ (D * Xt) * (D * Yt) := by
      rw [abs_mul]; exact mul_le_mul hda hdb (abs_nonneg _) (by positivity)
    have t2 : |(ah - a) * b| ≤ (D * Xt) * Yt := by
      rw [abs_mul, abs_of_nonneg hb0]; exact mul_le_mul hda hbY hb0 (by positivity)
    have t3 : |a * (bh - b)| ≤ Xt * (D * Yt) := by
      rw [abs_mul, abs_of_nonneg ha0]; exact mul_le_mul haX hdb (abs_nonneg _) hX0
    calc |(ah - a) * (bh - b) + (ah - a) * b + a * (bh - b)|
        ≤ |(ah - a) * (bh - b)| + |(ah - a) * b| + |a * (bh - b)| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ (D * Xt) * (D * Yt) + (D * Xt) * Yt + Xt * (D * Yt) := by linarith
      _ = D * (2 + D) * (Xt * Yt) := by ring
  -- |ah bh| ≤ (1+D)² Xt Yt
  have hah : |ah| ≤ (1 + D) * Xt := by
    calc |ah| = |a + (ah - a)| := by ring_nf
      _ ≤ |a| + |ah - a| := abs_add_le _ _
      _ ≤ Xt + D * Xt := by rw [abs_of_nonneg ha0]; linarith
      _ = (1 + D) * Xt := by ring
  have hbh : |bh| ≤ (1 + D) * Yt := by
    calc |bh| = |b + (bh - b)| := by ring_nf
      _ ≤ |b| + |bh - b| := abs_add_le _ _
      _ ≤ Yt + D * Yt := by rw [abs_of_nonneg hb0]; linarith
      _ = (1 + D) * Yt := by ring
  have k2 : |ah * bh| ≤ (1 + D) ^ 2 * (Xt * Yt) := by
    rw [abs_mul]
    calc |ah| * |bh| ≤ ((1 + D) * Xt) * ((1 + D) * Yt) :=
          mul_le_mul hah hbh (abs_nonneg _) (by positivity)
      _ = (1 + D) ^ 2 * (Xt * Yt) := by ring
  -- the three roundings: |m - 1| ≤ 4u
  have hu := u_pos
  have hu2 := u_le
  have b1 := abs_le.mp h1
  have b2 := abs_le.mp h2
  have b3 := abs_le.mp h3
  set m := (1 + η1) * (1 + η2) * (1 + η3)
  have hm : |m - 1| ≤ 4 * u := by
    have p12lo : (1 - u) * (1 - u) ≤ (1 + η1) * (1 + η2) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have p12hi : (1 + η1) * (1 + η2) ≤ (1 + u) * (1 + u) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have plo : (1 - u) * (1 - u) * (1 - u) ≤ m :=
      mul_le_mul p12lo (by linarith) (by linarith) (by nlinarith)
    have phi : m ≤ (1 + u) * (1 + u) * (1 + u) :=
      mul_le_mul p12hi (by linarith) (by linarith) (by nlinarith)
    rw [abs_le]
    constructor
    · nlinarith [mul_pos hu hu, mul_pos (mul_pos hu hu) hu]
    · nlinarith [mul_le_mul_of_nonneg_left hu2 hu.le, mul_pos (mul_pos hu hu) hu]
  have e : ah * (1 + η1) * (bh * (1 + η2)) * (1 + η3) = ah * bh * m := by
    simp only [m]; ring
  rw [e]
  have k3 : |ah * bh * m - ah * bh| ≤ (1 + D) ^ 2 * (Xt * Yt) * (4 * u) := by
    rw [show ah * bh * m - ah * bh = (ah * bh) * (m - 1) by ring, abs_mul]
    exact mul_le_mul k2 hm (abs_nonneg _) (by positivity)
  calc |ah * bh * m - a * b| = |(ah * bh * m - ah * bh) + (ah * bh - a * b)| := by ring_nf
    _ ≤ |ah * bh * m - ah * bh| + |ah * bh - a * b| := abs_add_le _ _
    _ ≤ (1 + D) ^ 2 * (Xt * Yt) * (4 * u) + D * (2 + D) * (Xt * Yt) := by linarith
    _ = (D * (2 + D) + 4 * u * (1 + D) ^ 2) * (Xt * Yt) := by ring

/-- `err = 4.0 * eps * X * Y` is at least `4ε(1-D)²(1-u)² Xt Yt`. -/
theorem err_lower {Xt Yt Xe Ye D ε η4 η5 : ℚ} (hX0 : 0 ≤ Xt) (hY0 : 0 ≤ Yt) (hε : 0 ≤ ε)
    (hXe : Xt * (1 - D) ≤ Xe) (hYe : Yt * (1 - D) ≤ Ye) (hD1 : D ≤ 1)
    (h4 : |η4| ≤ u) (h5 : |η5| ≤ u) :
    4 * ε * (1 - D) ^ 2 * (1 - u) ^ 2 * (Xt * Yt) ≤ 4 * ε * Xe * (1 + η4) * Ye * (1 + η5) := by
  have hu := u_le
  have b4 := (abs_le.mp h4).1
  have b5 := (abs_le.mp h5).1
  have hX1 : 0 ≤ Xt * (1 - D) := mul_nonneg hX0 (by linarith)
  have hY1 : 0 ≤ Yt * (1 - D) := mul_nonneg hY0 (by linarith)
  have hu1 : (0 : ℚ) ≤ 1 - u := by linarith
  have s1 : 4 * ε * (Xt * (1 - D)) ≤ 4 * ε * Xe := mul_le_mul_of_nonneg_left hXe (by positivity)
  have s2 : 4 * ε * (Xt * (1 - D)) * (1 - u) ≤ 4 * ε * Xe * (1 + η4) :=
    mul_le_mul s1 (by linarith) hu1 (by have := mul_nonneg hε hX1; nlinarith)
  have s3 : 4 * ε * (Xt * (1 - D)) * (1 - u) * (Yt * (1 - D)) ≤
      4 * ε * Xe * (1 + η4) * Ye :=
    mul_le_mul s2 hYe hY1 (by
      have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℚ) ≤ 4) hε) hX1) hu1
      linarith)
  have s4 : 4 * ε * (Xt * (1 - D)) * (1 - u) * (Yt * (1 - D)) * (1 - u) ≤
      4 * ε * Xe * (1 + η4) * Ye * (1 + η5) :=
    mul_le_mul s3 (by linarith) hu1 (by
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℚ) ≤ 4) hε)
        hX1) hu1) hY1
      linarith)
  calc 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 2 * (Xt * Yt)
      = 4 * ε * (Xt * (1 - D)) * (1 - u) * (Yt * (1 - D)) * (1 - u) := by ring
    _ ≤ _ := s4

/-- `prod > 1.0 + err` means the exact product is above 1. -/
theorem prod_above {Pt Ph K XY err ε D η6 : ℚ} (hP : |Ph - Pt| ≤ K * XY) (hXY : 1 ≤ XY)
    (hε0 : 0 ≤ ε) (herr : 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 2 * XY ≤ err)
    (hC : K + u ≤ 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 3) (h6 : |η6| ≤ u)
    (h : (1 + err) * (1 + η6) < Ph) : 1 < Pt := by
  have hu := u_pos
  have hu2 := u_le
  have hu1 : (0 : ℚ) ≤ 1 - u := by linarith
  have b6 := (abs_le.mp h6).1
  have hP' := (abs_le.mp hP).2
  have herr0 : 0 ≤ err := le_trans (by positivity) herr
  have s1 : (1 + err) * (1 - u) ≤ (1 + err) * (1 + η6) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have s2 : (K + u) * XY ≤ 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 3 * XY :=
    mul_le_mul_of_nonneg_right hC (by linarith)
  have s3 : 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 2 * XY * (1 - u) ≤ err * (1 - u) :=
    mul_le_mul_of_nonneg_right herr hu1
  have e1 : 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 3 * XY =
      4 * ε * (1 - D) ^ 2 * (1 - u) ^ 2 * XY * (1 - u) := by ring
  have e2 : (1 + err) * (1 - u) = 1 - u + err * (1 - u) := by ring
  have e3 : (K + u) * XY = K * XY + u * XY := by ring
  have s4 : u ≤ u * XY := le_mul_of_one_le_right hu.le hXY
  linarith

/-- `prod < 1.0 - err` means the exact product is below 1. -/
theorem prod_below {Pt Ph K XY err ε D η7 : ℚ} (hP : |Ph - Pt| ≤ K * XY) (hXY : 1 ≤ XY)
    (hε0 : 0 ≤ ε) (herr : 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 2 * XY ≤ err)
    (hC : K + u ≤ 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 3) (h7 : |η7| ≤ u)
    (h : Ph < (1 - err) * (1 + η7)) : Pt < 1 := by
  have hu := u_pos
  have hu2 := u_le
  have hu1 : (0 : ℚ) ≤ 1 - u := by linarith
  have b7 := abs_le.mp h7
  have hP' := (abs_le.mp hP).1
  have herr0 : 0 ≤ err := le_trans (by positivity) herr
  -- (1 - err)(1 + η7) ≤ 1 + u - err (1 - u)
  have s1 : (1 - err) * (1 + η7) ≤ 1 + u - err * (1 - u) := by
    have e : (1 - err) * (1 + η7) = 1 - err + η7 * (1 - err) := by ring
    have e' : 1 + u - err * (1 - u) = 1 - err + u * (1 + err) := by ring
    rw [e, e']
    have : η7 * (1 - err) ≤ u * (1 + err) := by
      rcases le_total 0 (1 - err) with h0 | h0
      · have := mul_le_mul_of_nonneg_right b7.2 h0; nlinarith
      · have := mul_le_mul_of_nonpos_right b7.1 h0; nlinarith
    linarith
  have s2 : (K + u) * XY ≤ 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 3 * XY :=
    mul_le_mul_of_nonneg_right hC (by linarith)
  have s3 : 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 2 * XY * (1 - u) ≤ err * (1 - u) :=
    mul_le_mul_of_nonneg_right herr hu1
  have e1 : 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 3 * XY =
      4 * ε * (1 - D) ^ 2 * (1 - u) ^ 2 * XY * (1 - u) := by ring
  have e3 : (K + u) * XY = K * XY + u * XY := by ring
  have s4 : u ≤ u * XY := le_mul_of_one_le_right hu.le hXY
  linarith

/-! ### The exact tests `upper_ok_exact`, `lower_ok_exact` -/

/-- `sigma_and_pow(q, e)`: `sq = 1, qe = 1; repeat e times { qe *= q; sq += qe; }`. -/
def sigmaPow (q : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | i + 1 => ((sigmaPow q i).1 + (sigmaPow q i).2 * q, (sigmaPow q i).2 * q)

theorem sigmaPow_snd (q : ℤ) : ∀ e, (sigmaPow q e).2 = q ^ e
  | 0 => by simp [sigmaPow]
  | e + 1 => by simp only [sigmaPow, sigmaPow_snd q e, pow_succ]

theorem sigmaPow_fst (q : ℤ) : ∀ e, (sigmaPow q e).1 = ∑ i ∈ range (e + 1), q ^ i
  | 0 => by simp [sigmaPow]
  | e + 1 => by
    rw [sigmaPow, Finset.sum_range_succ (n := e + 1), ← sigmaPow_fst q e, sigmaPow_snd, pow_succ]

theorem Hq_mul_pow {q : ℚ} (hq : q ≠ 0) (e : ℕ) :
    Hq q e * q ^ e = ∑ i ∈ range (e + 1), q ^ i := by
  unfold Hq
  rw [Finset.sum_mul, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show e + 1 - 1 - j = e - j by omega, one_div_pow]
  have hsplit : q ^ e = q ^ (e - j) * q ^ j := by rw [← pow_add, Nat.sub_add_cancel hj']
  rw [hsplit]
  field_simp

/-- `upper_ok_exact`'s numerator for one side: `s · [σ(qᵉ)] · (q+1)ʲ · ∏ (L+1)`. -/
def XN (s q : ℤ) (e j : ℕ) (hs : Bool) (Ls : List ℤ) : ℤ :=
  s * (if hs then (sigmaPow q e).1 else 1) * (q + 1) ^ j * (Ls.map fun L : ℤ => L + 1).prod

/-- Its denominator: `p · [qᵉ] · qʲ · ∏ L`. -/
def XD (p q : ℤ) (e j : ℕ) (hs : Bool) (Ls : List ℤ) : ℤ :=
  p * (if hs then (sigmaPow q e).2 else 1) * q ^ j * Ls.prod

theorem floatProd_cast {Ls : List ℤ} (hL : ∀ L ∈ Ls, 1 ≤ L) :
    (((Ls.map fun L : ℤ => L + 1).prod : ℤ) : ℚ) / ((Ls.prod : ℤ) : ℚ) =
      ((Ls.map fun L : ℤ => (L : ℚ)).map fun L => 1 + 1 / L).prod := by
  induction Ls with
  | nil => simp
  | cons L Ls ih =>
    have hL1 : 1 ≤ L := hL L (List.mem_cons_self ..)
    have hL0 : (0 : ℚ) < L := by exact_mod_cast (show 0 < L by omega)
    have hP : (0 : ℚ) < ((Ls.prod : ℤ) : ℚ) := by
      have : 0 < Ls.prod := List.prod_pos fun a ha => by
        have := hL a (List.mem_cons_of_mem _ ha); omega
      exact_mod_cast this
    have ih' := ih fun a ha => hL a (List.mem_cons_of_mem _ ha)
    simp only [List.map_cons, List.prod_cons]
    rw [← ih']
    push_cast
    field_simp

theorem XN_div_XD {s p q : ℤ} {e j : ℕ} {hs : Bool} {Ls : List ℤ} (hp : 0 < p) (hq : 2 ≤ q)
    (hL : ∀ L ∈ Ls, 1 ≤ L) :
    (XN s q e j hs Ls : ℚ) / (XD p q e j hs Ls : ℚ) =
      Xexact ((s : ℚ) / p) q e j hs (Ls.map fun L : ℤ => (L : ℚ)) := by
  have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq0 : (q : ℚ) ≠ 0 := by positivity
  have hp0 : (p : ℚ) ≠ 0 := by
    have : (0 : ℚ) < p := by exact_mod_cast hp
    positivity
  have hP : ((Ls.prod : ℤ) : ℚ) ≠ 0 := by
    have : 0 < Ls.prod := List.prod_pos fun a ha => by have := hL a ha; omega
    exact_mod_cast this.ne'
  have hF := floatProd_cast hL
  have hPN : (0 : ℚ) ≤ (((Ls.map fun L : ℤ => L + 1).prod : ℤ) : ℚ) := by
    have : 0 < (Ls.map fun L : ℤ => L + 1).prod := List.prod_pos fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have := hL b hb; omega
    exact_mod_cast this.le
  unfold XN XD Xexact
  rw [← hF]
  cases hs
  · simp only [Bool.false_eq_true, ite_false]
    push_cast
    field_simp
    have hqj : (q : ℚ) ^ j ≠ 0 := pow_ne_zero _ hq0
    rw [div_pow]
    field_simp
  · simp only [ite_true, sigmaPow_fst, sigmaPow_snd]
    push_cast
    rw [← Hq_mul_pow hq0]
    field_simp
    have hqj : (q : ℚ) ^ j ≠ 0 := pow_ne_zero _ hq0
    rw [div_pow]
    field_simp

/-- `upper_ok_exact`: `XN ≤ 2XD → false; YN ≤ YD → false; (XN-XD)(YN-YD) > XD·YD`. -/
def upperExact (XN XD YN YD : ℤ) : Bool :=
  !decide (XN ≤ 2 * XD) && !decide (YN ≤ YD) && decide (XD * YD < (XN - XD) * (YN - YD))

/-- `lower_ok_exact`: `yn ≥ 2yd → false; (xn-xd)(yn-yd) < xd·yd`. -/
def lowerExact (xn xd yn yd : ℤ) : Bool :=
  !decide (2 * yd ≤ yn) && decide ((xn - xd) * (yn - yd) < xd * yd)

theorem upperExact_iff {XN XD YN YD : ℤ} (hXD : 0 < XD) (hYD : 0 < YD) :
    upperExact XN XD YN YD = true ↔ Utest ((XN : ℚ) / XD) ((YN : ℚ) / YD) := by
  have hX : (0 : ℚ) < XD := by exact_mod_cast hXD
  have hY : (0 : ℚ) < YD := by exact_mod_cast hYD
  unfold upperExact Utest
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    not_le]
  rw [lt_div_iff₀ hX, lt_div_iff₀ hY, one_mul]
  have e : ((XN : ℚ) / XD - 1) * ((YN : ℚ) / YD - 1) = ((XN - XD) * (YN - YD) : ℚ) / (XD * YD) := by
    field_simp
  rw [e, lt_div_iff₀ (mul_pos hX hY), one_mul]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, by exact_mod_cast h3⟩

theorem lowerExact_iff {xn xd yn yd : ℤ} (hxd : 0 < xd) (hyd : 0 < yd) :
    lowerExact xn xd yn yd = true ↔ Ltest ((xn : ℚ) / xd) ((yn : ℚ) / yd) := by
  have hX : (0 : ℚ) < xd := by exact_mod_cast hxd
  have hY : (0 : ℚ) < yd := by exact_mod_cast hyd
  unfold lowerExact Ltest
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    not_le]
  rw [div_lt_iff₀ hY]
  have e : ((xn : ℚ) / xd - 1) * ((yn : ℚ) / yd - 1) = ((xn - xd) * (yn - yd) : ℚ) / (xd * yd) := by
    field_simp
  rw [e, div_lt_iff₀ (mul_pos hX hY), one_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ### The pre-screens and the combined predicates -/

/-- `upper_filter`'s decision from the doubles it computed: `some true` = 1, `some false` = 0,
`none` = -1. -/
def upperDecide (X thr0 thr1 P thrP thrM : ℚ) : Option Bool :=
  if X < thr0 then some false
  else if thr1 < X then (if thrP < P then some true else if P < thrM then some false else none)
  else none

/-- `lower_filter`'s decision. -/
def lowerDecide (Y thr1 thr0 P thrM thrP : ℚ) : Option Bool :=
  if thr1 < Y then some false
  else if Y < thr0 then (if P < thrM then some true else if thrP < P then some false else none)
  else none

/-- `upper_ok` / `lower_ok`: `f >= 0 ? f == 1 : exact`. -/
def combine (f : Option Bool) (exact : Bool) : Bool :=
  match f with
  | some b => b
  | none => exact

/-- The margin `ε = max(1e-13, 16·(n+3)·2⁻⁵³)` is large enough: with `M = 6(n+2)` rounding
factors (`D = 2Mu`), all four decision conditions hold, for `n ≤ 10⁸`. -/
theorem margin_ok {n : ℕ} (hn : n ≤ 10 ^ 8) {ε : ℚ} (hε : 16 * ((n : ℚ) + 3) * u ≤ ε) :
    ((6 * (n + 2) : ℕ) : ℚ) * u ≤ 1 / 2 ∧ 0 ≤ 2 * ((6 * (n + 2) : ℕ) : ℚ) * u ∧
    2 * ((6 * (n + 2) : ℕ) : ℚ) * u ≤ 1 ∧ 2 * ((6 * (n + 2) : ℕ) : ℚ) * u + 2 * u ≤ ε ∧
    0 ≤ ε ∧
    (2 * ((6 * (n + 2) : ℕ) : ℚ) * u) * (2 + 2 * ((6 * (n + 2) : ℕ) : ℚ) * u) +
      4 * u * (1 + 2 * ((6 * (n + 2) : ℕ) : ℚ) * u) ^ 2 + u ≤
      4 * ε * (1 - 2 * ((6 * (n + 2) : ℕ) : ℚ) * u) ^ 2 * (1 - u) ^ 3 := by
  have hu := u_pos
  have hu2 := u_le
  have hn' : (n : ℚ) ≤ 10 ^ 8 := by exact_mod_cast hn
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  push_cast
  set D := 2 * (6 * ((n : ℚ) + 2)) * u with hD
  set w := ((n : ℚ) + 3) * u with hw
  have hw0 : 0 ≤ w := by positivity
  have hwle : w ≤ 2 / 10 ^ 7 := by
    have : ((n : ℚ) + 3) * u ≤ (10 ^ 8 + 3) * (1 / 10 ^ 15) :=
      mul_le_mul (by linarith) hu2 hu.le (by norm_num)
    linarith [show ((10:ℚ) ^ 8 + 3) * (1 / 10 ^ 15) ≤ 2 / 10 ^ 7 by norm_num]
  have hDw : D ≤ 12 * w := by simp only [hD, hw]; nlinarith
  have huw : 3 * u ≤ w := by simp only [hw]; nlinarith
  have hD0 : 0 ≤ D := by positivity
  have hDs : D ≤ 1 / 10 ^ 5 := by linarith
  have hε0 : 0 ≤ ε := le_trans (by positivity) hε
  have hεw : 16 * w ≤ ε := by simp only [hw]; linarith
  refine ⟨?_, hD0, by linarith, by linarith, hε0, ?_⟩
  · have : 6 * ((n : ℚ) + 2) * u ≤ 6 * w := by simp only [hw]; nlinarith
    linarith
  · have h1 : 99 / 100 ≤ (1 - D) ^ 2 := by nlinarith
    have h2 : 99 / 100 ≤ (1 - u) ^ 3 := by
      have := cpow_ge 3; unfold c at this; push_cast at this; nlinarith
    have h3 : (99 / 100) * (99 / 100) ≤ (1 - D) ^ 2 * (1 - u) ^ 3 :=
      mul_le_mul h1 h2 (by norm_num) (by positivity)
    have hR : 4 * ε * ((99 / 100) * (99 / 100)) ≤ 4 * ε * ((1 - D) ^ 2 * (1 - u) ^ 3) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have hL1 : D * D ≤ D * (1 / 10 ^ 5) := mul_le_mul_of_nonneg_left hDs hD0
    have hL2 : (1 + D) ^ 2 ≤ 2 := by nlinarith
    have hL3 : 4 * u * (1 + D) ^ 2 ≤ 4 * u * 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
    have e1 : 4 * ε * (1 - D) ^ 2 * (1 - u) ^ 3 = 4 * ε * ((1 - D) ^ 2 * (1 - u) ^ 3) := by ring
    rw [e1]
    nlinarith

theorem XD_pos {p q : ℤ} {e j : ℕ} {hs : Bool} {Ls : List ℤ} (hp : 0 < p) (hq : 2 ≤ q)
    (hL : ∀ L ∈ Ls, 1 ≤ L) : 0 < XD p q e j hs Ls := by
  have hq0 : 0 < q := by omega
  have hP : 0 < Ls.prod := List.prod_pos fun a ha => by have := hL a ha; omega
  unfold XD
  cases hs
  · simp only [Bool.false_eq_true, ite_false, mul_one]; positivity
  · simp only [ite_true, sigmaPow_snd]; positivity

/-- Every evaluation bounded by `M` factors is within `D = 2Mu` (relative) of the exact value. -/
theorem bounds_of_A {M : ℕ} {Z Zt : ℚ} (hZt : 0 ≤ Zt) (h : A M Z Zt) (hM : (M : ℚ) * u ≤ 1 / 2) :
    Zt * (1 - 2 * M * u) ≤ Z ∧ Z ≤ Zt * (1 + 2 * M * u) ∧ |Z - Zt| ≤ 2 * M * u * Zt :=
  ⟨(abs_le_of_A hZt h hM).1, (abs_le_of_A hZt h hM).2, A_abs hZt h hM⟩

theorem cast_floats_pos {Ls : List ℤ} (hL : ∀ L ∈ Ls, 1 ≤ L) :
    ∀ L ∈ Ls.map (fun L : ℤ => (L : ℚ)), 0 < L := by
  intro L h
  obtain ⟨L', hL', rfl⟩ := List.mem_map.mp h
  have := hL L' hL'
  exact_mod_cast (show 0 < L' by omega)

theorem ratio_ge_one {s p : ℤ} (hp : 0 < p) (hs : p ≤ s) : (1 : ℚ) ≤ (s : ℚ) / p := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ hp', one_mul]; exact_mod_cast hs

/-- **Appendix B, upper test.** Whenever `upper_filter` decides, its answer is the exact
`upper_ok_exact`; so `upper_ok = upper_ok_exact` (which is `U(q)`, `upperExact_iff`).  Each
use of `X` and `Y` may come from a different evaluation (FMA contraction), each threshold from
its own rounding.  `n = e + j0 + j1 + (number of floating primes)` is the code's `ops`, and `ε`
is any value `≥ 16(n+3)u` (the code's `filter_eps`), `ε ≤ 1`. -/
theorem upper_ok_eq_exact
    {sx px sy py q : ℤ} {e j0 j1 : ℕ} {side0 : Bool} {Lx Ly : List ℤ}
    (hpx : 0 < px) (hpy : 0 < py) (hsx : px ≤ sx) (hsy : py ≤ sy) (hq : 2 ≤ q)
    (hLx : ∀ L ∈ Lx, 1 ≤ L) (hLy : ∀ L ∈ Ly, 1 ≤ L)
    (hn : e + j0 + j1 + Lx.length + Ly.length ≤ 10 ^ 8)
    {ε : ℚ} (hε : 16 * (((e + j0 + j1 + Lx.length + Ly.length : ℕ) : ℚ) + 3) * u ≤ ε)
    (hε1 : ε ≤ 1)
    {X Xp Yp Xe Ye Xe' Ye' η1 η2 η3 η4 η5 η4' η5' η6 η7 η8 η9 : ℚ}
    (hX : IsXEval ((sx : ℚ) / px) q e j0 side0 (Lx.map fun L : ℤ => (L : ℚ)) X)
    (hXp : IsXEval ((sx : ℚ) / px) q e j0 side0 (Lx.map fun L : ℤ => (L : ℚ)) Xp)
    (hXe : IsXEval ((sx : ℚ) / px) q e j0 side0 (Lx.map fun L : ℤ => (L : ℚ)) Xe)
    (hXe' : IsXEval ((sx : ℚ) / px) q e j0 side0 (Lx.map fun L : ℤ => (L : ℚ)) Xe')
    (hYp : IsXEval ((sy : ℚ) / py) q e j1 (!side0) (Ly.map fun L : ℤ => (L : ℚ)) Yp)
    (hYe : IsXEval ((sy : ℚ) / py) q e j1 (!side0) (Ly.map fun L : ℤ => (L : ℚ)) Ye)
    (hYe' : IsXEval ((sy : ℚ) / py) q e j1 (!side0) (Ly.map fun L : ℤ => (L : ℚ)) Ye')
    (h1 : |η1| ≤ u) (h2 : |η2| ≤ u) (h3 : |η3| ≤ u) (h4 : |η4| ≤ u) (h5 : |η5| ≤ u)
    (h4' : |η4'| ≤ u) (h5' : |η5'| ≤ u) (h6 : |η6| ≤ u) (h7 : |η7| ≤ u) (h8 : |η8| ≤ u)
    (h9 : |η9| ≤ u) :
    combine
      (upperDecide X (2 * ((1 - ε) * (1 + η8))) (2 * ((1 + ε) * (1 + η9)))
        ((Xp - 1) * (1 + η1) * ((Yp - 1) * (1 + η2)) * (1 + η3))
        ((1 + 4 * ε * Xe * (1 + η4) * Ye * (1 + η5)) * (1 + η6))
        ((1 - 4 * ε * Xe' * (1 + η4') * Ye' * (1 + η5')) * (1 + η7)))
      (upperExact (XN sx q e j0 side0 Lx) (XD px q e j0 side0 Lx)
        (XN sy q e j1 (!side0) Ly) (XD py q e j1 (!side0) Ly)) =
    upperExact (XN sx q e j0 side0 Lx) (XD px q e j0 side0 Lx)
        (XN sy q e j1 (!side0) Ly) (XD py q e j1 (!side0) Ly) := by
  obtain ⟨hM, hD0, hD1, hT1, hε0, hC⟩ := margin_ok hn hε
  set n := e + j0 + j1 + Lx.length + Ly.length with hn_def
  set M := 6 * (n + 2) with hM_def
  set D := 2 * (M : ℚ) * u with hD_def
  have hT0 : D + u ≤ ε := by have := u_pos; linarith
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℚ) < q := by linarith
  have hLx' := cast_floats_pos hLx
  have hLy' := cast_floats_pos hLy
  have hx0 := ratio_ge_one hpx hsx
  have hy0 := ratio_ge_one hpy hsy
  set Xt := Xexact ((sx : ℚ) / px) q e j0 side0 (Lx.map fun L : ℤ => (L : ℚ)) with hXt_def
  set Yt := Xexact ((sy : ℚ) / py) q e j1 (!side0) (Ly.map fun L : ℤ => (L : ℚ)) with hYt_def
  have hXt1 : 1 ≤ Xt := one_le_Xexact hx0 hq0 hLx'
  have hYt1 : 1 ≤ Yt := one_le_Xexact hy0 hq0 hLy'
  have hXt0 : 0 ≤ Xt := by linarith
  have hYt0 : 0 ≤ Yt := by linarith
  have he : e ≤ 10 ^ 9 := by omega
  have hNX : 5 * e + 6 * j0 + 6 * (Lx.map fun L : ℤ => (L : ℚ)).length + 11 ≤ M := by
    simp only [List.length_map, hM_def, hn_def]; omega
  have hNY : 5 * e + 6 * j1 + 6 * (Ly.map fun L : ℤ => (L : ℚ)).length + 11 ≤ M := by
    simp only [List.length_map, hM_def, hn_def]; omega
  have evX : ∀ {Z : ℚ}, IsXEval ((sx : ℚ) / px) q e j0 side0 (Lx.map fun L : ℤ => (L : ℚ)) Z →
      Xt * (1 - D) ≤ Z ∧ Z ≤ Xt * (1 + D) ∧ |Z - Xt| ≤ D * Xt := fun hZ =>
    bounds_of_A hXt0 (A_mono hXt0 hNX (hZ.approx (by linarith) hq' hLx' he)) hM
  have evY : ∀ {Z : ℚ}, IsXEval ((sy : ℚ) / py) q e j1 (!side0) (Ly.map fun L : ℤ => (L : ℚ)) Z →
      Yt * (1 - D) ≤ Z ∧ Z ≤ Yt * (1 + D) ∧ |Z - Yt| ≤ D * Yt := fun hZ =>
    bounds_of_A hYt0 (A_mono hYt0 hNY (hZ.approx (by linarith) hq' hLy' he)) hM
  have hexact : upperExact (XN sx q e j0 side0 Lx) (XD px q e j0 side0 Lx)
      (XN sy q e j1 (!side0) Ly) (XD py q e j1 (!side0) Ly) = true ↔ Utest Xt Yt := by
    rw [upperExact_iff (XD_pos hpx hq hLx) (XD_pos hpy hq hLy), XN_div_XD hpx hq hLx,
      XN_div_XD hpy hq hLy]
  have hXY : 1 ≤ Xt * Yt := one_le_mul_of_one_le_of_one_le hXt1 hYt1
  unfold upperDecide
  split_ifs with c1 c2 c3 c4
  · -- X < 2(1-ε): U is false
    have hlt : Xt < 2 := below_two (evX hX).1 hD0 hD1 h8 hT0 hε1 c1
    simp only [combine]
    symm
    rw [Bool.eq_false_iff]
    intro hT
    have := ((hexact.mp hT).1)
    linarith
  · -- X > 2(1+ε) and prod > 1 + err: U is true
    have hX2 : 2 < Xt := above_two (evX hX).2.1 hD0 h9 hT1 hε1 c2
    have hPe := prod_err hXt1 hYt1 (evX hXp).2.2 (evY hYp).2.2 hD0 h1 h2 h3
    have herr := err_lower hXt0 hYt0 hε0 (evX hXe).1 (evY hYe).1 hD1 h4 h5
    have hP1 := prod_above hPe hXY hε0 herr hC h6 c3
    simp only [combine]
    symm
    rw [hexact]
    refine ⟨hX2, ?_, hP1⟩
    by_contra hY
    have hY1 : Yt - 1 = 0 := by linarith
    rw [hY1, mul_zero] at hP1
    linarith
  · -- X > 2(1+ε) and prod < 1 - err: U is false
    have hPe := prod_err hXt1 hYt1 (evX hXp).2.2 (evY hYp).2.2 hD0 h1 h2 h3
    have herr := err_lower hXt0 hYt0 hε0 (evX hXe').1 (evY hYe').1 hD1 h4' h5'
    have hP0 := prod_below hPe hXY hε0 herr hC h7 c4
    simp only [combine]
    symm
    rw [Bool.eq_false_iff]
    intro hT
    have := (hexact.mp hT).2.2
    linarith
  · rfl
  · rfl

/-- **Appendix B, lower test.** Whenever `lower_filter` decides, its answer is the exact
`lower_ok_exact`; so `lower_ok = lower_ok_exact` (`= L(q)`, `lowerExact_iff`).  Here the
code's `ops` is `e` (`ε ≥ 16(e+3)u`); the evaluations of `X⁻`, `Y⁻` are `IsXEval` with `j = 0`
and no floating primes (`isXEval_lower` shows the code's one-product evaluation is one). -/
theorem lower_ok_eq_exact
    {sx px sy py q : ℤ} {e : ℕ} {side0 : Bool}
    (hpx : 0 < px) (hpy : 0 < py) (hsx : px ≤ sx) (hsy : py ≤ sy) (hq : 2 ≤ q)
    (hn : e ≤ 10 ^ 8) {ε : ℚ} (hε : 16 * ((e : ℚ) + 3) * u ≤ ε) (hε1 : ε ≤ 1)
    {Y Xp Yp Xe Ye Xe' Ye' η1 η2 η3 η4 η5 η4' η5' η6 η7 η8 η9 : ℚ}
    (hY : IsXEval ((sy : ℚ) / py) q e 0 (!side0) [] Y)
    (hXp : IsXEval ((sx : ℚ) / px) q e 0 side0 [] Xp)
    (hXe : IsXEval ((sx : ℚ) / px) q e 0 side0 [] Xe)
    (hXe' : IsXEval ((sx : ℚ) / px) q e 0 side0 [] Xe')
    (hYp : IsXEval ((sy : ℚ) / py) q e 0 (!side0) [] Yp)
    (hYe : IsXEval ((sy : ℚ) / py) q e 0 (!side0) [] Ye)
    (hYe' : IsXEval ((sy : ℚ) / py) q e 0 (!side0) [] Ye')
    (h1 : |η1| ≤ u) (h2 : |η2| ≤ u) (h3 : |η3| ≤ u) (h4 : |η4| ≤ u) (h5 : |η5| ≤ u)
    (h4' : |η4'| ≤ u) (h5' : |η5'| ≤ u) (h6 : |η6| ≤ u) (h7 : |η7| ≤ u) (h8 : |η8| ≤ u)
    (h9 : |η9| ≤ u) :
    combine
      (lowerDecide Y (2 * ((1 + ε) * (1 + η9))) (2 * ((1 - ε) * (1 + η8)))
        ((Xp - 1) * (1 + η1) * ((Yp - 1) * (1 + η2)) * (1 + η3))
        ((1 - 4 * ε * Xe' * (1 + η4') * Ye' * (1 + η5')) * (1 + η7))
        ((1 + 4 * ε * Xe * (1 + η4) * Ye * (1 + η5)) * (1 + η6)))
      (lowerExact (XN sx q e 0 side0 []) (XD px q e 0 side0 [])
        (XN sy q e 0 (!side0) []) (XD py q e 0 (!side0) [])) =
    lowerExact (XN sx q e 0 side0 []) (XD px q e 0 side0 [])
        (XN sy q e 0 (!side0) []) (XD py q e 0 (!side0) []) := by
  obtain ⟨hM, hD0, hD1, hT1, hε0, hC⟩ := margin_ok hn hε
  set M := 6 * (e + 2) with hM_def
  set D := 2 * (M : ℚ) * u with hD_def
  have hT0 : D + u ≤ ε := by have := u_pos; linarith
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℚ) < q := by linarith
  have hnil : ∀ L ∈ ([] : List ℚ), 0 < L := by simp
  have hx0 := ratio_ge_one hpx hsx
  have hy0 := ratio_ge_one hpy hsy
  set Xt := Xexact ((sx : ℚ) / px) q e 0 side0 [] with hXt_def
  set Yt := Xexact ((sy : ℚ) / py) q e 0 (!side0) [] with hYt_def
  have hXt1 : 1 ≤ Xt := one_le_Xexact hx0 hq0 hnil
  have hYt1 : 1 ≤ Yt := one_le_Xexact hy0 hq0 hnil
  have hXt0 : 0 ≤ Xt := by linarith
  have hYt0 : 0 ≤ Yt := by linarith
  have he : e ≤ 10 ^ 9 := by omega
  have hN : 5 * e + 6 * 0 + 6 * ([] : List ℚ).length + 11 ≤ M := by
    simp only [List.length_nil, hM_def]; omega
  have evX : ∀ {Z : ℚ}, IsXEval ((sx : ℚ) / px) q e 0 side0 [] Z →
      Xt * (1 - D) ≤ Z ∧ Z ≤ Xt * (1 + D) ∧ |Z - Xt| ≤ D * Xt := fun hZ =>
    bounds_of_A hXt0 (A_mono hXt0 hN (hZ.approx (by linarith) hq' hnil he)) hM
  have evY : ∀ {Z : ℚ}, IsXEval ((sy : ℚ) / py) q e 0 (!side0) [] Z →
      Yt * (1 - D) ≤ Z ∧ Z ≤ Yt * (1 + D) ∧ |Z - Yt| ≤ D * Yt := fun hZ =>
    bounds_of_A hYt0 (A_mono hYt0 hN (hZ.approx (by linarith) hq' hnil he)) hM
  have hnil' : ∀ L ∈ ([] : List ℤ), 1 ≤ L := by simp
  have hexact : lowerExact (XN sx q e 0 side0 []) (XD px q e 0 side0 [])
      (XN sy q e 0 (!side0) []) (XD py q e 0 (!side0) []) = true ↔ Ltest Xt Yt := by
    rw [lowerExact_iff (XD_pos hpx hq hnil') (XD_pos hpy hq hnil'), XN_div_XD hpx hq hnil',
      XN_div_XD hpy hq hnil']
    rfl
  have hXY : 1 ≤ Xt * Yt := one_le_mul_of_one_le_of_one_le hXt1 hYt1
  unfold lowerDecide
  split_ifs with c1 c2 c3 c4
  · -- Y > 2(1+ε): L is false
    have hY2 : 2 < Yt := above_two (evY hY).2.1 hD0 h9 hT1 hε1 c1
    simp only [combine]
    symm
    rw [Bool.eq_false_iff]
    intro hT
    have := (hexact.mp hT).1
    linarith
  · -- Y < 2(1-ε) and prod < 1 - err: L is true
    have hY2 : Yt < 2 := below_two (evY hY).1 hD0 hD1 h8 hT0 hε1 c2
    have hPe := prod_err hXt1 hYt1 (evX hXp).2.2 (evY hYp).2.2 hD0 h1 h2 h3
    have herr := err_lower hXt0 hYt0 hε0 (evX hXe').1 (evY hYe').1 hD1 h4' h5'
    have hP0 := prod_below hPe hXY hε0 herr hC h7 c3
    simp only [combine]
    symm
    rw [hexact]
    exact ⟨hY2, hP0⟩
  · -- Y < 2(1-ε) and prod > 1 + err: L is false
    have hPe := prod_err hXt1 hYt1 (evX hXp).2.2 (evY hYp).2.2 hD0 h1 h2 h3
    have herr := err_lower hXt0 hYt0 hε0 (evX hXe).1 (evY hYe).1 hD1 h4 h5
    have hP1 := prod_above hPe hXY hε0 herr hC h6 c4
    simp only [combine]
    symm
    rw [Bool.eq_false_iff]
    intro hT
    have := (hexact.mp hT).2
    linarith
  · rfl
  · rfl

end Amicable.FP
