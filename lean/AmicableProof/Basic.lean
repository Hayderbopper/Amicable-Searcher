/-
  §3 of exhaustive_search_proof.md: the three basic facts.

  * Lemma 3.1  (abundancy identity)            `abundancy_identity`
  * Lemma 3.2  (one prime power)               `abund_prime_pow_bounds`, `abund_prime_pow_lt_L`,
                                               `abund_prime_pow_strictAnti`
  * Lemma 3.3  (decomposition, equation (E))   `decomposition`
  * (P) and Corollary 3.4 (abundancy grows)    `abund_mul`, `abund_grows`
-/
import AmicableProof.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Amicable

/-! ### Abundancy -/

/-- The abundancy `h(n) = σ(n)/n`, as a rational number (`h(0) = 0` by Lean's `x/0 = 0`). -/
def abund (n : ℕ) : ℚ := (σ 1 n : ℚ) / n

theorem abund_mul {m n : ℕ} (h : Nat.Coprime m n) : abund (m * n) = abund m * abund n := by
  unfold abund
  rw [isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  rw [mul_div_mul_comm]

theorem sigma_one_ge_self (n : ℕ) : n ≤ σ 1 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

theorem sigma_one_gt_self {n : ℕ} (hn : 1 < n) : n + 1 ≤ σ 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, add_comm]
  have h1 : 1 ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hn
  have := Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) h1
  omega

theorem one_le_abund {n : ℕ} (hn : 0 < n) : 1 ≤ abund n := by
  unfold abund
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn', one_mul]
  exact_mod_cast sigma_one_ge_self n

theorem one_lt_abund {n : ℕ} (hn : 1 < n) : 1 < abund n := by
  unfold abund
  have hn' : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lt_div_iff₀ hn', one_mul]
  have := sigma_one_gt_self hn
  exact_mod_cast (show n < σ 1 n by omega)

theorem abund_one : abund 1 = 1 := by simp [abund]

/-! ### Lemma 3.1 -/

/-- **Lemma 3.1 (abundancy identity).** For an amicable pair, with `x = σ(N1)/N1` and
`y = σ(N2)/N2`: `(x-1)(y-1) = 1`, `x > 2`, `1 < y < 2`. -/
theorem abundancy_identity {N1 N2 : ℕ} (h : IsAmicablePair N1 N2) :
    (abund N1 - 1) * (abund N2 - 1) = 1 ∧ 2 < abund N1 ∧ 1 < abund N2 ∧ abund N2 < 2 := by
  obtain ⟨h0, hlt, h1, h2⟩ := h
  have hN1 : (0 : ℚ) < N1 := by exact_mod_cast h0
  have hN2 : (0 : ℚ) < N2 := by exact_mod_cast (h0.trans hlt)
  have hlt' : (N1 : ℚ) < N2 := by exact_mod_cast hlt
  unfold abund
  rw [h1, h2]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
    ring
  · rw [lt_div_iff₀ hN1]; linarith
  · rw [lt_div_iff₀ hN2]; linarith
  · rw [div_lt_iff₀ hN2]; linarith

/-! ### Lemma 3.2 -/

/-- `h(p^e) = 1 + 1/p + … + 1/p^e`. -/
theorem abund_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    abund (p ^ e) = ∑ i ∈ range (e + 1), (1 / (p : ℚ)) ^ i := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold abund
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rw [Finset.sum_div, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsplit : (p : ℚ) ^ e = (p : ℚ) ^ j * (p : ℚ) ^ (e - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [show e + 1 - 1 - j = e - j by omega, hsplit, one_div_pow]
  field_simp

/-- The geometric sum `G e r = 1 + r + … + r^e`. -/
def G (e : ℕ) (r : ℚ) : ℚ := ∑ i ∈ range (e + 1), r ^ i

theorem G_gt_one {e : ℕ} (he : 1 ≤ e) {r : ℚ} (hr : 0 < r) : 1 < G e r := by
  unfold G
  rw [Finset.sum_range_succ', pow_zero]
  have : 0 < ∑ i ∈ range e, r ^ (i + 1) :=
    Finset.sum_pos (fun i _ => pow_pos hr _) ⟨0, Finset.mem_range.mpr he⟩
  linarith

theorem G_mul_one_sub (e : ℕ) (r : ℚ) : G e r * (1 - r) = 1 - r ^ (e + 1) :=
  geom_sum_mul_neg r (e + 1)

theorem G_strictMono {e : ℕ} (he : 1 ≤ e) {r s : ℚ} (hr : 0 ≤ r) (hrs : r < s) :
    G e r < G e s := by
  unfold G
  refine Finset.sum_lt_sum (fun i _ => pow_le_pow_left₀ hr hrs.le i) ⟨1, ?_, ?_⟩
  · exact Finset.mem_range.mpr (by omega)
  · simpa using hrs

/-- **Lemma 3.2, first part.** For a prime `p` and `e ≥ 1`, `1 < h(p^e) < p/(p-1)`.
(The upper bound holds for every `e`, so it is stated separately.) -/
theorem abund_prime_pow_lt {p : ℕ} (hp : p.Prime) (e : ℕ) :
    abund (p ^ e) < (p : ℚ) / (p - 1) := by
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℚ) < p - 1 := by linarith
  have hp0 : (0 : ℚ) < p := by linarith
  rw [abund_prime_pow hp, lt_div_iff₀ hp1]
  have key := G_mul_one_sub e (1 / (p : ℚ))
  unfold G at key
  have hrp : 0 < (1 / (p : ℚ)) ^ (e + 1) := by positivity
  have : (∑ i ∈ range (e + 1), (1 / (p : ℚ)) ^ i) * ((p : ℚ) - 1)
      = (1 - (1 / (p : ℚ)) ^ (e + 1)) * p := by
    rw [← key]; field_simp
  rw [this]
  nlinarith

theorem abund_prime_pow_bounds {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    1 < abund (p ^ e) ∧ abund (p ^ e) < (p : ℚ) / (p - 1) := by
  refine ⟨?_, abund_prime_pow_lt hp e⟩
  rw [abund_prime_pow hp]
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  exact G_gt_one he (by positivity)

/-- **Lemma 3.2, second part.** If `p > L ≥ 1`, then `h(p^e) < (L+1)/L` (for every `e`). -/
theorem abund_prime_pow_lt_L {p e L : ℕ} (hp : p.Prime) (hL : 1 ≤ L) (hpL : L < p) :
    abund (p ^ e) < ((L : ℚ) + 1) / L := by
  refine (abund_prime_pow_lt hp e).trans_le ?_
  have hL' : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have hpL' : (L : ℚ) + 1 ≤ p := by exact_mod_cast hpL
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Lemma 3.2, third part.** For `e ≥ 1`, `h(p^e)` strictly decreases as the prime grows. -/
theorem abund_prime_pow_strictAnti {p q e : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 ≤ e)
    (hpq : p < q) : abund (q ^ e) < abund (p ^ e) := by
  rw [abund_prime_pow hp, abund_prime_pow hq]
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpq' : (p : ℚ) < q := by exact_mod_cast hpq
  have hq0 : (0 : ℚ) < q := hp0.trans hpq'
  exact G_strictMono he (by positivity) (one_div_lt_one_div_of_lt hp0 hpq')

/-! ### Lemma 3.3: the decomposition (E)

For a side `M` (with the other member `N`):
* the side's **bound** slot primes are the primes with `v_p(N) < v_p(M)` and `v_p(N) > 0`
  (slot `(e, b) = (v_p(M) - v_p(N), v_p(N))` with `b > 0`);
* its **free** slot primes are those with `v_p(N) = 0 < v_p(M)` (slot `(v_p(M), 0)`).

`boundSet`/`freeSet` are proved below to be exactly the slot primes of `slotPrimes`
(the primes listed in the hash) with `b > 0`, resp. `b = 0`. -/

/-- Bound slot primes of side `M`. -/
noncomputable def boundSet (M N : ℕ) : Finset ℕ :=
  M.primeFactors.filter fun p => N.factorization p < M.factorization p ∧ 0 < N.factorization p

/-- Free slot primes of side `M`. -/
noncomputable def freeSet (M N : ℕ) : Finset ℕ :=
  M.primeFactors.filter fun p => N.factorization p = 0

/-- `∏ (bound slot primes)^e`. -/
noncomputable def boundPart (M N : ℕ) : ℕ :=
  ∏ p ∈ boundSet M N, p ^ (M.factorization p - N.factorization p)

/-- `X = ∏ P^e` over the free slots (`e = v_P(M)` since `v_P(N) = 0`). -/
noncomputable def freePart (M N : ℕ) : ℕ :=
  ∏ p ∈ freeSet M N, p ^ (M.factorization p - N.factorization p)

theorem mem_primeFactors_iff_fact {M p : ℕ} : p ∈ M.primeFactors ↔ M.factorization p ≠ 0 := by
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]

/-- Bound set = slot primes (as listed in the hash) whose slot has `b > 0`. -/
theorem mem_boundSet_iff {M N p : ℕ} :
    p ∈ boundSet M N ↔ p ∈ slotPrimes M N ∧ 0 < (⟨M.factorization p - N.factorization p,
      N.factorization p⟩ : Slot).b := by
  simp only [boundSet, slotPrimes, Finset.mem_filter, Finset.mem_sort]
  tauto

/-- Free set = slot primes (as listed in the hash) whose slot has `b = 0`. -/
theorem mem_freeSet_iff {M N p : ℕ} :
    p ∈ freeSet M N ↔ p ∈ slotPrimes M N ∧ (⟨M.factorization p - N.factorization p,
      N.factorization p⟩ : Slot).b = 0 := by
  simp only [freeSet, slotPrimes, Finset.mem_filter, Finset.mem_sort, mem_primeFactors_iff_fact]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩

/-- A slot `(e, b)` of side `M`: the prime divides `k = gcd(M, N)` exactly `b` times. -/
theorem slot_b_eq_vk {M N p : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hp : p ∈ slotPrimes M N) :
    (Nat.gcd M N).factorization p = N.factorization p := by
  simp only [slotPrimes, Finset.mem_filter, Finset.mem_sort] at hp
  rw [Nat.factorization_gcd hM hN, Finsupp.inf_apply]
  exact inf_eq_right.mpr hp.2.le

theorem factorization_prod_pow {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (f : ℕ → ℕ) (q : ℕ) :
    (∏ p ∈ S, p ^ f p).factorization q = if q ∈ S then f q else 0 := by
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hS p hp).ne_zero),
    Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by rw [(hS p hp).factorization_pow, Finsupp.single_apply])]
  simp

theorem boundSet_prime {M N p : ℕ} (h : p ∈ boundSet M N) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1

theorem freeSet_prime {M N p : ℕ} (h : p ∈ freeSet M N) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1

theorem boundPart_fact (M N q : ℕ) :
    (boundPart M N).factorization q =
      if M.factorization q ≠ 0 ∧ N.factorization q < M.factorization q ∧ 0 < N.factorization q
      then M.factorization q - N.factorization q else 0 := by
  rw [boundPart, factorization_prod_pow (fun _ hp => boundSet_prime hp)]
  simp only [boundSet, Finset.mem_filter, mem_primeFactors_iff_fact]

theorem freePart_fact (M N q : ℕ) :
    (freePart M N).factorization q =
      if M.factorization q ≠ 0 ∧ N.factorization q = 0
      then M.factorization q - N.factorization q else 0 := by
  rw [freePart, factorization_prod_pow (fun _ hp => freeSet_prime hp)]
  simp only [freeSet, Finset.mem_filter, mem_primeFactors_iff_fact]

theorem boundPart_ne_zero (M N : ℕ) : boundPart M N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => pow_ne_zero _ (boundSet_prime hp).ne_zero

theorem freePart_ne_zero (M N : ℕ) : freePart M N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => pow_ne_zero _ (freeSet_prime hp).ne_zero

/-- One side of the decomposition: `M = (gcd(M,N) · ∏ bound^e) · X` and the two factors are
coprime. -/
theorem side_decomp {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) :
    M = (Nat.gcd M N * boundPart M N) * freePart M N ∧
      Nat.Coprime (Nat.gcd M N * boundPart M N) (freePart M N) := by
  have hg : Nat.gcd M N ≠ 0 := Nat.gcd_ne_zero_left hM
  have hK : Nat.gcd M N * boundPart M N ≠ 0 := mul_ne_zero hg (boundPart_ne_zero M N)
  have hfK : ∀ q, (Nat.gcd M N * boundPart M N).factorization q =
      min (M.factorization q) (N.factorization q) +
        (if M.factorization q ≠ 0 ∧ N.factorization q < M.factorization q ∧
            0 < N.factorization q
          then M.factorization q - N.factorization q else 0) := by
    intro q
    rw [Nat.factorization_mul hg (boundPart_ne_zero M N), Finsupp.add_apply,
      Nat.factorization_gcd hM hN, Finsupp.inf_apply, boundPart_fact]
  constructor
  · refine Nat.eq_of_factorization_eq hM (mul_ne_zero hK (freePart_ne_zero M N)) fun q => ?_
    rw [Nat.factorization_mul hK (freePart_ne_zero M N), Finsupp.add_apply, hfK, freePart_fact]
    split_ifs <;> omega
  · refine Nat.coprime_of_dvd fun q hq h1 h2 => ?_
    rw [hq.dvd_iff_one_le_factorization hK, hfK] at h1
    rw [hq.dvd_iff_one_le_factorization (freePart_ne_zero M N), freePart_fact] at h2
    split_ifs at h1 h2 <;> omega

/-- **Lemma 3.3 (decomposition).** For an amicable pair with `k = gcd(N1, N2)`, let
`K1 = k · ∏ (bound side-0 slot primes)^e`, `X = ∏ P^e` over the free side-0 slots, and
`K2`, `Y` likewise for side 1. Then `N1 = K1·X`, `N2 = K2·Y`, `gcd(K1,X) = gcd(K2,Y) = 1`, and
`σ(K1)σ(X) = σ(K2)σ(Y) = K1·X + K2·Y`  (E). -/
theorem decomposition {N1 N2 : ℕ} (h : IsAmicablePair N1 N2) :
    let k := Nat.gcd N1 N2
    let K1 := k * boundPart N1 N2
    let X := freePart N1 N2
    let K2 := k * boundPart N2 N1
    let Y := freePart N2 N1
    N1 = K1 * X ∧ N2 = K2 * Y ∧ Nat.Coprime K1 X ∧ Nat.Coprime K2 Y ∧
      σ 1 K1 * σ 1 X = K1 * X + K2 * Y ∧ σ 1 K2 * σ 1 Y = K1 * X + K2 * Y := by
  obtain ⟨h0, hlt, h1, h2⟩ := h
  have hN1 : N1 ≠ 0 := h0.ne'
  have hN2 : N2 ≠ 0 := (h0.trans hlt).ne'
  obtain ⟨e1, c1⟩ := side_decomp hN1 hN2
  obtain ⟨e2, c2⟩ := side_decomp hN2 hN1
  rw [Nat.gcd_comm] at e2 c2
  intro k K1 X K2 Y
  refine ⟨e1, e2, c1, c2, ?_, ?_⟩
  · rw [← isMultiplicative_sigma.map_mul_of_coprime c1, ← e1, ← e2, h1]
  · rw [← isMultiplicative_sigma.map_mul_of_coprime c2, ← e1, ← e2, h2]

/-! ### (P) and Corollary 3.4 -/

/-- **(P) and Corollary 3.4.** If the chosen part `A` and the remaining part `R` of a side are
coprime and positive, then `h(A·R) = h(A)·h(R) ≥ h(A)`, strictly exactly when `R > 1`
(i.e. some prime remains). -/
theorem abund_grows {A R : ℕ} (hA : 0 < A) (hR : 0 < R) (h : Nat.Coprime A R) :
    abund (A * R) = abund A * abund R ∧ abund A ≤ abund (A * R) ∧
      (abund A < abund (A * R) ↔ 1 < R) := by
  have hm := abund_mul h
  have hApos : 0 < abund A := by linarith [one_le_abund hA]
  refine ⟨hm, ?_, ?_⟩
  · rw [hm]; nlinarith [one_le_abund hR]
  · constructor
    · intro hlt
      by_contra hR1
      have : R = 1 := by omega
      subst this
      rw [mul_one] at hlt
      exact lt_irrefl _ hlt
    · intro hR1
      rw [hm]
      nlinarith [one_lt_abund hR1]

end Amicable
