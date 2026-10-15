/-
  The hypotheses of the Main Theorem are consistent: there is an `Impl` satisfying A1–A5
  together, a valid hash, a `k > 0`, and a report satisfying A6.  So `MainTheorem Run` is not
  true merely because its premises are contradictory.

  The witness `Impl` is deliberately not "exact": every floating-point operation is perturbed
  by the largest relative error A5 allows (`(1±u)`), and the conversion takes the largest
  truncation it allows (`1-2u`).  Hence A5 does not force exact arithmetic, and the model of
  rounding is realised by something other than the identity.
-/
import AmicableProof.MainStatement

namespace Amicable

open FP

/-- A concrete implementation of the primitives: exact integer arithmetic, exact primality, the
true factorization and prime ranges, and floating point with the worst allowed errors. -/
noncomputable def witnessImpl : Impl where
  mulMod a b m := a * b % m
  iroot n r := Nat.findGreatest (fun x => x ^ r ≤ n) n
  primesIn lo hi := by
    classical
    exact if hi ≤ 2 ^ 64 then some ((List.range' lo (hi + 1 - lo)).filter Nat.Prime) else none
  maxStop := 2 ^ 64
  factor n := n.primeFactors.sort.map fun p => (p, n.factorization p)
  isPrime n := by classical exact decide n.Prime
  fadd x y := (x + y) * (1 + u)
  fsub x y := (x - y) * (1 - u)
  fmul x y := x * y * (1 + u)
  fdiv x y := x / y * (1 - u)
  toDouble n := (n : ℚ) * (1 - 2 * u)

theorem witness_A1 : A1 witnessImpl := by
  refine ⟨fun a b m _ => rfl, fun n r hr => ?_⟩
  show Nat.findGreatest (fun x => x ^ r ≤ n) n ^ r ≤ n ∧
    n < (Nat.findGreatest (fun x => x ^ r ≤ n) n + 1) ^ r
  refine ⟨Nat.findGreatest_spec (P := fun x => x ^ r ≤ n) (m := 0) (Nat.zero_le n)
    (by simp [zero_pow hr.ne']), ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : Nat.findGreatest (fun x => x ^ r ≤ n) n + 1 ≤ (Nat.findGreatest (fun x => x ^ r ≤ n) n + 1) ^ r :=
    Nat.le_self_pow hr.ne' _
  have h2 := Nat.findGreatest_is_greatest (P := fun x => x ^ r ≤ n)
    (Nat.lt_succ_self (Nat.findGreatest (fun x => x ^ r ≤ n) n))
    (by omega)
  exact h2 hcon

theorem witness_A2 : A2 witnessImpl := by
  classical
  refine ⟨fun lo hi h => ?_, fun lo hi h => ?_⟩
  · simp only [witnessImpl]
    have h' : hi ≤ 2 ^ 64 := h
    simp
    omega
  · simp only [witnessImpl]
    have h' : ¬ hi ≤ 2 ^ 64 := not_le.2 h
    simp
    omega

theorem witness_A3 : A3 witnessImpl := by
  refine ⟨fun n _ => ?_, fun n _ pe hpe => ?_⟩
  · simp [witnessImpl, Function.comp_def]
  · simp only [witnessImpl, List.mem_map] at hpe
    obtain ⟨p, _, rfl⟩ := hpe
    rfl

theorem witness_A4 : A4 witnessImpl := by
  classical
  refine ⟨fun p hp => ?_, fun n _ => ?_⟩
  · simp [witnessImpl, hp]
  · simp [witnessImpl]

theorem witness_A5 : A5 witnessImpl := by
  have hu := u_pos
  have hu1 : u ≤ 1 / 10 ^ 15 := u_le
  refine ⟨fun x y _ => ⟨u, by rw [abs_of_pos hu], rfl⟩, fun x y _ => ⟨-u, by rw [abs_neg, abs_of_pos hu], by
      simp only [witnessImpl]; ring⟩,
    fun x y _ => ⟨u, by rw [abs_of_pos hu], rfl⟩,
    fun x y _ _ => ⟨-u, 0, by rw [abs_neg, abs_of_pos hu], by rw [abs_zero]; exact lam_pos.le, by
      simp only [witnessImpl]; ring⟩,
    fun x y hx hy => ?_, fun n hn => ?_⟩
  · show 0 ≤ x / y * (1 - u)
    exact mul_nonneg (div_nonneg hx hy.le) (by linarith)
  · show (n : ℚ) * (1 - 2 * u) ≤ (n : ℚ) * (1 - 2 * u) ∧ (n : ℚ) * (1 - 2 * u) ≤ n
    refine ⟨le_rfl, ?_⟩
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    nlinarith

/-- A1–A5 hold together. -/
theorem assumptions_satisfiable : ∃ I : Impl, A1 I ∧ A2 I ∧ A3 I ∧ A4 I ∧ A5 I :=
  ⟨witnessImpl, witness_A1, witness_A2, witness_A3, witness_A4, witness_A5⟩

/-- A hash the program accepts: `(220, 284)`'s. -/
theorem validHash_exists : ValidHash ([⟨1, 0⟩, ⟨1, 0⟩], [⟨1, 0⟩]) := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  intro s hs
  simp at hs
  subst hs
  simp

/-- The whole premise list of `MainTheorem` is jointly satisfiable: primitives meeting A1–A5, an
accepted hash, `k > 0`, and a report meeting A6 (here with `Run` the run that reports the
witness report). -/
theorem mainTheorem_premises_satisfiable :
    ∃ (I : Impl) (H : Hash) (k : ℕ) (R : KReport),
      A1 I ∧ A2 I ∧ A3 I ∧ A4 I ∧ A5 I ∧ ValidHash H ∧ 0 < k ∧
        A6 R.Item R.queued R.executed R.stopped ∧ MainTheoremFor H k R :=
  ⟨witnessImpl, _, 4, ⟨True, none, ∅, ∅, T _ 4, Unit, ∅, ∅, False⟩,
    witness_A1, witness_A2, witness_A3, witness_A4, witness_A5, validHash_exists, by norm_num,
    ⟨fun _ => Set.empty_subset _⟩, mainTheoremFor_witness _ _⟩

end Amicable
