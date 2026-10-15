/-
  §1.4 of exhaustive_search_proof.md: the exact statement of the Main Theorem, against an
  interface that both the program and the Lean model of it (milestone M2) report through.

  This file only *states* the theorem (as a `Prop`); it proves nothing about the search.
  The proof is open: see `Open/README.md`.
-/
import AmicableProof.Defs
import AmicableProof.Assumptions

namespace Amicable

/-- The reasons a `k` is written to `incomplete.txt` (§1.4, §12). -/
inductive IncReason
  /-- a time limit was set and reached -/
  | timeout
  /-- some prime's proven range could not be capped below `2^400` ("bound_not_finite") -/
  | boundNotFinite
  /-- a range lies beyond `2^64`, where primesieve cannot scan it ("range_beyond_2^64") -/
  | rangeBeyond64
  deriving DecidableEq, Repr

/-- The hashes the program accepts (`hash_spec.cpp`): both members have a slot, at most 16
slots in all, every exponent `e` in `[1, 1000]`, every multiplicity `b` at most 1000. -/
def ValidHash (H : Hash) : Prop :=
  H.1 ≠ [] ∧ H.2 ≠ [] ∧ H.1.length + H.2.length ≤ 16 ∧
  ∀ s ∈ H.1 ++ H.2, 1 ≤ s.e ∧ s.e ≤ 1000 ∧ s.b ≤ 1000

/-- What one run (in any mode: `range`, `single`, `skipped`) reports about one `k` it
processed.  `fileAfter` is the mode's results file after the run (`multi_k_results.txt` for
`range` and `skipped`, `single_k_results.txt` for `single`), including lines written by earlier
runs; `writtenNow` the pairs this run wrote for `k`.  `Item`, `queued`, `executed`, `stopped`
describe the run's work items, for A6. -/
structure KReport where
  finished : Prop
  incomplete : Option IncReason
  events : Set IncReason
  writtenNow : Set (ℕ × ℕ)
  fileAfter : Set (ℕ × ℕ)
  Item : Type
  queued : Set Item
  executed : Set Item
  stopped : Prop

/-- **Main Theorem (§1.4) for one hash `H` and one `k`.**
* completeness: if `k` was finished and is not listed in `incomplete.txt`, every pair of
  `T(H, k)` is in the mode's results file;
* soundness: every pair written for `k` is an amicable pair with hash `H` and `gcd = k`;
* `k` is listed in `incomplete.txt` only with one of the three reasons, and only if that
  event happened during its search. -/
def MainTheoremFor (H : Hash) (k : ℕ) (R : KReport) : Prop :=
  ((R.finished ∧ R.incomplete = none) → T H k ⊆ R.fileAfter) ∧
  R.writtenNow ⊆ T H k ∧
  (∀ r, R.incomplete = some r → r ∈ R.events)

/-- **Main Theorem (§1.4).** For a model `Run` of `multi_k_searcher` with the general engine
(`Run I H k R`: a run with primitives `I` and hash `H` may report `R` for `k`), under A1–A5
for the primitives and A6 for the run. -/
def MainTheorem (Run : Impl → Hash → ℕ → KReport → Prop) : Prop :=
  ∀ (I : Impl), A1 I → A2 I → A3 I → A4 I → A5 I →
    ∀ (H : Hash) (k : ℕ) (R : KReport), ValidHash H → 0 < k → Run I H k R →
      A6 R.Item R.queued R.executed R.stopped → MainTheoremFor H k R

/-- The interface is not vacuous: a report that lists nothing as incomplete, wrote nothing,
and whose file holds exactly `T(H, k)` satisfies the statement, while a report that finished
`k`, lists nothing, and whose file misses a pair of `T(H, k)` violates it. -/
theorem mainTheoremFor_witness (H : Hash) (k : ℕ) :
    MainTheoremFor H k ⟨True, none, ∅, ∅, T H k, Unit, ∅, ∅, False⟩ := by
  refine ⟨fun _ => le_refl _, fun _ h => absurd h (Set.notMem_empty _), fun r h => ?_⟩
  cases h

theorem mainTheoremFor_detects_miss (H : Hash) (k : ℕ) (π : ℕ × ℕ) (hπ : π ∈ T H k)
    (file : Set (ℕ × ℕ)) (hmiss : π ∉ file) :
    ¬ MainTheoremFor H k ⟨True, none, ∅, ∅, file, Unit, ∅, ∅, False⟩ := by
  intro h
  exact hmiss (h.1 ⟨trivial, rfl⟩ hπ)

end Amicable
