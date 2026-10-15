/-
  §13 of exhaustive_search_proof.md: resuming a stopped single-k / skipped run.

  The search of one k is modelled as a tree given by a children function `ch`:
  `ch p` lists the values of the children of the node with path `p = (root, q1, …)`,
  in the order the search visits them.  A node with no children is a leaf (a tail
  together with its final checks; a Progression tail's `u` is one more level, §13).
  `run ch d p r` lists the leaves the search visits below `p` (depth bound `d`), either the
  whole subtree (`r = none`) or a restart from the point `p ++ X` (`r = some X`), which at each
  node on the point's path starts the children at the point's next entry (by value).

  Proven here:
  * `before_iff_lt_not_prefix` : the recursive `Before` is the proof's definition
    "L < X lexicographically and X does not begin with L".
  * `ple_iff_le` : the order used on points is the standard lexicographic order on
    lists (the one `std::vector<uint64_t>::operator<` implements, a proper prefix is smaller).
  * `mem_restart_iff` : a run restarted from `X` visits exactly the leaves that do not lie
    before `X`.  So the leaves before `X` plus the restart cover every leaf (`restart_covers`),
    and nothing before `X` is redone.
  * `leaves_pairwise_before` : with children in increasing order the search visits its leaves
    in strictly increasing order, so the leaves before any point form an initial segment of
    the search (`before_initial_segment`).
  * `restart_covers_of_ple`, `ple_prefix`, `ple_last_le`, `decVal_take_le` : an earlier point
    (a truncated point, a point whose last number lost digits, or the empty point) is still
    safe to restart from.
  * `point_sound` : the minimum of the component points (generator, unfinished pieces) is a
    sound point when each component is sound for the leaves it owns.
-/
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

namespace Amicable.Resume

/-- A point or a leaf of one k's search: `(root, q1, q2, …)`. -/
abbrev Path := List ℕ

/-- `Before L X`: at the first position where `L` and `X` both have an entry and differ,
`L`'s entry is the smaller one. -/
def Before : Path → Path → Prop
  | [], _ => False
  | _ :: _, [] => False
  | a :: L, b :: X => a < b ∨ (a = b ∧ Before L X)

@[simp] theorem before_nil_left (X : Path) : ¬ Before [] X := fun h => h

@[simp] theorem before_nil_right (L : Path) : ¬ Before L [] := by
  cases L <;> exact fun h => h

@[simp] theorem before_cons_cons {a b : ℕ} {L X : Path} :
    Before (a :: L) (b :: X) ↔ a < b ∨ (a = b ∧ Before L X) := Iff.rfl

/-- The proof's definition (§13): "`L` lies before `X` when `L < X` and `X` does not begin
with `L`". -/
theorem before_iff_lt_not_prefix (L X : Path) : Before L X ↔ L < X ∧ ¬ L <+: X := by
  induction L generalizing X with
  | nil => simp
  | cons a L ih =>
    cases X with
    | nil => simp
    | cons b X =>
      rw [before_cons_cons, List.cons_lt_cons_iff, List.cons_prefix_cons, ih]
      constructor
      · rintro (h | ⟨rfl, h1, h2⟩)
        · exact ⟨Or.inl h, fun h' => absurd h'.1 (Nat.ne_of_lt h)⟩
        · exact ⟨Or.inr ⟨rfl, h1⟩, fun h' => h2 h'.2⟩
      · rintro ⟨h | ⟨rfl, h1⟩, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl, h1, fun h' => h2 ⟨rfl, h'⟩⟩

theorem before_append_left (p L X : Path) : Before (p ++ L) (p ++ X) ↔ Before L X := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [ih]

theorem before_append_right {L X : Path} (M : Path) (h : Before L X) : Before L (X ++ M) := by
  induction L generalizing X with
  | nil => exact absurd h (before_nil_left _)
  | cons a L ih =>
    cases X with
    | nil => exact absurd h (before_nil_right _)
    | cons b X =>
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, ih h⟩

/-- A leaf on the point's own path (the point begins with it) is not before the point. -/
theorem not_before_of_prefix_left {L X : Path} (h : L <+: X) : ¬ Before L X := by
  obtain ⟨M, rfl⟩ := h
  have := before_append_left L [] M
  simp only [List.append_nil] at this
  rw [this]; exact before_nil_left _

/-- A leaf inside the point's subtree (it begins with the point) is not before the point. -/
theorem not_before_of_prefix_right {L X : Path} (h : X <+: L) : ¬ Before L X := by
  obtain ⟨M, rfl⟩ := h
  have := before_append_left X M []
  simp only [List.append_nil] at this
  rw [this]; exact before_nil_right _

theorem before_trans {A B C : Path} (h1 : Before A B) (h2 : Before B C) : Before A C := by
  induction A generalizing B C with
  | nil => exact absurd h1 (before_nil_left _)
  | cons a A ih =>
    cases B with
    | nil => exact absurd h1 (before_nil_right _)
    | cons b B =>
      cases C with
      | nil => exact absurd h2 (before_nil_right _)
      | cons c C =>
        rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
        · exact Or.inl (Nat.lt_trans h1 h2)
        · exact Or.inl h1
        · exact Or.inl h2
        · exact Or.inr ⟨rfl, ih h1 h2⟩

theorem before_irrefl (L : Path) : ¬ Before L L :=
  not_before_of_prefix_left (List.prefix_refl L)

/-! ### The order on points -/

/-- `PLe X Y`: `X` is a prefix of `Y` or lies before it, i.e. `X ≤ Y` lexicographically
(`ple_iff_le`). -/
def PLe (X Y : Path) : Prop := X <+: Y ∨ Before X Y

theorem ple_iff_le (X Y : Path) : PLe X Y ↔ X ≤ Y := by
  unfold PLe
  induction X generalizing Y with
  | nil => simp
  | cons a X ih =>
    cases Y with
    | nil => simp
    | cons b Y =>
      rw [List.cons_le_cons_iff, List.cons_prefix_cons, before_cons_cons, ← ih]
      constructor
      · rintro (⟨rfl, h⟩ | h | ⟨rfl, h⟩)
        · exact Or.inr ⟨rfl, Or.inl h⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl, Or.inr h⟩
      · rintro (h | ⟨rfl, h | h⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr (Or.inr ⟨rfl, h⟩)

/-- Moving the point later never un-finishes a leaf: a leaf before `X` is before every
`Y ≥ X`. -/
theorem before_of_before_of_ple {L X Y : Path} (h : Before L X) (hXY : PLe X Y) :
    Before L Y := by
  rcases hXY with ⟨M, rfl⟩ | hXY
  · exact before_append_right M h
  · exact before_trans h hXY

/-- A point with entries dropped from its end (in particular the empty point) is earlier. -/
theorem ple_prefix {X' X : Path} (h : X' <+: X) : PLe X' X := Or.inl h

/-- A point whose last entry is smaller is earlier. -/
theorem ple_last_le (I : Path) {a' a : ℕ} (h : a' ≤ a) : PLe (I ++ [a']) (I ++ [a]) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · right
    rw [before_append_left]
    exact Or.inl h
  · exact Or.inl (List.prefix_refl _)

/-- Value of a decimal digit string, most significant digit first. -/
def decVal (ds : List ℕ) : ℕ := ds.foldl (fun acc d => 10 * acc + d) 0

theorem foldl_dec_ge (l : List ℕ) (acc : ℕ) :
    acc ≤ l.foldl (fun acc d => 10 * acc + d) acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons d l ih => exact Nat.le_trans (by omega) (ih (10 * acc + d))

/-- A number that lost digits from its end (a cut during a rewrite) is not larger. -/
theorem decVal_take_le (ds : List ℕ) (m : ℕ) : decVal (ds.take m) ≤ decVal ds := by
  conv_rhs => rw [← List.take_append_drop m ds]
  unfold decVal
  rw [List.foldl_append]
  exact foldl_dec_ge _ _

/-! ### The search tree and the restart -/

/-- The leaves visited below node `p`, with depth bound `d`.  `r = none`: the whole subtree.
`r = some X`: a restart from the point `p ++ X`: on the point's path the children with a value
below the point's next entry are skipped, the child equal to it continues along the point, and
the rest are searched whole.  A missing entry (`some []`) means the start of the level. -/
def run (ch : Path → List ℕ) : ℕ → Path → Option Path → List Path
  | 0, p, _ => [p]
  | d + 1, p, r =>
    if ch p = [] then [p] else
    (ch p).flatMap fun c =>
      match r with
      | some (x :: xs) =>
          if c < x then [] else if c = x then run ch d (p ++ [c]) (some xs)
          else run ch d (p ++ [c]) none
      | _ => run ch d (p ++ [c]) none

/-- All leaves of the search (depth bound `D`). -/
def leaves (ch : Path → List ℕ) (D : ℕ) : List Path := run ch D [] none

/-- The leaves visited by a run restarted from the point `X`. -/
def restart (ch : Path → List ℕ) (D : ℕ) (X : Path) : List Path := run ch D [] (some X)

theorem prefix_of_mem_run (ch : Path → List ℕ) :
    ∀ (d : ℕ) (p : Path) (r : Option Path) (L : Path), L ∈ run ch d p r → p <+: L := by
  intro d
  induction d with
  | zero =>
    intro p r L h
    simp only [run, List.mem_singleton] at h
    exact h ▸ List.prefix_refl _
  | succ d ih =>
    intro p r L h
    unfold run at h
    split_ifs at h with hch
    · simp only [List.mem_singleton] at h; exact h ▸ List.prefix_refl _
    · rw [List.mem_flatMap] at h
      obtain ⟨c, _, hc⟩ := h
      have key : ∀ r', L ∈ run ch d (p ++ [c]) r' → p <+: L := fun r' h' =>
        (List.prefix_append p [c]).trans (ih _ _ _ h')
      rcases r with _ | ⟨_ | ⟨x, xs⟩⟩
      · exact key _ hc
      · exact key _ hc
      · dsimp only at hc
        split_ifs at hc
        · simp at hc
        · exact key _ hc
        · exact key _ hc

/-- **Restart (§13).** A run restarted from `p ++ X` visits exactly the leaves of the subtree
of `p` that do not lie before `p ++ X`. -/
theorem mem_run_some_iff (ch : Path → List ℕ) :
    ∀ (d : ℕ) (p X L : Path),
      L ∈ run ch d p (some X) ↔ L ∈ run ch d p none ∧ ¬ Before L (p ++ X) := by
  intro d
  induction d with
  | zero =>
    intro p X L
    simp only [run, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, not_before_of_prefix_left (List.prefix_append _ _)⟩
    · exact fun h => h.1
  | succ d ih =>
    intro p X L
    unfold run
    split_ifs with hch
    · simp only [List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, not_before_of_prefix_left (List.prefix_append _ _)⟩
      · exact fun h => h.1
    · simp only [List.mem_flatMap]
      cases X with
      | nil =>
        simp only [List.append_nil]
        constructor
        · rintro ⟨c, hc, hL⟩
          exact ⟨⟨c, hc, hL⟩, not_before_of_prefix_right
            ((List.prefix_append p [c]).trans (prefix_of_mem_run ch d _ _ _ hL))⟩
        · exact fun h => h.1
      | cons x xs =>
        constructor
        · rintro ⟨c, hc, hL⟩
          dsimp only at hL
          split_ifs at hL with h1 h2
          · simp at hL
          · subst h2
            rw [ih] at hL
            refine ⟨⟨c, hc, hL.1⟩, ?_⟩
            simpa using hL.2
          · refine ⟨⟨c, hc, hL⟩, ?_⟩
            obtain ⟨s, rfl⟩ := prefix_of_mem_run ch d _ _ _ hL
            rw [List.append_assoc, before_append_left]
            simp only [List.singleton_append, before_cons_cons]
            omega
        · rintro ⟨⟨c, hc, hL⟩, hnb⟩
          refine ⟨c, hc, ?_⟩
          dsimp only
          split_ifs with h1 h2
          · exfalso
            obtain ⟨s, rfl⟩ := prefix_of_mem_run ch d _ _ _ hL
            apply hnb
            rw [List.append_assoc, before_append_left]
            exact Or.inl h1
          · subst h2
            rw [ih]
            exact ⟨hL, by simpa using hnb⟩
          · exact hL

/-- **Restart (§13), from the root.** A run restarted from the point `X` visits exactly the
leaves that do not lie before `X`. -/
theorem mem_restart_iff (ch : Path → List ℕ) (D : ℕ) (X L : Path) :
    L ∈ restart ch D X ↔ L ∈ leaves ch D ∧ ¬ Before L X := by
  simpa [restart, leaves] using mem_run_some_iff ch D [] X L

/-- **Coverage (§13).** Every leaf lies before `X` (finished, by the point's claim) or is
visited by the run restarted from `X`. -/
theorem restart_covers (ch : Path → List ℕ) (D : ℕ) (X : Path) :
    ∀ L ∈ leaves ch D, Before L X ∨ L ∈ restart ch D X := by
  intro L hL
  by_cases h : Before L X
  · exact Or.inl h
  · exact Or.inr ((mem_restart_iff ch D X L).mpr ⟨hL, h⟩)

/-- Restarting from any earlier point `X' ≤ X` (e.g. a truncated one, or one where the program
follows only the first entries of `X` and runs the rest whole) still covers every leaf. -/
theorem restart_covers_of_ple (ch : Path → List ℕ) (D : ℕ) {X' X : Path} (h : PLe X' X) :
    ∀ L ∈ leaves ch D, Before L X ∨ L ∈ restart ch D X' := by
  intro L hL
  rcases restart_covers ch D X' L hL with h' | h'
  · exact Or.inl (before_of_before_of_ple h' h)
  · exact Or.inr h'

/-! ### The search order -/

theorem run_pairwise_before (ch : Path → List ℕ) (hsorted : ∀ p, (ch p).Pairwise (· < ·)) :
    ∀ (d : ℕ) (p : Path), (run ch d p none).Pairwise Before := by
  intro d
  induction d with
  | zero => intro p; simp [run]
  | succ d ih =>
    intro p
    unfold run
    split_ifs with hch
    · simp
    · rw [List.pairwise_flatMap]
      refine ⟨fun c _ => ih _, (hsorted p).imp fun {c1 c2} hlt => ?_⟩
      intro x hx y hy
      obtain ⟨s, rfl⟩ := prefix_of_mem_run ch d _ _ _ hx
      obtain ⟨t, rfl⟩ := prefix_of_mem_run ch d _ _ _ hy
      rw [List.append_assoc, List.append_assoc, before_append_left]
      exact Or.inl hlt

/-- **The search order (§13).** With the children of every node visited in increasing order,
the search visits its leaves in strictly increasing order (`Before`). -/
theorem leaves_pairwise_before (ch : Path → List ℕ) (hsorted : ∀ p, (ch p).Pairwise (· < ·))
    (D : ℕ) : (leaves ch D).Pairwise Before :=
  run_pairwise_before ch hsorted D []

/-- The leaves before a point form an initial segment of the search order. -/
theorem before_initial_segment {l : List Path} (hl : l.Pairwise Before) (X : Path)
    {i j : ℕ} (hij : i < j) (hj : j < l.length) (hb : Before l[j] X) :
    Before l[i] X :=
  before_trans (List.pairwise_iff_getElem.mp hl i j (Nat.lt_trans hij hj) hj hij) hb

/-! ### The point is the minimum of the component points -/

/-- **The point (§13).** The search's leaves are covered by components (the generator, and
every queued piece), each with a point `c.1` and the set `c.2` of leaves it owns, or are already
finished.  If each component is sound for its own leaves (its leaves before its point are
finished) and `X` is at most every component point, then every leaf before `X` is finished. -/
theorem point_sound (lvs : List Path) (finished : Path → Prop)
    (comps : List (Path × (Path → Prop)))
    (hcover : ∀ L ∈ lvs, finished L ∨ ∃ c ∈ comps, c.2 L)
    (hsound : ∀ c ∈ comps, ∀ L, c.2 L → Before L c.1 → finished L)
    (X : Path) (hX : ∀ c ∈ comps, PLe X c.1) :
    ∀ L ∈ lvs, Before L X → finished L := by
  intro L hL hb
  rcases hcover L hL with h | ⟨c, hc, hLc⟩
  · exact h
  · exact hsound c hc L hLc (before_of_before_of_ple hb (hX c hc))

end Amicable.Resume
