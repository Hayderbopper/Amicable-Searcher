# Open items (not proved in Lean yet)

Everything in this folder is outside the library: `AmicableProof.lean` does not import it,
and nothing here is used by a proved theorem. `OpenGoals.lean` states Lemmas 6.2, 6.3 and 8.3
as propositions and checks that the library's theorems prove exactly them; `check.sh`
checks that it elaborates.

| proof section | statement | status | planned |
|---|---|---|---|
| §1–§3 | definitions, Lemmas 3.1–3.3, (P), Cor. 3.4 | **proved** (library) | — |
| §13 | search order, restart cover, truncated points, min of points | **proved** (library), over an abstract tree; the concurrency premises of `point_sound` are assumed | M2: derive them from a model of `Engine::status` |
| App. B | pre-screen = exact test, FMA, underflow | **proved** (library) | — |
| §1.4 | Main Theorem | **stated** (`MainStatement.lean`) | M3 |
| §5 | every k processed once; frontier | open | M2 (model) |
| §6.1 | Lemma 6.1 (configuration built) | open | M3 |
| §6.2 | Lemma 6.2 (abundant k) | **proved** (`Search.lean`, `lemma_6_2`) | — |
| §6.2 | Lemma 6.3 (dead configuration) | **proved** (`Search.lean`, `lemma_6_3`) | — |
| §6.2 | Lemma 6.4 (σ(K) factorizations checked) | open | M2 (A3 + product check) |
| §7 | Lemma 7.1 (some root's rules hold) | open | M3 |
| §8.1 | Lemma 8.1 (`make_child` accepts q*) | open | M3 |
| §8.2 | Lemma 8.2 (true prime passes U and L) | open | M3 |
| §8.2 | Lemma 8.3 (monotone) | **proved** (`Search.lean`, `FP.lemma_8_3`) | — |
| §8.3 | Lemma 8.4 (bisection) | **proved** (`Search.lean`, `lemma_8_4`) | — |
| §8.3 | `find_lower`/`find_upper`, L(∞), 2^400 cap | open | M3 |
| §8.4 | Lemma 8.5 (extra exact filter) | open | M3 |
| §8.5 | Lemma 8.6 (next node visited), blocks partition `[lo, hi]` | open | M3 |
| §9.2, §9.3, §9.5 | the algebra of the tails: SameSide equations, Mixed2 closed form, Divisor3's `D'(u) ∣ R*`, Lemma 9.2 | **proved** (`Search.lean`) | — |
| §9.1–9.5 | the tails as the code runs them: Done, SameSide walker, Mixed2 with `integer_roots` (Lemma 9.1), Progression, Divisor3's divisor enumeration, Lemma 9.3 | open | M3 |
| §10 | final check: soundness and completeness | open | M2 (soundness), M3 |
| §11 | assembly of the Main Theorem | open | M3 |
| §12 | termination and "incomplete" | open | M2 |
