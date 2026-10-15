# Lean check of `exhaustive_search_proof.md` — milestone M1, and the update for publication

## 0. Update for publication (October 2026)

Sections 1–11 below are the M1 report as written; this section lists what changed since.

* **New module `AmicableProof/Search.lean`**, proved with no `sorry` and no extra axioms:
  `abund_le_of_dvd` (a divisor is at most as abundant), **Lemma 6.2** (`lemma_6_2`),
  **Lemma 6.3** (`lemma_6_3`), **Lemma 8.3** (`FP.lemma_8_3`, with `Xexact_anti`),
  **Lemma 8.4** (`bisect`, `bisect_spec`, `lemma_8_4`), the SameSide equations (`sameSide`,
  `sameSide_two`), the Mixed2 closed form (`mixed2`, `mixed2_D_ne_zero`), the Divisor3 divisor
  condition `D'(u) ∣ R*` (`divisor3_D`, `divisor3_dvd`) and **Lemma 9.2** (`lemma_9_2`).
  `Open/OpenGoals.lean` now checks that the library's statements of 6.2, 6.3 and 8.3 are
  exactly the ones it used to list as open. The audit counts 208 theorems.
* These are the mathematical facts the search relies on. Still open: the **model of the
  program** (M2) and the proof of the Main Theorem for it (M3). The lemmas that are about what
  the program does (6.1, 6.4, 7.1, 8.1, 8.2, 8.5, 8.6, 9.1, 9.3, §10–§12) need that model.
* **The special engine was removed** from the program; the proof and the Lean statements only
  ever covered the general engine.
* `patches/proof_text_m1.patch` (F1–F4) has been applied to `exhaustive_search_proof.md` and
  is no longer shipped.
* **The check scripts were fixed.** On Windows the old `check.ps1` looked hung: `lake`'s
  full clone of Mathlib failed (`fetch-pack: invalid index-pack output`), and the script then
  built Mathlib from source with all output hidden. Both scripts now download each
  dependency as a shallow copy of exactly the pinned commit (step 2), show the build's progress
  as it runs, and `check.ps1` gives up on the Mathlib cache after 15 minutes. Run for this
  version: `SKIP_CACHE=1 bash check.sh --selftest` and `check.ps1 -SkipCache` (PowerShell 7 on
  Linux), both `ALL CHECKS PASSED`, with Mathlib built from source (the cache is blocked from that
  machine).

Checked files (md5, first 8 hex digits): `exhaustive_search_proof.md` ff2a512c,
`README.md` fdb0e4ae, `general.cpp` e9a5cc4a, `engine.cpp` 75d02f2a,
`multi_k_main.cpp` 015d84fa, `hash_spec.cpp` f489f597 (identical on your disk on 10 Oct).
Nothing in `Data\`, `Old_Data\` or `config.txt` was read. (These hashes are of the files as
they were for M1, before the update of section 0.)

## 1. Result

M1 covers the definitions (§1), the three basic facts (§3), resuming (§13) and the
floating-point pre-screen (Appendix B), plus the exact statement of the Main Theorem.
Every proof is checked by Lean's kernel: 190 theorems (45 of them generated equation lemmas),
no `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`, and 0 build
warnings from a clean rebuild of the library. The Main Theorem is stated (and type-checked),
not proved.

* **The statement is not vacuous.** `Consistency.lean` builds an `Impl` that satisfies A1–A5
  together (integer arithmetic, prime ranges, factorization and primality exact; every
  floating-point operation perturbed by the *largest* error A5 allows, so A5 does not force
  exactness), a valid hash, `k > 0`, and a report meeting A6 and `MainTheoremFor`
  (`mainTheorem_premises_satisfiable`). So the premises of `MainTheorem` are jointly
  satisfiable. This says nothing about whether the real program meets A1–A5; that stays an
  assumption.

* **No error that could make the program miss a pair** was found in these parts, in the
  proof or in the code it describes.
* The pre-screen is now proved to agree with the exact test whenever it decides, with the
  code's own margin `ε = max(1e-13, 16(n+3)·2⁻⁵³)`, for every hash the program accepts,
  including fused multiply-add and floating-point underflow (which the written proof does not
  mention).
* Four places in the written proof state less than they use (F1–F4 below, all low severity);
  `patches/proof_text_m1.patch` adds the missing premises to the text.
* What M1 does **not** do: the model of the search (§4–§10), the Main Theorem's proof, and the
  differential tests against the program. Those are milestones M2 and M3 (section 10).

## 2. How to run

Pinned: Lean `leanprover/lean4:v4.34.1` (`lean-toolchain`), Mathlib `v4.34.1` =
commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, all other packages in
`lake-manifest.json`.

* **Linux / macOS / WSL**: `bash check.sh` (add `--selftest` to also prove the checks reject a
  planted `sorry` and a planted `axiom`; `SKIP_CACHE=1` skips `lake exe cache get`). Needs
  [elan](https://github.com/leanprover/elan).
* **Windows**: `powershell -ExecutionPolicy Bypass -File .\check.ps1` (`-SelfTest`,
  `-SkipCache`). It installs elan from the official script if it is missing (no default
  toolchain; the pinned one is used).

Both scripts: check the pins → fetch the pinned dependencies (shallow) → `lake exe cache get`
→ `lake build` → grep the library for
`sorry admit native_decide unsafe implemented_by extern` and `axiom` declarations →
`CheckAxioms.lean` (the axioms of every theorem, as `#print axioms` gives them; fails on
anything else, and on `axiom`/`unsafe`/`implemented_by`/`extern` declarations) → elaborate
`Open/`. Logs go to `logs/`.

**Mathlib cache.** `lake exe cache get` works from this machine (8908 files from
`cache.mathlib.org`; `logs/cache.log` of the earlier run, from a machine where it was blocked,
is kept). One snag: `lake`'s own full-history clone of the Mathlib repository stalled, so the
nine pinned packages were fetched with `git fetch --depth 1 <rev>` at exactly the commits of
`lake-manifest.json` first; `lake` then used them as they were.

**What was run for this version** (Debian on WSL, Lean 4.34.1, the pinned Mathlib):
`SKIP_CACHE=1 bash check.sh --selftest` after `lake exe cache get`, ending `ALL CHECKS PASSED`
(`logs/check.log`); and a clean rebuild of the library (`rm -rf .lake/build; lake build`):
`Build completed successfully (1231 jobs)`, 0 warnings. `check.ps1` was **not** rerun for this
version (it was run for the previous one, which differs only by `Consistency.lean`).

## 3. Proven, assumed, gap

| item | status | where |
|---|---|---|
| σ, amicable pair, slots, hash, k, T(H,k); each pair in exactly one T(H,k) | proved | `Defs.lean` |
| the definitions give the README's hashes for (220,284), (1184,1210), (6232,6368) | proved | `Sanity.lean` |
| Lemma 3.1, Lemma 3.2 (all three parts), Lemma 3.3 / (E), (P), Corollary 3.4 | proved | `Basic.lean` |
| a slot `(e,b)`'s prime divides k exactly b times; bound/free slots = the hash's b>0 / b=0 slots | proved | `Basic.lean` |
| §13: the proof's "before" = lexicographic order with "X does not begin with L"; that order = `std::vector` `operator<` | proved | `Resume.lean` |
| §13: a run restarted from X visits exactly the leaves not before X (so the two cover every leaf); leaves are visited in increasing order; leaves before X form an initial segment | proved, for any search tree | `Resume.lean` |
| §13: a cut point (dropped entries, shortened last number, empty file) is earlier, so still safe | proved | `Resume.lean` |
| §13: the minimum of the component points is sound if each component is sound for its leaves | proved; the per-component premises are **assumed** (concurrency in `engine.cpp`, M2) | `Resume.lean` |
| App. B: `h_ld`, `ipow_ld`, the floating factors, `ratio_d`, conversions: error bounds | proved (with underflow) | `FP.lean` |
| App. B: `upper_ok = upper_ok_exact`, `lower_ok = lower_ok_exact` (any FMA contraction) | proved | `FP.lean` |
| App. B: `upper_ok_exact` ⇔ U, `lower_ok_exact` ⇔ L, integers = the fractions of §8.2 | proved | `FP.lean` |
| A1–A6 | **assumed**, as hypothesis structures (never `axiom`) | `Assumptions.lean` |
| A1–A5 are jointly satisfiable; a valid hash, `k > 0`, an A6 report exist; so `MainTheorem`'s premises are not contradictory | proved | `Consistency.lean` |
| Main Theorem | **stated** only | `MainStatement.lean` |
| §4–§12 | **open** | `Open/README.md` |

## 4. Statement audit (what each theorem says, in plain mathematics)

`σ` is Mathlib's `ArithmeticFunction.sigma 1` (sum of divisors), `v_p` is `Nat.factorization`.

**Definitions (`Defs.lean`)**
* `IsAmicablePair N1 N2`: `0 < N1 < N2` and `σ(N1) = σ(N2) = N1 + N2`. §1.2 omits `0 < N1`;
  it changes nothing (σ(0)=0 in Mathlib makes (AP) fail for N1 = 0).
* `slotsOf M N`: for the primes p with `v_p(N) < v_p(M)`, in increasing order, the slot
  `(v_p(M) − v_p(N), v_p(N))`. `hashOf N1 N2 = (slotsOf N1 N2, slotsOf N2 N1)`. Matches §1.3.
* `T H k = {(N1,N2) amicable : hashOf N1 N2 = H, gcd(N1,N2) = k}`. Matches §1.4.
* `T_partition`: every amicable pair lies in `T(hashOf, gcd)` and in no other `T(H,k)`.
* `sanity_*`: `(220,284) ∈ T([(1,0),(1,0)] _ [(1,0)], 4)`, `(1184,1210) ∈ T([(4,1),(1,0)] _ [(1,0),(2,0)], 2)`,
  `(6232,6368) ∈ T([(1,0),(1,0)] _ [(2,3),(1,0)], 8)`, `(220,285)` in no `T`. These guard
  against a definition that is well typed but wrong.

**§3 (`Basic.lean`)**, with `h(n) = σ(n)/n` in ℚ:
* `abundancy_identity`: for an amicable pair, `(h(N1)−1)(h(N2)−1) = 1`, `h(N1) > 2`, `1 < h(N2) < 2`. = Lemma 3.1.
* `abund_prime_pow`: `h(p^e) = Σ_{i≤e} p^{-i}` for p prime.
* `abund_prime_pow_bounds`: p prime, `e ≥ 1` ⇒ `1 < h(p^e) < p/(p−1)`; `abund_prime_pow_lt`: the upper bound for every `e ≥ 0`.
* `abund_prime_pow_lt_L`: p prime, `1 ≤ L < p` ⇒ `h(p^e) < (L+1)/L`.
* `abund_prime_pow_strictAnti`: primes `p < q`, `e ≥ 1` ⇒ `h(q^e) < h(p^e)`. (Lemma 3.2 says "strictly decreases" without `e ≥ 1`; for `e = 0` it is constant.)
* `slot_b_eq_vk`: for a slot prime of M, `v_p(gcd(M,N)) = v_p(N) = b`.
* `mem_boundSet_iff` / `mem_freeSet_iff`: the primes used for `K1` / `X` below are exactly the hash's slot primes with `b > 0` / `b = 0`.
* `decomposition`: for an amicable pair, with `k = gcd`, `K1 = k·∏_{bound side-0 slots} p^e`, `X = ∏_{free side-0 slots} p^e`, and `K2`, `Y` likewise: `N1 = K1·X`, `N2 = K2·Y`, `gcd(K1,X) = gcd(K2,Y) = 1`, `σ(K1)σ(X) = σ(K2)σ(Y) = K1X + K2Y`. = Lemma 3.3.
* `abund_grows`: `A, R > 0` coprime ⇒ `h(AR) = h(A)h(R) ≥ h(A)`, with `h(A) < h(AR)` iff `R > 1`. = (P) and Corollary 3.4 ("a prime remains" = `R > 1`).

**§13 (`Resume.lean`)**, a point/leaf is a list of naturals `(root, q1, q2, …)`. The search is
any tree given by `ch p` = the child values of node p in visiting order; `run` is the search
(whole, or restarted from a point: on the point's path, children below the point's next entry
are skipped, the child equal to it follows the point, the rest are searched whole — what
`generate`/`expand` do, by value).
* `before_iff_lt_not_prefix`: `Before L X` ⇔ `L < X` lexicographically and X does not begin with L. = the proof's definition.
* `ple_iff_le`: "X is a prefix of Y or X is before Y" ⇔ `X ≤ Y` in Lean's list order, which is `std::vector`'s `operator<` order (`Engine::status` takes the minimum with it).
* `mem_restart_iff`: L is visited by the run restarted from X ⇔ L is a leaf and not before X. `restart_covers`: every leaf is before X or visited by the restart.
* `leaves_pairwise_before`: if every node's children are visited in increasing order, each leaf of the search is before every later one. `before_initial_segment`: the leaves before X are an initial segment of the search.
* `restart_covers_of_ple`, `ple_prefix`, `ple_last_le`, `decVal_take_le`: if `X' ≤ X` (in particular X' = X with entries dropped from the end, or with its last number cut to fewer digits), every leaf is before X or visited by the restart from X'.
* `point_sound`: if every leaf is finished or owned by some component (generator or queued piece) whose leaves before its own point are finished, then every leaf before a point `X ≤` all component points is finished. The two premises are what §13's "three reasons" argue from `engine.cpp`; here they are assumptions (F5).

**Appendix B (`FP.lean`)**, `u = 2⁻⁵³`, `λ = 2⁻¹⁰⁷⁵`:
* Rounding model: each operation result `x(1+η)`, `|η| ≤ u`; divisions in `h_ld` may also add `ζ`, `|ζ| ≤ λ` (underflow); GMP conversions give `d ∈ [x(1−2u), x]`; rounding keeps nonnegative quotients nonnegative. FMA = a product with `η = 0`.
* `hS_A`: `h_ld(q̂, e)`, `q ≥ 2`, `q̂` within 3 roundings of q, `e ≤ 10⁹` ⇒ `H_e(q)(1−u)^{5e+1} ≤ ĥ` and `ĥ(1−u)^{5e+1} ≤ H_e(q)`.
* `IsXEval.approx`: every evaluation of `X = x0l·[h]·ipow_ld(1+1/q̂, j)·∏(1+1/L̂)` as the code writes it is within `N = 5e + 6j + 6f + 11` roundings of `X⁺ = x0·[H_e(q)]·((q+1)/q)^j·∏(L+1)/L`.
* `margin_ok`: `n ≤ 10⁸`, `ε ≥ 16(n+3)u` ⇒ with `D = 12(n+2)u`: `ε ≥ D + 2u` and `4ε(1−D)²(1−u)³ ≥ D(2+D) + 4u(1+D)² + u`.
* `upperExact_iff`: the integer test `upper_ok_exact` (`XN > 2XD`, `YN > YD`, `(XN−XD)(YN−YD) > XD·YD`) ⇔ `U(XN/XD, YN/YD)`; `lowerExact_iff` likewise for L; `XN_div_XD`: the code's integers (`sigma_and_pow`, `(q+1)^j`, `∏(L+1)`) give exactly `X⁺`.
* `upper_ok_eq_exact`: sx ≥ px > 0, sy ≥ py > 0, q ≥ 2, every L ≥ 1, `n = e+j0+j1+f ≤ 10⁸`, `16(n+3)u ≤ ε ≤ 1`, and any evaluations X (comparisons), Xp, Yp (product), Xe, Ye, Xe′, Ye′ (the two `err`s), any 11 rounding errors ⇒ `upper_ok = upper_ok_exact`. `lower_ok_eq_exact`: the same for `lower_filter` (`ε ≥ 16(e+3)u`). These are Appendix B's conclusion, "whenever the pre-screen decides, its answer equals the exact test".

**Main Theorem (`MainStatement.lean`)**, stated, not proved:
* `MainTheoremFor H k R`: (finished ∧ not listed ⇒ `T(H,k)` ⊆ the mode's results file after the run) ∧ (pairs written for k ⊆ `T(H,k)`) ∧ (listed with reason r ⇒ event r happened). The three reasons are `timeout`, `boundNotFinite`, `rangeBeyond64`. This is §1.4 sentence by sentence; "(or was already in it)" is why the file after the run, not only this run's lines, is used.
* `MainTheorem Run`: for every `Impl` satisfying A1–A5, every accepted hash (`ValidHash`: both sides nonempty, ≤ 16 slots, `1 ≤ e ≤ 1000`, `b ≤ 1000`, as `hash_spec.cpp`), every `k > 0` and every report of a run satisfying A6, `MainTheoremFor` holds.
* `mainTheoremFor_witness`, `mainTheoremFor_detects_miss`: the *conclusion* is satisfiable and a report missing a pair of `T(H,k)` violates it, so it has content. (This alone did not show that the *premises* A1–A5 can hold together; `Consistency.lean` below does.)

**Consistency of the premises (`Consistency.lean`)**
* `witnessImpl`: `mulMod = a·b mod m`; `iroot n r = max{x ≤ n : x^r ≤ n}`; `primesIn lo hi` = the primes of `[lo,hi]` if `hi ≤ 2⁶⁴`, else `none` (`maxStop = 2⁶⁴`); `factor n` = `(p, v_p(n))` over the increasing primes of `n`; `isPrime` = `Nat.Prime`; `fadd x y = (x+y)(1+u)`, `fsub = (x−y)(1−u)`, `fmul = xy(1+u)`, `fdiv = (x/y)(1−u)`; `toDouble n = n(1−2u)`. The last five take the worst errors A5 permits, so A5 is met by something that is not exact arithmetic.
* `witness_A1` … `witness_A5`, `assumptions_satisfiable`: `∃ I, A1 I ∧ A2 I ∧ A3 I ∧ A4 I ∧ A5 I`.
* `validHash_exists`: the hash of (220, 284) is `ValidHash`.
* `mainTheorem_premises_satisfiable`: some `I, H, k, R` satisfy A1–A5, `ValidHash H`, `0 < k`, A6 for `R`, and `MainTheoremFor H k R`.
* What this does **not** show: that `multi_k_searcher`'s primitives meet A1–A5 (primesieve, hurchalla/FLINT, GMP, the FPU are outside Lean), or anything about the search. It only rules out a theorem that is true because its hypotheses are contradictory.
* Audit remarks on the statements: `A2.exact` with `hi < lo` gives the empty list (natural subtraction); `A3` constrains `factor` only for `n > 0`; `A4` allows a probabilistic test above 2⁶⁴ (it only forbids rejecting a prime), and `isPrime = Nat.Prime` is one instance. I did not check these against the program's behaviour for degenerate inputs (`hi < lo`, `n = 0`); the proof does not call the primitives there as far as M1 goes. None of them needed a change to the statements.

**A1–A6 (`Assumptions.lean`)**: structures over `Impl`, the program's primitives. A1:
`mulMod a b m = ab mod m`, `iroot` exact. A2: `primesIn lo hi` = the primes of `[lo,hi]` for
`hi ≤ maxStop`, fatal beyond. A3: `factor n` = the factorization, primes increasing. A4:
`isPrime` never rejects a prime, exact below 2⁶⁴. A5: the rounding model above (results in the
normal range for `+ − ×`). A6: unless the run was stopped, every queued item is executed.

## 5. `#print axioms`

`logs/axioms.log` has one line per theorem (190, of which 45 generated equation lemmas).
Summary line: `AXIOM CHECK OK: 190 theorems; every one uses at most propext,
Classical.choice, Quot.sound; no axiom/unsafe/implemented_by/extern declarations.`
The main ones:

```
Amicable.T_partition                         Classical.choice, Quot.sound, propext
Amicable.abundancy_identity                  Classical.choice, Quot.sound, propext
Amicable.abund_prime_pow_bounds              Classical.choice, Quot.sound, propext
Amicable.abund_prime_pow_lt_L                Classical.choice, Quot.sound, propext
Amicable.abund_prime_pow_strictAnti          Classical.choice, Quot.sound, propext
Amicable.decomposition                       Classical.choice, Quot.sound, propext
Amicable.abund_grows                         Classical.choice, Quot.sound, propext
Amicable.Resume.before_iff_lt_not_prefix     Quot.sound, propext
Amicable.Resume.ple_iff_le                   Classical.choice, Quot.sound, propext
Amicable.Resume.mem_restart_iff              Quot.sound, propext
Amicable.Resume.restart_covers               Classical.choice, Quot.sound, propext
Amicable.Resume.leaves_pairwise_before       Quot.sound, propext
Amicable.Resume.restart_covers_of_ple        Classical.choice, Quot.sound, propext
Amicable.Resume.decVal_take_le               Quot.sound, propext
Amicable.Resume.point_sound                  (no axioms)
Amicable.FP.hS_A                             Classical.choice, Quot.sound, propext
Amicable.FP.IsXEval.approx                   Classical.choice, Quot.sound, propext
Amicable.FP.margin_ok                        Classical.choice, Quot.sound, propext
Amicable.FP.upper_ok_eq_exact                Classical.choice, Quot.sound, propext
Amicable.FP.lower_ok_eq_exact                Classical.choice, Quot.sound, propext
Amicable.mainTheoremFor_detects_miss         Classical.choice, Quot.sound, propext
Amicable.assumptions_satisfiable             Classical.choice, Quot.sound, propext
Amicable.mainTheorem_premises_satisfiable    Classical.choice, Quot.sound, propext
```

## 6. Correspondence, every section of the proof

Table 6a is what Lean covers (M1). Table 6b lists every other section with its C++ and says
what is not formalised; the C++ names in 6b are those of the proof's own Appendix A; I checked that each one
occurs in `Source/` (name present, not that it does what the proof says; the 6a rows were
carried over from the previous version of this report). Where a Lean name is `—`, there is none.

**6a. Covered by Lean**

| proof | Lean | C++ |
|---|---|---|
| §1.2–1.4 pair, hash, k, T | `IsAmicablePair`, `slotsOf`, `hashOf`, `T`, `T_partition` | `parse_hash_spec` (`hash_spec.cpp`); `emit` (`general.cpp`) |
| accepted hashes | `ValidHash` | `parse_hash_spec`: both sides nonempty, ≤ 16, `1 ≤ e`, numbers ≤ 1000 |
| Lemma 3.1 | `abundancy_identity` | the thresholds 2, 1 and 1 in `upper_ok_exact`, `lower_ok_exact` |
| Lemma 3.2 | `abund_prime_pow_*` | `(q+1)/q` and `(L+1)/L` factors in `upper_ok_exact`, `upper_filter` |
| Lemma 3.3 (E) | `decomposition`, `side_decomp`, `slot_b_eq_vk` | `build_search_k` (K1, K2), `root_node` (`sx = σ(K1)`, `px = K1`, …) |
| (P), Cor. 3.4 | `abund_mul`, `abund_grows` | `make_child` (`sx *= σ(q^e)`, `px *= q^e`) |
| §13 order | `Before`, `PLe`, `ple_iff_le` | `Engine::status` (`cand < best` on `std::vector<u64>`) |
| §13 restart | `run`, `mem_restart_iff`, `restart_covers` | `Engine::generate` (`ri < R[0]`), `expand` (`lo = R[ri]`, `child_on_path`, `resumed`), `split_progression` |
| §13 cut points | `ple_prefix`, `ple_last_le`, `decVal_take_le` | `on_tick` write order, `status_resume`, `parse_resume_token` (`multi_k_main.cpp`) |
| §13 the point | `point_sound` | `Engine::status`, `set_gen`, `push_job` |
| App. B `h_ld` | `hT`, `hS`, `hS_A` | `h_ld` |
| App. B powers, factors | `ipowC`, `prodL`, `onePlusInv` | `ipow_ld`, `1.0 + 1.0/ql`, `1.0 + 1.0/fl_d[i]` |
| App. B conversions | `A_trunc`, `ratio_d_A` | `big_d`, `ratio_d`, `mpz_get_d`; `static_cast<double>` (u64) |
| App. B filters | `upperDecide`, `lowerDecide`, `combine` | `upper_filter`, `lower_filter`, `upper_ok(_q)`, `lower_ok(_q)` |
| App. B margin | `margin_ok` | `filter_eps(ops)`, `FILTER_EPS` |
| exact tests | `sigmaPow`, `XN`, `XD`, `upperExact`, `lowerExact` | `sigma_and_pow`, `upper_ok_exact`, `lower_ok_exact` |
| §2 A1–A5 consistent | `witnessImpl`, `assumptions_satisfiable`, `mainTheorem_premises_satisfiable` | — (the program's primitives meeting A1–A5 is the assumption) |

**6b. Not formalised yet (every other section)**

| proof | Lean | C++ (Appendix A) | status |
|---|---|---|---|
| §1.4 Main Theorem | `MainTheoremFor`, `MainTheorem` (statement) | `emit`, results/`incomplete.txt` writers | stated; proof M3 |
| §2 A6 | `A6` (hypothesis) | the scheduler (`Engine::worker`, `run_item`) | assumed |
| §4 shape of the search | — | `Engine`, `run_k` | M2 model |
| §5 loop over k, frontier | — | `Engine::worker`, `run_k`, `k_done`, `generate` | M2 |
| §6.1 Lemma 6.1 configurations | — | `build_search_k` (`rec`, `add_config`) | M3 |
| §6.2 Lemmas 6.2, 6.3 early exits | `lemma_6_2`, `lemma_6_3` (statements, `Open/`) | start of `build_search_k`; checks in `add_config` | statements only |
| §6.2 Lemma 6.4 | — | `cached_sigma_nat`; product check in `add_config` | M2 (A3 + product) |
| §7 Lemma 7.1 roots | — | `make_shapes`, `split_shape`, `interleave`, `root_shapes` | M3 |
| §8.1 Lemma 8.1 | — | `root_node`, `make_child` | M3 (the (P)/(E) facts it uses are proved) |
| §8.2 Lemma 8.2 | — | `range_for`, `upper_ok(_exact)`, `lower_ok(_exact)` | M3 (the exact test = U/L is proved) |
| §8.2–8.3 Lemma 8.3 monotone | `lemma_8_3` (statement) | `upper_filter`, `lower_filter`, `find_upper`, `find_lower`, `refine_*`, `lower_ok_limit` | statement only |
| §8.3 Lemma 8.4 bisection, 2⁴⁰⁰ cap | — | `find_upper`, `find_lower` | M3 (floating-point side proved) |
| §8.4 Lemma 8.5 | — | first block of `range_for` | M3 |
| §8.5 Lemma 8.6 | — | `process`, `scan_children`, `run_block` | M3 |
| §9.1–9.4 tails Done, SameSide, Mixed2, Progression | — | `run_tail`, `tail_same`, `solve_same`, `tail_mixed2`, `mixed_closed`, `integer_roots`, `tail_progression`, `prog_plan`, `prog_visit`, `lin_congr`, `crt2`, `prog_class_native` | M3 |
| §9.5 Divisor3 (R*, Lemmas 9.2, 9.3) | — | `tail_divisor3(_split)`, `divisor3_native`, `rstar_native128`, `divisor3_scan`, `divisor3_cap`, `alone_filter`, `signed_divisors_mod`, `divisors_with_residue`, `ModD` | M3, hardest |
| §10 final check | — | `emit` | M2 (soundness), M3 |
| §11 assembly | — | — | M3 |
| §12 termination, "incomplete" | `IncReason` (statement only) | `Engine::k_done`, `append_incomplete`, `search_one_k`, `permanent_reason`, `run_skipped`, `read_skip_file`, `append_skip_line`, `edit_skip_file` | M2 |
| §13 | see 6c | see 6c | M1 abstract part proved |
| §14 tests | — | the logged-trace test | M2 differential tests |
| App. A–C | — | — | text only; Appendix B is `FP.lean` |

**6c. §13 notes: each claim of §13 and what backs it**

| §13 claim | backed by | status |
|---|---|---|
| mode range: the state file is one number; a kill leaves a prefix of its digits (smaller, so the restart is earlier); empty file = start at `start_k` | `decVal_take_le` (a number cut to fewer digits is ≤); `ple_prefix` | digit part proved; the frontier's meaning (§5) is M2; the "empty file" case is by reading the code only |
| a point is `(root, q1, …)`, compared lexicographically; leaf `L` lies before `X` iff `L < X` and `X` does not begin with `L` | `Before`, `before_iff_lt_not_prefix` | proved |
| a missing entry means the start of its level | lists and prefixes: `ple_prefix`, `PLe` | proved as a fact about lists |
| a Progression tail's `u` is one more level | the search tree is arbitrary, so any extra level is covered | the tree for §9.4 is M3 |
| the restart skips, at each level, the children before `X`'s entry, searches the rest whole; every leaf is before `X` or visited | `run`, `mem_restart_iff`, `restart_covers` | proved |
| a skipped child has a smaller value, so its subtree lies before `X` | `leaves_pairwise_before`, `before_initial_segment` | proved (children visited in increasing order is a premise: it holds for the code by `generate`/`expand`, checked by reading) |
| a cut point (entries dropped, last number shortened) is earlier, so nothing is skipped | `restart_covers_of_ple`, `ple_prefix`, `ple_last_le`, `decVal_take_le` | proved |
| the point = the smallest of the generator's point and the unfinished pieces' points; every leaf before it is finished | `point_sound` | proved from two premises: every leaf is finished or owned by a component, and each component is sound for its leaves. Those premises are F5: **assumed**, not derived from `engine.cpp` (locks, "registered before the block counts as finished", Appendix C item 8) |
| job depth, batches of 32, sweeps, blocks partition `[lo, hi]`, a node on `X` at the job depth becomes a sweep | — | scheduling; not modelled. It does not enter the covering argument above, which holds for any partition into pieces; the partition itself is M2 |
| points of the earlier 3-entry version keep their meaning; a point whose root does not exist is ignored (the `k` starts over) | missing entries as above; "starts over" is the earliest point | meaning proved; the ignore-rule by reading the code only |
| output deduplicated, a pair counts as written only when both lines are in the file | — | not formalised (`pairs_in_file`); needed for `MainTheoremFor`'s "(or was already in it)", M2 |
| the point is used from `resume_with=`, from `single_k_status.txt` (same mode, hash, engine, `k`, state `running`/`timeout`), from `resume=` in `incomplete.txt` | — | not formalised; the mode-match and no-resume-when-`incomplete` rules protect completeness of the results files and are M2 (§12 model) |
| the status file is written in the order `resume_root, q1, q2, deeper` after the other lines, so a cut either fails a check or gives a prefix or a shorter number | `ple_prefix`, `decVal_take_le` for the consequence | the order was **checked by reading the code** (see below), not proved |

Checked by reading the code for these rows: the restart skips by value as `run` does; a
point entry below a range's start or above its end behaves as `run` does; the status file
writes `resume_root, resume_q1, resume_q2, resume_deeper` in that order after the state, mode,
hash, engine and k lines, so a cut either fails a check (start over) or gives a prefix or a
shorter last number; the q passed to the pre-screen stays below about 2⁴⁰⁴, so its double never
overflows.

## 7. Differential results

None yet: the executable model and the comparison with the program (type 23 k ≤ 200, type 21
k ≤ 1000, one Progression and one Divisor3 case) are milestone M2.

## 8. Findings, by severity

No finding in M1 can cause a missed pair or a wrong pair.

| # | severity | where | finding |
|---|---|---|---|
| F1 | low (proof text) | App. B | "each operation adds a relative error of at most u" is false for `t /= q` in `h_ld` when `q⁻ⁱ` underflows, which happens (q near 2⁴⁰⁰ in `find_upper`/`find_lower`, e ≥ 3). The effect is an absolute error ≤ 3e·2⁻¹⁰⁷⁵ on a sum ≥ 1, far below the margin; `hS_A` proves the bound with it. |
| F2 | low (proof text) | App. B | the product bound `(2δ+2δ)X⁺Y⁺` needs `X⁺, Y⁺ ≥ 1` (`|X⁺−1| ≤ X⁺`), true because x0, y0 are abundancies, but not stated. |
| F3 | low (proof text) | App. B | `δ = 5(e+j+f+2)u` and `ε ≥ 3δ` are first-order statements: O(u²) terms and the rounding of the thresholds `2(1±ε)` and `1±err` are dropped. The exact conditions the argument needs (`margin_ok`) do hold with the code's margin, with room (needed ≈ 12(n+2)u, available 16(n+3)u). |
| F4 | info (proof text) | §1.2, Lemma 3.2 | `0 < N1` is missing from the definition; "h(p^e) strictly decreases in p" needs `e ≥ 1`. |
| F5 | gap (this check) | §13 | the concurrency argument (generator point read before the piece list, split-off pieces registered before their block finishes) is a premise of `point_sound`, not yet derived from `engine.cpp`. The logged-trace test of §14 backs it. |
| F6 | info | §2 A5 | A5 as written omits underflow and that a rounding keeps the sign; `Assumptions.lean` states the refined form the proof needs. |

## 9. Patches

`patches/proof_text_m1.patch`: text-only changes to `exhaustive_search_proof.md` for F1–F4
(apply inside `Amicable_Search/` with `patch -p1`; dry-run checked against your current file).
Its "test" is the Lean build: the lines it adds describe `abund_prime_pow_lt`,
`abund_prime_pow_strictAnti`, `hS_A`, `IsXEval.approx`, `margin_ok`, `upper_ok_eq_exact`,
`lower_ok_eq_exact`. No code patch: M1 found nothing to fix in the code.

## 10. Next steps and estimates

| milestone | contents | estimate |
|---|---|---|
| **M2** | an executable Lean model of §4–§10 (configurations, roots, exact ranges, the five tails, `emit`); building the program with `build.sh`; differential runs (type 23 k ≤ 200, type 21 k ≤ 1000, one Progression and one Divisor3 case) with identical pair lists required; soundness (every emitted pair is in `T(H,k)`) and termination for the model; deriving F5's premises from a model of `Engine::status` | 25–40 h |
| **M3** | completeness: Lemmas 6.1–6.3, 7.1, 8.1–8.6, 9.1–9.5 (Divisor3's R*, Lemmas 9.2, 9.3), §10, then the Main Theorem for the model | 40–80 h; Divisor3 and the root interleavings are the hardest parts |

## 11. Final Verification

**What the Lean kernel has verified.** The library `AmicableProof` builds with Lean 4.34.1 and
the pinned Mathlib: 190 theorems, no `sorry`, no `native_decide`, no `axiom` declaration, and
every theorem depends on at most `propext`, `Classical.choice`, `Quot.sound`
(`logs/check.log`, `logs/axioms.log`, `logs/build_clean.log`: 0 warnings; the self-test shows the
checks reject a planted `sorry` and a planted `axiom`). What is verified is milestone M1: the
definitions (§1), the basic facts (§3), the resume argument (§13, over an abstract tree), the
floating-point pre-screen (Appendix B), and that the premises A1–A5 are jointly satisfiable
(`Consistency.lean`).

**What it has not verified.** The **completeness theorem is not proved.** `MainTheorem` is only
*stated* (`MainStatement.lean`). The model of the search (§4–§10), Lemmas 6.1–6.4, 7.1, 8.1–8.6,
9.1–9.5, the assembly of §11, and the concurrency premises of `point_sound` (F5) are open
(section 6b, `Open/README.md`; milestones M2 and M3). No "the program never misses a pair"
statement has been mechanically verified; M1 found no error that could make it miss one in the
parts it covers.

**What correctness rests on.** Even a finished proof would be a proof about the assumptions, not
about the compiled program. It holds only if the C++ code matches the model and A1–A6:
* A1: exact integer arithmetic (GMP, 128-bit with overflow checks, `ModD`);
* A2: primesieve returns exactly the primes of `[lo, hi]` for `hi` up to its limit and fails
  loudly beyond;
* A3: the factorization routines (hurchalla, FLINT) return the true factorization;
* A4: the primality tests never reject a prime and are exact below 2⁶⁴;
* A5: binary64 round-to-nearest behaviour of the FPU and of GMP's `mpz_get_d` (compiler flags
  that change floating-point semantics, e.g. `-ffast-math`, would break it);
* A6: the scheduler runs every queued item unless the run is stopped.

`Consistency.lean` shows these assumptions do not contradict one another; it does not show the
program meets them. That part rests on the code review, the differential tests of milestone M2
(not yet run), and the logged-trace test of §14.

## Files

```
lean/
  README.md                 how to build and check
  REPORT.md                 this report
  check.sh, check.ps1       build + all trust checks (see §2)
  CheckAxioms.lean          the axiom audit run by both scripts
  lakefile.toml, lean-toolchain, lake-manifest.json   pinned project
  AmicableProof.lean        the library root (imports below)
  AmicableProof/Defs.lean, Sanity.lean, Basic.lean, Resume.lean, FP.lean,
                Assumptions.lean, MainStatement.lean, Consistency.lean, Search.lean
  Open/README.md, Open/OpenGoals.lean   open items (outside the library)
```

`logs/` is written by the check scripts.
