# AmicableProof: the Lean formalization

A Lean 4 + Mathlib project that checks parts of
[`../exhaustive_search_proof.md`](../exhaustive_search_proof.md) with Lean's kernel.

## What is proved

Everything below is proved with no `sorry` and no axioms beyond Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`). `CheckAxioms.lean` prints the axioms of every
theorem and fails on anything else.

| file | proof section | contents |
|---|---|---|
| `Defs.lean` | §1 | amicable pair, slot, hash, `k`, `T(H,k)`; every pair lies in exactly one `T(H,k)` |
| `Basic.lean` | §3 | Lemma 3.1 (abundancy identity), Lemma 3.2 (prime powers), Lemma 3.3 (decomposition), (P) and Corollary 3.4 |
| `Search.lean` | §6, §8, §9 | Lemma 6.2 (abundant `k`), Lemma 6.3 (dead configuration), Lemma 8.3 (the tests are monotone), Lemma 8.4 (bisection), the SameSide equations, the Mixed2 closed form, Divisor3's `D'(u) ∣ R*`, Lemma 9.2 (cap on `u`) |
| `FP.lean` | Appendix B | the floating-point pre-screen agrees with the exact test whenever it decides, including FMA and underflow |
| `Resume.lean` | §13 | stopping and resuming never skips a leaf of the search tree |
| `Assumptions.lean`, `MainStatement.lean` | §2, §1.4 | the assumptions A1–A6 about the computer, and the Main Theorem's statement |
| `Consistency.lean` | §2 | A1–A5 can all hold at once, so the Main Theorem's premises are not contradictory |

**Not proved:** the Main Theorem itself. It is *stated* (`MainStatement.lean`); proving it
needs a Lean model of what the program does (§4–§12). [`Open/README.md`](Open/README.md)
lists every open item, and [`REPORT.md`](REPORT.md) is the full audit.

## How to build and check

You need [elan](https://github.com/leanprover/elan) (Lean's installer) and git. The Lean
version (`lean-toolchain`) and every dependency (`lake-manifest.json`) are pinned.

```bash
bash check.sh               # Linux, macOS, WSL
bash check.sh --selftest    # also shows the checks reject a planted sorry and axiom
```

```powershell
powershell -ExecutionPolicy Bypass -File .\check.ps1          # Windows
powershell -ExecutionPolicy Bypass -File .\check.ps1 -SelfTest
```

`check.ps1` installs elan if it is missing. Both scripts end with `ALL CHECKS PASSED`, and
the logs go to `logs/`.

What the scripts do:

1. Check the pinned versions.
2. Download each dependency (Mathlib and the eight packages it uses) as a shallow copy of
   exactly the pinned commit. This is much smaller than the full Mathlib history.
3. Try to download Mathlib's prebuilt files (`lake exe cache get`). Skip this with
   `SKIP_CACHE=1` or `-SkipCache`.
4. Build. Without the prebuilt files, this compiles the about 1200 Mathlib files the project
   imports, which can take 30–90 minutes the first time. The progress is shown as it goes.
   Later runs take seconds.
5. Search the sources for `sorry`, `admit`, `native_decide` and `axiom`.
6. Run `CheckAxioms.lean`.
7. Check that `Open/OpenGoals.lean` elaborates.

### Windows tips

* Put the folder on a short path without spaces, for example `C:\lean\amicable`. Mathlib's
  file names are long, and the script turns on git's `core.longpaths` for what it downloads.
* If an earlier attempt left a broken `.lake` folder behind, delete `.lake` and run the
  script again.
