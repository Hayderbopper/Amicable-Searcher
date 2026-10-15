# History, measurements and verification

This file keeps the detailed record from development: speed measurements,
the verification runs, and every defect found and fixed. Some entries refer
to parts that have since been removed to keep the program small: the
specialized engine (`--engine special`, the former `Multi_K_Auto_Cached`
algebra, with `divisor_explorer.cpp`, `poly.cpp`, `equations.cpp` and
`derive_equations.py`). The test scripts mentioned below (`self_test.sh`,
`tests/check_resume_trace.py`, `resume_e2e.py`, the trace build) came with
an earlier Linux package and are not part of this repository. The results of
those comparisons and tests stand for the general engine, which is the only
engine now and gives the same pairs as before the removal.

## Speed

Measured on the 2-core test machine, before the specialized engine was
removed. Both columns found the same pairs. The left column is the former
`Multi_K_Auto_Cached`'s algebra (the old `--engine special`); that program
itself gave the same times.

| run | Multi_K_Auto_Cached algebra | general engine |
|---|---|---|
| type 23, k = 611,488 (one heavy k) | 2.0 s | **1.3 s** |
| type 23, k = 1,401,000 – 1,402,000 | 19.8 s | **18.3 s** |
| type 23, k = 1 – 8191 (591 pairs) | 35.6 s | **19.0 s** |
| `[(1,0),(1,0)] _ [(2,1),(1,0),(1,0)]`, k ≤ 2,000,000 | 22.9 s | **13.1 s** |
| `[(1,0),(1,0)] _ [(1,1),(1,0),(1,0)]`, k ≤ 1,000,000 | 17.6 s | **6.8 s** |
| type 23, k = 20,000,000 – 20,003,000 | 64 s | 67 s |

The last row is almost entirely one k, 20,002,816 = 2¹¹·9767, with
σ(k)/k = 1.99972. Nearly perfect k like this are the expensive ones for both
programs, and there the two are about equal.

`[(1,0),(1,0)] _ [(2,1),(1,0),(1,0)]` at large k, 100,000 consecutive k on one
thread:

| k from | 1.8·10⁶ | 5·10⁶ | 2·10⁷ | 6·10⁷ | 9.9·10⁷ |
|---|---|---|---|---|---|
| Multi_K_Auto_Cached algebra | 2.3 s | 2.8 s | 2.8 s | 3.5 s | 3.3 s |
| general engine | **1.3 s** | **1.8 s** | **2.0 s** | **2.5 s** | **2.5 s** |

Other members of that family, 2 threads (times include about 0.25 s of
program start and stop):

| hash, k range | Multi_K_Auto_Cached algebra | general engine |
|---|---|---|
| `(3,1),(1,0),(1,0)`, k = 100,000 – 131,000 | 0.8 s | **0.5 s** |
| `(1,0),(2,1),(1,0)`, k = 100,000 – 131,000 | 1.3 s | **0.3 s** |
| `(1,1),(1,0),(1,0)`, k = 5,000,000 – 5,100,000 | 2.0 s | **1.0 s** |
| `(2,1),(1,0),(1,0)`, k = 5,000,000 – 5,100,000 | 1.5 s | **1.0 s** |

Hashes with many free primes are expensive by nature: every prime except
the last two or three has to be scanned. For example, a 10-prime hash at k = 2
runs for hours.

## Verification

All runs below use the final version (general engine unless noted).

* **Every pair below 10^9, over many hash shapes.** A σ-sieve listed all 564
  amicable pairs with larger member ≤ 10^9. They have 89 different hashes,
  including primes of A1, exponents up to 5, and up to 10 primes.
  * **Exhaustive runs:** the single-k search was run on each pair's own
    hash and k. All 267 (hash, k) groups that finish within the test's 30 s
    limit found every pair. The other 12 groups (24 pairs) are hashes with
    7 to 10 primes at k = 2 … 135. Those are huge exhaustive searches; their
    pairs are covered by the guided check below.
  * **Guided check, all 564 pairs:** the search tree was followed along each
    pair's own primes. Every scanned prime (1,387 levels) lay inside the
    computed range, and the exact final step produced the pair every time.
* **AP23.txt (sech's type-23 list).**
  * Exhaustive: all 591 pairs with k < 8192 were found, and no others.
  * Guided check, all 28,503 pairs with k < 2^64: 28,500 are found along
    their own path through the search, including ones with hundreds of
    digits. The other 3 lie on a branch with a prime range beyond 2^64.
    The program lists those k as `range_beyond_2^64` instead of finding the
    pairs, as the guarantee allows. There were no failures.
* **The two engines against each other:** identical pairs on all five
  ranges of the first speed table, the four ranges of the last one,
  `(2,0),(1,0),(1,0)` at k = 100,805 – 102,000, and type 23 at
  k = 30,000 – 31,000 (8 pairs).
* **Stop and resume:** the single-k search on k = 4096 (type 23), stopped
  after 3 s and resumed from its status file's `resume_with` line, gives the
  same 72 pairs as an uninterrupted run, with either engine.
* **Modes single and skipped** (type 23, k < 8192, each engine):
  * A range run with a 1 s limit per k, then `mode = skipped`: the
    skipped k values are searched and deleted, `incomplete.txt` ends
    empty, and the results file holds exactly the 591 reference pairs,
    with no pair written twice.
  * The same with `single_timeout_seconds = 2` first: the stopped k keep
    `resume=` points, and a second run continues them to the same 591 pairs.
  * Killed mid-k with `kill -9`, the next skipped run continues that k
    from `single_k_status.txt`, again with the same 591 pairs.
  * `mode = single`, k = 4096: stopped at 4 s, then run again; it
    continues by itself and ends with the same 72 pairs as one
    uninterrupted run, and k leaves `incomplete.txt`.
  * Lock test: three processes appended 12,000 lines while a fourth
    rewrote the file 7,200 times, on Linux and as Windows programs (under
    Wine). No line was lost. Without the lock, most were.
  * Range mode still gives the same pairs on all five ranges of the first
    speed table, with both engines.
* **Unit tests:** the divisor search against brute force (20,000 random
  cases); σ(p^e) through cyclotomic pieces against direct computation; the
  64-bit congruence solver against the BigInt one on 200,000 cases.
* **The independent review's tests,** re-run on the fixed code (type 23,
  k ≤ 3000):
  * a range run with a 1 s limit, then a skipped run;
  * repeated skipped runs with a 1 s limit;
  * `kill -9` inside a k, then a skipped run;
  * a range run and skipped runs at the same time.

  All end with exactly the reference pairs, none twice, and `incomplete.txt`
  empty. Each defect listed under *Fixes from the independent review* was
  reproduced on the old code and passes on the new.
* **Resume points (deep points).** A test build logs every finished piece
  of work and every resume point. A checker
  (`tests/check_resume_trace.py` in the Linux zip) confirms that each point
  only claims work that was already finished.
  * The test build is made with `EXTRA_CXXFLAGS=-DAMICABLE_TRACE bash build.sh`
    and run with `AMICABLE_TRACE_FILE=trace.txt`. Three settings make
    blocks small, points frequent and the generator slow:
    `AMICABLE_TEST_WIDTH`, `AMICABLE_TEST_TICK_MS` and
    `AMICABLE_TEST_GEN_SLEEP_US`. The normal build has none of this.
  * It ran with tiny blocks and a point every 2 ms, on types 23, 33, 43,
    32, 22 and whole-root congruences (types 31 and 41). Long congruence
    tails were split off 5,709 times.
  * Over 31,000 points against up to 450,000 pieces of work, it found 0
    violations.
  * Three deliberately broken engines are all caught:
    * one that claims one block too many: 1,612 violations;
    * one whose point ignores a batch still being filled: 44,301;
    * one that does not register a split-off tail: 67,022 to 2.3 million.
  * The second review's end-to-end check (`resume_e2e.py`) restarts a k
    from points sampled during a run, up to 5 entries deep. In 53 restarts
    on types 23, 43, 33 and 32, every pair was found either before the point
    or by the restart. The status file was also cut at every length (321
    cuts of a 4-entry point), and no cut gave a later point.
* **Restarts (deep points).** Each k was searched in pieces until done:
  types 23 (k = 4096, 8192), 43 (k = 68, 124) and 32 (k = 4096).
  * The pieces were stopped either by a 2-5 s time limit or by `kill -9` at
    random moments.
  * Every one ended with exactly the pairs of one uninterrupted run, with no
    pair written twice.
* The sources pass a MinGW (Windows) compile check with both thread models
  (posix and win32).
* **Linux.** `self_test.sh` from the Linux zip passes on Ubuntu 22.04
  (g++ 11, FLINT 2.8, primesieve 7.8) and on Ubuntu 24.04 (g++ 13, FLINT 3,
  primesieve 12). On 22.04 the five ranges of the first speed table give the
  same pairs with all three searchers. This is where the primesieve fix
  below was found.

## Fixes made along the way

These were found while building this program. The first two also affected
the specialized algebra of the former `Multi_K_Auto_Cached` (and the original
Multi K code it came from); all three are fixed here.

* **Where a prime scan starts (`prime_iterator.h`).** After
  `primesieve::iterator it(lo, hi)`, primesieve 11 and later return the primes
  `≥ lo`, but versions 7 to 10 return only the primes `> lo`. The code assumed
  the first behaviour, so with an older library a prime lying exactly on a
  computed lower bound was skipped. This was found on Ubuntu 22.04
  (primesieve 7.8), where the general engine missed 2 of the 4 X22 pairs
  with k ≤ 300,000. The Windows build links primesieve 11 or later, so its
  runs were never affected. Every iterator now starts at
  `prime_iter_start(lo)`, which gives `≥ lo` with any version. Each program
  also checks the convention at start-up and refuses to run if it does not
  hold.

* **Divisor search (`divisor_explorer.cpp`).** The meet-in-the-middle search
  for P4 looked for the wrong residue when three things happened at once:
  * a divisor shared two or more primes with the modulus only partly;
  * the rest of the modulus was 2^16 or more;
  * both held on a real solution.

  A valid P4 could then be missed. It is rare: all regression runs gave the
  same pairs before and after the fix.
* **Floating-point margins (`divisor_explorer.cpp`, `poly.cpp`).** The
  closed-form bounds (P1_Max, the P3 edge, P4_Max, the P3 range) are computed
  in floating point. Each one now has a safety margin, and the quadratic
  roots use the numerically stable formula, so rounding cannot make a bound
  slightly too small. This changed no result in any test.

Earlier runs of `Multi_K_Auto_Cached` can be re-checked with this program
(the old hash `(a,b),(c,d),(e,f)` is `[(1,0),(1,0)] _ [(a,b),(c,d),(e,f)]`).

## Fixes from the independent review

An independent review checked the Windows and Linux code against
`exhaustive_search_proof.md`. It found no error in the mathematics of the
search (Sections 3–11 of the proof). It found two other kinds of problems:
* nine defects in the code around the search, listed below; all are fixed,
  and Appendix C of the proof (items 5–13) has the details;
* ten statements elsewhere in the proof that were wrong or missing (its
  P1–P10); all are corrected, and the table at the end of Appendix C lists
  them.

* **A flag lost at a time limit** (modes single and skipped). A
  `range_beyond_2^64` or `bound_not_finite` flag raised before the time limit
  was dropped. The next run then resumed past it and reported the k as
  complete. Now any flag keeps the k listed, with no resume point.
* **A fatal error in one k** could let another k that was running at the same
  time count as finished. Now every k cut short stays unfinished. The same
  fix is in both engines.
* **Writing `incomplete.txt` while another program had it open** failed
  silently. Now it retries for 10 s, then stops with an error. Both
  engines have this fix.
* **A resume point read between two updates** could point past work that
  had not been generated yet. The updates are now made in a safe order.
* **Modes single and skipped used each other's resume points,** although
  they write different results files. Now each mode uses only its own.
* **A pair cut in half by a power cut** was treated as already written. Now
  it is written again in full.
* **Windows: `unsigned long` is 32 bits.** A factor-list helper of the
  specialized engine compared 64-bit primes as 32-bit numbers, so it could
  merge two different primes. It is rare (about one chance in 10⁹ per
  factorization) and the general engine was never affected.
* **Windows: x87 precision.** A modular product used `long double` and
  assumed 64-bit precision. Programs built with MinGW's "win32" thread model
  run new threads at 53 bits, and there the product was often wrong.
  * Your builds (MSYS2, posix thread model) were not affected.
  * The product is now checked exactly.
  * Every thread also sets full precision at start (`Source\fpu.h`).
* **Windows: `incomplete.txt` erased while another program had it open**
  (modes single and skipped). Another program sometimes opens the file
  without sharing for a moment: an editor, a virus scanner or a sync client.
  If that happened while the file was being rewritten after a k, the program
  read it as empty and wrote back only its own change. Every other listed k
  was lost, with no message.
  * Now it waits up to 10 s for the file, then stops with an error and leaves
    the file as it was.
  * Mode range only appends to the file and was not affected.

The seven run-control defects needed one of two things: a stop at the wrong
moment (a time limit, a crash or a kill), or another program holding
`incomplete.txt` open. A run without either was correct before, and gives
the same pairs now. The last defect leaves no trace. If an `incomplete.txt`
on Windows ever lost lines you did not expect it to lose, search those k
values again.

## Finer resume points, and report timing on Windows

* **Resume points go as deep as the search.** Before, the saved point
  stopped at the second prime. Everything below it was one unsaved chunk.
  * For hashes with more primes (3,3; 4,3 and up), one chunk could take
    hours, and the point did not move at all. For example, type 33 at
    k = 1024 sat at `(0, 1031, 131968)` for the whole run.
  * In modes single and skipped, the work is now cut at the last scanned
    prime. A long congruence tail's `u` is cut too.
    * The thread that runs the tail does that cut.
    * The thread that hands out the work never plans tails, so it cannot
      leave the others waiting. The second review found that problem in a
      first version of this change.
  * The same run now saves `(0, 1031, 131969, 13503533251)` after 30 s, and
    a restart continues from there.
  * Speed is unchanged: the same times on every test, a little faster on
    deep hashes. The pairs are identical.
  * Mode range is unchanged. There, each k is the unit.
* **The progress line keeps time on Windows.** The report every 60 s was
  timed by counting 240 sleeps of 250 ms. On Windows a sleep can last up to
  15.6 ms longer than asked, and writing the status file takes time, so the
  line drifted by a few seconds a minute. The loop now follows the clock, so
  reports come at 60, 120, 180 s, ... on both systems.

## Performance check before publication (October 2026)

A 5-hash benchmark (type 23 k < 8192, 33 k < 100, 32 k < 4000,
`[(2,0),(1,0)] _ [(1,0),(1,0),(1,0)]` k < 3000, 24 k < 100; 4 threads, GCC 13 /
clang 18 on Linux, 12,886 pairs, identical in every build):

| build | seconds |
|---|---|
| g++ + clang factoring (default) | 24.8 |
| g++ only | 26.4 |
| clang++ only | 24.4 |
| -O2 instead of -O3 | 25.2 |
| g++ LTO | 27.1 |
| clang ThinLTO | 25.1 |
| g++ PGO | 21.8 (with the scheduling fix; 20.7 without PGO) |
| mimalloc / jemalloc | 24.3 / 26.8 |

None of them is outside the noise (about ±3%). The one large gain was in the
scheduler: a range run left every `k` to the thread that started it, below
its first prime, so a `k` much slower than its neighbours ran on one thread
(type 33, `k = 64`: 10 s of the 11 s total; 4 threads gave 1.8×). A range
run now splits each `k` like a single-k run (sweeps and batches down to the
last scanned prime): `k = 64` 5.6 s → 2.5 s, the benchmark 24.8 s → 20.7 s
(type 33: 5.7 → 2.9 s, type 24: 2.8 → 1.1 s), the other hashes unchanged.
The gain grows with the number of threads.

## Pair type: every non-(1,0) slot is irregular (October 2026)

The `X` (irregular) prefix of a pair's type used to be set only when a
shared prime has different exponents, so e.g. 248658488 = 2³·13²·183919,
256201912 = 2³·37·43·20129 (hash `[(2,0),(1,0)] _ [(1,0),(1,0),(1,0)]`) was
written as type 23. It is now set whenever the hash has a slot other than
`(1,0)`, as in te Riele's definition of a regular pair (`N1 = g·M1`,
`N2 = g·M2` with `M1`, `M2` squarefree and coprime to `g`): that pair is
X23. `collect_results` writes the corrected type for pairs written before. The pairs
in `results/all_pairs.txt` were all regular by both rules; none changed.
