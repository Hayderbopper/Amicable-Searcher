# Amicable-Searcher

An exhaustive search for amicable pairs of **any hash**, with a written proof
that it never misses a pair and a Lean formalization of the proof's
foundations.

For a chosen hash (the shape of a pair's prime factorization, see below) and
a range of `k = gcd(N1, N2)`, `multi_k_searcher` finds **every** amicable
pair with that hash and that `k`, or lists the `k` as incomplete with the
reason. Nothing is skipped silently.

* Multi-core C++20, with GMP, FLINT, primesieve and Jeffrey Hurchalla's
  factoring library.
* Every bound is decided in exact integer arithmetic. Floating point only
  proposes values, which are then checked exactly.
* Every pair is checked independently before it is written
  (`σ(N1) = σ(N2) = N1 + N2`, `gcd = k`, primes really prime).
* Runs can be stopped and resumed at any moment without losing work.
* Output is in the [sech.me/ap](https://sech.me/ap/) submission format.

The proof is [`exhaustive_search_proof.md`](exhaustive_search_proof.md).
The Lean project is in [`lean/`](lean/); see [Lean](#lean) for what it
covers.

## Download

Prebuilt programs for Windows and Linux (x86-64) are on the
[Releases](../../releases) page: unzip and run `multi_k_searcher` in that
folder. Building from source (below) gives a program tuned for your own CPU.

## Quick start

### Linux

```bash
bash install_deps.sh        # g++, clang, git, GMP, MPFR, FLINT, primesieve
./build.sh                  # tuned for this CPU (-march=native)
./Build/multi_k_searcher --hash "[(1,0),(1,0)] _ [(1,0)]" 1 100000
```

`./build.sh --portable` makes a generic x86-64-v2 build that runs on any
x86-64 CPU from about 2009 on. `./build.sh --help` lists every option.

### Windows (MSYS2)

1. Install [MSYS2](https://www.msys2.org). In the **MSYS2 MINGW64** shell run

   ```bash
   pacman -S --needed git mingw-w64-x86_64-gcc mingw-w64-x86_64-clang mingw-w64-x86_64-gmp mingw-w64-x86_64-mpfr mingw-w64-x86_64-flint mingw-w64-x86_64-cmake mingw-w64-x86_64-ninja
   ```

2. In PowerShell, in this folder:

   ```powershell
   powershell -ExecutionPolicy Bypass -File .\build.ps1
   .\Build\multi_k_searcher.exe --hash "[(1,0),(1,0)] _ [(1,0)]" 1 100000
   ```

`-Portable`, `-Avx512` (any CPU with AVX-512, tuned for Zen 5), `-Clean`,
`-NoClangFactoring`, `-NoMimalloc` and `-Msys2Root D:\msys64` are the
options. The build copies the MinGW DLLs into `Build\`, so the folder
runs on its own.

### What the build does

* The first build downloads Hurchalla's header-only factoring library into
  `third_party/hurchalla/` at pinned commits (`third_party/get_hurchalla.sh`
  or `.ps1`, needs git). Set `HURCHALLA_INCLUDE` to use a copy you already
  have.
* **Clang factoring is on by default.** `Source/external_factoring.cpp`
  (the factoring code) is compiled with clang++ and everything else with
  g++. With GCC 14–16, hurchalla's factoring runs about 25–35% faster when
  clang compiles it. The file's interface passes no `__int128` by value, so
  the two compilers' objects link safely. `--no-clang-factoring` (Linux) or
  `-NoClangFactoring` (Windows) turns it off.
* **Windows uses mimalloc.** The search makes many small allocations from
  several threads, which the Windows heap handles slowly. `build.ps1`
  downloads Microsoft's mimalloc into `third_party/mimalloc/`
  (`third_party/get_mimalloc.ps1`) and compiles it in
  (`Source/fast_alloc.cpp`); on GitHub's Windows runners that made the test
  runs 1.15–1.35x faster. `-NoMimalloc` leaves it out. The Linux build
  keeps glibc's allocator, which is already fast.
* Check a new build with a run whose pairs you know, for example type 23
  for `k` from 1 to 8191: 591 pairs.

## The hash

```
[(a1,b1),(a2,b2),...] _ [(c1,d1),(c2,d2),...]
     smaller member N1        larger member N2
```

* `N1 = k · P1^a1 · P2^a2 · …` with `P1 < P2 < …`
* `N2 = k · Q1^c1 · Q2^c2 · …` with `Q1 < Q2 < …`
* `k = gcd(N1, N2)`.
* Each slot is `(exponent, multiplicity)`. The prime divides `k` exactly
  *multiplicity* times (0 = not at all). On its own side it has *exponent*
  extra powers.

So a prime with exponent `e1` in N1 and `e2` in N2 is written on the side
where it is bigger, as `(|e1−e2|, min(e1,e2))`. Primes with `e1 = e2` belong
to `k` only. Every amicable pair has exactly one hash and one `k`.

| hash | example pair |
|---|---|
| `[(1,0),(1,0)] _ [(1,0)]` | 220 = 2²·5·11, 284 = 2²·71 (k = 4) |
| `[(4,1),(1,0)] _ [(1,0),(2,0)]` | 1184 = 2⁵·37, 1210 = 2·5·11² (k = 2) |
| `[(1,0),(1,0)] _ [(2,3),(1,0)]` | 6232 = 2³·19·41, 6368 = 2⁵·199 (k = 8) |
| `[(1,0),(1,0)] _ [(1,0),(1,0),(1,0)]` | the type-23 family |

Any number of primes (up to 16 slots) on either side, with exponents and
multiplicities up to 1000. Folder-style hashes like
`((1,0),(1,0)) _ ((1,0),(1,0),(1,0))` are accepted too.

## Running it

Settings come from `config.txt`; anything on the command line overrides
them. `multi_k_searcher --help` lists the options.

| mode | what it does |
|---|---|
| `range` | every `k` in `[start_k, end_k)`, many at once. Resumes from `Data/<hash>/multi_k_state.txt`. |
| `single` | all threads on one `k` (`single_k`). Run it again to continue after any stop. |
| `skipped` | works through `Data/<hash>/incomplete.txt`, smallest `k` first, and deletes each `k` once it has been searched completely. |

```bash
./Build/multi_k_searcher                                   # everything from config.txt
./Build/multi_k_searcher --hash "[(1,0),(1,0)] _ [(2,1),(1,0),(1,0)]" 1 100000001
./Build/multi_k_searcher --timeout 600 1 0                 # open-ended, give up on a k after 10 min
./Build/multi_k_searcher --mode single 611488              # one k, every thread
./Build/multi_k_searcher --mode skipped                    # finish the listed k
./Build/multi_k_searcher --hash "..." --plan 12345         # how each root of the hash is solved
```

* `end_k = 0` runs until stopped. Without `start_k` a range run resumes where
  it stopped; every `k` below the saved number is finished.
* A `k` that runs past `timeout_seconds` (range) or `single_timeout_seconds`
  (single, skipped) is listed in `incomplete.txt`. In mode skipped its line
  keeps the exact point to continue from (`resume=general:root,q1,q2,…`).
* Mode single saves a resume point about once a second in
  `single_k_status.txt` and continues from it by itself. Its `resume_with=`
  line shows the explicit command. Delete the file to start that `k` over.
* A range run and a skipped run of the same hash can run at the same time.
  Every change to `incomplete.txt` is made under a lock.
* A pair already in the results file is never written twice.

### The guarantee

For every `k` that finished and is not listed in `incomplete.txt`, every
amicable pair with this hash and `gcd = k` is in the results file. A `k` is
listed only when

* a time limit was set and reached, or
* some prime's proven range cannot be capped below 2⁴⁰⁰, or lies beyond 2⁶⁴,
  where primesieve cannot scan it.

The reason is written next to the `k`. At the end of a range run the program
prints either "complete: every k in the range was searched exhaustively" or
how many `k` are incomplete.

## Results

`Data/<hash>/multi_k_results.txt` (modes range and skipped) and
`single_k_results.txt` (mode single):

```
21 Amicable-Searcher 2026
220=2^2*5*11
284=2^2*71

X12 Amicable-Searcher 2026
1184=2^5*37
1210=2*5*11^2
```

The type is (primes only in the smaller)(primes only in the larger), with an
`X` prefix for an irregular pair: one whose hash has any slot other than
`(1,0)`, that is, a shared prime with different exponents or a prime of one
member only with exponent 2 or more. Set `author` and `year` in `config.txt`.

`collect_results` gathers every results file under `Data/` into one
deduplicated, re-verified `all_pairs.txt`:

```bash
./Build/collect_results                          # Data/ -> all_pairs.txt
./Build/collect_results --known AP23.txt         # only pairs not already in that list
./Build/collect_results Data other_dir --out everything.txt
```

It only reads the results files, so it can run while a search is going. In
`all_pairs.txt` it writes each pair's type as its factorizations give it, so
pairs written by older versions (which marked only shared primes with
different exponents) get the `X` rule above; the results files themselves are
not changed.
[`results/all_pairs.txt`](results/all_pairs.txt) holds the pairs found so
far, and [`tools/lowest_gcd_abundancy.py`](tools/lowest_gcd_abundancy.py)
ranks them by the abundancy of their gcd.

## How the search works

The proof explains each step against the code. In short:

1. **The primes of k.** Bound slots (multiplicity > 0) must be primes of `k`
   with exactly that exponent. Every assignment is tried.
2. **The order of the free primes.** The other primes do not divide `k`.
   Every interleaving of the two members' sorted prime lists is a separate
   search (a *root*), except where the last steps do not depend on the
   order, where they are merged.
3. **A proven range for every scanned prime.** With `x = σ(N1)/N1` and
   `y = σ(N2)/N2`, every pair has `(x−1)(y−1) = 1`, `x > 2` and `y < 2`.
   Each prime still to come raises the abundancy by less than `(L+1)/L` for
   a proven lower limit `L`. That gives an exact smallest and largest value
   for the next prime.
4. **The last two or three primes are solved, not scanned:** closed forms,
   integer roots of a small polynomial, a congruence class, or the divisors
   of a number that does not depend on the unknown prime (found with a
   meet-in-the-middle residue search).
5. **Every candidate is checked** from its full factorization before it is
   written.

## Lean

[`lean/`](lean/) is a Lean 4 + Mathlib project (`AmicableProof`). It proves,
with no `sorry` and no axioms beyond Lean's standard three:

* the definitions of §1 (pair, hash, `k`, `T(H,k)`) and that each pair lies
  in exactly one `T(H,k)`;
* the basic facts of §3 (the abundancy identity, the prime-power bounds,
  the decomposition);
* the early exits of §6 (Lemmas 6.2 and 6.3), the monotonicity of the two
  tests (Lemma 8.3), the bisection (Lemma 8.4), and the algebra the tails
  solve: the SameSide and Mixed2 equations, Divisor3's divisor condition and
  the cap of Lemma 9.2;
* the resume argument of §13, for any search tree;
* the floating-point pre-screen of Appendix B: whenever it decides, it
  agrees with the exact test;
* that the assumptions A1–A5 about the computer are consistent.

The Main Theorem is **stated** in Lean, not yet proved: it needs a Lean model
of what the program does (§4–§12), which is open.
[`lean/README.md`](lean/README.md) explains how to build and check it, and
[`lean/REPORT.md`](lean/REPORT.md) is the full audit.

## Repository layout

```
build.sh, build.ps1     the Linux and Windows builds
install_deps.sh         Linux dependencies
config.txt              mode, hash, k range, time limits, threads, author/year
Source/                 the C++ sources
third_party/            get_hurchalla.sh / .ps1, get_mimalloc.ps1 (the libraries are downloaded)
exhaustive_search_proof.md   the proof
lean/                   the Lean formalization
results/all_pairs.txt   pairs found so far
tools/                  helper scripts (package_linux.sh for releases, bench/ for old-vs-new timing)
.github/workflows/       builds and checks both releases for a tag v*
docs/HISTORY.md         speed measurements, verification runs, every defect fixed
credits/                the libraries this project uses, and their licenses
LICENSE                 MIT
```

`Build/` and `Data/` are created when you build and run.

## Credits and license

The factoring is done by Jeffrey Hurchalla's
[factoring library](https://github.com/hurchalla/factoring) and the primes
come from Kim Walisch's [primesieve](https://github.com/kimwalisch/primesieve);
GMP, MPFR and FLINT do the big-number arithmetic. See
[`credits/`](credits/README.md) for every library and its license.

This project is released under the [MIT License](LICENSE).
