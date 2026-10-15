# Credits

Amicable Search is built on these libraries. None of their code is stored in
this repository: the build downloads hurchalla's headers (`third_party/`) and
uses the others as installed system packages. Each keeps its own license.

| library | author | used for | license |
|---|---|---|---|
| [hurchalla factoring](https://github.com/hurchalla/factoring), with [modular_arithmetic](https://github.com/hurchalla/modular_arithmetic) and [util](https://github.com/hurchalla/util) | Jeffrey Hurchalla (its ECM, `microecm.h`, also by Ben Buhrow) | factoring numbers below 2¹²⁸ (Pollard–Brent rho, ECM, deterministic Miller–Rabin), the program's main factoring route | factoring and modular_arithmetic: Mozilla Public License 2.0; util: MIT |
| [primesieve](https://github.com/kimwalisch/primesieve) | Kim Walisch | generating every prime in each proven range | BSD 2-Clause |
| [GMP](https://gmplib.org) | the GMP developers | exact big-integer arithmetic, BPSW probable-prime tests | LGPL 3 or GPL 2 |
| [MPFR](https://www.mpfr.org) | the MPFR developers | (dependency of FLINT) | LGPL 3 |
| [FLINT](https://flintlib.org) | the FLINT developers | factoring numbers above 2¹²⁸ | LGPL 3 |
| [Lean 4](https://lean-lang.org) and [Mathlib](https://github.com/leanprover-community/mathlib4) | the Lean and Mathlib communities | the formal proof in `lean/` | Apache 2.0 |

hurchalla's library is pinned to the commits in `third_party/get_hurchalla.sh`;
the download puts the factoring license in `third_party/hurchalla/LICENSE`
and each repository's own license under `third_party/hurchalla/src/`. On Windows,
`build.ps1` copies the MinGW DLLs of GMP, MPFR, FLINT and primesieve into
`Build\`; those files are distributed under the licenses above.

The output format follows Sergei Chernykh's amicable pairs list,
[sech.me/ap](https://sech.me/ap/).
