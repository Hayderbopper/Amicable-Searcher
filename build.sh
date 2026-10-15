#!/usr/bin/env bash
# Linux build: makes Build/multi_k_searcher (one program; config.txt "mode"
# picks range, single or skipped) and Build/collect_results.
# (build.ps1 is the Windows/MSYS2 build of the same sources.)
#
#   ./build.sh               fastest build, tuned for THIS machine's CPU
#   ./build.sh --portable    generic x86-64-v2 build that runs on any x86-64 CPU
#                            from about 2009 on (use it if you copy the
#                            programs to another computer)
#   ./build.sh --clean       delete the object files first
#   ./build.sh --jobs N      compile N files at once (default: all cores)
#   ./build.sh --no-clang-factoring
#                            compile external_factoring.cpp with $CXX too
#                            (only if clang++ cannot be installed)
#
# Needs a C++20 compiler (g++ 10+ or clang++ 12+), clang++ (for the factoring
# file, see below) and the development packages of GMP, MPFR, FLINT and
# primesieve; install_deps.sh installs them all.  The hurchalla factoring
# headers are found in, in order:
#   $HURCHALLA_INCLUDE, ./third_party/hurchalla/include,
#   ../third_party/hurchalla/include, /usr/local/include, /usr/include
# and, if none has them, downloaded by third_party/get_hurchalla.sh (needs git).
#
# Libraries installed into a prefix of their own are picked up with DEPS_PREFIX
# (or ./third_party/local).
# Environment overrides: CXX, EXTRA_CXXFLAGS, EXTRA_LDFLAGS, CXX_FACTORING.
#
# Clang factoring (on by default): external_factoring.cpp (hurchalla's
# factoring) is compiled with clang++, everything else with $CXX.  With GCC
# 14-16 the factoring code is about 25-35% faster when clang compiles it.  The
# file's interface passes no __int128 by value, so the two compilers' objects
# link safely.  CXX_FACTORING=<compiler> picks another one.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC="$ROOT/Source"
BUILD="$ROOT/Build"

MODE=native
JOBS=""
CLEAN=0
CLANG_FACTORING=1
while [ $# -gt 0 ]; do
    case "$1" in
        --portable) MODE=portable ;;
        --native)   MODE=native ;;
        --clean)    CLEAN=1 ;;
        --no-clang-factoring) CLANG_FACTORING=0 ;;
        --jobs|-j)  shift; JOBS="${1:-}" ;;
        -j*)        JOBS="${1#-j}" ;;
        -h|--help)  sed -n '2,/^set -euo/p' "$0" | sed '$d'; exit 0 ;;
        *) echo "build.sh: unknown option '$1' (try --help)" >&2; exit 2 ;;
    esac
    shift
done
if [ -z "$JOBS" ]; then
    JOBS="$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)"
fi
case "$JOBS" in ''|*[!0-9]*|0) echo "build.sh: --jobs needs a positive number" >&2; exit 2 ;; esac

die() { echo "" >&2; echo "build.sh: $*" >&2; exit 1; }

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# ---------------------------------------------------------------- compiler
CXX="${CXX:-}"
if [ -z "$CXX" ]; then
    for c in g++ clang++ c++; do
        if command -v "$c" >/dev/null 2>&1; then CXX="$c"; break; fi
    done
fi
[ -n "$CXX" ] && command -v "$CXX" >/dev/null 2>&1 \
    || die "no C++ compiler found.  Run  bash install_deps.sh  (or install g++ yourself)"
echo "compiler : $CXX ($("$CXX" --version 2>/dev/null | head -n1))"

cat > "$TMP/cxx20.cpp" <<'EOF'
#include <bit>
#include <concepts>
#include <cstdint>
#include <filesystem>
template <std::unsigned_integral T> int w(T x) { return std::bit_width(x); }
int main() { unsigned __int128 v = 1; v <<= 100; return w(std::uint64_t(v >> 90)) == 11 ? 0 : 1; }
EOF
"$CXX" -std=c++20 "$TMP/cxx20.cpp" -o "$TMP/cxx20" >"$TMP/cxx20.log" 2>&1 \
    || { cat "$TMP/cxx20.log" >&2; die "$CXX cannot compile C++20 with unsigned __int128 (needs g++ 10+ or clang++ 12+ on a 64-bit system)."; }

# ---------------------------------------------------------------- CPU flags
ARCH="$(uname -m)"
try_flags() {  # succeeds if the compiler accepts these flags
    echo 'int main(){return 0;}' > "$TMP/f.cpp"
    "$CXX" "$@" "$TMP/f.cpp" -o "$TMP/f" >/dev/null 2>&1
}
CPUFLAGS=()
if [ "$MODE" = native ]; then
    case "$ARCH" in
        x86_64|amd64)   cand=(-march=native -mtune=native) ;;
        aarch64|arm64)  cand=(-mcpu=native) ;;
        *)              cand=(-march=native) ;;
    esac
    if try_flags "${cand[@]}"; then CPUFLAGS=("${cand[@]}")
    else echo "note: $CXX does not accept ${cand[*]}; building without CPU tuning"; fi
else
    case "$ARCH" in
        x86_64|amd64)
            if try_flags -march=x86-64-v2; then CPUFLAGS=(-march=x86-64-v2 -mtune=generic)
            else CPUFLAGS=(-march=x86-64 -msse4.2 -mpopcnt -mtune=generic); fi ;;
        *) CPUFLAGS=() ;;
    esac
fi
echo "mode     : $MODE (${CPUFLAGS[*]:-no CPU-specific flags})"

# ---------------------------------------------------------------- libraries
INC=(-I"$SRC")
LIBDIRS=()
add_prefix() {
    [ -d "$1/include" ] && INC+=(-I"$1/include")
    for l in lib lib64; do
        if [ -d "$1/$l" ]; then LIBDIRS+=(-L"$1/$l" -Wl,-rpath,"$1/$l"); fi
    done
}
if [ -n "${DEPS_PREFIX:-}" ]; then add_prefix "$DEPS_PREFIX"; fi
if [ -d "$ROOT/third_party/local" ]; then add_prefix "$ROOT/third_party/local"; fi

find_hurchalla() {
    HB=""
    for d in "${HURCHALLA_INCLUDE:-}" "$ROOT/third_party/hurchalla/include" \
             "$ROOT/../third_party/hurchalla/include" /usr/local/include /usr/include; do
        if [ -n "$d" ] && [ -f "$d/hurchalla/factoring/factorize.h" ]; then HB="$(cd "$d" && pwd)"; return 0; fi
    done
    return 1
}
if ! find_hurchalla; then
    echo "hurchalla factoring headers not found; downloading them (third_party/get_hurchalla.sh)"
    bash "$ROOT/third_party/get_hurchalla.sh" || die "could not download the hurchalla headers.
Run  bash third_party/get_hurchalla.sh  by hand, or set HURCHALLA_INCLUDE=<dir>/include"
    find_hurchalla || die "hurchalla headers still not found after the download"
fi
[ "$HB" = /usr/include ] || [ "$HB" = /usr/local/include ] || INC+=(-I"$HB")
echo "hurchalla: $HB"

read -r -a XCXX <<< "${EXTRA_CXXFLAGS:-}"
read -r -a XLD  <<< "${EXTRA_LDFLAGS:-}"
CXXFLAGS=(-O3 -DNDEBUG -std=c++20 -pthread "${CPUFLAGS[@]}" -DAMICABLE_USE_FLINT "${INC[@]}" "${XCXX[@]}")
LIBS=("${LIBDIRS[@]}" "${XLD[@]}" -lprimesieve -lflint -lmpfr -lgmpxx -lgmp -pthread)

hint_pkgs() {
    echo "Install the development packages (or run  bash install_deps.sh):"
    echo "  Ubuntu/Debian/Mint : sudo apt install g++ clang git libgmp-dev libmpfr-dev libflint-dev libprimesieve-dev"
    echo "  Fedora             : sudo dnf install gcc-c++ clang git gmp-devel mpfr-devel flint-devel primesieve-devel"
    echo "  Arch/Manjaro       : sudo pacman -S gcc clang git gmp mpfr flint primesieve"
    echo "  openSUSE           : sudo zypper install gcc-c++ clang git gmp-devel mpfr-devel flint-devel primesieve-devel"
}

check_lib() {  # name, test program, link flags...
    local name="$1" prog="$2"; shift 2
    printf '%s\n' "$prog" > "$TMP/t_$name.cpp"
    if ! "$CXX" -std=c++20 "${INC[@]}" "${XCXX[@]}" "$TMP/t_$name.cpp" -o "$TMP/t_$name" \
            "${LIBDIRS[@]}" "${XLD[@]}" "$@" >"$TMP/t_$name.log" 2>&1; then
        sed -n '1,12p' "$TMP/t_$name.log" >&2
        die "$name was not found or does not link.
$(hint_pkgs)"
    fi
    "$TMP/t_$name" >"$TMP/t_$name.out" 2>&1 \
        || die "$name links but the test program does not run:
$(cat "$TMP/t_$name.out")
(if it was built from source into a prefix, check LD_LIBRARY_PATH / DEPS_PREFIX)"
}
check_lib GMP '#include <gmpxx.h>
int main(){ mpz_class a = 1; a <<= 100; return a.get_str() == "1267650600228229401496703205376" ? 0 : 1; }' -lgmpxx -lgmp
check_lib MPFR '#include <mpfr.h>
int main(){ mpfr_t x; mpfr_init2(x, 128); mpfr_set_ui(x, 2, MPFR_RNDN); mpfr_sqrt(x, x, MPFR_RNDN); int ok = mpfr_cmp_d(x, 1.41421) > 0; mpfr_clear(x); return ok ? 0 : 1; }' -lmpfr -lgmp
check_lib FLINT '#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>
#include <cstdio>
int main(){ fmpz_t n; fmpz_factor_t f; fmpz_init(n); fmpz_factor_init(f);
  fmpz_set_ui(n, 1000000007UL); fmpz_mul_ui(n, n, 998244353UL); fmpz_factor(f, n);
  int ok = (f->num == 2); fmpz_factor_clear(f); fmpz_clear(n);
  std::printf("%d.%d.%d\n", __FLINT_VERSION, __FLINT_VERSION_MINOR, __FLINT_VERSION_PATCHLEVEL); return ok ? 0 : 1; }' -lflint -lmpfr -lgmp
check_lib primesieve '#include <primesieve.hpp>
#include <cstdio>
int main(){ primesieve::iterator it(1000000, 2000000); unsigned long long p = it.next_prime();
  std::printf("%s\n", primesieve::primesieve_version().c_str()); return p == 1000003ULL ? 0 : 1; }' -lprimesieve -pthread
echo "libraries: GMP, MPFR, FLINT $(cat "$TMP/t_FLINT.out"), primesieve $(cat "$TMP/t_primesieve.out")  ok"

# ---------------------------------------------------------------- compile
OBJ="$BUILD/obj-linux-$MODE"
[ "$CLEAN" = 1 ] && rm -rf "$OBJ"
mkdir -p "$OBJ" "$BUILD" "$ROOT/Data"

# rebuild everything when the flags change
if [ -z "${CXX_FACTORING:-}" ]; then
    if [ "$CLANG_FACTORING" = 1 ]; then
        CXX_FACTORING=""
        for c in clang++ clang++-20 clang++-19 clang++-18 clang++-17 clang++-16 clang++-15 clang++-14; do
            if command -v "$c" >/dev/null 2>&1; then CXX_FACTORING="$c"; break; fi
        done
        [ -n "$CXX_FACTORING" ] || die "clang++ not found.  The factoring code is compiled with clang by default.
Install it (bash install_deps.sh, or Ubuntu/Debian: sudo apt install clang), or
build without it:  ./build.sh --no-clang-factoring"
    else
        CXX_FACTORING="$CXX"
    fi
fi
command -v "$CXX_FACTORING" > /dev/null 2>&1 || die "CXX_FACTORING=$CXX_FACTORING not found."
echo "factoring: $CXX_FACTORING ($("$CXX_FACTORING" --version 2>/dev/null | head -n1))"
FLAGSIG="$(printf '%s ' "$CXX" "$CXX_FACTORING" "${CXXFLAGS[@]}")"
if [ ! -f "$OBJ/flags.txt" ] || [ "$(cat "$OBJ/flags.txt")" != "$FLAGSIG" ]; then
    rm -f "$OBJ"/*.o
    printf '%s' "$FLAGSIG" > "$OBJ/flags.txt"
fi

SOURCES=()
for f in "$SRC"/*.cpp; do
    case "$(basename "$f")" in *_main.cpp) ;; *) SOURCES+=("$f") ;; esac
done
ALL=("${SOURCES[@]}" "$SRC/multi_k_main.cpp" "$SRC/collect_results_main.cpp")

NEWEST_H="$(ls -t "$SRC"/*.h | head -n1)"
TODO=()
for f in "${ALL[@]}"; do
    o="$OBJ/$(basename "${f%.cpp}").o"
    if [ ! -f "$o" ] || [ "$f" -nt "$o" ] || [ "$NEWEST_H" -nt "$o" ]; then TODO+=("$f"); fi
done

if [ ${#TODO[@]} -gt 0 ]; then
    echo "compiling ${#TODO[@]} file(s), $JOBS at a time..."
    export OBJ
    printf '%s\n' "${CXXFLAGS[@]}" > "$TMP/flags"
    # one file per job; each prints its own errors
    printf '%s\n' "${TODO[@]}" | xargs -P "$JOBS" -I{} bash -c '
        f="$1"; o="$OBJ/$(basename "${f%.cpp}").o"
        mapfile -t FL < "$2"
        C="$3"; [ "$(basename "$f")" = external_factoring.cpp ] && C="$4"
        if "$C" "${FL[@]}" -c "$f" -o "$o.tmp" 2> "$o.log"; then
            mv "$o.tmp" "$o"; echo "  ok  $(basename "$f")"
            [ -s "$o.log" ] && cat "$o.log" >&2; rm -f "$o.log"
        else
            rm -f "$o.tmp"; echo "  FAILED  $(basename "$f")"; cat "$o.log" >&2; exit 255
        fi' _ {} "$TMP/flags" "$CXX" "$CXX_FACTORING" || die "compilation failed (errors above)."
else
    echo "objects are up to date"
fi

# ---------------------------------------------------------------- link
COMMON=()
for f in "${SOURCES[@]}"; do COMMON+=("$OBJ/$(basename "${f%.cpp}").o"); done
# multi_k_searcher (the search) and collect_results (all pairs in one file)
for prog in multi_k:multi_k_searcher collect_results:collect_results; do
    main="${prog%%:*}"; out="$BUILD/${prog##*:}"
    "$CXX" "${CXXFLAGS[@]}" "$OBJ/${main}_main.o" "${COMMON[@]}" "${LIBS[@]}" -o "$out.tmp" \
        || die "linking $(basename "$out") failed."
    mv -f "$out.tmp" "$out"
    echo "built    : $out"
done
echo ""
echo "Done.  Try:  $BUILD/multi_k_searcher --help    (all pairs in one file: $BUILD/collect_results)"
