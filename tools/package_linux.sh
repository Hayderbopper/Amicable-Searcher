#!/usr/bin/env bash
# Makes a self-contained Linux release folder from a portable build:
#   ./build.sh --portable && bash tools/package_linux.sh [NAME]
# The programs and the shared libraries they need (GMP, MPFR, FLINT,
# primesieve, libstdc++) go into dist/NAME/, the programs with an rpath of
# $ORIGIN/lib, so the folder runs without installing anything.  Only glibc is
# taken from the system (the build machine's version or newer).
set -euo pipefail
cd "$(dirname "$0")/.."
NAME="${1:-amicable-searcher-linux-x86_64}"
command -v patchelf >/dev/null || { echo "patchelf not found (sudo apt install patchelf)" >&2; exit 1; }
D="dist/$NAME"
rm -rf "$D"; mkdir -p "$D/lib"
for p in multi_k_searcher collect_results; do cp "Build/$p" "$D/"; done
# every shared library except glibc's own
for p in multi_k_searcher collect_results; do
    ldd "Build/$p" | awk '/=> \//{print $3}'
done | sort -u | while read -r lib; do
    case "$(basename "$lib")" in
        libc.so*|libm.so*|libpthread.so*|libdl.so*|librt.so*|ld-linux*) continue ;;
    esac
    cp -L "$lib" "$D/lib/"
done
for f in "$D"/lib/*.so*; do patchelf --set-rpath '$ORIGIN' "$f"; done
for p in multi_k_searcher collect_results; do patchelf --set-rpath '$ORIGIN/lib' "$D/$p"; done
cp README.md LICENSE config.txt "$D/"
cp -r credits "$D/"
[ -f third_party/hurchalla/LICENSE ] && cp third_party/hurchalla/LICENSE "$D/credits/hurchalla-LICENSE"
tar -C dist -czf "dist/$NAME.tar.gz" "$NAME"
echo "dist/$NAME.tar.gz"
