#!/usr/bin/env bash
# Downloads Jeffrey Hurchalla's header-only factoring library (see hurchalla/LICENSE) at
# the commits this project was tested with and puts its headers in
#   third_party/hurchalla/include
# build.sh runs this by itself when the headers are missing.  Needs git.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEST="$HERE/hurchalla"

# factoring pins the other two (see its CMakeLists.txt)
FACTORING=a1dfea9e38daab9e25ba7c0f1b38af1959fbdd6a
MODULAR=cb5e74a154dc665ffd50ab04348677e596dd362a
UTIL=9163344ee69f21a21cb8928dd30fc2ff15e94f0c

command -v git >/dev/null 2>&1 || { echo "get_hurchalla.sh: git is needed (sudo apt install git)" >&2; exit 1; }

fetch() {  # repo commit dir
    local dir="$DEST/src/$1"
    if [ ! -d "$dir/.git" ]; then
        rm -rf "$dir"
        git init -q "$dir"
        git -C "$dir" remote add origin "https://github.com/hurchalla/$1.git"
    fi
    git -C "$dir" fetch -q --depth 1 origin "$2"
    git -C "$dir" checkout -q --force FETCH_HEAD
}

echo "fetching hurchalla factoring, modular_arithmetic and util..."
fetch factoring "$FACTORING"
fetch modular_arithmetic "$MODULAR"
fetch util "$UTIL"

rm -rf "$DEST/include"
mkdir -p "$DEST/include"
for inc in "$DEST/src/factoring/include" \
           "$DEST/src/modular_arithmetic/modular_arithmetic/include" \
           "$DEST/src/modular_arithmetic/montgomery_arithmetic/include" \
           "$DEST/src/util/include"; do
    cp -R "$inc/." "$DEST/include/"
done
cp "$DEST/src/factoring/LICENSE" "$DEST/LICENSE"
[ -f "$DEST/include/hurchalla/factoring/factorize.h" ] \
    && [ -f "$DEST/include/hurchalla/util/programming_by_contract.h" ] \
    || { echo "get_hurchalla.sh: headers incomplete after download" >&2; exit 1; }
echo "hurchalla headers: $DEST/include"
