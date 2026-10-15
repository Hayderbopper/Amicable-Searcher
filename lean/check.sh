#!/usr/bin/env bash
# Builds the Lean formalization and runs every trust check.  Exit code 0 only if all pass.
#
#   bash check.sh             build + checks, logs in logs/
#   bash check.sh --selftest  also proves that the checks fail on a planted `sorry` / `axiom`
#   SKIP_CACHE=1 bash check.sh   skip `lake exe cache get` (e.g. no access to the Mathlib cache)
#
# Needs elan (https://github.com/leanprover/elan) and git.  The toolchain (lean-toolchain) and
# every dependency (lake-manifest.json) are pinned.  Step 2 downloads each dependency as a
# shallow copy of exactly the pinned commit (much smaller and more reliable than the full
# Mathlib history that `lake` would clone).  Without the Mathlib cache, step 4 compiles the
# ~1200 Mathlib files this project imports: 30-90 minutes, with progress shown as it goes.
set -uo pipefail
cd "$(dirname "$0")"
mkdir -p logs
export PATH="$HOME/.elan/bin:$PATH"

fail() { echo "CHECK FAILED: $*" | tee -a logs/check.log; exit 1; }
step() { echo "== $*" | tee -a logs/check.log; }
: > logs/check.log

PINNED_LEAN='leanprover/lean4:v4.34.1'
PINNED_MATHLIB='d13f23b723b8a846827a245b89c10fc7d3f11612'
LIB_FILES=(AmicableProof.lean AmicableProof)

step "1. toolchain"
command -v elan >/dev/null || fail "elan not found; install it from https://github.com/leanprover/elan"
grep -qx "$PINNED_LEAN" lean-toolchain || fail "lean-toolchain is not $PINNED_LEAN"
grep -q "\"rev\": \"$PINNED_MATHLIB\"" lake-manifest.json || fail "lake-manifest.json does not pin mathlib $PINNED_MATHLIB"
{ elan --version; lean --version; lake --version; } 2>&1 | tee -a logs/check.log

step "2. dependencies (shallow fetch of the commits pinned in lake-manifest.json)"
command -v git >/dev/null || fail "git not found"
command -v python3 >/dev/null || fail "python3 not found (used to read lake-manifest.json)"
python3 -c 'import json; [print(p["name"], p["url"], p["rev"]) for p in json.load(open("lake-manifest.json"))["packages"]]' \
  > logs/packages.txt || fail "cannot read lake-manifest.json"
while read -r name url rev; do
  dir=".lake/packages/$name"
  if [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null)" = "$rev" ]; then
    echo "$name: present" | tee -a logs/check.log; continue
  fi
  echo "$name: fetching $rev" | tee -a logs/check.log
  if [ ! -d "$dir/.git" ]; then
    rm -rf "$dir"; mkdir -p "$dir"
    git init -q "$dir" && git -C "$dir" remote add origin "$url" || fail "git init $dir"
  fi
  ok=0
  for t in 1 2 3; do
    git -C "$dir" fetch --depth 1 origin "$rev" && { ok=1; break; }
    echo "  retry $t" | tee -a logs/check.log; sleep 5
  done
  [ $ok = 1 ] || fail "could not download $name from $url"
  git -C "$dir" checkout -q --force FETCH_HEAD || fail "checkout $name"
done < logs/packages.txt

step "3. Mathlib cache (optional: without it, lake compiles the imported Mathlib files)"
if [ "${SKIP_CACHE:-0}" = "1" ]; then
  echo "skipped (SKIP_CACHE=1)" | tee -a logs/check.log
else
  TO=""; command -v timeout >/dev/null && TO="timeout 900"
  if $TO lake exe cache get > logs/cache.log 2>&1; then
    echo "cache OK" | tee -a logs/check.log
  else
    echo "cache unavailable (see logs/cache.log); building from source" | tee -a logs/check.log
  fi
fi

step "4. build (progress below; from source this takes 30-90 minutes the first time)"
lake build 2>&1 | tee logs/build.log
[ "${PIPESTATUS[0]}" = 0 ] || fail "lake build failed (logs/build.log)"
tail -1 logs/build.log | tee -a logs/check.log
if grep -q "declaration uses 'sorry'" logs/build.log; then fail "a declaration uses sorry"; fi
NWARN=$(grep -c '^warning' logs/build.log || true)
echo "build warnings in AmicableProof: $NWARN" | tee -a logs/check.log

step "5. forbidden words in the library sources"
if grep -rnwE 'sorry|admit|native_decide|unsafe|implemented_by|extern' "${LIB_FILES[@]}" \
     | tee -a logs/check.log | grep -q .; then
  fail "forbidden word in the library (listed above)"
fi
if grep -rnE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable)[[:space:]]+)*axiom[[:space:]]' \
     "${LIB_FILES[@]}" | tee -a logs/check.log | grep -q .; then
  fail "axiom declaration in the library (listed above)"
fi
echo "none found" | tee -a logs/check.log

step "6. axioms of every theorem (kernel-level: #print axioms for each)"
lake env lean CheckAxioms.lean > logs/axioms.log 2>&1 || { tail -20 logs/axioms.log; fail "axiom check failed (logs/axioms.log)"; }
grep -q '^AXIOM CHECK OK' logs/axioms.log || fail "axiom check did not report OK"
grep '^AXIOM CHECK OK' logs/axioms.log | tee -a logs/check.log

step "7. open goals elaborate (Open/, outside the library; statements only)"
for f in Open/*.lean; do
  [ -e "$f" ] || continue
  lake env lean "$f" > "logs/open_$(basename "$f" .lean).log" 2>&1 || fail "$f does not elaborate"
  echo "$f elaborates" | tee -a logs/check.log
done

if [ "${1:-}" = "--selftest" ]; then
  step "8. self-test: the checks must reject a planted sorry and a planted axiom"
  T=AmicableProof/ZzSelfTest.lean
  cp AmicableProof.lean logs/AmicableProof.lean.bak
  printf 'theorem zz_planted : 1 = 2 := by sorry\n' > "$T"
  if grep -rnwE 'sorry' "$T" >/dev/null; then echo "grep catches planted sorry: yes" | tee -a logs/check.log
  else rm -f "$T"; fail "grep missed planted sorry"; fi
  echo 'import AmicableProof.ZzSelfTest' >> AmicableProof.lean
  lake build AmicableProof > logs/selftest_build.log 2>&1
  if lake env lean CheckAxioms.lean > logs/selftest_axioms.log 2>&1; then
    cp logs/AmicableProof.lean.bak AmicableProof.lean; rm -f "$T"; fail "axiom check accepted a sorry"
  fi
  grep -q 'sorryAx' logs/selftest_axioms.log && echo "axiom check rejects planted sorry (sorryAx): yes" | tee -a logs/check.log
  printf 'axiom zz_planted_ax : 1 = 2\ntheorem zz_uses : 1 = 2 := zz_planted_ax\n' > "$T"
  if grep -rnE '^[[:space:]]*axiom[[:space:]]' "$T" >/dev/null; then echo "grep catches planted axiom: yes" | tee -a logs/check.log; fi
  lake build AmicableProof > logs/selftest_build2.log 2>&1
  if lake env lean CheckAxioms.lean > logs/selftest_axioms2.log 2>&1; then
    cp logs/AmicableProof.lean.bak AmicableProof.lean; rm -f "$T"; fail "axiom check accepted an axiom"
  fi
  grep -q 'axiom declared' logs/selftest_axioms2.log && echo "axiom check rejects planted axiom: yes" | tee -a logs/check.log
  cp logs/AmicableProof.lean.bak AmicableProof.lean; rm -f "$T" logs/AmicableProof.lean.bak
  lake build > /dev/null 2>&1 || fail "rebuild after self-test failed"
  echo "self-test passed; library restored" | tee -a logs/check.log
fi

echo "ALL CHECKS PASSED" | tee -a logs/check.log
