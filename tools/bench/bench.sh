#!/usr/bin/env bash
# Times two builds of multi_k_searcher against each other on the runs in
# suites.txt and checks that both find exactly the same pairs.
#
#   bash tools/bench/bench.sh OLD_PROGRAM NEW_PROGRAM [threads] [repeats]
#
# threads defaults to all cores, repeats to 3 (the median time is reported).
# The runs alternate old/new so both see the same machine conditions.  Work
# folders go to a temporary directory; the report is printed and saved as
# bench_report.txt in the current folder.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OLD="$(readlink -f "$1")"; NEW="$(readlink -f "$2")"
THREADS="${3:-$(nproc)}"; REPS="${4:-3}"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
REPORT="$PWD/bench_report.txt"

pairs() {  # sorted pair lines of a run folder
    cat "$1"/Data/*/multi_k_results.txt 2>/dev/null | grep -E '^[0-9]+=' | sort -u
}
run() {  # program, folder, hash, start, end -> prints seconds
    rm -rf "$2"; mkdir -p "$2"
    local t0 t1
    t0=$(date +%s.%N)
    "$1" --root "$2" --mode range --hash "$3" --workers "$THREADS" --timeout 0 --report 0 "$4" "$5" > "$2/out.txt" 2>&1 \
        || { echo "run failed: $1 (see $2/out.txt)" >&2; cat "$2/out.txt" >&2; exit 1; }
    t1=$(date +%s.%N)
    grep -q "complete: every k" "$2/out.txt" || { echo "run did not complete: $1" >&2; exit 1; }
    echo "$t1 - $t0" | bc
}
median() { sort -g | awk '{a[NR]=$1} END{print (NR%2) ? a[(NR+1)/2] : (a[NR/2]+a[NR/2+1])/2}'; }

{
echo "old: $OLD"
echo "new: $NEW"
echo "threads: $THREADS   repeats: $REPS   $(date)"
printf '%-34s %9s %9s %8s  %s\n' "run" "old (s)" "new (s)" "speedup" "same pairs"
} | tee "$REPORT"
tot_old=0; tot_new=0; all_same=1
while IFS='|' read -r name hash k0 k1; do
    name="$(echo "$name" | xargs)"; [ -z "$name" ] && continue
    case "$name" in \#*) continue ;; esac
    hash="$(echo "$hash" | xargs -0 | sed 's/^ *//; s/ *$//')"; k0="$(echo "$k0" | xargs)"; k1="$(echo "$k1" | xargs)"
    to=(); tn=()
    for ((r = 0; r < REPS; ++r)); do
        to+=("$(run "$OLD" "$WORK/old" "$hash" "$k0" "$k1")"); pairs "$WORK/old" > "$WORK/old.pairs"
        tn+=("$(run "$NEW" "$WORK/new" "$hash" "$k0" "$k1")"); pairs "$WORK/new" > "$WORK/new.pairs"
        if ! cmp -s "$WORK/old.pairs" "$WORK/new.pairs"; then all_same=0; same="NO (old $(wc -l < "$WORK/old.pairs"), new $(wc -l < "$WORK/new.pairs") lines)"; break; fi
        same="yes ($(( $(wc -l < "$WORK/new.pairs") / 2 )) pairs)"
    done
    mo="$(printf '%s\n' "${to[@]}" | median)"; mn="$(printf '%s\n' "${tn[@]}" | median)"
    tot_old="$(echo "$tot_old + $mo" | bc)"; tot_new="$(echo "$tot_new + $mn" | bc)"
    printf '%-34s %9.2f %9.2f %7.2fx  %s\n' "$name" "$mo" "$mn" "$(echo "$mo / $mn" | bc -l)" "$same" | tee -a "$REPORT"
done < "$HERE/suites.txt"
printf '%-34s %9.2f %9.2f %7.2fx  %s\n' "total" "$tot_old" "$tot_new" "$(echo "$tot_old / $tot_new" | bc -l)" \
    "$([ $all_same = 1 ] && echo "all runs found the same pairs" || echo "PAIRS DIFFER")" | tee -a "$REPORT"
[ $all_same = 1 ]
