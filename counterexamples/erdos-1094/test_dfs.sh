#!/usr/bin/env bash
# Soundness tests for the box-tree search dfs_1094.c.  Run inside WSL / Linux after build_dfs.sh:
#     bash test_dfs.sh            (about 2 minutes, one core; the brute force takes most of it)
# Every test prints PASS or FAIL; the script exits non-zero on the first FAIL.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p work/test
T=work/test
BRUTE_N=${BRUTE_N:-60000}
rows() { grep -v '^#' "$1" | sort -n -k1,1 -k2,2; }
fail() { echo "FAIL: $1"; exit 1; }

echo "== (a) brute force (brute_1094.c) against the tree, 2 <= k <= n/2, n <= $BRUTE_N =="
./bin/brute "$BRUTE_N" 64 > $T/brute_B64.txt
./bin/dfs64 search 0 "$BRUTE_N" 64 > $T/dfs_B64.txt
./bin/dfs128 search 0 "$BRUTE_N" 64 > $T/dfs128_B64.txt
./bin/dfs64 search 0 "$BRUTE_N" 64 --fixedS > $T/dfs_B64_fixedS.txt
tail -1 $T/brute_B64.txt
tail -1 $T/dfs_B64.txt
tail -1 $T/dfs_B64_fixedS.txt
diff <(rows $T/brute_B64.txt) <(rows $T/dfs_B64.txt) > /dev/null || fail "tree != brute (B=64)"
diff <(rows $T/brute_B64.txt) <(rows $T/dfs128_B64.txt) > /dev/null || fail "128-bit tree != brute (B=64)"
diff <(rows $T/brute_B64.txt) <(rows $T/dfs_B64_fixedS.txt) > /dev/null || fail "fixed-S tree != brute (B=64)"
# in fixed-S mode the leaves are exactly the pairs with lpf > 13: compare the count with brute force
bg=$(tail -1 $T/brute_B64.txt | sed 's/.*lpf_gt_13=\([0-9]*\).*/\1/')
dl=$(tail -1 $T/dfs_B64_fixedS.txt | sed 's/.*leaves=\([0-9]*\).*/\1/')
[ "$bg" = "$dl" ] || fail "fixed-S leaves ($dl) != brute count of lpf > 13 ($bg)"
echo "PASS (a): region n <= 64k, n <= $BRUTE_N: $(rows $T/brute_B64.txt | wc -l) pairs, identical sets" \
     "(64-bit, 128-bit, fixed-S); fixed-S leaves = brute count of lpf > 13 = $bg"

echo "== (a') the same with no ratio limit (B = 0) =="
./bin/brute "$BRUTE_N" 0 > $T/brute_B0.txt
./bin/dfs64 search 0 "$BRUTE_N" 0 > $T/dfs_B0.txt
./bin/dfs64 search 0 "$BRUTE_N" 0 --fixedS > $T/dfs_B0_fixedS.txt
tail -1 $T/brute_B0.txt
tail -1 $T/dfs_B0.txt
diff <(rows $T/brute_B0.txt) <(rows $T/dfs_B0.txt) > /dev/null || fail "tree != brute (B=0)"
diff <(rows $T/brute_B0.txt) <(rows $T/dfs_B0_fixedS.txt) > /dev/null || fail "fixed-S tree != brute (B=0)"
diff <(rows $T/brute_B0.txt) <(rows $T/brute_B64.txt) > /dev/null || fail "a pair with n > 64k exists below $BRUTE_N"
bg=$(tail -1 $T/brute_B0.txt | sed 's/.*lpf_gt_13=\([0-9]*\).*/\1/')
dl=$(tail -1 $T/dfs_B0_fixedS.txt | sed 's/.*leaves=\([0-9]*\).*/\1/')
[ "$bg" = "$dl" ] || fail "fixed-S leaves ($dl) != brute count of lpf > 13 ($bg), B=0"
echo "PASS (a'): all 2 <= k <= n/2, n <= $BRUTE_N: identical sets; no pair has n > 64k; lpf > 13 count $bg"

echo "== (a'') sub-ranges of n add up =="
./bin/dfs64 search 0 20000 64 > $T/r1.txt
./bin/dfs64 search 20001 57074 64 > $T/r2.txt
./bin/dfs64 search 57075 "$BRUTE_N" 64 > $T/r3.txt
diff <(rows $T/brute_B64.txt) <(cat $T/r1.txt $T/r2.txt $T/r3.txt | grep -v '^#' | sort -n -k1,1 -k2,2) > /dev/null \
    || fail "sub-ranges do not add up"
echo "PASS (a''): three n-ranges give the same set as one run"

echo "== (b) the earlier submask scan to n <= 10^7 (data/exceptions_1094.tsv) =="
./bin/dfs64 search 0 10000000 64 > $T/dfs_1e7.txt
./bin/dfs128 search 0 10000000 64 > $T/dfs128_1e7.txt
tail -1 $T/dfs_1e7.txt
# rows of the TSV that are exceptions to max(n/k,13): flag bit 2
awk -F'\t' 'NR>1 && int($5/2)%2==1 {print $1, $2, $3}' data/exceptions_1094.tsv | sort -n -k1,1 -k2,2 > $T/tsv_B.txt
awk -F'\t' 'NR>1 && int($5/2)%2==1 && $1 > 64*$2 {print $1, $2, $3}' data/exceptions_1094.tsv > $T/tsv_B_outside.txt
awk -F'\t' 'NR>1 && int($5/2)%2==0 {print $1, $2, $3}' data/exceptions_1094.tsv > $T/tsv_notB.txt
diff $T/tsv_B.txt <(rows $T/dfs_1e7.txt) > /dev/null || fail "tree to 1e7 != TSV rows with flag B"
diff $T/tsv_B.txt <(rows $T/dfs128_1e7.txt) > /dev/null || fail "128-bit tree to 1e7 != TSV rows with flag B"
echo "PASS (b): tree to 10^7 gives exactly the $(wc -l < $T/tsv_B.txt) TSV rows with lpf > max(n/k,13);" \
     "TSV rows of that kind with n > 64k: $(wc -l < $T/tsv_B_outside.txt);" \
     "other TSV rows (lpf <= 13, exceptions to max(n/k,k) only): $(wc -l < $T/tsv_notB.txt)"
echo "    the other rows, all with k <= 11, n <= 95 and n <= 64k, are covered by the brute force of (a'):"
awk '{printf "    (%s,%s) lpf %s\n", $1, $2, $3}' $T/tsv_notB.txt | tr '\n' ' '; echo

echo "== (c) randomized path tests: pruning never drops a carry-free pair =="
./bin/dfs64 selftest 1 3000000 || fail "selftest 64"
./bin/dfs64 selftest 2 3000000 || fail "selftest 64"
./bin/dfs128 selftest 3 2000000 || fail "selftest 128"
./bin/dfs128 selftest 4 2000000 || fail "selftest 128"
echo "PASS (c)"

echo "== (d) submask windows (brute_1094.c, window mode) against the tree at 10^8 .. 5*10^11 =="
# each window is [n-300, n+300] around the first n of a cluster of rows; BIG=1 adds three
# windows that cost about 10^10 submasks together (a few minutes)
WINDOWS="113186693:113187293 114780869:114781469"
if [ "${BIG:-0}" = 1 ]; then
    WINDOWS="$WINDOWS 539245098271:539245098871 454771460947:454771461547 48810917510:48810918110"
fi
for w in $WINDOWS; do
    lo=${w%:*}; hi=${w#*:}
    ./bin/brute window "$lo" "$hi" 64 > $T/win_brute.txt
    ./bin/dfs64 search "$lo" "$hi" 64 > $T/win_dfs.txt
    diff <(rows $T/win_brute.txt) <(rows $T/win_dfs.txt) > /dev/null || fail "window [$lo,$hi]: tree != submask enumeration"
    echo "  window [$lo, $hi]: $(rows $T/win_dfs.txt | wc -l) rows in both;" \
         "$(tail -1 $T/win_brute.txt | sed 's/.*submasks_tested=\([0-9]*\).*/\1/') submasks tested"
done
echo "PASS (d)"
echo "ALL TESTS PASSED"
