#!/usr/bin/env python3
"""Tables for the README from the output of run_dfs.py (works on the plain or the gzipped TSV).

    python analyze_dfs.py data/dfs_B64.tsv.gz data/dfs_B64.runs.tsv [--md data/dfs_B64_summary.md]

All rows of the TSV have lpf > max(n/k, 13), so the sub-list for a threshold T >= 13 is simply the
rows with lpf > T.  Heuristic exponents: a "random" pair below N is carry-free in base p with
probability about N^(-e_p), e_p = log(2p/(p+1))/log(p); for the primes up to P this suggests
about N^alpha(P) pairs below N, alpha(P) = 2 - sum_{p<=P} e_p.
"""
import argparse
import gzip
import math
import sys
from fractions import Fraction

KNOWN_1094 = {(7, 3), (13, 4), (14, 4), (23, 5), (44, 8), (46, 10), (47, 10), (47, 11), (62, 6),
              (74, 10), (94, 10), (95, 10), (241, 16), (284, 28)}
MATHWORLD_12 = {(241, 16), (439, 33), (317, 56), (482, 130), (998, 256), (998, 260), (14273, 896),
                (14277, 900), (62, 6), (959, 56), (474, 66), (284, 28)}
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def alpha(P):
    return 2 - sum(math.log(2 * p / (p + 1)) / math.log(p) for p in PRIMES if p <= P)


def read_rows(path):
    op = gzip.open if path.endswith(".gz") else open
    rows = []
    with op(path, "rt", encoding="ascii") as f:
        assert f.readline().split()[:3] == ["n", "k", "lpf"]
        for line in f:
            p = line.split()
            if p:
                rows.append((int(p[0]), int(p[1]), int(p[2])))
    return rows


def ndigits(x, p):
    d = 0
    while x:
        d += 1
        x //= p
    return d


def chance(k, P):
    """Independence model: chance that a pair which is carry-free for the primes <= 13 is also
    carry-free for every prime 17 <= p <= P: (p+1)/(2p) for each base-p digit of k."""
    c = 1.0
    for p in PRIMES:
        if 13 < p <= P:
            c *= ((p + 1) / (2 * p)) ** ndigits(k, p)
    return c


def slope(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tsv")
    ap.add_argument("runs")
    ap.add_argument("--md", default=None)
    args = ap.parse_args()
    rows = read_rows(args.tsv)
    runs = []
    with open(args.runs) as f:
        f.readline()
        for line in f:
            p = line.split()
            runs.append((int(p[0]), int(p[1]), int(p[3]), int(p[5]), float(p[6])))
    nmax = max(r[1] for r in runs)
    D = len(str(nmax)) - 1 if str(nmax)[0] == "1" and set(str(nmax)[1:]) <= {"0"} else len(str(nmax))
    out = []
    w = out.append

    w(f"Region: 2 <= k, 2k <= n <= min(N, 64k), N = {nmax}. Rows: {len(rows)} pairs with "
      f"lpf(C(n,k)) > max(n/k, 13).\n")
    w("| threshold T | pairs with lpf > max(n/k, T) | largest n among them | heuristic exponent alpha(T) |")
    w("|---:|---:|---:|---:|")
    for T in (13, 17, 19, 23, 29):
        sub = [r for r in rows if r[2] > T]
        w(f"| {T} | {len(sub)} | {max((r[0] for r in sub), default='-')} | {alpha(T):+.4f} |")
    w("")
    w("Rows by lpf: " + ", ".join(f"lpf {l}: {sum(1 for r in rows if r[2] == l)}"
                                 for l in sorted({r[2] for r in rows})) + ".\n")

    e = sorted(r for r in rows if r[2] > r[1])
    w(f"Pairs with lpf > max(n/k, k) (Erdős #1094) among the rows: {len(e)}: "
      + ", ".join(f"({n},{k})" for n, k, _ in e)
      + f". All are among the 14 known exceptions: {set((n, k) for n, k, _ in e) <= KNOWN_1094}. "
      "(The other known ones have lpf <= 13 and are not rows of this list.)\n")
    g = sorted(r for r in rows if 8 * r[0] > 137 * r[1])
    w(f"Pairs with n > 17.125 k (and lpf > n/k): {len(g)}: "
      + ", ".join(f"({n},{k}) lpf {l}, n/k = {float(Fraction(n, k)):.4f}" for n, k, l in g) + ".\n")
    top = max(rows, key=lambda r: Fraction(r[0], r[1]))
    w(f"Largest ratio n/k in the list: {float(Fraction(top[0], top[1])):.6f} at ({top[0]},{top[1]}), "
      f"lpf {top[2]}.\n")
    w(f"The 12 pairs of the MathWorld table are all rows: {MATHWORLD_12 <= set((n, k) for n, k, _ in rows)}; "
      f"rows not in that table: {len(rows) - 12}.\n")

    w("Pairs with lpf >= 19 (i.e. lpf > max(n/k, 17)), complete list:\n")
    w("| n | k | lpf | n/k |")
    w("|---:|---:|---:|---:|")
    for n, k, l in rows:
        if l >= 19:
            w(f"| {n} | {k} | {l} | {float(Fraction(n, k)):.4f} |")
    w("")

    # per decade
    w("Counts by decade of n (10^d <= n < 10^(d+1)); `cum` = pairs with n < 10^(d+1); "
      f"alpha(13) = {alpha(13):.4f}; nodes = boxes visited by the tree for n < 10^(d+1), "
      "interpolated inside the octave that contains 10^(d+1):\n")
    w("| d | lpf>13 | cum | cum / 10^(alpha(13)(d+1)) | lpf>17 | model for lpf>17 | lpf>19 | lpf>23 | lpf>29 | distinct n | tree nodes (cum) |")
    w("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    cum = 0
    xs, ys = [], []
    a13 = alpha(13)
    for d in range(1, D):
        lo, hi = 10 ** d, 10 ** (d + 1)
        sub = [r for r in rows if lo <= r[0] < hi]
        cum += len(sub) if d > 1 else len([r for r in rows if r[0] < hi])
        nodes = 0
        for rlo, rhi, nd, _, _ in runs:
            if rhi < hi:
                nodes += nd
            elif rlo < hi:
                nodes += nd * (hi - rlo) // (rhi - rlo + 1)
        c = [sum(1 for r in sub if r[2] > T) for T in (17, 19, 23, 29)]
        m17 = sum(chance(r[1], 17) for r in sub)
        w(f"| {d} | {len(sub)} | {cum} | {cum / 10 ** (a13 * (d + 1)):.2f} | {c[0]} | {m17:.3f} | {c[1]} | {c[2]} | {c[3]} | "
          f"{len({r[0] for r in sub})} | {nodes} |")
        if d >= 6:
            xs.append((d + 1) * math.log(10)); ys.append(math.log(cum))
    w("")
    w(f"Least-squares slope of log(cum) against log(N) over N = 10^7 .. 10^{D}: {slope(xs, ys):.4f} "
      f"(heuristic alpha(13) = {a13:.4f}).\n")
    w("Independence model for the higher thresholds (each row is given the chance "
      "prod_{17 <= p <= T} ((p+1)/(2p))^(number of base-p digits of k) of also being carry-free "
      "for the primes 17..T; rows of one cluster are far from independent, so this is only an "
      "expected value):\n")
    w("| threshold T | observed, all n | model, all n | observed, n >= 10^8 | model, n >= 10^8 |")
    w("|---:|---:|---:|---:|---:|")
    for T in (17, 19, 23, 29):
        w(f"| {T} | {sum(1 for r in rows if r[2] > T)} | {sum(chance(r[1], T) for r in rows):.3f} | "
          f"{sum(1 for r in rows if r[2] > T and r[0] >= 10 ** 8)} | "
          f"{sum(chance(r[1], T) for r in rows if r[0] >= 10 ** 8):.4f} |")
    w("")
    tot_nodes = sum(r[2] for r in runs)
    w(f"Tree size: {tot_nodes} boxes visited in total ({tot_nodes / len(rows):.0f} per pair found), "
      f"{sum(r[4] for r in runs):.1f} s of CPU.\n")

    # clusters: rows grouped by runs of n with gaps < n/1000
    clusters = []
    for r in rows:
        if clusters and r[0] - clusters[-1][-1][0] <= clusters[-1][-1][0] // 1000:
            clusters[-1].append(r)
        else:
            clusters.append([r])
    big = sorted(clusters, key=len, reverse=True)[:8]
    w(f"Clustering: {len(clusters)} clusters (consecutive rows whose n differ by at most 0.1%); "
      "the largest:\n")
    w("| pairs | first n | last n | n/k range | lpf values |")
    w("|---:|---:|---:|---|---|")
    for c in big:
        rs = [float(Fraction(n, k)) for n, k, _ in c]
        w(f"| {len(c)} | {c[0][0]} | {c[-1][0]} | {min(rs):.4f} .. {max(rs):.4f} | "
          f"{sorted({l for _, _, l in c})} |")
    text = "\n".join(out) + "\n"
    if args.md:
        with open(args.md, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
    sys.stdout.reconfigure(encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
