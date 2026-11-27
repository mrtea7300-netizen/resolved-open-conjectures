#!/usr/bin/env python3
"""Stdlib-only verifier for the complete list of integer counterexamples to Ramanujan's inequality
       pi(x)^2 < e*x*pi(x/e)/log(x)       (counterexample: x >= 2 with pi(x)^2 >= e*x*pi(x/e)/log x).
Usage: python3 verify.py counterexample_runs.txt [N_brute] [--lucy]
  1. structure: runs sorted, disjoint, non-adjacent; total count reported.
  2. brute force: sieve pi up to N_brute (default 2*10^6), test every 2 <= x <= N_brute with 50-digit
     Decimal arithmetic, compare with the runs.
  3. --lucy: for the last 2 runs and the boundaries around them, recompute pi(x), pi(floor(x/e)) with an
     independent Lucy_Hedgehog prime count (no sieve) and recheck every claimed status (slow, ~minutes).
"""
import sys
from decimal import Decimal, getcontext
getcontext().prec = 50
E = Decimal(1).exp()

def fails(x, a, b):
    if b == 0:
        return True
    return Decimal(a * a) >= E * x * b / Decimal(x).ln()

def floor_x_over_e(x):
    q = int(Decimal(x) / E)          # 50 digits: exact floor since x/e is never within 1e-30 of an integer here
    return q

def pi_lucy(n):
    if n < 2:
        return 0
    r = int(n ** 0.5)
    while r * r > n: r -= 1
    while (r + 1) * (r + 1) <= n: r += 1
    S = [v - 1 for v in range(r + 1)]; S[0] = 0
    L = [0] + [n // i - 1 for i in range(1, r + 1)]
    for p in range(2, r + 1):
        if S[p] == S[p - 1]:
            continue
        sp = S[p - 1]; p2 = p * p
        lim = min(r, n // p2)
        for i in range(1, lim + 1):
            d = i * p
            L[i] -= (L[d] if d <= r else S[n // d]) - sp
        for v in range(r, p2 - 1, -1):
            S[v] -= S[v // p] - sp
    return L[1]

def main():
    fn = sys.argv[1]
    N = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 2 * 10 ** 6
    runs = [tuple(map(int, l.split())) for l in open(fn) if l.strip()]
    for (lo, hi) in runs:
        assert 2 <= lo <= hi
    for (l1, h1), (l2, h2) in zip(runs, runs[1:]):
        assert h1 + 1 < l2, (h1, l2)
    total = sum(h - lo + 1 for lo, hi in [(r[0], r[1]) for r in runs] for h in [hi])
    print(f"runs={len(runs)} total counterexamples={total} first={runs[0]} last={runs[-1]}")
    # brute force
    sieve = bytearray([1]) * (N + 1); sieve[0] = sieve[1] = 0
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(range(i * i, N + 1, i)))
    pi = [0] * (N + 1); c = 0
    for i in range(N + 1):
        c += sieve[i]; pi[i] = c
    brute = set(x for x in range(2, N + 1) if fails(x, pi[x], pi[floor_x_over_e(x)]))
    claimed = set()
    for lo, hi in runs:
        if lo > N: break
        claimed.update(range(lo, min(hi, N) + 1))
    assert brute == claimed, (sorted(brute ^ claimed)[:10])
    print(f"brute force 2..{N}: {len(brute)} counterexamples, identical to the runs file")
    if '--lucy' in sys.argv:
        for lo, hi in runs[-2:]:
            for x, want in [(lo - 1, False), (lo, True), (hi, True), (hi + 1, False)]:
                a, b = pi_lucy(x), pi_lucy(floor_x_over_e(x))
                got = fails(x, a, b)
                print(f"  x={x} pi(x)={a} pi(x/e)={b} fails={got}")
                assert got == want
        print("Lucy checks at the last 2 runs: OK")
    print("ALL CHECKS PASSED")

main()
