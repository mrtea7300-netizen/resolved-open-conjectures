#!/usr/bin/env python3
"""Numerical tests of Lemmas 2, 3, 4, 5(i) and Proposition 6 of proof.md (not part of the proof).

For n with F = floor(sqrt(n)), e = n - F^2 and p = F + s (s >= 1, p prime or not):
   c = floor((s^2+e)/p),  b = s^2 + e - c*p,  a = F - s + c.
Tested against divmod and direct digit sums:
  L2  n = a*p + b, 0 <= b < p, 0 <= a < p, and (a + b >= p)  <=>  (b >= 2s - c);
      for p prime the base-p digit sum of n (computed by repeated division) equals a + b.
  L3  for a fixed value of c, the failing s (a + b < p) are at most two, and if two then they are
      consecutive (so at most one of the two p is prime when F >= 2).
  L4  c(s) is nondecreasing in s and c(S) <= K(F,S) := floor((S^2 + 2F)/(F + S)); the number of
      failing PRIMES in (F, F+S] is at most (number of distinct values of c) <= K(F,S) + 1.
  P6  at most one prime p > F divides n + i (i = 1, 2; Lemma 5(i)), so the primes in (F, F+S] that fail
      "s_p(n) >= p and p does not divide (n+1)...(n+j)" number at most K(F,S) + 1 + j.

Usage:  python lemma_test.py [NEXH] [NRAND]   (defaults 60000 and 4000; about 2 minutes)
"""
import sys
import random
from math import isqrt
from collections import defaultdict

NEXH = int(sys.argv[1]) if len(sys.argv) > 1 else 60_000
NRAND = int(sys.argv[2]) if len(sys.argv) > 2 else 4_000


def primes_upto(n):
    sv = bytearray([1]) * (n + 1)
    sv[:2] = b"\0\0"
    for i in range(2, isqrt(n) + 1):
        if sv[i]:
            sv[i * i::i] = bytearray(len(sv[i * i::i]))
    return sv


PLIM = 3_000_000
IS_PRIME = primes_upto(PLIM)


def digit_sum(n, p):
    s = 0
    while n:
        n, r = divmod(n, p)
        s += r
    return s


stats = dict(n=0, pairs=0, two_per_c=0, max_fail_primes_minus_bound=-10 ** 9, max_ratio=0.0)


def test(n, smax):
    F = isqrt(n)
    e = n - F * F
    assert 0 <= e <= 2 * F
    fails = defaultdict(list)
    prev_c = -1
    fail_primes = []      # s with F+s prime and a+b < p
    bad_j = [[], [], []]  # s with F+s prime and (a+b < p or p | (n+1)..(n+j))
    for s in range(1, smax + 1):
        p = F + s
        c = (s * s + e) // p
        b = s * s + e - c * p
        a = F - s + c
        # Lemma 2
        assert (a, b) == divmod(n, p) and 0 <= a < p and 0 <= b < p
        assert (a + b >= p) == (b >= 2 * s - c)
        # monotonicity used in Lemma 4
        assert c >= prev_c
        prev_c = c
        prime = IS_PRIME[p]
        if prime:
            assert digit_sum(n, p) == a + b
        if a + b < p:
            fails[c].append(s)
            if prime:
                fail_primes.append(s)
        if prime:
            for j in range(3):
                if a + b < p or any((n + u) % p == 0 for u in range(1, j + 1)):
                    bad_j[j].append(s)
        # Lemma 4 / Proposition 6 at every intermediate S = s
        C = (s * s + 2 * F) // (F + s)
        assert c <= C
        if F >= 2:
            assert len(fail_primes) <= len({(x * x + e) // (F + x) for x in fail_primes}) <= C + 1
            for j in range(3):
                assert len(bad_j[j]) <= C + 1 + j, (n, s, j)
            stats["max_fail_primes_minus_bound"] = max(stats["max_fail_primes_minus_bound"],
                                                       len(bad_j[2]) - (C + 3))
        stats["pairs"] += 1
    # Lemma 3
    for c, lst in fails.items():
        assert len(lst) <= 2, (n, c, lst)
        if len(lst) == 2:
            stats["two_per_c"] += 1
            assert lst[1] == lst[0] + 1, (n, c, lst)
            # the proof shows more: the first of the two has b = 0
            assert n % (F + lst[0]) == 0
    # Lemma 5(i): primes > F dividing n+1, n+2
    for u in (1, 2):
        if F >= 2:
            assert sum(1 for s in range(1, smax + 1) if IS_PRIME[F + s] and (n + u) % (F + s) == 0) <= 1
    stats["n"] += 1


for n in range(1, NEXH + 1):
    test(n, 3 * isqrt(n) + 5)            # every s up to 3F+5: far beyond what the proof uses
random.seed(20261126)
for _ in range(NRAND):
    n = random.randrange(10 ** 6, 10 ** 12)
    test(n, min(isqrt(n), 3000))
for F in (60183, 60184, 60185, 10 ** 5, 10 ** 6):   # around the threshold, extreme e
    for e in (0, 1, 2, F - 1, F, F + 1, 2 * F - 1, 2 * F):
        test(F * F + e, isqrt(F * F + e) // 8)

print(f"tested {stats['n']} values of n, {stats['pairs']} pairs (n, s): no assertion failed")
print(f"values of c with two failing s (always consecutive, first with p | n): {stats['two_per_c']}")
print(f"max over all (n, S) of  #bad primes(j=2) - (C+3)  = {stats['max_fail_primes_minus_bound']}  (must be <= 0)")
