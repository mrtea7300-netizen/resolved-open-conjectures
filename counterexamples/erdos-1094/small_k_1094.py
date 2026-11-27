#!/usr/bin/env python3
"""Erdős #1094 for small k and ALL n: the exceptions to lpf(C(N,k)) <= max(N/k, k) with k <= KMAX.

Lemma (the argument on p. 522 of Erdős-Lacampagne-Selfridge, Acta Arith. 49 (1988), completed in
the README).  Let k >= 2, N >= 2k and lpf(C(N,k)) > max(N/k, k).  Let m be the multiple of k
among N-k+1, ..., N.  Then m divides k!.

So for a given k only the N in [m, m+k-1], m a divisor of k! with k | m, can be exceptions.
This script enumerates all of them and decides each one exactly:

  1. Lucas: if some prime p <= k divides C(N,k) (a base-p digit of k exceeds the digit of N),
     the pair is not an exception.
  2. Otherwise C(N,k) = prod b_i, where b_i is N-k+i with all primes <= k removed.  If N < k^2
     then max(N/k, k) = k < lpf and the pair is an exception.  If N >= k^2, every prime factor
     of every b_i must exceed N/k >= sqrt(N) >= sqrt(b_i), i.e. every b_i must be 1 or a prime
     greater than N/k.  Primality is tested with gmpy2.is_prime, which never rejects a prime, so
     no exception can be lost; a composite that passed would show up as an extra output line.

Usage:  python small_k_1094.py [KMAX]      (default 30: 20 s; 34: 1.5 min; 40: about half an hour)
"""
import sys
import time

import gmpy2

KNOWN = {(7, 3), (13, 4), (14, 4), (23, 5), (44, 8), (46, 10), (47, 10), (47, 11), (62, 6),
         (74, 10), (94, 10), (95, 10), (241, 16), (284, 28)}


def primes_upto(m):
    return [q for q in range(2, m + 1) if all(q % d for d in range(2, int(q ** 0.5) + 1))]


def lucas_divides(N, k, p):
    while k:
        if k % p > N % p:
            return True
        N //= p
        k //= p
    return False


def divisors_multiple_of(k, primes):
    """All divisors m of k! with k | m."""
    exps = []
    for p in primes:
        e, q = 0, p
        while q <= k:
            e += k // q
            q *= p
        lo, t = 0, k
        while t % p == 0:
            t //= p
            lo += 1
        exps.append((p, lo, e))
    # the parts made of primes >= 5 are kept in a list; the powers of 2 and 3 are looped over
    # lazily, so that the full divisor list (10^8 entries for k = 40) is never stored
    rest = [1]
    for p, lo, e in exps[2:]:
        rest = [m * p ** a for m in rest for a in range(lo, e + 1)]
    small = [1]
    for p, lo, e in exps[:2]:
        small = [m * p ** a for m in small for a in range(lo, e + 1)]
    return rest, small


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    found = set()
    t0 = time.time()
    total = 0
    for k in range(2, kmax + 1):
        primes = primes_upto(k)
        odd_primes = primes[1:]
        rest, small = divisors_multiple_of(k, primes)
        ndivs = len(rest) * len(small)
        cand = 0
        survive1 = 0
        for m in (r * s for r in rest for s in small):
            for N in range(max(m, 2 * k), m + k):
                cand += 1
                if k & ~N:                       # p = 2
                    continue
                if any(lucas_divides(N, k, p) for p in odd_primes):
                    continue
                survive1 += 1
                ok = True
                if N >= k * k:
                    for x in range(N - k + 1, N + 1):
                        b = x
                        for p in primes:
                            while b % p == 0:
                                b //= p
                        if b == 1:
                            continue
                        if b * k <= N or not gmpy2.is_prime(b, 30):
                            ok = False
                            break
                if ok:
                    found.add((N, k))
        total += cand
        print(f"k = {k:2d}: {ndivs:9d} divisors m of k! with k | m, {cand:10d} candidates N, "
              f"{survive1:6d} with no prime factor <= k, exceptions so far: {len(found)} "
              f"({time.time() - t0:.0f}s)", flush=True)
    print("exceptions with k <=", kmax, ":", sorted(found))
    expected = {(n, k) for n, k in KNOWN if k <= kmax}
    if found == expected:
        print(f"PASS: for 2 <= k <= {kmax} and every N >= 2k the exceptions to "
              f"lpf(C(N,k)) <= max(N/k, k) are exactly the {len(expected)} known ones with k <= {kmax} "
              f"({total} candidates tested)")
    else:
        print("MISMATCH: extra", sorted(found - expected), "missing", sorted(expected - found))
        sys.exit(1)


if __name__ == "__main__":
    main()
