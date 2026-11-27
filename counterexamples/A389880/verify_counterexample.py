#!/usr/bin/env python3
"""
Standalone, zero-dependency independent verifier for the counterexample at n = 146
to both:
  - OEIS A321651 Conjecture 2 (Zhi-Wei Sun, 2018)
  - OEIS A389880 (Zhi-Wei Sun, Nov 2025)

Uses ONLY the textbook subset-sum definition of a practical number (no Stewart's
theorem, no external libraries):
  m >= 1 is practical iff every integer r with 1 <= r <= m is a sum of distinct
  positive divisors of m.

Step 1: Reproduces exact published OEIS A389880 terms for n = 1..8:
        [1, 1, 0, 2, 0, 4, 0, 44].
Step 2: Verifies the explicit Hall's Marriage Theorem witness at n = 146:
        |S| = 72, |N(S)| = 71, and for every u in S and every v in {1..146} \\ N(S),
        exhibits an integer r with 1 <= r <= u*v that cannot be written as a sum of
        distinct divisors of u*v.
"""

import itertools
import time

OEIS_A389880_FIRST_8 = [1, 1, 0, 2, 0, 4, 0, 44]

# Explicit 72-element subset S of {1..146}
S_146 = [
    5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 34, 35, 37, 38, 41, 43, 46, 47,
    49, 51, 53, 55, 57, 58, 59, 61, 62, 65, 67, 69, 71, 73, 74, 77, 79, 82,
    83, 85, 86, 87, 89, 91, 93, 94, 95, 97, 101, 103, 106, 107, 109, 111,
    113, 115, 118, 119, 121, 122, 123, 125, 127, 129, 131, 133, 134, 137,
    139, 141, 142, 143, 145, 146,
]

# Explicit 71-element neighborhood N(S) in {1..146}
NS_146 = [
    4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 26, 27, 28, 30, 32,
    33, 36, 39, 40, 42, 44, 45, 48, 50, 52, 54, 56, 60, 63, 64, 66, 68, 70,
    72, 75, 76, 78, 80, 81, 84, 88, 90, 92, 96, 98, 99, 100, 102, 104, 105,
    108, 110, 112, 114, 116, 117, 120, 124, 126, 128, 130, 132, 135, 136,
    138, 140, 144,
]


def divisors(m):
    divs = []
    d = 1
    while d * d <= m:
        if m % d == 0:
            divs.append(d)
            if d * d != m:
                divs.append(m // d)
        d += 1
    divs.sort()
    return divs


def first_unrepresentable(m):
    """
    Directly from the subset-sum definition: sorted positive divisors d_1 < ... < d_t
    of m represent every integer in [1, m] as a sum of distinct divisors iff the
    running reachable bound `reach` never encounters a divisor d > reach + 1 before
    reaching m. If d > reach + 1, then r = reach + 1 <= m cannot be written as any
    sum of distinct divisors of m (since all divisors <= reach sum to at most reach,
    and every remaining divisor is >= d > reach + 1).
    Returns None if m is practical, or the exact unrepresentable integer r <= m.
    """
    reach = 0
    for d in divisors(m):
        if d > reach + 1:
            return reach + 1
        reach += d
        if reach >= m:
            return None
    return reach + 1 if reach < m else None


def is_practical_direct(m):
    return m >= 1 and first_unrepresentable(m) is None


def count_a389880(n):
    if n == 1:
        return 1
    prac = {}
    cnt = 0
    for perm in itertools.permutations(range(2, n + 1)):
        seen = {1}
        ok = True
        for k, fk in enumerate(perm, 2):
            prod = k * fk
            if prod in seen:
                ok = False
                break
            p = prac.get(prod)
            if p is None:
                p = is_practical_direct(prod)
                prac[prod] = p
            if not p:
                ok = False
                break
            seen.add(prod)
        if ok:
            cnt += 1
    return cnt


def main():
    t0 = time.time()

    # Step 1: Reproduce OEIS A389880 for n = 1..8
    got = [count_a389880(n) for n in range(1, 9)]
    assert got == OEIS_A389880_FIRST_8, f"OEIS mismatch: got {got}, expected {OEIS_A389880_FIRST_8}"
    print(f"Step 1: Reproduced OEIS A389880 n=1..8 ({got}) in {time.time() - t0:.2f}s: PASS")

    # Step 2: Verify Hall witness at n = 146 directly from subset-sum definition
    t1 = time.time()
    n = 146
    assert len(S_146) == 72 and len(set(S_146)) == 72
    assert len(NS_146) == 71 and len(set(NS_146)) == 71
    assert all(1 <= x <= n for x in S_146)
    assert all(1 <= x <= n for x in NS_146)
    assert set(S_146).isdisjoint(set(NS_146))

    ns_set = set(NS_146)
    forbidden_v = [v for v in range(1, n + 1) if v not in ns_set]
    assert len(forbidden_v) == n - len(NS_146) == 75

    checked_pairs = 0
    for u in S_146:
        for v in forbidden_v:
            r = first_unrepresentable(u * v)
            assert r is not None and 1 <= r <= u * v, (
                f"FAILED: {u} * {v} = {u * v} IS practical!"
            )
            checked_pairs += 1

    print(f"Step 2: Verified Hall witness at n = 146 in {time.time() - t1:.2f}s:")
    print(f"  |S| = {len(S_146)}, |N(S)| = {len(NS_146)}, |S| > |N(S)|")
    print(f"  All {checked_pairs} forbidden pairs (u in S, v not in N(S)) have an explicit")
    print(f"  unrepresentable integer r <= u*v (not practical by subset-sum definition).")
    print("  By the pigeonhole principle, no permutation f of {1..146} has k*f(k) practical for all k.")
    print("COUNTEREXAMPLE CONFIRMED for both A321651 (Conjecture 2) and A389880.")


if __name__ == "__main__":
    main()
