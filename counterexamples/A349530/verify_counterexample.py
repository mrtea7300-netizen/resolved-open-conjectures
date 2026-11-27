#!/usr/bin/env python3
"""
Standalone brute-force verifier for the counterexamples to Conjecture 3 of
OEIS A349530 (Zhi-Wei Sun, Nov 2021).

Conjecture 3 states:
  For n not among {26, 27, 28, 626, 627, 628, 629, 630}, let D(n) be the least
  positive integer m such that k*(k^4 + 1) (k = 1..n) are pairwise distinct mod m.
  If 5^a < n <= 3*5^a, then D(n) = 3*5^a.

Counterexample family:
  For every k >= 1 and a = 5*k + 4, every n in {5^a + 1, ..., 5^a + 5} satisfies
  D(n) <= 11 * 5^(a - 1) < 3 * 5^a.
  Smallest new counterexamples (k = 1, a = 9):
    n = 1,953,126..1,953,130 with m = 11 * 5^8 = 4,296,875 < 5,859,375 = 3 * 5^9.
"""

import time

OEIS_A349530_FIRST_30 = [
    1, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
    15, 15, 15, 15, 15,
]


def is_distinct_mod(m, n):
    seen = bytearray(m)
    for k in range(1, n + 1):
        v = (k * (pow(k, 4, m) + 1)) % m
        if seen[v]:
            return False
        seen[v] = 1
    return True


def main():
    t0 = time.time()

    # Step 1: Reproduce published OEIS A349530 (mod m^2) for n = 1..30
    got = []
    m = 1
    for n in range(1, 31):
        while not is_distinct_mod(m * m, n):
            m += 1
        got.append(m)
    assert got == OEIS_A349530_FIRST_30, f"OEIS mismatch: {got}"
    print(f"Step 1: Reproduced OEIS A349530 n=1..30 in {time.time() - t0:.2f}s: PASS")

    # Step 2: Reproduce Sun's listed Conj 3 exceptions n = 626..630 (D(n) = 1375 < 1875)
    assert is_distinct_mod(11 * 5**3, 630)
    assert not is_distinct_mod(11 * 5**3, 631)
    print("Step 2: Confirmed Sun's listed exceptions n=626..630 (m = 11*5^3 = 1375): PASS")

    # Step 3: Brute-force verify the smallest new counterexamples n = 5^9 + 1 .. 5^9 + 5
    t1 = time.time()
    a = 9
    n_lo = 5**a + 1
    n_hi = 5**a + 5
    m_wit = 11 * 5**(a - 1)
    conj_val = 3 * 5**a
    assert 5**a < n_lo and n_hi <= conj_val and m_wit < conj_val
    assert is_distinct_mod(m_wit, n_hi), f"Collision found for n={n_hi}, m={m_wit}!"
    assert not is_distinct_mod(m_wit, n_hi + 1), "Expected collision at 5^9 + 6"
    print(f"Step 3: Brute-force verified n = {n_lo}..{n_hi} in {time.time() - t1:.2f}s:")
    print(f"  All {n_hi} values k*(k^4 + 1) (k = 1..{n_hi}) are pairwise distinct mod {m_wit}")
    print(f"  Thus D(n) <= {m_wit} < {conj_val} = 3 * 5^9 for all n in [{n_lo}, {n_hi}].")
    print("COUNTEREXAMPLE CONFIRMED.")


if __name__ == "__main__":
    main()
