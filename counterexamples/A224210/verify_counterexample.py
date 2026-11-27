#!/usr/bin/env python3
"""
Standalone independent verifier for the counterexample to Zhi-Wei Sun's
conjecture in OEIS A224210, using SymPy directly from the OEIS definition.

OEIS A224210:
  a(n) = least prime p such that sum_{k=0}^n (k+1)^2 * x^(n-k) is irreducible mod p.
  Conjecture: a(n) does not exceed the (4n-3)-th prime for each n > 0.

Counterexample: n = 63, where 4*63 - 3 = 249, prime(249) = 1579,
but a(63) = 1627 = prime(258) > 1579.
"""

import time
import sympy as sp

OEIS_FIRST_50 = [
    2, 11, 7, 17, 11, 3, 7, 97, 3, 89, 31, 113, 43, 7, 23, 23, 17, 67, 23,
    109, 17, 277, 103, 283, 59, 101, 157, 127, 29, 79, 23, 223, 73, 269,
    433, 137, 5, 659, 109, 401, 419, 7, 373, 131, 89, 269, 149, 61, 829, 881,
]


def compute_a_sympy(n, x):
    poly_expr = sum((k + 1) ** 2 * x ** (n - k) for k in range(n + 1))
    p = 2
    idx = 1
    while True:
        P = sp.Poly(poly_expr, x, modulus=p)
        if P.degree() == n and P.is_irreducible:
            return p, idx
        p = sp.nextprime(p)
        idx += 1


def main():
    x = sp.Symbol("x")
    t0 = time.time()

    # Step 1: Reproduce published OEIS data n = 1..50
    for n, expected in enumerate(OEIS_FIRST_50, 1):
        got, _ = compute_a_sympy(n, x)
        assert got == expected, f"Mismatch at n={n}: got {got}, expected {expected}"
    print(f"Step 1: Reproduced all 50 published OEIS A224210 terms in {time.time() - t0:.2f}s: PASS")

    # Step 2: Independently verify counterexample at n = 63
    t1 = time.time()
    n = 63
    bound_idx = 4 * n - 3
    bound_prime = sp.prime(bound_idx)
    a63, a63_idx = compute_a_sympy(n, x)
    assert bound_idx == 249 and bound_prime == 1579
    assert a63 == 1627 and a63_idx == 258
    assert a63 > bound_prime

    # Also spot-check explicit factorizations at the boundary primes p=1579 and p=1621
    poly63 = sum((k + 1) ** 2 * x ** (n - k) for k in range(n + 1))
    fac_1579 = sp.factor_list(poly63, modulus=1579)[1]
    fac_1621 = sp.factor_list(poly63, modulus=1621)[1]
    assert sum(sp.Poly(f, x, modulus=1579).degree() * e for f, e in fac_1579) == 63
    assert len(fac_1579) > 1 or fac_1579[0][1] > 1
    assert len(fac_1621) > 1 or fac_1621[0][1] > 1

    print(f"Step 2: Verified counterexample at n = 63 in {time.time() - t1:.2f}s:")
    print(f"  Bound: prime(4*63 - 3) = prime({bound_idx}) = {bound_prime}")
    print(f"  Actual: a(63) = {a63} = prime({a63_idx}) > {bound_prime}")
    print(
        f"  Factor degrees mod 1579: {[sp.Poly(f, x, modulus=1579).degree() for f, e in fac_1579 for _ in range(e)]}"
    )
    print(
        f"  Factor degrees mod 1621: {[sp.Poly(f, x, modulus=1621).degree() for f, e in fac_1621 for _ in range(e)]}"
    )
    print("COUNTEREXAMPLE CONFIRMED.")


if __name__ == "__main__":
    main()
