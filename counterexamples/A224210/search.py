#!/usr/bin/env python3
"""
Search for counterexamples to Zhi-Wei Sun's conjecture in OEIS A224210:
  a(n) = least prime p such that f_n(x) = sum_{k=0}^n (k+1)^2 * x^(n-k) is irreducible mod p.
  Conjecture: a(n) <= prime(4*n - 3) for all n > 0.

Uses python-flint (FLINT C library) for fast finite-field polynomial arithmetic.
"""

import time
import flint
import sympy as sp

OEIS_FIRST_50 = [
    2, 11, 7, 17, 11, 3, 7, 97, 3, 89, 31, 113, 43, 7, 23, 23, 17, 67, 23,
    109, 17, 277, 103, 283, 59, 101, 157, 127, 29, 79, 23, 223, 73, 269,
    433, 137, 5, 659, 109, 401, 419, 7, 373, 131, 89, 269, 149, 61, 829, 881,
]


def is_irred_mod_p(coeffs_asc, p, n):
    f = flint.nmod_poly(coeffs_asc, p)
    if f.degree() != n:
        return False
    # Fast linear-factor filter (for n > 1): gcd(x^p - x, f) != 1 eliminates ~63% of reducible polys.
    if n > 1:
        x = flint.nmod_poly([0, 1], p)
        if (pow(x, p, f) - x).gcd(f).degree() > 0:
            return False
    _, facs = f.factor()
    return len(facs) == 1 and facs[0][1] == 1


def main(n_max=200):
    primes = [int(p) for p in sp.primerange(2, 20000)]
    t0 = time.time()
    counterexamples = []
    top_ratios = []

    for n in range(1, n_max + 1):
        # f_n(x) = sum_{k=0}^n (k+1)^2 x^(n-k) = sum_{j=0}^n (n-j+1)^2 x^j
        coeffs_asc = [(n - j + 1) ** 2 for j in range(n + 1)]
        lim_idx = 4 * n - 3
        lim_prime = primes[lim_idx - 1]
        found_p = None
        found_idx = None
        for idx, pr in enumerate(primes, 1):
            if is_irred_mod_p(coeffs_asc, pr, n):
                found_p = pr
                found_idx = idx
                break
        assert found_p is not None, f"Increase prime table for n={n}"
        if n <= len(OEIS_FIRST_50):
            assert found_p == OEIS_FIRST_50[n - 1], (
                f"OEIS mismatch at n={n}: got {found_p}, expected {OEIS_FIRST_50[n - 1]}"
            )
        ratio = found_idx / lim_idx
        top_ratios.append((ratio, n, found_p, found_idx, lim_idx, lim_prime))
        if found_idx > lim_idx:
            counterexamples.append((n, found_p, found_idx, lim_idx, lim_prime))
            print(
                f"COUNTEREXAMPLE at n={n}: a({n}) = {found_p} = prime({found_idx}) "
                f"> prime({lim_idx}) = {lim_prime} (ratio {ratio:.4f})"
            )

    dt = time.time() - t0
    print(f"Verified OEIS A224210 n=1..{len(OEIS_FIRST_50)}: PASS")
    print(f"Scanned n=1..{n_max} in {dt:.2f}s. Counterexamples found: {len(counterexamples)}")
    top_ratios.sort(reverse=True)
    print("Top 5 hardest cases (largest prime_index(a(n)) / (4n-3)):")
    for ratio, n, fp, fi, li, lp in top_ratios[:5]:
        print(f"  n={n:3d}: a(n)={fp:5d} (prime #{fi:4d}) vs prime({li:3d})={lp:5d}  ratio={ratio:.4f}")


if __name__ == "__main__":
    main()
