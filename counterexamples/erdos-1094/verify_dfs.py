#!/usr/bin/env python3
"""Independent confirmation of the pairs found by the box-tree search (dfs_1094.c).

Shares no code with the search.  For every row (n, k, lpf) of the TSV it checks, with Python
integers only:

  1. region:      2 <= k,  2k <= n,  n <= B*k;
  2. Legendre:    v_p(C(n,k)) = sum_{i>=1} ( floor(n/p^i) - floor(k/p^i) - floor((n-k)/p^i) )
                  is 0 for every prime p < lpf and positive for p = lpf;
  3. Lucas:       C(n,k) mod p = prod_i C(n_i, k_i) mod p over the base-p digits, evaluated with
                  math.comb on the digits: non-zero for p < lpf, zero for p = lpf;
  4. exact:       when C(n,k) has at most --exact-bits bits (default 3e7), the binomial
                  coefficient itself is computed (gmpy2.bincoef if available, else math.comb) and
                  reduced modulo every prime p <= lpf;
  5. the claim:   lpf > 13 and lpf * k > n   (i.e. lpf > max(n/k, 13)).

Usage:  python verify_dfs.py data/dfs_B64.tsv.gz [--B 64] [--exact-bits 30000000]
"""
import argparse
import gzip
import math
import sys

try:
    import gmpy2
except ImportError:  # pragma: no cover
    gmpy2 = None


def primes_upto(m):
    return [q for q in range(2, m + 1) if all(q % d for d in range(2, int(q ** 0.5) + 1))]


def legendre_vp(n, k, p):
    v, pw = 0, p
    while pw <= n:
        v += n // pw - k // pw - (n - k) // pw
        pw *= p
    return v


def lucas_mod(n, k, p):
    r = 1
    while k:
        r = r * math.comb(n % p, k % p) % p
        if r == 0:
            return 0
        n //= p
        k //= p
    return r


def log2_binom(n, k):
    return (math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)) / math.log(2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tsv")
    ap.add_argument("--B", type=int, default=64)
    ap.add_argument("--exact-bits", type=float, default=3e7)
    args = ap.parse_args()

    rows = []
    op = gzip.open if args.tsv.endswith(".gz") else open
    with op(args.tsv, "rt", encoding="ascii") as f:
        header = f.readline().split()
        assert header[:3] == ["n", "k", "lpf"], header
        for line in f:
            if line.strip():
                parts = line.split()
                rows.append((int(parts[0]), int(parts[1]), int(parts[2])))
    assert rows == sorted(rows) and len(set(rows)) == len(rows), "rows must be sorted and distinct"
    maxl = max(l for _, _, l in rows)
    primes = primes_upto(maxl)
    n_exact = 0
    by_lpf = {}
    for idx, (n, k, l) in enumerate(rows):
        assert k >= 2 and 2 * k <= n, (n, k)
        assert args.B == 0 or n <= args.B * k, (n, k)
        assert l in primes, (n, k, l)
        for p in primes:
            if p > l:
                break
            v = legendre_vp(n, k, p)
            m = lucas_mod(n, k, p)
            if p < l:
                assert v == 0, f"Legendre: {p} divides C({n},{k})"
                assert m != 0, f"Lucas: {p} divides C({n},{k})"
            else:
                assert v > 0, f"Legendre: claimed lpf {l} does not divide C({n},{k})"
                assert m == 0, f"Lucas: claimed lpf {l} does not divide C({n},{k})"
        if n < 2 ** 1000 and log2_binom(n, k) <= args.exact_bits:
            c = gmpy2.bincoef(n, k) if gmpy2 else math.comb(n, k)
            for p in primes:
                if p > l:
                    break
                assert (c % p == 0) == (p == l), f"exact: C({n},{k}) mod {p}"
            n_exact += 1
        assert l > 13 and l * k > n, (n, k, l)
        by_lpf[l] = by_lpf.get(l, 0) + 1
    print(f"PASS: {len(rows)} rows of {args.tsv} confirmed by Legendre's formula and by Lucas' "
          f"theorem; {n_exact} of them also by the exact binomial coefficient "
          f"({'gmpy2.bincoef' if gmpy2 else 'math.comb'}, C(n,k) up to {args.exact_bits:.0e} bits)")
    print("rows by lpf:", ", ".join(f"{l}: {c}" for l, c in sorted(by_lpf.items())))
    print("largest n:", rows[-1][0])


if __name__ == "__main__":
    sys.exit(main())
