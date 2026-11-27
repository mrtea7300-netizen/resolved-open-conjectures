#!/usr/bin/env python3
"""Reproduce the OEIS data of A094960 / A195441 / A324370 / A366168 / A366169 from actual
Bernoulli polynomials (exact rational arithmetic), and test the criteria used in proof.md.

Nothing here uses the lemmas of proof.md to *decide* membership: membership is decided from the
coefficients of the polynomials. The lemmas and the product formulas of Kellner / Kellner-Sondow
are then compared against that ground truth.

Usage:  python check_bernoulli.py [KMAX]      (default KMAX = 1100, which covers every exception of
                                               the finite check; Lemma 1 is tested for m <= 300)

Data sections were copied on 2026-11-26 from the mirror
https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A094/A094960.seq (and A195441, A324370,
A366168, A366169).  No request to oeis.org was made.
"""
import sys
from fractions import Fraction
from math import comb, gcd, lcm, isqrt

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1100
LEMMA_MAX = 300

# ---------------------------------------------------------------- OEIS data (mirror, 2026-11-26)
A094960 = [1, 2, 4, 6, 10, 12, 28, 30, 36, 60]
A195441 = [1, 1, 2, 1, 6, 2, 6, 3, 10, 2, 6, 2, 210, 30, 6, 3, 30, 10, 210, 42, 330, 30, 30, 30, 546, 42,
           14, 2, 30, 2, 462, 231, 3570, 210, 6, 2, 51870, 2730, 210, 42, 2310, 330, 2310, 210,
           4830, 210, 210, 210, 6630, 1326, 858, 66, 330, 110, 798, 114, 870, 30, 30, 6]      # offset 0
A324370 = [1, 1, 2, 1, 6, 1, 6, 3, 10, 1, 6, 1, 210, 15, 2, 3, 30, 5, 210, 21, 110, 15, 30, 5, 546, 21,
           14, 1, 30, 1, 462, 231, 1190, 105, 6, 1, 51870, 1365, 70, 21, 2310, 55, 2310, 105, 322,
           105, 210, 35, 6630, 663, 286, 33, 330, 55, 798, 57, 290, 15, 30, 1, 930930, 15015, 1430,
           2145, 1122, 85, 82110, 2415, 70, 3, 330, 55, 21111090, 285285]                    # offset 1
A366168 = [1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 15, 1, 1, 3, 5, 5, 21, 1, 5, 15, 5, 1, 21, 7, 1, 1, 1, 1,
           231, 7, 35, 3, 1, 1, 1365, 35, 7, 21, 55, 55, 105, 7, 7, 105, 35, 5, 663, 13, 11, 33, 55, 1,
           57, 1, 5, 15, 1, 1, 15015, 715, 715, 33, 17, 85, 2415, 35, 1, 3, 55, 55, 285285, 19019, 1001]  # offset 1
A366169 = [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 21, 25, 28, 29, 30, 31, 36, 37, 55, 57, 60,
           61, 70, 121, 190]
# Kellner, arXiv:2310.01325v2: the sets R (before Theorem 9) and S_3 (before Conjecture 15)
KELLNER_R = [3, 5, 8, 9, 11, 27, 29, 35, 59]
KELLNER_S3 = (list(range(1, 19)) + [20, 21, 22, 25, 26] + list(range(28, 33)) + list(range(35, 39))
              + [42, 50, 52] + list(range(55, 59)) + [60, 61, 62, 66, 70, 71, 72, 78, 80, 92, 110, 121,
                                                     122, 156, 176, 177, 190, 191, 210, 392])


# ---------------------------------------------------------------- Bernoulli numbers and polynomials
def bernoulli_numbers(m):
    """B_0..B_m with B_1 = -1/2, from sum_{j<=n} C(n+1,j) B_j = 0."""
    B = [Fraction(1)]
    for n in range(1, m + 1):
        B.append(-sum(comb(n + 1, j) * B[j] for j in range(n)) / (n + 1))
    return B


B = bernoulli_numbers(KMAX)


def bernoulli_poly(n):
    """Coefficient list c[i] of x^i in B_n(x) = sum_i C(n,i) B_{n-i} x^i."""
    return [comb(n, i) * B[n - i] for i in range(n + 1)]


def derivative(c):
    return [i * c[i] for i in range(1, len(c))]


def denom(c):
    d = 1
    for q in c:
        d = lcm(d, Fraction(q).denominator)
    return d


def digit_sum(n, p):
    s = 0
    while n:
        s += n % p
        n //= p
    return s


def primes_upto(n):
    sv = bytearray([1]) * (n + 1)
    sv[:2] = b"\0\0"
    for i in range(2, isqrt(n) + 1):
        if sv[i]:
            sv[i * i::i] = bytearray(len(sv[i * i::i]))
    return [i for i in range(n + 1) if sv[i]]


PR = primes_upto(KMAX + 5)


def rad(n):
    r = 1
    for p in PR:
        if p > n:
            break
        if n % p == 0:
            r *= p
    return r


def prod_formula(n, extra):
    """prod of primes p with s_p(n) >= p and p not dividing n*(n+1)*...*(n+extra)."""
    r = 1
    for p in PR:
        if p > n:
            break
        if digit_sum(n, p) >= p and all((n + i) % p for i in range(extra + 1)):
            r *= p
    return r


ok = True


def report(name, cond, detail=""):
    global ok
    ok &= bool(cond)
    print(f"[{'ok' if cond else 'FAIL'}] {name} {detail}")


d1, d2, d3, DD = {}, {}, {}, {}
for k in range(1, KMAX + 1):
    c = bernoulli_poly(k)
    DD[k] = denom(c[1:])                       # denominator(B_k(x) - B_k)
    c1 = derivative(c)
    c2 = derivative(c1)
    c3 = derivative(c2)
    d1[k], d2[k], d3[k] = denom(c1), denom(c2), denom(c3)

S1 = [k for k in d1 if d1[k] == 1]
S2 = [k for k in d2 if d2[k] == 1]
S3 = [k for k in d3 if d3[k] == 1]
R = [n for n in DD if DD[n] == rad(n + 1)]

print(f"Exact Bernoulli polynomials B_k(x) for 1 <= k <= {KMAX}")
report("A094960: k with B_k'(x) integral", S1 == A094960, str(S1))
report("A366169: k with B_k''(x) integral", S2 == A366169, str(S2))
report("Kellner's S_3: k with B_k'''(x) integral", S3 == KELLNER_S3, f"largest {S3[-1]}, {len(S3)} terms")
report("Kellner's R: n >= 1 with denom(B_n(x)-B_n) = rad(n+1)", R == KELLNER_R, str(R))
report("A195441 data (a(n) = denom(B_{n+1}(x)-B_{n+1}))",
       [1] + [DD[n + 1] for n in range(1, len(A195441))] == A195441 and A195441[0] == 1)
report("A324370 data = denom(B_n'(x))", [d1[n] for n in range(1, len(A324370) + 1)] == A324370)
report("A366168 data = denom(B_n''(x))", [d2[n] for n in range(1, len(A366168) + 1)] == A366168)

# product formulas quoted in proof.md, section 1 (Kellner-Sondow / Kellner), against ground truth
report("denom(B_n(x)-B_n) = prod_{s_p(n)>=p} p",
       all(DD[n] == prod_formula(n, -1) for n in DD))
report("denom(B_n'(x)) = prod_{p !| n, s_p(n)>=p} p", all(d1[n] == prod_formula(n, 0) for n in d1))
report("denom(B_n''(x)) = prod_{p !| n(n-1), s_p(n-1)>=p} p",
       all(d2[n] == prod_formula(n - 1, 1) for n in d2 if n >= 2))
report("denom(B_n'''(x)) = prod_{p !| n(n-1)(n-2), s_p(n-2)>=p} p",
       all(d3[n] == prod_formula(n - 2, 2) for n in d3 if n >= 3))

# Lemma 1 of proof.md, tested coefficient by coefficient
bad = 0
cases = 0
for m in range(1, min(KMAX - 2, LEMMA_MAX) + 1):
    for p in PR:
        if p < 3 or p > m:
            continue
        a, b = (m // p) % p, m % p
        if a + b < p:
            continue
        j = (a + 1) * (p - 1)
        cases += 1
        # (i) p divides the denominator of C(m,j) B_j, a coefficient of B_m(x) - B_m
        if j >= m or (Fraction(comb(m, j)) * B[j]).denominator % p:
            bad += 1
        # (ii) for i = 1,2,3: if p !| m(m+1)...(m+i-1) then the coefficient of x^(m-1-j) in the
        #      i-th derivative of B_{m+i-1} is (m+i-1)_i * C(m-1,j) * B_j and has p in its denominator
        for i in (1, 2, 3):
            ff = 1
            for u in range(i):
                ff *= m + u
            if ff % p == 0:
                continue
            coef = ff * comb(m - 1, j) * B[j]
            poly = bernoulli_poly(m + i - 1)
            for _ in range(i):
                poly = derivative(poly)
            if poly[m - 1 - j] != coef or Fraction(coef).denominator % p:
                bad += 1
report(f"Lemma 1 (Lucas + von Staudt-Clausen) on every (m, p), m <= {LEMMA_MAX}, with a+b >= p", bad == 0,
       f"{cases} cases, {bad} failures")

print("ALL OK" if ok else "SOMETHING FAILED")
sys.exit(0 if ok else 1)
