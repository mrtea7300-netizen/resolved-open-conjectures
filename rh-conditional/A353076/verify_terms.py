"""Independent check (stdlib only): every listed term is odd and satisfies
sigma(k) > (e^gamma/2) k log log k (exact sigma, 60-digit Decimal logs), and the list equals a
brute-force sigma sieve for all odd k <= 3e6.   usage: python3 verify_terms.py b353076_full_884.txt"""
import sys, math
from decimal import Decimal as D, getcontext
getcontext().prec = 60
gamma = D("0.57721566490153286060651209008240243104215933593992")
eg = gamma.exp() / 2
def sigma(n):
    s, p, m = 1, 2, n
    while p * p <= m:
        if m % p == 0:
            pk = 1
            while m % p == 0: m //= p; pk *= p
            s *= (pk * p - 1) // (p - 1)
        p += 1
    if m > 1: s *= m + 1
    return s
terms = [int(l.split()[1]) for l in open(sys.argv[1])]
assert terms == sorted(set(terms)) and all(t % 2 for t in terms)
mn = min((D(sigma(t)) - eg * D(t) * D(t).ln().ln()) / (eg * D(t) * D(t).ln().ln()) for t in terms)
print(len(terms), "terms; all satisfy the inequality:", mn > 0, "; min relative margin", f"{mn:.3e}")
N = 3 * 10**6; sig = [0] * (N + 1)
for d in range(1, N + 1, 2):
    for k in range(d, N + 1, 2 * d): sig[k] += d
brute = [k for k in range(3, N + 1, 2) if sig[k] > float(eg) * k * math.log(math.log(k))]
print("brute force to 3e6:", len(brute), "terms; identical to the list:", brute == [t for t in terms if t <= N])
