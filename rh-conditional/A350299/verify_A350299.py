#!/usr/bin/env python3
"""A350299: k>1 with G(k) > G(m) for all m>k, G(k)=sigma(k)/(k log log k).  Stdlib only.
Given RH (Robin: G(m) < e^gamma for all m > 5040) and Gronwall (limsup G = e^gamma, unconditional):
  k is a term  <=>  k <= 5040, G(k) > e^gamma and G(k) > G(m) for all k < m <= 5040.
(If G(k) < e^gamma, Gronwall gives m > k with G(m) > G(k); G(k) = e^gamma never occurs below 5041,
 checked below; for k > 5040, G(k) < e^gamma by Robin.)  Computes the list with 40-digit Decimals."""
from decimal import Decimal, getcontext
getcontext().prec = 40
EG = Decimal('1.781072417990197985236504103107179549169645214303430205357665876')  # e^gamma
N = 5040
sig = [0] * (N + 1)
for d in range(1, N + 1):
    for m in range(d, N + 1, d):
        sig[m] += d
G = {k: Decimal(sig[k]) / (k * Decimal(k).ln().ln()) for k in range(3, N + 1)}
assert min(abs(G[k] - EG) for k in G) > Decimal('1e-6')
terms, best = [], Decimal(-1)
for k in range(N, 2, -1):          # scan downward keeping max_{m>k, m<=N} G(m)
    if G[k] > EG and G[k] > best:
        terms.append(k)
    best = max(best, G[k])
terms.reverse()
print(terms)
assert terms == [3, 4, 6, 12, 24, 60, 120, 180, 360, 2520, 5040]
print("A350299 complete (given RH): 11 terms, last 5040 -- OK")
