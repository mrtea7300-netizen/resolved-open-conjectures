#!/usr/bin/env python3
"""Sun, arXiv:1208.2683, Conj. 2.1: for any alpha>0,
      (1/n) sum_{k<=n} p_k^alpha < p_n^alpha/(alpha+1)   for all n >= 2*ceil(alpha)^2+ceil(alpha)+6.
Part 1: counterexample n=9 (threshold for 0<alpha<=1 is 9), small alpha.  Decimal, 80 digits.
Part 2: exact integer check of  (n p_n - 2 S_n)(2 p_n - 23) > 23 n p_n  for 10<=n, p_n<10^6,
        and Mandl 2S_9 < 9 p_9.
Part 3: the constant in Lemma 2 (x>=10^6) with J(10^6) computed exactly.
Part 4: (sanity, float, not part of the proof) direct check of the inequality on an alpha-grid."""
from decimal import Decimal as D, getcontext
import math
getcontext().prec = 80
X0 = 10**6
s = bytearray([1])*(X0+1); s[0] = s[1] = 0
for i in range(2, int(X0**.5)+1):
    if s[i]: s[i*i::i] = bytearray(len(range(i*i, X0+1, i)))
P = [i for i in range(X0+1) if s[i]]
assert len(P) == 78498 and P[8] == 23
# ---------- Part 1
P9 = P[:9]
def f9(a):   # (1/9) sum p^a - 23^a/(1+a)
    a = D(a)
    return sum((D(p).ln()*a).exp() for p in P9)/9 - (D(23).ln()*a).exp()/(1+a)
print("Part 1 (n=9): primes", P9, " S_9 =", sum(P9))
th = sum(D(p).ln() for p in P9)
print("  first-order coefficient theta(23) - 9(log 23 - 1) =", +(th - 9*(D(23).ln()-1)))
for a in ["1e-12", "1e-6", "0.0001", "0.001", "0.002", "0.0023", "0.0024", "0.003", "0.01", "0.5", "1"]:
    v = f9(a)
    print("  alpha=%-7s  (1/9)sum p^a - 23^a/(1+a) = %+.12E  -> %s" % (a, v, "VIOLATION" if v >= 0 else "ok"))
lo, hi = D("0.002"), D("0.003")
for _ in range(120):
    m = (lo+hi)/2
    if f9(m) > 0: lo = m
    else: hi = m
print("  sign change (bisection) at alpha0 = %.15f" % lo)
# ---------- Part 2
S = 0; bad = []; mand = []; minratio = None
for n, p in enumerate(P, 1):
    S += p
    if n >= 9 and not 2*S < n*p: mand.append(n)
    if n >= 10:
        lhs = (n*p - 2*S)*(2*p - 23); rhs = 23*n*p
        if not lhs > rhs: bad.append(n)
        r = D(lhs)/D(rhs)
        if minratio is None or r < minratio[0]: minratio = (r, n)
print("Part 2: n from 10 to %d (p_n < 10^6): failures of (n p_n-2S_n)(2p_n-23) > 23 n p_n: %s;"
      " min lhs/rhs = %.6f at n=%d" % (len(P), bad, minratio[0], minratio[1]))
print("        Mandl 2S_m < m p_m failures for 9<=m<=%d: %s" % (len(P), mand))
# ---------- Part 3   x0 = 10^6 (not prime); J(x0) = x0*pi(x0) - sum_{p<=x0} p
pix0 = len(P); sumP = sum(P)
J0 = X0*pix0 - sumP
L0 = D(X0).ln(); x0 = D(X0)
K0 = 2*D(J0) - x0*x0/L0
K1 = K0 - D("1.5")*x0*x0/(L0*L0)
beta = D("0.5") - D("2.51")/L0 - 12*(L0/x0)*(1 + 1/L0 + D("2.51")/(L0*L0))
G = K1 + beta*x0*x0/(L0*L0)
print("Part 3: pi(1e6)=%d, sum p=%d, J(1e6)=%d" % (pix0, sumP, J0))
print("        K1 = %.6E, beta = %.8f, beta*x0^2/L0^2 = %.6E, lower bound for g = %.6E  (%s)"
      % (K1, beta, beta*x0*x0/(L0*L0), G, "POSITIVE" if G > 0 else "NOT positive"))
# sanity: Dusart bounds at integer points in [1e6, 1e6] range only (cheap) - real proof cites them
# ---------- Part 4 (float sanity)
import numpy as np
Pa = np.array(P[:20000], dtype=float); lp = np.log(Pa); nn = np.arange(1, len(Pa)+1)
viol = []
for a in np.concatenate([np.linspace(1e-5, 1, 2001)]):
    w = np.exp(a*(lp - lp[-1])); cs = np.cumsum(w)
    v = np.nonzero((cs/nn >= w/(a+1)) & (nn >= 9))[0]
    if len(v): viol.append((float(a), list(v[:5]+1)))
print("Part 4 (float sanity, n<=20000, 2001 alphas in [1e-5,1]): violations (alpha, n):", viol[:12], "count", len(viol))
