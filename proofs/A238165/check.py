#!/usr/bin/env python3
"""Sun, arXiv:1402.6641 Conj. 2.7(i) / OEIS A238165(ii):
   for n>4 and k=1..n:  pi(kn)^(1/k) > pi((k+1)n)^(1/(k+1)),
   i.e. pi(kn)^(k+1) > pi((k+1)n)^k  (exact integers).
Part A (needed by the proof): all pairs (n,k) with n>=5, k>=1, kn<17 -- exact.
Part B (independent sanity check of the analytic lemma, not needed by the proof):
   all n<=NB, k with (k+1)n<=XB, using exact integers when the float margin is small.
Also re-verifies the elementary facts used in the proof."""
import math, sys
XB = int(sys.argv[1]) if len(sys.argv) > 1 else 2*10**6
NB = int(sys.argv[2]) if len(sys.argv) > 2 else 200
s = bytearray([1])*(XB+1); s[0] = s[1] = 0
for i in range(2, int(XB**.5)+1):
    if s[i]: s[i*i::i] = bytearray(len(range(i*i, XB+1, i)))
pi = [0]*(XB+1); c = 0
for i in range(XB+1):
    c += s[i]; pi[i] = c
assert pi[100] == 25 and pi[10**6] == 78498
def ok(n, k):
    return pi[k*n]**(k+1) > pi[(k+1)*n]**k
# Part A
A = [(n, k) for n in range(5, 17) for k in range(1, 17) if k*n < 17]
badA = [(n, k) for (n, k) in A if not ok(n, k)]
print("Part A: %d pairs with n>=5, kn<17 checked exactly; failures: %s" % (len(A), badA))
# Rosser-Schoenfeld pi(x) > x/log x for 17<=x<=XB (re-checked here at integers; pi is a step fn
# and x/log x increasing, so checking pi(m) > (m+1)/log(m+1) for integers m covers reals in [m,m+1))
badRS = [m for m in range(17, XB) if not pi[m] > (m+1)/math.log(m+1)]
print("RS check pi(x)>x/log x on [17,%d): failures %s" % (XB, badRS[:5]))
# Part B
fails = []; exact = 0; tot = 0
for n in range(1, NB+1):
    for k in range(1, XB//n):
        a, b = pi[k*n], pi[(k+1)*n]
        tot += 1
        if a == 0: fails.append((n, k)); continue
        d = (k+1)*math.log(a) - k*math.log(b)
        if abs(d) < 1e-6:
            exact += 1; good = a**(k+1) > b**k
        else: good = d > 0
        if not good: fails.append((n, k))
print("Part B: %d pairs (n<=%d, (k+1)n<=%d), %d decided exactly; failures:" % (tot, NB, XB, exact))
from collections import defaultdict
F = defaultdict(list)
for n, k in fails: F[n].append(k)
for n in sorted(F): print("  n=%d: %d failures, first k: %s" % (n, len(F[n]), F[n][:10]))
