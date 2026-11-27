#!/usr/bin/env python3
"""Rigorous (interval) certification, for 9 <= n <= 30, of the sign of
      Q_n(alpha) = n*x^alpha - (1+alpha)*sum_{k<=n} p_k^alpha ,  x = p_n,   alpha in (0,1].
Q_n > 0  <=>  (1/n) sum p_k^alpha < p_n^alpha/(alpha+1)  (Sun's inequality holds).
Method: adaptive subdivision of [A,B]. On a cell [a,b] we use Taylor with Lagrange remainder:
   Q(alpha) >= Q(a) + min(Q'(a),0)*h + min(Q''_low[a,b],0)*h^2/2 ,   h = b-a,
where Q''_low is a rigorous lower bound of Q'' on [a,b] obtained from monotonicity of p^alpha in alpha.
On the first cell [0,h] (Q(0)=0) we use Q(alpha) >= alpha*(Q'(0) + min(Q''_low,0)*h/2).
For an upper bound (to certify Q<0) the symmetric formula is used.
All arithmetic in Decimal with 50 digits; a safety margin EPS = 1e-30 absorbs rounding
(each exp/ln is correctly rounded to 50 digits, the sums have < 100 terms)."""
from decimal import Decimal as D, getcontext
import sys
getcontext().prec = 50
EPS = D("1e-30")
PR = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]
def data(n):
    ps = PR[:n]; x = ps[-1]
    return n, D(x).ln(), [D(p).ln() for p in ps]
def Q(d, a):
    n, lx, lp = d
    return n*(a*lx).exp() - (1+a)*sum((a*l).exp() for l in lp)
def Q1(d, a):
    n, lx, lp = d
    return n*(a*lx).exp()*lx - sum((a*l).exp() for l in lp) - (1+a)*sum((a*l).exp()*l for l in lp)
def Q2bounds(d, a, b):
    # Q'' = n x^al lx^2 - 2 sum p^al lp - (1+al) sum p^al lp^2 ; each piece monotone increasing in al
    n, lx, lp = d
    t1lo, t1hi = n*(a*lx).exp()*lx*lx, n*(b*lx).exp()*lx*lx
    s1lo = sum((a*l).exp()*l for l in lp); s1hi = sum((b*l).exp()*l for l in lp)
    s2lo = (1+a)*sum((a*l).exp()*l*l for l in lp); s2hi = (1+b)*sum((b*l).exp()*l*l for l in lp)
    return t1lo - 2*s1hi - s2hi, t1hi - 2*s1lo - s2lo
def certify(d, A, B, sign, h0=D("0.01"), depth=0):
    """certify sign*Q > 0 on (A,B] (A=0 allowed, then Q(0)=0 is used). returns #cells"""
    stack = [(D(A), D(B))]; cells = 0
    while stack:
        a, b = stack.pop()
        h = b - a
        lo2, hi2 = Q2bounds(d, a, b)
        if sign > 0:
            q2 = min(lo2, D(0))
            if a == 0:
                good = Q1(d, a) + q2*h/2 > EPS
            else:
                good = Q(d, a) + min(Q1(d, a), D(0))*h + q2*h*h/2 > EPS
        else:
            q2 = max(hi2, D(0))
            if a == 0:
                good = Q1(d, a) + q2*h/2 < -EPS
            else:
                good = Q(d, a) + max(Q1(d, a), D(0))*h + q2*h*h/2 < -EPS
        if good: cells += 1
        else:
            if h < D("1e-12"): raise RuntimeError("cannot certify near %s" % a)
            m = (a+b)/2; stack.append((m, b)); stack.append((a, m))
    return cells
log = []
d9 = data(9)
lo9, hi9 = D("0.0023363"), D("0.0023364")
print("n=9: Q(0.0023363) = %.6E, Q(0.0023364) = %.6E" % (Q(d9, lo9), Q(d9, hi9)))
c1 = certify(d9, 0, lo9, -1); c2 = certify(d9, hi9, 1, +1)
print("n=9: certified Q<0 on (0, 0.0023363] (%d cells) and Q>0 on [0.0023364, 1] (%d cells)" % (c1, c2))
for n in range(10, 31):
    d = data(n)
    c = certify(d, 0, 1, +1)
    print("n=%d: x=%d, Q'(0)=%.6f, certified Q>0 on (0,1] with %d cells" % (n, PR[n-1], Q1(d, D(0)), c), flush=True)
