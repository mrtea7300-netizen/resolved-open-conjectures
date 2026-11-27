# Which restricted families of cover relations already suffice for Conjecture 3.28 ?  (max closure = 0)
import sys, numpy as np
from fractions import Fraction as Fr
from math import factorial
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
def comps_of(N):
    out = []
    def rec(rem, cur):
        if rem == 0: out.append(tuple(cur)); return
        for p in range(2, rem + 1):
            if rem - p == 0 or rem - p >= 2: cur.append(p); rec(rem - p, cur); cur.pop()
    rec(N, []); return out
def weight(c, d):
    U = Fr(c[-1] * factorial(d + 1), 1)
    for n in c: U /= factorial(n)
    P = 1
    for n in c: P *= (n - 1)
    return U * P * Fr(sum(n * (n - 3) for n in c), 2)
FILTERS = {
 'all':        lambda c, t, p: True,
 'split off 2 or 3 at either end of a block': lambda c, t, p: p in (2, 3) or c[t] - p in (2, 3),
 'split off 2 or 3 on the left':  lambda c, t, p: p in (2, 3),
 'split off 2 or 3 on the right': lambda c, t, p: c[t] - p in (2, 3),
 'split off 2 on either side':    lambda c, t, p: p == 2 or c[t] - p == 2,
 'only the first block >= 4':     lambda c, t, p: t == min(i for i, n in enumerate(c) if n >= 4),
 'only the last block >= 4':      lambda c, t, p: t == max(i for i, n in enumerate(c) if n >= 4),
 'first block>=4, split off 2 or 3 on the left': lambda c, t, p: t == min(i for i, n in enumerate(c) if n >= 4) and p in (2, 3),
 'last block>=4, split off 2 or 3 on the right': lambda c, t, p: t == max(i for i, n in enumerate(c) if n >= 4) and c[t] - p in (2, 3),
}
def run(d, flt):
    comps = comps_of(d + 2); idx = {c: i for i, c in enumerate(comps)}
    a = [weight(c, d) for c in comps]
    rows, cols, vals = [], [], []; k = 0
    for c in comps:
        for t, n in enumerate(c):
            for p in range(2, n - 1):
                if not flt(c, t, p): continue
                f = c[:t] + (p, n - p) + c[t + 1:]
                rows += [k, k]; cols += [idx[c], idx[f]]; vals += [1.0, -1.0]; k += 1
    scale = float(max(abs(v) for v in a)); cf = np.array([float(v) / scale for v in a])
    A = coo_matrix((vals, (rows, cols)), shape=(k, len(comps))).tocsr()
    res = linprog(-cf, A_ub=A, b_ub=np.zeros(k), bounds=(0, 1), method='highs')
    return -res.fun
if __name__ == '__main__':
  for name, flt in FILTERS.items():
    print('%-48s' % name, ' '.join('%d:%s' % (d, 'ok' if run(d, flt) < 1e-9 else 'FAIL') for d in range(4, int(sys.argv[1]) + 1)), flush=True)
