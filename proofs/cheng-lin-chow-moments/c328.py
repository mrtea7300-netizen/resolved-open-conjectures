# Cheng-Lin (arXiv:2603.21680v1) Conjecture 3.28: the inequality of Corollary 3.26,
#   sum_J c_J N_J <= 0,  c_J = prod(n_i - 1) * sum(n_i(n_i-3)/2),   J subset of [d], blocks n_1..n_{m+1},
# is a nonnegative combination of the inequalities N_J/U_J <= N_J'/U_J' (J subset J').
# Put x_J = N_J/U_J and a_J = c_J U_J. By LP duality (Farkas) the conjecture for a given d is equivalent to:
#   sum_J a_J = 0  and  a(F) := sum_{J in F} a_J <= 0 for every up-set F of the Boolean lattice 2^[d].
# a_J = 0 unless all blocks are >= 2, and the sets with all blocks >= 2 are closed under taking subsets,
# so only those matter. We maximise a(F) over up-sets with an LP (totally unimodular): optimum 0 <=> true.
import sys, itertools, time
from fractions import Fraction as Fr
from math import factorial
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
def run(d):
    N = d + 2
    comps = []                         # compositions of N into parts >= 2
    def rec(rem, cur):
        if rem == 0: comps.append(tuple(cur)); return
        for p in range(2, rem + 1):
            if rem - p == 0 or rem - p >= 2: cur.append(p); rec(rem - p, cur); cur.pop()
    rec(N, [])
    idx = {c: i for i, c in enumerate(comps)}
    a = []
    for c in comps:
        U = Fr(c[-1] * factorial(d + 1), 1)
        for n in c: U /= factorial(n)
        P = 1
        for n in c: P *= (n - 1)
        a.append(U * P * Fr(sum(n * (n - 3) for n in c), 2))
    assert sum(a) == 0
    rows, cols, vals = [], [], []; k = 0
    for c in comps:                    # cover relations: split one block n into (p, n-p), both >= 2
        i = idx[c]
        for t, n in enumerate(c):
            for p in range(2, n - 1):
                f = c[:t] + (p, n - p) + c[t + 1:]
                rows += [k, k]; cols += [i, idx[f]]; vals += [1.0, -1.0]; k += 1     # x_c - x_f <= 0
    scale = float(max(abs(v) for v in a))
    cf = np.array([float(v) / scale for v in a])
    A = coo_matrix((vals, (rows, cols)), shape=(k, len(comps))).tocsr()
    res = linprog(-cf, A_ub=A, b_ub=np.zeros(k), bounds=(0, 1), method='highs')
    x = np.round(res.x).astype(int)
    exact = sum(v for v, xi in zip(a, x) if xi)
    # is the rounded solution an up-set?  (check constraints)
    ok = bool((A @ x <= 0).all())
    return len(comps), k, -res.fun, exact, int(x.sum()), ok
if __name__ == '__main__':
    for d in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        t0 = time.time(); n, k, val, exact, sz, ok = run(d)
        print('d=%d  nodes=%d covers=%d  LP max of a(F)/max|a| = %.3e  rounded up-set: size %d, valid %s, exact a(F) = %s  (%.1fs)'
              % (d, n, k, val, sz, ok, exact, time.time() - t0), flush=True)
