# Explicit certificate for Conjecture 3.28 of Cheng-Lin (arXiv:2603.21680v1), built by the recursion in
# the README, and an exact check that it is an identity of linear forms.
#
# N = d+2. C_N = compositions of N with all parts >= 2 (these are the J with coefficient != 0).
# w(n) = (n-1)/n!, wl(n) = n w(n), g(n) = n(n-3)/2, mu(c) = prod_{i<k} w(n_i) * wl(n_k), G(c) = sum g(n_i).
# Coefficient of x_J = N_J/U_J in Corollary 3.26 is (d+1)! mu(c) G(c).
# cert(N) = {(coarse, fine): lam >= 0} with   sum_c mu(c) G(c) e_c  =  sum lam * (e_coarse - e_fine),
# every pair being "fine refines coarse" (so e_coarse - e_fine <= 0 is one of the Lemma 3.27 inequalities).
import sys
from fractions import Fraction as Fr
from math import factorial
from functools import lru_cache
w = lambda n: Fr(n - 1, factorial(n)); wl = lambda n: n * w(n); g = lambda n: Fr(n * (n - 3), 2)
@lru_cache(None)
def comps(N):
    if N == 0: return ((),)
    return tuple((p,) + r for p in range(2, N + 1) if N - p == 0 or N - p >= 2 for r in comps(N - p))
def mu(c):
    m = wl(c[-1])
    for n in c[:-1]: m *= w(n)
    return m
def G(c): return sum(g(n) for n in c)
@lru_cache(None)
def cert(N):
    assert N >= 3
    out = {}
    def add(coarse, fine, lam):
        if lam: out[(coarse, fine)] = out.get((coarse, fine), 0) + lam
    if N == 3: return out
    for a in range(2, N - 2):                         # first block a, rest of size N-a >= 3: induction
        for (co, fi), lam in cert(N - a).items(): add((a,) + co, (a,) + fi, w(a) * lam)
    for r in comps(N - 2):                            # merge a leading 2 into the next block (left peel)
        add((r[0] + 2,) + r[1:], (2,) + r, w(2) * mu(r))
    add((N,), (N - 2, 2), w(N - 2))                   # right peel of the single block
    return out
def refines(coarse, fine):
    acc = lambda c: {sum(c[:i]) for i in range(1, len(c))}
    return acc(coarse) < acc(fine) or (acc(coarse) <= acc(fine) and coarse != fine)
def check(N):
    C = cert(N)
    lhs = {c: mu(c) * G(c) for c in comps(N)}
    rhs = {c: Fr(0) for c in comps(N)}
    for (co, fi), lam in C.items():
        assert lam > 0 and refines(co, fi), (co, fi, lam)
        rhs[co] += lam; rhs[fi] -= lam
    assert lhs == rhs, N
    kinds = set()
    for (co, fi), lam in C.items():                   # which kind of refinement is used
        t = next(i for i in range(len(co)) if co[i] != fi[i])
        kinds.add('left peel (n -> 2, n-2)' if fi[t] == 2 else ('right peel of the last block (n -> n-2, 2)' if t == len(co) - 1 and fi[t + 1] == 2 else 'other'))
    return len(comps(N)), len(C), sorted(kinds)
if __name__ == '__main__':
    for N in range(3, int(sys.argv[1]) + 3):
        n, m, kinds = check(N)
        print('d=%d (N=%d): %d index sets with nonzero coefficient, certificate uses %d inequalities, identity holds exactly; moves: %s' % (N - 2, N, n, m, '; '.join(kinds)), flush=True)
