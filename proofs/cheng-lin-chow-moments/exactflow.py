# Exact test of: "sum_J a_J x_J <= 0 for every monotone x"  <=>  a is a nonnegative combination of
# e_coarse - e_fine  <=>  a transportation flow exists (exact max-flow with Python integers).
# a_J = U_J P_J(1) ( E psi(F_J - d/2) - E psi(X_d - d/2) ),  psi = t^k (k even) or psi = (t - c)_+ .
# A feasible flow for psi = t^k proves Conjecture 3.14 of arXiv:2603.21680v3 for that (d, k), for every
# matroid of rank d+1 (using only Lemma 3.29 of the paper). All psi = (t-c)_+ together give convex order.
import sys, time
from fractions import Fraction as Fr
from math import factorial, lcm
from collections import deque
from restrict import comps_of
def dist(c):
    d_ = {0: Fr(1)}
    for n in c:
        nd = {}
        for s, p in d_.items():
            for u in range(1, n): nd[s + u] = nd.get(s + u, 0) + p / (n - 1)
        d_ = nd
    return d_
def weights(d, psi, cache={}):
    if d not in cache:
        comps = comps_of(d + 2); mass = []; dists = []
        for c in comps:
            U = Fr(c[-1] * factorial(d + 1), 1)
            for n in c: U /= factorial(n)
            P = 1
            for n in c: P *= (n - 1)
            mass.append(U * P); dists.append(dist(c))
        cache.clear(); cache[d] = (comps, mass, dists)
    comps, mass, dists = cache[d]
    mean = Fr(d + 2, 2)
    val = [sum(psi(s - mean) * p for s, p in D.items()) for D in dists]
    E = sum(m * v for m, v in zip(mass, val)) / sum(mass)
    return comps, [m * (v - E) for m, v in zip(mass, val)]
def feasible(comps, a):
    """exact max-flow (Dinic). returns (ok, shortfall/total)"""
    L = 1
    for v in a: L = lcm(L, v.denominator)
    A = [int(v * L) for v in a]; assert sum(A) == 0
    n = len(comps); S, T = n, n + 1; idx = {c: i for i, c in enumerate(comps)}
    INF = sum(abs(v) for v in A) + 1
    head = [[] for _ in range(n + 2)]; to = []; cap = []
    def add(u, v, c):
        head[u].append(len(to)); to.append(v); cap.append(c); head[v].append(len(to)); to.append(u); cap.append(0)
    tot = 0
    for i, v in enumerate(A):
        if v > 0: add(S, i, v); tot += v
        elif v < 0: add(i, T, -v)
    for c in comps:
        for t, m in enumerate(c):
            for p in range(2, m - 1):
                add(idx[c], idx[c[:t] + (p, m - p) + c[t + 1:]], INF)
    flow = 0
    while True:
        level = [-1] * (n + 2); level[S] = 0; dq = deque([S])
        while dq:
            u = dq.popleft()
            for e in head[u]:
                if cap[e] > 0 and level[to[e]] < 0: level[to[e]] = level[u] + 1; dq.append(to[e])
        if level[T] < 0: break
        it = [0] * (n + 2)
        def dfs(u, f):
            if u == T: return f
            while it[u] < len(head[u]):
                e = head[u][it[u]]; v = to[e]
                if cap[e] > 0 and level[v] == level[u] + 1:
                    r = dfs(v, min(f, cap[e]))
                    if r > 0: cap[e] -= r; cap[e ^ 1] += r; return r
                it[u] += 1
            return 0
        while True:
            f = dfs(S, INF)
            if f == 0: break
            flow += f
    return flow == tot, Fr(tot - flow, tot) if tot else Fr(0)
if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    mode = sys.argv[1]; d0, d1 = int(sys.argv[2]), int(sys.argv[3])
    for d in range(d0, d1 + 1):
        t0 = time.time(); out = []
        if mode == 'moments':
            for k in (2, 4, 6, 8, 10, 12):
                comps, a = weights(d, lambda t, k=k: t ** k)
                ok, sh = feasible(comps, a); out.append('k=%d:%s' % (k, 'ok' if ok else 'FAIL(%.3g)' % float(sh)))
        else:
            fails = []; ncut = 0
            for c2 in range(-d - 2, d + 3):                 # thresholds c = c2/2
                comps, a = weights(d, lambda t, c=Fr(c2, 2): max(t - c, 0))
                if all(v == 0 for v in a): continue
                ncut += 1; ok, sh = feasible(comps, a)
                if not ok: fails.append((c2, float(sh)))
            out.append('thresholds tested %d, failures %s' % (ncut, fails if fails else 'none'))
        print('d=%d (%d sets): %s  (%.1fs)' % (d, len(comps), '  '.join(out), time.time() - t0), flush=True)
