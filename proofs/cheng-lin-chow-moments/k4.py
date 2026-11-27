# k=4 exploration: which move families suffice, and does the form without the N*G/12 part still hold?
import sys
from fractions import Fraction as Fr
from math import factorial, lcm
from collections import deque
from restrict import comps_of
import exactflow as E
def w(n): return Fr(n - 1, factorial(n))
def mu(c):
    r = Fr(1)
    for n in c[:-1]: r *= w(n)
    return r * c[-1] * w(c[-1])
g = lambda n: Fr(n * (n - 3), 2)
h = lambda n: Fr(n + 1 - (n - 1) ** 4, 120)
def feas(comps, a, edge):
    L = 1
    for v in a: L = lcm(L, v.denominator)
    A = [int(v * L) for v in a]; assert sum(A) == 0, sum(A)
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
                if edge(c, t, p): add(idx[c], idx[c[:t] + (p, m - p) + c[t + 1:]], INF)
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
    return flow == tot
FAM = {
 'all': lambda c, t, p: True,
 'L2 any + R2 last': lambda c, t, p: p == 2 or (t == len(c) - 1 and p == c[t] - 2),
 'L2,R2 any': lambda c, t, p: p == 2 or p == c[t] - 2,
 'L any size': lambda c, t, p: True if True else 0,
 'L2,L3 any + R2,R3 last': lambda c, t, p: p in (2, 3) or (t == len(c) - 1 and p >= c[t] - 3),
 'L2,L3,R2,R3 any': lambda c, t, p: p in (2, 3) or p >= c[t] - 3,
 'L2..4,R2..4 any': lambda c, t, p: p <= 4 or p >= c[t] - 4,
}
del FAM['L any size']
if __name__ != "__main__": D = 1
else:
    sys.setrecursionlimit(100000); D = int(sys.argv[1])

for name, form in (('full k=4: H+G(G+N)/12', lambda c, N: sum(map(h, c)) + sum(map(g, c)) * (sum(map(g, c)) + N) / 12),
                   ('reduced: H+G^2/12', lambda c, N: sum(map(h, c)) + sum(map(g, c)) ** 2 / 12)):
    print(name)
    for fam, edge in FAM.items():
        out = []
        for d in range(2, D + 1):
            comps = comps_of(d + 2); N = d + 2
            a = [mu(c) * form(c, N) for c in comps]
            s = sum(a)
            if s != 0: out.append('%d:sum!=0(%s)' % (d, s)); continue
            out.append('%d:%s' % (d, 'ok' if feas(comps, a, edge) else 'FAIL'))
        print('  %-26s %s' % (fam, ' '.join(out)), flush=True)
# cross-check the closed form against exactflow's a_J for k=4
for d in range(2, 9):
    comps, a = E.weights(d, lambda t: t ** 4)
    b = [mu(c) * (sum(map(h, c)) + sum(map(g, c)) * (sum(map(g, c)) + d + 2) / 12) for c in comps]
    r = {x / y for x, y in zip(a, b) if y != 0}
    print('d=%d closed form ratio set' % d, r, all((x == 0) == (y == 0) for x, y in zip(a, b)))
