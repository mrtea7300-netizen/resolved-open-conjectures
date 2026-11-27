# feasibility of: sources (a>0) can be shipped along coarse->fine edges into sinks (a<0), sinks need not fill
from math import lcm
from collections import deque
def feas_sink(comps, a, edge):
    L = 1
    for v in a: L = lcm(L, v.denominator)
    A = [int(v * L) for v in a]
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
