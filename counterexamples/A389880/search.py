#!/usr/bin/env python3
"""
Search for counterexamples to:
  - OEIS A321651, Conjecture 2 (Zhi-Wei Sun, 2018):
      For every n >= 1, there exists a permutation f of {1,...,n} such that
      k * f(k) is practical for all k = 1,...,n.
  - OEIS A389880 (Zhi-Wei Sun, Nov 2025):
      Number of permutations f of {1,...,n} with f(1) = 1 such that k * f(k)
      (k = 1,...,n) are distinct practical numbers satisfies a(n) > 0 except
      for n = 3, 5, 7.

Uses Hopcroft-Karp maximum bipartite matching on the practical-product graph
G_n = ({1,...,n}, {(i, j) : i * j is practical}) and extracts an explicit
Hall's Marriage Theorem witness (S, N(S)) with |S| > |N(S)| whenever no
perfect matching exists.
"""

from collections import deque
import time
import sympy as sp


def build_graph(n_max):
    facs = [sp.factorint(i) if i >= 1 else {} for i in range(n_max + 1)]

    def is_prod_practical(i, j):
        if i == 1 and j == 1:
            return True
        if ((i * j) & 1) == 1:
            return False
        f = dict(facs[i])
        for p, e in facs[j].items():
            f[p] = f.get(p, 0) + e
        sig = 1
        for p in sorted(f):
            if p > sig + 1:
                return False
            e = f[p]
            sig *= (p ** (e + 1) - 1) // (p - 1)
        return True

    adj = [[] for _ in range(n_max + 1)]
    for i in range(1, n_max + 1):
        for j in range(1, n_max + 1):
            if is_prod_practical(i, j):
                adj[i].append(j)
    return adj


def max_matching_and_hall(adj, n):
    pair_u = [0] * (n + 1)
    pair_v = [0] * (n + 1)
    dist = [0] * (n + 1)
    inf = 10 ** 9

    def bfs():
        q = deque()
        for u in range(1, n + 1):
            if pair_u[u] == 0:
                dist[u] = 0
                q.append(u)
            else:
                dist[u] = inf
        found = False
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v > n:
                    break
                pu = pair_v[v]
                if pu == 0:
                    found = True
                elif dist[pu] == inf:
                    dist[pu] = dist[u] + 1
                    q.append(pu)
        return found

    def dfs(u):
        for v in adj[u]:
            if v > n:
                break
            pu = pair_v[v]
            if pu == 0 or (dist[pu] == dist[u] + 1 and dfs(pu)):
                pair_u[u] = v
                pair_v[v] = u
                return True
        dist[u] = inf
        return False

    matched = 0
    while bfs():
        for u in range(1, n + 1):
            if pair_u[u] == 0 and dfs(u):
                matched += 1

    if matched == n:
        return matched, [], []

    # Alternating-path reachable set from unmatched vertices gives a Hall witness S
    S = {u for u in range(1, n + 1) if pair_u[u] == 0}
    NS = set()
    q = deque(S)
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v > n:
                break
            if v not in NS:
                NS.add(v)
                pu = pair_v[v]
                if pu != 0 and pu not in S:
                    S.add(pu)
                    q.append(pu)
    return matched, sorted(S), sorted(NS)


def main(n_max=250):
    t0 = time.time()
    adj = build_graph(n_max)
    print(f"Built practical-product graph up to n={n_max} in {time.time() - t0:.2f}s")

    counterexamples = []
    for n in range(1, n_max + 1):
        matched, S, NS = max_matching_and_hall(adj, n)
        if matched < n:
            counterexamples.append((n, matched, len(S), len(NS)))
            print(
                f"COUNTEREXAMPLE n={n:3d}: max_matching={matched}/{n} "
                f"(Hall witness |S|={len(S)} > |N(S)|={len(NS)})"
            )
            if n == 146:
                print(f"  S    = {S}")
                print(f"  N(S) = {NS}")

    print(
        f"Scanned n=1..{n_max} in {time.time() - t0:.2f}s. "
        f"Total counterexamples: {len(counterexamples)}"
    )


if __name__ == "__main__":
    main()
