#!/usr/bin/env python3
"""Numerical attack on the LP constraints of proof.md.

For every test graph G (checked C4-free first) we verify, exactly in integers:
  * Lemma 1: G[N(v)] has maximum degree <= 1 for every v;
  * (I4)   2 * sum_v C(d_v, 2) + #{v : d_v odd} <= n(n-1), together with the two counts used in
           its proof: |P_1| = sum_v C(d_v, 2) and |E_0| = (1/2) sum_v s(v) >= #odd / 2;
  * (I5) per vertex: sum_{u in N(v)} d(u) <= n - 1 + d_v - (d_v mod 2), and the disjointness of
           the sets N(u) minus N[v], u in N(v);
  * the LP vector of G (n_d, e_ij) satisfies every row of lp_c4.primal(n, m, dmin) exactly, with
           dmin = 0 and, when ex(n-1) is known (n <= 41), with dmin = m - ex(n-1) whenever G has m = ex(n) edges.
Test families:
  1. all C4-free graphs on n <= NMAX vertices up to isomorphism (vertex extension + isomorphism
     dedup; counts are compared with OEIS A006786);
  2. McKay-Afzaly extremal graphs, n = 4..49 (sparse6 files from c4_all.tar.gz, path as argument);
  3. Erdos-Renyi polarity graphs ER_q, q = 2, 3, 4, 5, 7 (n = q^2 + q + 1);
  4. random maximal C4-free graphs (random greedy), n = 10..60.
Reports the minimum slack of (I4) and (I5) seen in each family (0 = tight).

    python test_constraints.py --nmax 9 --mckay <dir with c4_*.s6> --random 2000
"""
from __future__ import annotations

import argparse
import glob
import os
import random
import re
import sys
from collections import defaultdict

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lp_c4  # noqa: E402

# OEIS A006786 (number of squarefree graphs on n vertices), mirror copy read 2026-11-27
A006786 = {1: 1, 2: 2, 3: 4, 4: 8, 5: 18, 6: 44, 7: 117, 8: 351, 9: 1230, 10: 5069, 11: 25181}


def adj_sets(G):
    return {v: set(G[v]) for v in G}


def is_c4_free(N):
    V = list(N)
    for i, x in enumerate(V):
        for y in V[i + 1:]:
            if len(N[x] & N[y]) > 1:
                return False
    return True


def check_graph(N, stats, tag, known_prev=None):
    """N: dict vertex -> set of neighbours.  Raises AssertionError on any violation."""
    n = len(N)
    assert is_c4_free(N), f"{tag}: not C4-free"
    deg = {v: len(N[v]) for v in N}
    m = sum(deg.values()) // 2
    # Lemma 1
    for v in N:
        for u in N[v]:
            assert len(N[u] & N[v]) <= 1, f"{tag}: G[N(v)] has a vertex of degree >= 2"
    # (I4) and its proof
    pairs1 = 0
    V = list(N)
    for i, x in enumerate(V):
        for y in V[i + 1:]:
            if len(N[x] & N[y]) == 1:
                pairs1 += 1
    assert pairs1 == sum(d * (d - 1) // 2 for d in deg.values()), f"{tag}: |P1| != sum C(d,2)"
    E0 = sum(1 for x in V for y in N[x] if x < y and not (N[x] & N[y]))
    s = {v: sum(1 for u in N[v] if not (N[u] & N[v])) for v in N}
    assert 2 * E0 == sum(s.values())
    for v in N:
        assert s[v] % 2 == deg[v] % 2 and s[v] >= deg[v] % 2
    odd = sum(d % 2 for d in deg.values())
    assert 2 * E0 >= odd
    assert pairs1 + E0 <= n * (n - 1) // 2
    sl4 = n * (n - 1) - (2 * sum(d * (d - 1) // 2 for d in deg.values()) + odd)
    assert sl4 >= 0, f"{tag}: (I4) violated"
    # (I5)
    sl5 = None
    for v in N:
        d = deg[v]
        closed = N[v] | {v}
        seen = set()
        for u in N[v]:
            out = N[u] - closed
            assert not (out & seen), f"{tag}: N(u)-N[v] not disjoint"
            seen |= out
        slack = (n - 1 + d - d % 2) - sum(deg[u] for u in N[v])
        assert slack >= 0, f"{tag}: (I5) violated at a vertex of degree {d}"
        sl5 = slack if sl5 is None else min(sl5, slack)
    # LP vector
    x = defaultdict(int)
    for v in N:
        x[("n", deg[v])] += 1
    for a in V:
        for b in N[a]:
            if a < b:
                i, j = sorted((deg[a], deg[b]))
                x[("e", i, j)] += 1
    assert lp_c4.check_primal_exact(n, m, 0, dict(x)), f"{tag}: LP vector fails the LP"
    if known_prev is not None and m - known_prev > 0:
        dmin = m - known_prev
        assert min(deg.values()) >= dmin, f"{tag}: min degree {min(deg.values())} < m - ex(n-1) = {dmin}"
        assert lp_c4.check_primal_exact(n, m, dmin, dict(x)), f"{tag}: LP vector fails LP with (I6)"
    st = stats[tag.split(":")[0]]
    st["graphs"] += 1
    st["min_slack_I4"] = min(st.get("min_slack_I4", 10 ** 9), sl4)
    st["min_slack_I5"] = min(st.get("min_slack_I5", 10 ** 9), sl5 if sl5 is not None else 10 ** 9)
    return m


def all_c4_free(nmax):
    """Yield (n, list of graphs as adjacency dicts), all iso classes of C4-free graphs, n = 1..nmax."""
    level = [nx.empty_graph(1)]
    yield 1, level
    for n in range(2, nmax + 1):
        buckets = defaultdict(list)
        new = []
        for G in level:
            N = adj_sets(G)
            old = list(range(n - 1))
            # neighbourhood S of the new vertex: every old vertex w has |N(w) & S| <= 1
            def rec(k, S):
                if k == len(old):
                    H = G.copy()
                    H.add_node(n - 1)
                    H.add_edges_from((n - 1, s) for s in S)
                    h = nx.weisfeiler_lehman_graph_hash(H, iterations=3)
                    h = (h, tuple(sorted(d for _, d in H.degree())))
                    for K in buckets[h]:
                        if nx.is_isomorphic(H, K):
                            return
                    buckets[h].append(H)
                    new.append(H)
                    return
                rec(k + 1, S)
                v = old[k]
                # adding v keeps |N(w) & S| <= 1 for every old w  <=>  N(v) & N(s) empty for all s in S
                if all(not (N[v] & N[s]) for s in S):
                    rec(k + 1, S + [v])
            rec(0, [])
        level = new
        yield n, level


def er_polarity(q):
    """ER_q for prime q: vertices = points of PG(2,q); x ~ y iff x.y = 0, x != y."""
    pts = []
    for a in range(q):
        for b in range(q):
            pts.append((1, a, b))
    for b in range(q):
        pts.append((0, 1, b))
    pts.append((0, 0, 1))
    N = {i: set() for i in range(len(pts))}
    for i, x in enumerate(pts):
        for j, y in enumerate(pts):
            if i < j and (x[0] * y[0] + x[1] * y[1] + x[2] * y[2]) % q == 0:
                N[i].add(j)
                N[j].add(i)
    return N


def random_maximal(n, rng):
    N = {v: set() for v in range(n)}
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    rng.shuffle(pairs)
    for a, b in pairs:
        # adding ab creates a C4 iff some neighbour of a and some neighbour of b are adjacent
        # (path b-x-y-a with x in N(b), y in N(a), x != a, y != b), or a and b already have... (C4 a-b-x-y)
        if any(N[x] & (N[a] - {b}) for x in N[b] if x != a):
            continue
        N[a].add(b)
        N[b].add(a)
    return N


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=9)
    ap.add_argument("--mckay", default=None)
    ap.add_argument("--random", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    stats = defaultdict(lambda: defaultdict(int))

    print("1. exhaustive")
    for n, graphs in all_c4_free(args.nmax):
        for G in graphs:
            N = adj_sets(G)
            check_graph(N, stats, f"exhaustive:n{n}", None)
        assert len(graphs) == A006786[n], f"enumeration found {len(graphs)} graphs on {n} vertices, OEIS A006786 says {A006786[n]}"
        print(f"   n={n}: {len(graphs)} C4-free graphs up to isomorphism, all constraints hold", flush=True)

    if args.mckay:
        print("2. McKay-Afzaly extremal graphs")
        for p in sorted(glob.glob(os.path.join(args.mckay, "c4_n*.s6")), key=lambda s: int(re.search(r"n(\d+)e", s).group(1))):
            nn, ee = map(int, re.search(r"n(\d+)e(\d+)", p).groups())
            cnt = 0
            with open(p, "rb") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    G = nx.from_sparse6_bytes(line)
                    N = adj_sets(G)
                    assert len(N) == nn and G.number_of_edges() == ee
                    prev = lp_c4.EXACT.get(nn - 1) if (nn <= 40 or nn == 41) and nn > 1 else None
                    check_graph(N, stats, f"mckay:n{nn}", prev)
                    cnt += 1
            print(f"   {os.path.basename(p)}: {cnt} graphs OK", flush=True)

    print("3. polarity graphs")
    for q in (2, 3, 5, 7):
        N = er_polarity(q)
        m = check_graph(N, stats, f"polarity:q{q}")
        print(f"   ER_{q}: n={len(N)}, m={m} OK")

    print("4. random maximal C4-free graphs")
    rng = random.Random(args.seed)
    for t in range(args.random):
        n = rng.randint(10, 60)
        check_graph(random_maximal(n, rng), stats, f"random:{n}")
    print(f"   {args.random} graphs OK")

    print("\nMinimum slack per family (0 = constraint tight on some graph):")
    for fam, st in stats.items():
        print(f"   {fam:12s} graphs={st['graphs']:7d}  min slack (I4) = {st['min_slack_I4']}  (I5) = {st['min_slack_I5']}")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
