#!/usr/bin/env python3
"""
Standalone brute-force verifier for a perfect 1-factorization (P1F) of K_{2n}.

No shared code with any search engine. Checks directly from the definition:
  1. Exactly 2n - 1 lines (one 1-factor per line), vertices labeled 0..2n-1.
  2. Each line contains exactly n disjoint edges covering 0..2n-1 once (a perfect matching).
  3. All n*(2n-1) edges across all 1-factors are distinct (partition of E(K_{2n})).
  4. For EVERY unordered pair (F_i, F_j), 0 <= i < j < 2n-1, the union F_i U F_j
     is a single Hamiltonian cycle of length 2n.

Input format:
  One matching per line; edges written as `u-v` separated by whitespace.
  Blank lines and `#` comment lines are ignored.
"""
import sys
import time


def parse_matchings(path):
    matchings = []
    with open(path, "r", encoding="utf-8") as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            edges = []
            for tok in line.split():
                if "-" not in tok:
                    raise ValueError(f"Line {lineno}: bad edge token {tok!r}")
                a_s, b_s = tok.split("-", 1)
                a, b = int(a_s), int(b_s)
                if a == b:
                    raise ValueError(f"Line {lineno}: self-loop {a}-{b}")
                edges.append((a, b) if a < b else (b, a))
            matchings.append(edges)
    return matchings


def verify_p1f(matchings):
    t0 = time.perf_counter()
    num_f = len(matchings)
    if num_f < 3 or num_f % 2 == 0:
        raise ValueError(f"Expected odd number of 1-factors >= 3, got {num_f}")
    vcount = num_f + 1  # 2n
    half = vcount // 2  # n

    # Check each factor is a perfect matching on 0..2n-1 and build adjacency arrays
    adj = []
    seen_edges = set()
    for fi, edges in enumerate(matchings):
        if len(edges) != half:
            raise ValueError(f"Factor {fi}: expected {half} edges, got {len(edges)}")
        mate = [-1] * vcount
        for u, v in edges:
            if not (0 <= u < vcount and 0 <= v < vcount):
                raise ValueError(f"Factor {fi}: vertex out of range in ({u},{v})")
            if mate[u] != -1 or mate[v] != -1:
                raise ValueError(f"Factor {fi}: vertex repeated in ({u},{v})")
            mate[u] = v
            mate[v] = u
            e = (u, v) if u < v else (v, u)
            if e in seen_edges:
                raise ValueError(f"Duplicate edge {e} in factor {fi}")
            seen_edges.add(e)
        adj.append(mate)

    expected_edges = vcount * (vcount - 1) // 2
    if len(seen_edges) != expected_edges:
        raise ValueError(f"Expected {expected_edges} edges total, got {len(seen_edges)}")

    # Brute-force Hamiltonicity check over ALL unordered pairs (i, j)
    pairs_checked = 0
    for i in range(num_f):
        mi = adj[i]
        for j in range(i + 1, num_f):
            mj = adj[j]
            # Walk alternating edges of F_i and F_j starting from vertex 0
            cur = 0
            steps = 0
            while True:
                cur = mi[cur]
                steps += 1
                cur = mj[cur]
                steps += 1
                if cur == 0:
                    break
                if steps > vcount:
                    raise RuntimeError(f"Non-terminating walk for pair ({i}, {j})")
            if steps != vcount:
                raise ValueError(
                    f"Pair ({i}, {j}) is NOT Hamiltonian: cycle through 0 has length {steps} != {vcount}"
                )
            pairs_checked += 1

    dt = time.perf_counter() - t0
    return vcount, num_f, expected_edges, pairs_checked, dt


def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <matchings.txt>", file=sys.stderr)
        sys.exit(2)
    path = sys.argv[1]
    matchings = parse_matchings(path)
    vcount, num_f, edges, pairs, dt = verify_p1f(matchings)
    print(
        f"VERIFIED PERFECT 1-FACTORIZATION OF K_{vcount}: "
        f"{num_f} perfect matchings, {edges} edges partitioned, "
        f"all {pairs} pairs form a single Hamiltonian {vcount}-cycle "
        f"({dt:.3f} s)."
    )


if __name__ == "__main__":
    main()
