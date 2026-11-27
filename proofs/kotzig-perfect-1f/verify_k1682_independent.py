#!/usr/bin/env python3
"""
Completely independent verification of our Perfect 1-Factorization of K_1682 (q = 41^2 = 1681).

Zero shared code with `gen_ring_spec.py`, `ring_starter_bt_v2.c`, or `verify_p1f.c`.
This script:
  1. Constructs GF(41^2) = GF(41)[t] / (t^2 + t + 12) directly from first principles.
  2. Verifies t^2 + t + 12 is irreducible over GF(41) and t is a primitive root of GF(41^2)*.
  3. Constructs U = <t^16> (order 105) and verifies U acts freely on GF(41^2)* and -1 not in U.
  4. Expands the 8 representative pairs into an 840-pair starter S in GF(41^2), verifying:
       - S partitions GF(41^2) minus {0},
       - the differences {+(x-y), -(x-y)} partition GF(41^2) minus {0},
       - u*S = S for all u in U.
  5. Builds ALL 1681 matchings F_a = (S + a) U {{a, inf}} of K_1682 (vertices 0..1681).
  6. Runs TWO checks:
       (a) Pure-Python algebraic check of all 8 G-orbit representative pairs F_0 U F_{d_j}.
       (b) Full brute-force check over ALL C(1681, 2) = 1,412,040 pairs of matchings
           (using Numba JIT if installed, else pure Python) with NO use of symmetry!
"""
import lzma
import os
import sys
import time

P = 41
Q = P * P  # 1681
INF = Q    # 1681

# Representation: integer v in 0..1680 encodes a + b*t where a = v % 41, b = v // 41.
# Field modulus: t^2 + t + 12 = 0 => t^2 = -t - 12 = 40*t + 29 (mod 41).
REPS = [
    (1, 328),
    (3, 813),
    (15, 1532),
    (43, 387),
    (4, 1300),
    (6, 781),
    (2, 650),
    (11, 728),
]


def gf_add(x, y):
    ax, bx = x % P, x // P
    ay, by = y % P, y // P
    return ((bx + by) % P) * P + ((ax + ay) % P)


def gf_sub(x, y):
    ax, bx = x % P, x // P
    ay, by = y % P, y // P
    return ((bx - by) % P) * P + ((ax - ay) % P)


def gf_mul(x, y):
    ax, bx = x % P, x // P
    ay, by = y % P, y // P
    # (ax + bx*t)(ay + by*t) = ax*ay + (ax*by + bx*ay)*t + bx*by*(29 + 40*t)
    c0 = (ax * ay + 29 * bx * by) % P
    c1 = (ax * by + bx * ay + 40 * bx * by) % P
    return c1 * P + c0


def gf_pow(x, e):
    res = 1
    base = x
    while e > 0:
        if e & 1:
            res = gf_mul(res, base)
        base = gf_mul(base, base)
        e >>= 1
    return res


def main():
    t0 = time.perf_counter()

    # 1. Verify t^2 + t + 12 has no root in GF(41) (hence irreducible)
    for r in range(P):
        assert (r * r + r + 12) % P != 0
    # 2. Verify t (= 41) has exact multiplicative order 1680 = 2^4 * 3 * 5 * 7
    t_elem = P  # 0 + 1*t
    assert gf_pow(t_elem, 1680) == 1
    for qdiv in (2, 3, 5, 7):
        assert gf_pow(t_elem, 1680 // qdiv) != 1

    # 3. Build subgroup U = <t^16> of order 105
    u_gen = gf_pow(t_elem, 16)
    U = []
    cur = 1
    for _ in range(105):
        U.append(cur)
        cur = gf_mul(cur, u_gen)
    assert cur == 1 and len(set(U)) == 105
    neg1 = P - 1  # -1 = 40 + 0*t
    assert neg1 not in U
    print(f"[1] GF(41^2) = GF(41)[t]/(t^2+t+12) verified; u_gen = t^16 = {u_gen} ({u_gen % P} + {u_gen // P}*t), |U| = 105.")

    # 4. Expand starter S from the 8 representative pairs
    starter = []
    for a, b in REPS:
        for u in U:
            ua, ub = gf_mul(u, a), gf_mul(u, b)
            starter.append((ua, ub) if ua < ub else (ub, ua))
    assert len(starter) == 840 and len(set(starter)) == 840

    # Verify starter covers GF(41^2) \ {0} once and differences cover GF(41^2) \ {0} once
    covered_v = set()
    covered_d = set()
    for a, b in starter:
        assert a != 0 and b != 0 and a != b
        covered_v.add(a)
        covered_v.add(b)
        covered_d.add(gf_sub(a, b))
        covered_d.add(gf_sub(b, a))
    assert len(covered_v) == Q - 1 and 0 not in covered_v
    assert len(covered_d) == Q - 1 and 0 not in covered_d

    # Verify U-invariance u*S = S
    s_set = set(starter)
    for u in U:
        uS = set()
        for a, b in starter:
            ua, ub = gf_mul(u, a), gf_mul(u, b)
            uS.add((ua, ub) if ua < ub else (ub, ua))
        assert uS == s_set
    print("[2] 840-pair starter S verified: partitions GF(41^2)\\{0}, differences bijective, U-invariant.")

    # 5. Pure-Python check of all 8 G-orbit representatives (G = <-1, U>, order 210)
    # Build mate0 for F_0
    mate0 = [0] * (Q + 1)
    mate0[0] = INF
    mate0[INF] = 0
    for a, b in starter:
        mate0[a] = b
        mate0[b] = a

    # Partition GF(41^2)* into 8 G-orbits and test F_0 U F_d for one d per orbit
    seen_g = set()
    g_reps = []
    for x in range(1, Q):
        if x not in seen_g:
            g_reps.append(x)
            for u in U:
                ux = gf_mul(u, x)
                seen_g.add(ux)
                seen_g.add(gf_mul(neg1, ux))
    assert len(g_reps) == 8 and len(seen_g) == Q - 1

    for idx, d in enumerate(g_reps):
        mated = [0] * (Q + 1)
        mated[d] = INF
        mated[INF] = d
        for a, b in starter:
            ad, bd = gf_add(a, d), gf_add(b, d)
            mated[ad] = bd
            mated[bd] = ad
        # Walk cycle from 0
        v = 0
        steps = 0
        while True:
            v = mate0[v]
            steps += 1
            v = mated[v]
            steps += 1
            if v == 0:
                break
        assert steps == Q + 1, f"Orbit {idx} (d={d}) failed: cycle len {steps}"
    print(f"[3] Pure-Python orbit check PASSED: all 8 G-orbit reps {g_reps} induce a 1682-cycle.")

    # 6. Build full 1681 x 1682 matching matrix and run FULL BRUTE-FORCE check of all 1,412,040 pairs!
    import numpy as np
    adj = np.full((Q, Q + 1), -1, dtype=np.int32)
    edge_seen = np.zeros((Q + 1, Q + 1), dtype=np.uint8)
    for fi in range(Q):
        adj[fi, fi] = INF
        adj[fi, INF] = fi
        edge_seen[fi, INF] = 1
        for a, b in starter:
            u, v = gf_add(a, fi), gf_add(b, fi)
            adj[fi, u] = v
            adj[fi, v] = u
            if u < v:
                assert edge_seen[u, v] == 0
                edge_seen[u, v] = 1
            else:
                assert edge_seen[v, u] == 0
                edge_seen[v, u] = 1
    assert np.all(adj >= 0)
    assert int(edge_seen.sum()) == (Q + 1) * Q // 2

    from numba import njit

    @njit
    def brute_force_all_pairs(adj_mat):
        nf = adj_mat.shape[0]
        vc = adj_mat.shape[1]
        pairs = 0
        for i in range(nf):
            for j in range(i + 1, nf):
                cur = 0
                steps = 0
                while True:
                    cur = adj_mat[i, cur]
                    cur = adj_mat[j, cur]
                    steps += 2
                    if cur == 0:
                        break
                if steps != vc:
                    return -1
                pairs += 1
        return pairs

    t1 = time.perf_counter()
    checked = brute_force_all_pairs(adj)
    t2 = time.perf_counter()
    assert checked == Q * (Q - 1) // 2
    print(
        f"[4] Independent Numba brute-force check PASSED: "
        f"all {checked} unordered pairs of 1-factors of K_{Q+1} form a single {Q+1}-cycle "
        f"(brute-force {t2 - t1:.3f} s, total {t2 - t0:.3f} s)."
    )

    # Optionally write compressed matchings file (.xz) and compact starter file if requested
    if len(sys.argv) >= 2:
        out_xz = sys.argv[1]
        with lzma.open(out_xz, "wt", encoding="utf-8", preset=6) as f:
            f.write("# Perfect 1-factorization of K_1682 (q = 41^2 = 1681)\n")
            f.write("# Field: GF(41^2) = GF(41)[t]/(t^2 + t + 12), v = a + 41*b, inf = 1681\n")
            f.write("# U = <t^16> (order 105), 8 rep pairs: " + " ".join(f"{a}-{b}" for a, b in REPS) + "\n")
            for fi in range(Q):
                edges = []
                for u in range(Q + 1):
                    v = int(adj[fi, u])
                    if u < v:
                        edges.append(f"{u}-{v}")
                f.write(" ".join(edges) + "\n")
        sz = os.path.getsize(out_xz)
        print(f"[5] Wrote compressed certificate {out_xz} ({sz:,} bytes).")
    if len(sys.argv) >= 3:
        out_st = sys.argv[2]
        with open(out_st, "w", encoding="utf-8") as f:
            f.write("# Perfect 1-factorization of K_1682 via U-invariant starter in GF(41^2)\n")
            f.write("# Field: GF(41)[t]/(t^2 + t + 12); element v in 0..1680 represents (v % 41) + (v // 41)*t\n")
            f.write(f"# Multiplier subgroup: U = <t^16> = <{u_gen}> of order 105 (admissible: |U| odd, -1 not in U)\n")
            f.write("# 8 U-orbit representative pairs:\n")
            f.write("REPS: " + " ".join(f"{a}-{b}" for a, b in REPS) + "\n")
            f.write("# Full 840-pair starter S (inducing F_a = (S + a) U {{a, 1681}} for a in 0..1680):\n")
            for i in range(0, len(starter), 10):
                f.write(" ".join(f"{a}-{b}" for a, b in starter[i : i + 10]) + "\n")
        print(f"[6] Wrote starter certificate {out_st} ({os.path.getsize(out_st):,} bytes).")


if __name__ == "__main__":
    main()
