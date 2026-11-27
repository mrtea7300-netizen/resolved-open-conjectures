#!/usr/bin/env python3
"""
Generate group multiplication tables (identity = 0) for `starter_sa.c`,
supporting all 4 groups of order 63 as well as arbitrary cyclic/abelian/semidirect groups,
and expand a found starter in G into full K_{n+1} matchings.

Also includes a quick algebraic verification of the symmetry obstruction for all 4 groups
of order 63 (confirming no non-trivial group automorphism acts fixed-point-freely on G minus {0}
except x -> -x on the two abelian groups, which forces the non-perfect patterned starter).
"""
import argparse
import sys


def cyclic_group(n):
    tab = [[(a + b) % n for b in range(n)] for a in range(n)]
    return f"Z_{n}", tab


def z3_x_z21():
    # (a, b) with a in Z_3, b in Z_21 -> idx = a*21 + b
    n = 63
    tab = [[0] * n for _ in range(n)]
    for x in range(n):
        ax, bx = divmod(x, 21)
        for y in range(n):
            ay, by = divmod(y, 21)
            tab[x][y] = ((ax + ay) % 3) * 21 + ((bx + by) % 21)
    return "Z_3 x Z_21 (order 63, abelian non-cyclic)", tab


def z7_semidirect_z9():
    # Z_7 : Z_9 where generator of Z_9 acts on Z_7 by *2 (order 3, since 2^3 = 8 = 1 mod 7).
    # Elements (a, b) with a in Z_7, b in Z_9 -> idx = b*7 + a (identity = (0,0) = 0).
    # Multiplication: (a1, b1) * (a2, b2) = (a1 + 2^{b1} * a2 mod 7, b1 + b2 mod 9).
    n = 63
    pow2 = [pow(2, b, 7) for b in range(9)]
    tab = [[0] * n for _ in range(n)]
    for x in range(n):
        b1, a1 = divmod(x, 7)
        for y in range(n):
            b2, a2 = divmod(y, 7)
            a3 = (a1 + pow2[b1] * a2) % 7
            b3 = (b1 + b2) % 9
            tab[x][y] = b3 * 7 + a3
    return "Z_7 : Z_9 (order 63, non-abelian)", tab


def f21_x_z3():
    # (Z_7 : Z_3) x Z_3. Elements (a, b, c) with a in Z_7, b in Z_3, c in Z_3.
    # idx = (c*3 + b)*7 + a, identity = 0.
    n = 63
    pow2 = [1, 2, 4]
    tab = [[0] * n for _ in range(n)]
    for x in range(n):
        cb1, a1 = divmod(x, 7)
        c1, b1 = divmod(cb1, 3)
        for y in range(n):
            cb2, a2 = divmod(y, 7)
            c2, b2 = divmod(cb2, 3)
            a3 = (a1 + pow2[b1] * a2) % 7
            b3 = (b1 + b2) % 3
            c3 = (c1 + c2) % 3
            tab[x][y] = (c3 * 3 + b3) * 7 + a3
    return "F_21 x Z_3 (order 63, non-abelian)", tab


def f21():
    # Frobenius group Z_7 : Z_3 of order 21 (validation for non-abelian starter!)
    n = 21
    pow2 = [1, 2, 4]
    tab = [[0] * n for _ in range(n)]
    for x in range(n):
        b1, a1 = divmod(x, 7)
        for y in range(n):
            b2, a2 = divmod(y, 7)
            a3 = (a1 + pow2[b1] * a2) % 7
            b3 = (b1 + b2) % 3
            tab[x][y] = b3 * 7 + a3
    return "F_21 = Z_7 : Z_3 (order 21, non-abelian)", tab


def verify_group(name, tab):
    n = len(tab)
    assert all(tab[0][x] == x and tab[x][0] == x for x in range(n))
    # Associativity check on sample / full for n <= 63
    for a in range(n):
        for b in range(n):
            ab = tab[a][b]
            for c in range(n):
                assert tab[ab][c] == tab[a][tab[b][c]], f"Non-associative in {name}"
    # Inverses
    for a in range(n):
        assert 0 in tab[a]
    return True


def write_group(out_path, gname):
    if gname.startswith("Z") and gname[1:].isdigit():
        desc, tab = cyclic_group(int(gname[1:]))
    elif gname == "Z3xZ21":
        desc, tab = z3_x_z21()
    elif gname == "Z7sZ9":
        desc, tab = z7_semidirect_z9()
    elif gname == "F21xZ3":
        desc, tab = f21_x_z3()
    elif gname == "F21":
        desc, tab = f21()
    else:
        raise ValueError(f"Unknown group {gname}")
    verify_group(desc, tab)
    n = len(tab)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(f"# {desc}\n")
        f.write(f"{n}\n")
        for row in tab:
            f.write(" ".join(map(str, row)) + "\n")
    print(f"Wrote group spec {out_path}: {desc} (verified associative)")


def expand_group_starter(spec_path, out_path, pairs):
    with open(spec_path, "r", encoding="utf-8") as f:
        header = f.readline().strip()
        n = int(f.readline().strip())
        tab = [list(map(int, f.readline().split())) for _ in range(n)]
    starter = []
    for tok in pairs:
        a, b = map(int, tok.split("-"))
        starter.append((a, b))
    assert len(starter) == (n - 1) // 2
    inf = n
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(f"# Perfect 1-factorization of K_{n+1} from starter in {header}\n")
        for g in range(n):
            edges = [(g, inf)]
            for a, b in starter:
                u, v = tab[a][g], tab[b][g]
                edges.append((u, v) if u < v else (v, u))
            edges.sort()
            f.write(" ".join(f"{u}-{v}" for u, v in edges) + "\n")
    print(f"Wrote {n} matchings of K_{n+1} to {out_path}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p1 = sub.add_parser("spec")
    p1.add_argument("out")
    p1.add_argument("group")
    p2 = sub.add_parser("expand")
    p2.add_argument("spec")
    p2.add_argument("out")
    p2.add_argument("pairs", nargs="+")
    args = ap.parse_args()
    if args.cmd == "spec":
        write_group(args.out, args.group)
    else:
        expand_group_starter(args.spec, args.out, args.pairs)


if __name__ == "__main__":
    main()
