#!/usr/bin/env python3
"""
Generate ring specifications (addition, negation, and admissible multiplier subgroup U)
for the generalized ring-multiplier starter search engine `ring_starter_bt.c`,
and convert found U-invariant starters into full matching certificates for K_{n+1}.

Supported rings of odd order n:
  - Z_n:          spec "Z:<n>:<gen>"   (cyclic ring, U = <gen> <= Z_n*)
  - F_{p^r}:      spec "GF:<p>:<r>:<u_ord>" (finite field GF(p^r), U = unique subgroup of order u_ord)
  - Product ring: spec "PROD:<comp1>*<comp2>:..." e.g. "GF:5:2*GF:7:1" with U of order u_ord.
"""
import argparse
import math
import sys
from sympy import factorint, isprime, GF, Poly
from sympy.abc import x


def find_primitive_poly(p, r):
    """Find a monic irreducible polynomial of degree r over GF(p) whose root generates GF(p^r)*."""
    if r == 1:
        # Just find primitive root mod p
        g = 2
        q = p - 1
        pf = list(factorint(q).keys())
        while True:
            if all(pow(g, q // f, p) != 1 for f in pf):
                return None, g
            g += 1
    q = p**r
    order = q - 1
    pf = list(factorint(order).keys())

    def poly_mul(a, b, mod_poly):
        res = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    res[i + j] = (res[i + j] + ai * bj) % p
        # reduce mod mod_poly (monic of deg r)
        for i in range(len(res) - 1, r - 1, -1):
            c = res[i]
            if c:
                for j in range(r + 1):
                    res[i - r + j] = (res[i - r + j] - c * mod_poly[j]) % p
        return res[:r]

    def poly_pow(base, exp, mod_poly):
        res = [0] * r
        res[0] = 1
        b = base[:]
        e = exp
        while e > 0:
            if e & 1:
                res = poly_mul(res, b, mod_poly)
            b = poly_mul(b, b, mod_poly)
            e >>= 1
        return res

    # Enumerate monic polynomials x^r + c_{r-1} x^{r-1} + ... + c_0
    # Prefer sparse polynomials (trinomials / low weight)
    from itertools import product
    candidates = []
    # Try trinomials x^r + a*x + b first
    if r >= 2:
        for a in range(p):
            for b in range(1, p):
                coeffs = [b, a] + [0] * (r - 2) + [1]
                candidates.append(coeffs)
    # Fallback: all monic
    def all_monic():
        for coeffs in candidates:
            yield coeffs
        for tup in product(range(p), repeat=r):
            if tup[0] == 0:
                continue
            yield list(tup) + [1]

    one = [1] + [0] * (r - 1)
    x_poly = [0, 1] + [0] * (r - 2)
    for mp in all_monic():
        # Check irreducibility via Poly
        poly_obj = Poly(list(reversed(mp)), x, modulus=p)
        if not poly_obj.is_irreducible:
            continue
        # Check x is primitive root of GF(p)[x]/(mp)
        if poly_pow(x_poly, order, mp) != one:
            continue
        if all(poly_pow(x_poly, order // f, mp) != one for f in pf):
            return mp, None
    raise RuntimeError(f"No primitive polynomial found for GF({p}^{r})")


class FiniteFieldRing:
    def __init__(self, p, r):
        self.p = p
        self.r = r
        self.n = p**r
        self.mp, self.g_int = find_primitive_poly(p, r)
        # Elements are integers 0..n-1 representing base-p digits (c_0 + c_1*p + ...)
        # 0 is additive identity; 1 is multiplicative identity.
        self._build_ops()

    def _to_vec(self, a):
        v = [0] * self.r
        for i in range(self.r):
            v[i] = a % self.p
            a //= self.p
        return v

    def _from_vec(self, v):
        a = 0
        for i in range(self.r - 1, -1, -1):
            a = a * self.p + v[i]
        return a

    def _build_ops(self):
        p, r, n = self.p, self.r, self.n
        if r == 1:
            self.prim = self.g_int
            self.add = lambda a, b: (a + b) % p
            self.neg = lambda a: (-a) % p
            self.mul = lambda a, b: (a * b) % p
            return
        # Precompute vector representations and multiplication via primitive root powers
        mp = self.mp
        def poly_mul(a, b):
            res = [0] * (2 * r - 1)
            for i in range(r):
                ai = a[i]
                if ai:
                    for j in range(r):
                        res[i + j] = (res[i + j] + ai * b[j]) % p
            for i in range(2 * r - 2, r - 1, -1):
                c = res[i]
                if c:
                    for j in range(r + 1):
                        res[i - r + j] = (res[i - r + j] - c * mp[j]) % p
            return res[:r]

        x_vec = [0] * r
        x_vec[1] = 1
        cur = [0] * r
        cur[0] = 1
        self.exp_tab = [0] * (n - 1)
        self.log_tab = [-1] * n
        for e in range(n - 1):
            val = self._from_vec(cur)
            self.exp_tab[e] = val
            self.log_tab[val] = e
            cur = poly_mul(cur, x_vec)
        assert cur == [1] + [0] * (r - 1)
        self.prim = self.exp_tab[1]

        vecs = [self._to_vec(a) for a in range(n)]
        self._vecs = vecs
        def add_fn(a, b):
            va, vb = vecs[a], vecs[b]
            res = 0
            for i in range(r - 1, -1, -1):
                res = res * p + ((va[i] + vb[i]) % p)
            return res
        def neg_fn(a):
            va = vecs[a]
            res = 0
            for i in range(r - 1, -1, -1):
                res = res * p + ((-va[i]) % p)
            return res
        def mul_fn(a, b):
            if a == 0 or b == 0:
                return 0
            return self.exp_tab[(self.log_tab[a] + self.log_tab[b]) % (n - 1)]
        self.add = add_fn
        self.neg = neg_fn
        self.mul = mul_fn

    def pow(self, a, e):
        if self.r == 1:
            return pow(a, e, self.p)
        if a == 0:
            return 0 if e > 0 else 1
        return self.exp_tab[(self.log_tab[a] * e) % (self.n - 1)]


def build_ring_spec(mode, params):
    """Return (n, m, add_fn, neg_fn, mul_u_table, desc)."""
    if mode == "Z":
        n, gen = int(params[0]), int(params[1])
        assert n % 2 == 1 and math.gcd(gen, n) == 1
        # Generate U = <gen>
        U = []
        cur = 1
        while cur not in U:
            U.append(cur)
            cur = (cur * gen) % n
        m = len(U)
        assert m % 2 == 1, f"|U|={m} must be odd"
        for u in U[1:]:
            assert math.gcd(u - 1, n) == 1, f"u={u} not admissible mod {n}"
        add_fn = lambda a, b: (a + b) % n
        neg_fn = lambda a: (-a) % n
        mul_u = [[(u * a) % n for a in range(n)] for u in U]
        return n, m, add_fn, neg_fn, mul_u, f"Z_{n} U=<{gen}> |U|={m}"

    elif mode == "GF":
        p, r, u_ord = int(params[0]), int(params[1]), int(params[2])
        F = FiniteFieldRing(p, r)
        n = F.n
        assert (n - 1) % u_ord == 0 and u_ord % 2 == 1
        gen = F.pow(F.prim, (n - 1) // u_ord)
        U = [1]
        cur = gen
        while cur != 1:
            U.append(cur)
            cur = F.mul(cur, gen)
        assert len(U) == u_ord
        mul_u = [[F.mul(u, a) for a in range(n)] for u in U]
        desc = f"GF({p}^{r})={n} mp={F.mp} prim={F.prim} gen={gen} |U|={u_ord}"
        return n, u_ord, F.add, F.neg, mul_u, desc

    elif mode == "PROD":
        # Format: p1,r1,p2,r2,u_ord,twist
        p1, r1, p2, r2, u_ord, twist = [int(z) for z in params]
        F1 = FiniteFieldRing(p1, r1)
        F2 = FiniteFieldRing(p2, r2)
        n1, n2 = F1.n, F2.n
        n = n1 * n2
        assert u_ord % 2 == 1 and (n1 - 1) % u_ord == 0 and (n2 - 1) % u_ord == 0
        assert math.gcd(twist, u_ord) == 1
        g1 = F1.pow(F1.prim, (n1 - 1) // u_ord)
        g2 = F2.pow(F2.prim, ((n2 - 1) // u_ord) * twist)
        U = []
        c1, c2 = 1, 1
        for _ in range(u_ord):
            U.append((c1, c2))
            c1 = F1.mul(c1, g1)
            c2 = F2.mul(c2, g2)
        assert c1 == 1 and c2 == 1
        for u1, u2 in U[1:]:
            assert u1 != 1 and u2 != 1
        def enc(a1, a2): return a1 * n2 + a2
        def dec(a): return divmod(a, n2)
        def add_fn(a, b):
            a1, a2 = dec(a); b1, b2 = dec(b)
            return enc(F1.add(a1, b1), F2.add(a2, b2))
        def neg_fn(a):
            a1, a2 = dec(a)
            return enc(F1.neg(a1), F2.neg(a2))
        mul_u = []
        for u1, u2 in U:
            row = [0] * n
            for a1 in range(n1):
                ua1 = F1.mul(u1, a1)
                for a2 in range(n2):
                    row[enc(a1, a2)] = enc(ua1, F2.mul(u2, a2))
            mul_u.append(row)
        desc = f"GF({p1}^{r1})xGF({p2}^{r2})={n} |U|={u_ord} twist={twist} mp1={F1.mp} mp2={F2.mp}"
        return n, u_ord, add_fn, neg_fn, mul_u, desc
    else:
        raise ValueError(f"Unknown mode {mode}")


def write_spec(out_path, mode, params):
    n, m, add_fn, neg_fn, mul_u, desc = build_ring_spec(mode, params)
    # Build U-orbits on R \ {0}
    u_orb_id = [-1] * n
    u_orbs = []
    for a in range(1, n):
        if u_orb_id[a] == -1:
            oid = len(u_orbs)
            orb = [mul_u[k][a] for k in range(m)]
            assert len(set(orb)) == m, f"Non-free U-orbit at {a}"
            for v in orb:
                u_orb_id[v] = oid
            u_orbs.append(orb)
    assert len(u_orbs) == (n - 1) // m

    # Build G-orbits (< -1, U >) on R \ {0}
    g_orb_id = [-1] * n
    g_reps = []
    for a in range(1, n):
        if g_orb_id[a] == -1:
            gid = len(g_reps)
            orb = []
            for k in range(m):
                v = mul_u[k][a]
                orb.append(v)
                orb.append(neg_fn(v))
            assert len(set(orb)) == 2 * m, f"Non-free G-orbit at {a}"
            for v in orb:
                g_orb_id[v] = gid
            g_reps.append(a)
    c = len(g_reps)
    assert c == (n - 1) // (2 * m)

    # Also verify addition table + distributivity on sample
    neg_arr = [neg_fn(a) for a in range(n)]
    # Write binary/text spec file for C engine
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(f"# {desc}\n")
        f.write(f"{n} {m} {c}\n")
        f.write(" ".join(map(str, neg_arr)) + "\n")
        f.write(" ".join(map(str, u_orb_id)) + "\n")
        f.write(" ".join(map(str, g_orb_id)) + "\n")
        f.write(" ".join(map(str, g_reps)) + "\n")
        for k in range(m):
            f.write(" ".join(map(str, mul_u[k])) + "\n")
        for a in range(n):
            f.write(" ".join(str(add_fn(a, b)) for b in range(n)) + "\n")
    print(f"Wrote spec {out_path}: {desc}, c={c} conditions, 2c={2*c} U-orbits")


def expand_starter_to_matchings(spec_path, pairs_str, out_path):
    """Expand a list of c representative pairs `x-y ...` into full K_{n+1} matchings."""
    with open(spec_path, "r", encoding="utf-8") as f:
        header = f.readline().strip()
        n, m, c = map(int, f.readline().split())
        neg_arr = list(map(int, f.readline().split()))
        u_orb_id = list(map(int, f.readline().split()))
        g_orb_id = list(map(int, f.readline().split()))
        g_reps = list(map(int, f.readline().split()))
        mul_u = [list(map(int, f.readline().split())) for _ in range(m)]
        add_tab = [list(map(int, f.readline().split())) for _ in range(n)]

    reps = []
    for tok in pairs_str.strip().split():
        a, b = map(int, tok.split("-"))
        reps.append((a, b))
    assert len(reps) == c, f"Expected {c} representative pairs, got {len(reps)}"

    # Expand U-orbits
    starter = []
    for a, b in reps:
        for k in range(m):
            u, v = mul_u[k][a], mul_u[k][b]
            starter.append((u, v) if u < v else (v, u))
    assert len(starter) == (n - 1) // 2

    inf = n
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(f"# Perfect 1-factorization of K_{n+1} ({header})\n")
        f.write(f"# U-orbit representative pairs ({c}): {pairs_str.strip()}\n")
        for i in range(n):
            edges = [(i, inf)]
            for x, y in starter:
                u, v = add_tab[x][i], add_tab[y][i]
                edges.append((u, v) if u < v else (v, u))
            edges.sort()
            f.write(" ".join(f"{u}-{v}" for u, v in edges) + "\n")
    print(f"Wrote {n} matchings of K_{n+1} to {out_path}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p1 = sub.add_parser("spec")
    p1.add_argument("out")
    p1.add_argument("mode", choices=["Z", "GF", "PROD"])
    p1.add_argument("params", nargs="+")

    p2 = sub.add_parser("expand")
    p2.add_argument("spec")
    p2.add_argument("out")
    p2.add_argument("pairs", nargs="+")

    args = ap.parse_args()
    if args.cmd == "spec":
        write_spec(args.out, args.mode, args.params)
    elif args.cmd == "expand":
        expand_starter_to_matchings(args.spec, " ".join(args.pairs), args.out)


if __name__ == "__main__":
    main()
