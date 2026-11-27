#!/usr/bin/env python3
"""Degree-class LP for ex(n, C4) with exact certificates.

Independent re-implementation of the LP written out in proof.md (Section 2).  The constraint
numbering (E1), (E2), (E3_d), (I4), (I5_d), the degree range D and the dual multipliers
(a, b, c_d, z, w_d) follow proof.md exactly.

  * find_dual(n, m, dmin)    -> exact rational Farkas certificate (dict) or None
  * find_primal(n, m, dmin)  -> exact rational feasible point (dict) or None

Floating-point solves use HiGHS (scipy.optimize.linprog, dual simplex) only to *locate* a vertex;
the vertex is then recomputed exactly over Q from its active constraints with python-flint
and verified exactly.  Nothing is accepted unless the exact check passes.  The standalone
checker check_certificates.py re-verifies the dual certificates without this file.

Usage:
    python lp_c4.py --run            # compute bounds n = 41..57, write data/cert_*.txt, data/bounds.json
    python lp_c4.py --sanity         # LP feasible at a(n), n <= 40, and at McKay's lower bounds
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
from fractions import Fraction

import numpy as np
import flint
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

# OEIS A006855 data section, a(1..40) (mirror, header #86 Mar 03 2026).
A006855 = [0, 1, 3, 4, 6, 7, 9, 11, 13, 16, 18, 21, 24, 27, 30, 33, 36, 39, 42, 46, 50, 52, 56,
           59, 63, 67, 71, 76, 80, 85, 90, 92, 96, 102, 106, 110, 113, 117, 122, 127]
EXACT = {i + 1: v for i, v in enumerate(A006855)}
MCKAY_LB = {41: 132, 42: 137, 43: 142, 44: 148, 45: 154, 46: 157, 47: 163, 48: 168, 49: 174}
ALEKSEYEV_UB = {41: 133, 42: 139, 43: 145, 44: 151, 45: 158, 46: 165, 47: 171, 48: 176, 49: 182}


# ----------------------------------------------------------------------------------------------
# Primal LP (proof.md, Section 2).  Integer data only.
# ----------------------------------------------------------------------------------------------
def primal(n: int, m: int, dmin: int):
    """Return (D, var_names, rows) where rows = list of (coeffs:dict, sense, rhs)."""
    D = list(range(dmin, n))
    names = [("n", d) for d in D] + [("e", i, j) for i in D for j in D if i <= j]
    rows = []
    rows.append(({("n", d): 1 for d in D}, "=", n))                       # (E1)
    rows.append(({("n", d): d for d in D if d}, "=", 2 * m))              # (E2)
    for d in D:                                                            # (E3_d)
        r = {("n", d): -d} if d else {}
        for j in D:
            key = ("e", min(d, j), max(d, j))
            r[key] = r.get(key, 0) + (2 if j == d else 1)
        rows.append((r, "=", 0))
    rows.append(({("n", d): d * (d - 1) + d % 2 for d in D if d * (d - 1) + d % 2}, "<=", n * (n - 1)))  # (I4) x2
    for d in D:                                                            # (I5_d)
        r = {("n", d): -(n - 1 + d - d % 2)}
        for j in D:
            key = ("e", min(d, j), max(d, j))
            r[key] = r.get(key, 0) + (2 * d if j == d else j)
        rows.append(({k: v for k, v in r.items() if v}, "<=", 0))
    return D, names, rows


def check_primal_exact(n, m, dmin, x: dict) -> bool:
    D, names, rows = primal(n, m, dmin)
    if any(v < 0 for v in x.values()):
        return False
    for coeffs, sense, rhs in rows:
        s = sum(Fraction(c) * x.get(k, 0) for k, c in coeffs.items())
        if sense == "=" and s != rhs:
            return False
        if sense == "<=" and s > rhs:
            return False
    return True


# ----------------------------------------------------------------------------------------------
# Dual (Farkas) system, written out column by column (proof.md, Section 3).
# Unknowns u = (a, b, c_d [d in D], z, w_d [d in D]); a, b, c free; z, w >= 0.
#   col n_d : a + b d - c_d d + z (d(d-1) + d%2) - w_d (n-1+d-d%2) >= 0
#   col e_ij (i<j): c_i + c_j + j w_i + i w_j >= 0
#   col e_dd: 2 c_d + 2 d w_d >= 0
#   rhs: a n + 2 m b + z n(n-1) = -1   (normalised; any negative value certifies)
# ----------------------------------------------------------------------------------------------
def dual_system(n, m, dmin):
    D = list(range(dmin, n))
    k = len(D)
    idx = {"a": 0, "b": 1}
    for t, d in enumerate(D):
        idx[("c", d)] = 2 + t
    idx["z"] = 2 + k
    for t, d in enumerate(D):
        idx[("w", d)] = 3 + k + t
    N = 3 + 2 * k
    cols = []  # each: dict index->coef, meaning sum coef*u >= 0
    for d in D:
        cols.append(({idx["a"]: 1, idx["b"]: d, idx[("c", d)]: -d, idx["z"]: d * (d - 1) + d % 2,
                      idx[("w", d)]: -(n - 1 + d - d % 2)}, ("n", d)))
    for i in D:
        for j in D:
            if i < j:
                cols.append(({idx[("c", i)]: 1, idx[("c", j)]: 1, idx[("w", i)]: j, idx[("w", j)]: i}, ("e", i, j)))
            elif i == j:
                cols.append(({idx[("c", i)]: 2, idx[("w", i)]: 2 * i}, ("e", i, i)))
    rhs = {idx["a"]: n, idx["b"]: 2 * m, idx["z"]: n * (n - 1)}
    nonneg = [idx["z"]] + [idx[("w", d)] for d in D]
    return D, idx, N, cols, rhs, nonneg


def _clean(cmap):
    return {k: v for k, v in cmap.items() if v != 0}


def exact_solve(rows_eq, N, guess):
    """Solve the linear system rows_eq (list of (dict, rhs)) exactly; free variables are set to
    simple rationals near `guess`.  Returns list of Fractions or None if inconsistent."""
    M = flint.fmpq_mat(len(rows_eq), N + 1)
    for r, (cm, rhs) in enumerate(rows_eq):
        for c, v in cm.items():
            M[r, c] = v
        M[r, N] = rhs
    R, rank = M.rref()
    pivots = []
    for r in range(rank):
        for c in range(N + 1):
            if R[r, c] != 0:
                pivots.append(c)
                break
    if N in pivots:
        return None  # inconsistent
    free = [c for c in range(N) if c not in pivots]
    sol = [Fraction(0)] * N
    for c in free:
        sol[c] = Fraction(round(guess[c] * 2 ** 20), 2 ** 20)
    for r, pc in enumerate(pivots):
        val = Fraction(int(R[r, N].p), int(R[r, N].q))
        for c in free:
            coef = R[r, c]
            if coef != 0:
                val -= Fraction(int(coef.p), int(coef.q)) * sol[c]
        sol[pc] = val
    return sol


def check_dual_exact(n, m, dmin, u) -> bool:
    D, idx, N, cols, rhs, nonneg = dual_system(n, m, dmin)
    if any(u[i] < 0 for i in nonneg):
        return False
    for cm, _ in cols:
        if sum(c * u[i] for i, c in cm.items()) < 0:
            return False
    return sum(c * u[i] for i, c in rhs.items()) < 0


def find_dual(n, m, dmin, tol=1e-9):
    """Exact Farkas certificate of infeasibility of the primal at (n, m, dmin), or None."""
    D, idx, N, cols, rhs, nonneg = dual_system(n, m, dmin)
    A_ub = np.zeros((len(cols), N))
    for r, (cm, _) in enumerate(cols):
        for i, c in cm.items():
            A_ub[r, i] = -c
    A_eq = np.zeros((1, N))
    for i, c in rhs.items():
        A_eq[0, i] = c
    obj = np.zeros(N)
    for i in nonneg:
        obj[i] = 1.0  # minimise total multiplier mass -> a vertex with small support
    bounds = [(None, None)] * N
    for i in nonneg:
        bounds[i] = (0, None)
    res = linprog(obj, A_ub=A_ub, b_ub=np.zeros(len(cols)), A_eq=A_eq, b_eq=[-1.0],
                  bounds=bounds, method="highs-ds")
    if res.status != 0:
        return None
    u = res.x
    scale = max(1.0, float(np.max(np.abs(u))))
    for t in (tol, 1e-7, 1e-11, 1e-6, 1e-12):
        eqs = [(rhs, -1)]
        slack = A_ub @ u  # = -(col value)
        for r, (cm, _) in enumerate(cols):
            if abs(slack[r]) <= t * scale:
                eqs.append((cm, 0))
        for i in nonneg:
            if abs(u[i]) <= t * scale:
                eqs.append(({i: 1}, 0))
        sol = exact_solve(eqs, N, u)
        if sol is not None and check_dual_exact(n, m, dmin, sol):
            return {"D": D, "idx": idx, "u": sol}
    raise RuntimeError(f"HiGHS found a dual ray at n={n}, m={m}, dmin={dmin} but exact reconstruction failed")


def find_primal(n, m, dmin, tol=1e-9):
    """Exact rational feasible point of the primal at (n, m, dmin), or None if HiGHS says infeasible."""
    D, names, rows = primal(n, m, dmin)
    pos = {k: t for t, k in enumerate(names)}
    N = len(names)
    Aeq, beq, Aub, bub = [], [], [], []
    for cm, s, rhs in rows:
        v = np.zeros(N)
        for k, c in cm.items():
            v[pos[k]] = c
        (Aeq if s == "=" else Aub).append(v)
        (beq if s == "=" else bub).append(rhs)
    Aeq, Aub = np.array(Aeq), np.array(Aub)
    # objective: minimise sum of edge-class variables (any linear objective gives a vertex)
    obj = np.array([1.0 if k[0] == "e" else 0.0 for k in names])
    res = linprog(obj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=(0, None), method="highs-ds")
    if res.status != 0:
        return None
    x = res.x
    for t in (tol, 1e-7, 1e-11, 1e-6):
        eqs = []
        for cm, s, rhs in rows:
            cmi = {pos[k]: c for k, c in cm.items()}
            if s == "=":
                eqs.append((cmi, rhs))
            else:
                val = sum(c * x[i] for i, c in cmi.items())
                if abs(val - rhs) <= t * max(1.0, abs(rhs)):
                    eqs.append((cmi, rhs))
        for i in range(N):
            if abs(x[i]) <= t:
                eqs.append(({i: 1}, 0))
        sol = exact_solve(eqs, N, x)
        if sol is None:
            continue
        xd = {names[i]: sol[i] for i in range(N) if sol[i] != 0}
        if check_primal_exact(n, m, dmin, xd):
            return xd
    raise RuntimeError(f"HiGHS says feasible at n={n}, m={m}, dmin={dmin} but exact reconstruction failed")


# ----------------------------------------------------------------------------------------------
# Output
# ----------------------------------------------------------------------------------------------
def fmt(q: Fraction) -> str:
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def write_cert(path, n, m, dmin, cert, U_prev):
    D, idx, u = cert["D"], cert["idx"], cert["u"]
    # scale to integers (positive scaling preserves every inequality)
    L = math.lcm(*[q.denominator for q in u])
    ui = [q * L for q in u]
    assert all(q.denominator == 1 for q in ui)
    with open(path, "w", newline="\n") as f:
        f.write(f"# Farkas certificate: the degree-class LP of proof.md is infeasible at n={n}, m={m}.\n")
        if dmin > 0:
            f.write(f"# Uses the minimum-degree constraint (I6) with U(n-1) = {U_prev}: degrees d >= m - U(n-1) = {dmin}.\n")
        f.write("# Integer multipliers: a, b (E1, E2), z (I4 doubled), and per degree d: c_d (E3_d), w_d (I5_d).\n")
        f.write("# Verify with: python check_certificates.py\n")
        f.write(f"n {n}\nm {m}\ndmin {dmin}\n")
        f.write(f"a {fmt(ui[idx['a']])}\nb {fmt(ui[idx['b']])}\nz {fmt(ui[idx['z']])}\n")
        for d in D:
            f.write(f"d {d} c {fmt(ui[idx[('c', d)]])} w {fmt(ui[idx[('w', d)]])}\n")


def run(nmax=57, out=True):
    os.makedirs(DATA, exist_ok=True)
    U = {40: 127}
    table = []
    for n in range(41, nmax + 1):
        # pure LP bound
        m = (ALEKSEYEV_UB.get(n, 0) or 3 * n) - 15
        while find_dual(n, m, 0) is None:
            m += 1
        pure = m - 1
        assert find_dual(n, pure, 0) is None
        # combined: averaging + LP with (I6) from U(n-1)
        avg = (n * U[n - 1]) // (n - 2)
        cand = min(pure, avg)
        # walk down while the LP with (I6) at cand is infeasible
        while True:
            dmin = max(0, cand - U[n - 1])
            if find_dual(n, cand, dmin) is None:
                break
            cand -= 1
        Un = cand
        mm = Un + 1
        dmin = max(0, mm - U[n - 1])
        if mm > avg:
            method, cert, dmin = "averaging", None, None
        else:
            cert = find_dual(n, mm, dmin)
            method = "LP+I6" if dmin > 0 else "LP"
            assert cert is not None
        # prefer a pure-LP certificate when it gives the same bound (no dependence on U(n-1))
        if pure == Un:
            cert, dmin, method = find_dual(n, mm, 0), 0, "LP"
        prim = find_primal(n, Un, max(0, Un - U[n - 1]))
        assert prim is not None, "LP must be feasible at the bound itself"
        certfile = None
        if cert is not None and out:
            certfile = f"data/cert_n{n}_m{mm}.txt"
            write_cert(os.path.join(HERE, certfile), n, mm, dmin, cert, U[n - 1])
        U[n] = Un
        row = dict(n=n, mckay_lb=MCKAY_LB.get(n), prev_ub=ALEKSEYEV_UB.get(n), pure_lp=pure,
                   averaging=avg, new_ub=Un, method=method, dmin=dmin, uses_U_prev=U[n - 1] if method != "LP" else None,
                   cert=certfile)
        table.append(row)
        print(row, flush=True)
    if out:
        with open(os.path.join(DATA, "bounds.json"), "w", newline="\n") as f:
            json.dump(table, f, indent=1)
    return table


def sanity():
    bad = 0
    for n in range(2, 41):
        a = EXACT[n]
        p0 = find_primal(n, a, 0)
        p1 = find_primal(n, a, max(0, a - EXACT[n - 1]))
        ok = p0 is not None and p1 is not None
        bad += not ok
        print(f"n={n:2d} a(n)={a:3d}: LP feasible (exact point) pure={p0 is not None} with I6={p1 is not None}")
    try:
        with open(os.path.join(DATA, "bounds.json")) as f:
            U = {r["n"]: r["new_ub"] for r in json.load(f)}
    except OSError:
        U = {}
    U[40] = 127
    for n, lb in MCKAY_LB.items():
        p0 = find_primal(n, lb, 0)
        p1 = find_primal(n, lb, max(0, lb - U[n - 1])) if n - 1 in U else None
        bad += p0 is None or (n - 1 in U and p1 is None)
        print(f"n={n:2d} McKay lb={lb}: pure={p0 is not None} with I6 from U({n-1})={U.get(n-1)}: {p1 is not None}")
    print("ALL FEASIBLE" if not bad else f"{bad} FAILURES")
    return bad == 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", action="store_true")
    ap.add_argument("--sanity", action="store_true")
    ap.add_argument("--nmax", type=int, default=57)
    args = ap.parse_args()
    if args.run:
        run(args.nmax)
    if args.sanity:
        sys.exit(0 if sanity() else 1)
