#!/usr/bin/env python3
"""Standalone exact checker for the Farkas certificates in data/cert_*.txt.

Self-contained: does not import lp_c4.py.  Integer arithmetic only.  For a certificate with
multipliers a, b, z, and (c_d, w_d) for every degree d in D = {dmin, ..., n-1}, it checks the
conditions of proof.md, Section 3:

  (C0) z >= 0 and w_d >= 0 for all d in D;
  (C1) for every d in D:   a + b d - c_d d + z (d(d-1) + d mod 2) - w_d (n-1+d-(d mod 2)) >= 0;
  (C2) for every i < j in D:   c_i + c_j + j w_i + i w_j >= 0;
  (C3) for every d in D:   2 c_d + 2 d w_d >= 0;
  (C4) a n + 2 m b + z n(n-1) < 0.

If all hold, no nonnegative (n_d, e_ij) satisfies the LP, so no C4-free graph with n vertices
and exactly m edges exists (under the stated hypothesis ex(n-1, C4) <= m - dmin when dmin > 0),
hence ex(n, C4) <= m - 1.  It also prints the chain of hypotheses used.

    python check_certificates.py [files...]     (default: data/cert_*.txt)
"""
import glob
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def parse(path):
    cert = {"c": {}, "w": {}}
    with open(path) as f:
        for line in f:
            t = line.split()
            if not t or t[0].startswith("#"):
                continue
            if t[0] == "d":
                d = int(t[1])
                assert t[2] == "c" and t[4] == "w"
                cert["c"][d] = int(t[3])
                cert["w"][d] = int(t[5])
            else:
                cert[t[0]] = int(t[1])
    return cert


def check(cert):
    n, m, dmin = cert["n"], cert["m"], cert["dmin"]
    a, b, z, c, w = cert["a"], cert["b"], cert["z"], cert["c"], cert["w"]
    D = list(range(dmin, n))
    assert sorted(c) == D and sorted(w) == D, "multipliers must be given for exactly d = dmin..n-1"
    if z < 0 or any(w[d] < 0 for d in D):
        return False, "C0 fails"
    for d in D:
        if a + b * d - c[d] * d + z * (d * (d - 1) + d % 2) - w[d] * (n - 1 + d - d % 2) < 0:
            return False, f"C1 fails at d={d}"
    for i in D:
        if 2 * c[i] + 2 * i * w[i] < 0:
            return False, f"C3 fails at d={i}"
        for j in D:
            if i < j and c[i] + c[j] + j * w[i] + i * w[j] < 0:
                return False, f"C2 fails at ({i},{j})"
    rhs = a * n + 2 * m * b + z * n * (n - 1)
    if rhs >= 0:
        return False, f"C4 fails: {rhs}"
    return True, f"rhs = {rhs}"


def main():
    files = sys.argv[1:] or sorted(glob.glob(os.path.join(HERE, "data", "cert_*.txt")),
                                   key=lambda p: int(os.path.basename(p).split("_")[1][1:]))
    allok = True
    for p in files:
        cert = parse(p)
        ok, msg = check(cert)
        allok &= ok
        n, m, dmin = cert["n"], cert["m"], cert["dmin"]
        hyp = f"assumes ex({n-1}, C4) <= {m - dmin}" if dmin > 0 else "no hypothesis"
        print(f"{os.path.basename(p)}: {'OK  ' if ok else 'FAIL'} ex({n}, C4) <= {m-1}  [{hyp}]  {msg}")
    print("ALL CERTIFICATES VALID" if allok else "SOME CERTIFICATE FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
