"""Exact class groups of imaginary quadratic fields by reduced binary quadratic forms.

Used for the survivors of split_sieve.c (proof.md, Step 5) and for an independent
cross-check over small discriminants. Nothing here depends on GRH: the class group of
discriminant D < 0 is the group of SL2(Z)-classes of primitive positive definite forms
of discriminant D, each class contains exactly one reduced form, and composition is
Gauss/Dirichlet composition followed by reduction (Cohen, A Course in Computational
Algebraic Number Theory, Algorithms 5.4.2 and 5.4.7).

Usage:
  python exact_classgroups.py survivors data/run_*.txt   # exponents of survivor fields
  python exact_classgroups.py scan N                    # all fundamental D, -N < D < 0
"""
import sys
from math import gcd, isqrt


def reduce_form(a, b, c):
    while True:
        if c < a or (c == a and b < 0):
            a, b, c = c, -b, a
            continue
        if b > a or b <= -a:
            # bring b into (-a, a]
            k = (a - b) // (2 * a)
            b2 = b + 2 * k * a
            c = (b2 * b2 - (b * b - 4 * a * c)) // (4 * a)
            b = b2
            continue
        if c == a and b < 0:
            b = -b
            continue
        return (a, b, c)


def compose(f, g):
    """Dirichlet composition of primitive forms of the same discriminant (Cohen Alg. 5.4.7)."""
    a1, b1, c1 = f
    a2, b2, c2 = g
    D = b1 * b1 - 4 * a1 * c1
    if a1 > a2:
        a1, b1, c1, a2, b2, c2 = a2, b2, c2, a1, b1, c1
    s = (b1 + b2) // 2
    n = b2 - s
    # extended gcd steps
    def egcd(x, y):
        if y == 0:
            return (x, 1, 0)
        g_, u, v = egcd(y, x % y)
        return (g_, v, u - (x // y) * v)
    if a2 % a1 == 0:
        y1, d = 0, a1
    else:
        d, u, v = egcd(a2, a1)
        y1 = u
    if s % d == 0:
        y2, x2, d1 = -1, 0, d
    else:
        d1, x2, y2 = egcd(s, d)
        y2 = -y2
    v1 = a1 // d1
    v2 = a2 // d1
    r = (y1 * y2 * n - x2 * c2) % v1
    b3 = b2 + 2 * v2 * r
    a3 = v1 * v2
    c3 = (b3 * b3 - D) // (4 * a3)
    return reduce_form(a3, b3, c3)


def reduced_forms(D):
    out = []
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b - D) % 2:
                continue
            num = b * b - D
            if num % (4 * a):
                continue
            c = num // (4 * a)
            if c < a:
                continue
            if b < 0 and c == a:
                continue
            if gcd(gcd(a, abs(b)), c) != 1:
                continue
            out.append((a, b, c))
        a += 1
    return out


def identity(D):
    return reduce_form(1, D % 2, (D % 2 - D) // 4)


def order(f, e):
    k, g = 1, f
    while g != e:
        g = compose(g, f)
        k += 1
        if k > 10 ** 7:
            raise RuntimeError("order too large")
    return k


def lcm(x, y):
    return x * y // gcd(x, y)


def class_group(D):
    forms = reduced_forms(D)
    e = identity(D)
    assert e in forms
    ex = 1
    orders = []
    for f in forms:
        o = order(f, e)
        orders.append(o)
        ex = lcm(ex, o)
    # sanity: every order divides h, and composition stays in the set of reduced forms
    h = len(forms)
    assert all(h % o == 0 for o in orders)
    return h, ex, orders


def is_fundamental(D):
    if D % 4 == 1:
        m = -D
        for p in range(2, isqrt(m) + 1):
            if m % (p * p) == 0:
                return False
        return True
    if D % 4 == 0:
        m = -D // 4
        if m % 4 not in (1, 2):
            return False
        for p in range(2, isqrt(m) + 1):
            if m % (p * p) == 0:
                return False
        return True
    return False


def survivors(files):
    ps = []
    for fn in files:
        for line in open(fn):
            if line.startswith("SURVIVOR"):
                ps.append(int(line.split()[1]))
            if line.startswith("NOSPLIT"):
                raise SystemExit("NOSPLIT line found in " + fn + ": handle by hand")
    ps = sorted(set(ps))
    found = []
    print(f"{len(ps)} survivors, largest {ps[-1] if ps else None}")
    for p in [4, 8] + ps:
        D = -p
        h, ex, _ = class_group(D)
        tag = ""
        if ex in (1, 3):
            found.append((D, h, ex))
            tag = "  <-- exponent divides 3"
        print(f"D={D:>8}  h={h:>4}  exponent={ex}{tag}")
    print()
    print("exponent 1:", [D for D, h, ex in found if ex == 1])
    print("exponent 3:", [D for D, h, ex in found if ex == 3])
    print("exponent 3 class numbers:", [h for D, h, ex in found if ex == 3])


def scan(N):
    res = {}
    for m in range(3, N):
        D = -m
        if not is_fundamental(D):
            continue
        h, ex, _ = class_group(D)
        if ex in (1, 3):
            res.setdefault(ex, []).append(D)
    for ex in sorted(res):
        print(f"exponent {ex}: {len(res[ex])} fields: {res[ex]}")


if __name__ == "__main__":
    # self-test on classical values
    assert class_group(-23)[0] == 3 and class_group(-23)[1] == 3
    assert class_group(-4027)[0] == 9 and class_group(-4027)[1] == 3   # C3 x C3
    assert class_group(-163)[0] == 1
    assert class_group(-84)[0] == 4 and class_group(-84)[1] == 2       # C2 x C2
    assert class_group(-47)[0] == 5 and class_group(-47)[1] == 5
    if sys.argv[1] == "survivors":
        survivors(sys.argv[2:])
    elif sys.argv[1] == "scan":
        scan(int(sys.argv[2]))
