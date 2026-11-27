"""Independent verification of the proof of Zhi-Wei Sun's conjecture for OEIS A180364."""
import math
import sympy as sp

OEIS_A180364 = [
    1, 19, 205, 1839, 14961, 114483, 839917, 5975455, 41524897, 283272723,
    1903686093, 12636115407, 83007985425, 540484102707, 3492471392493,
    22418010385983, 143062290575937, 908253002030355, 5739641232682957,
    36121371405797743, 226475167518421681,
]


def a_def(n: int) -> int:
    return sum(math.comb(n, k) * math.comb(n + k, k) * (2 * k + 1) ** 2 for k in range(n + 1))


def verify_oeis_and_recurrence(N_check: int = 200):
    terms = [a_def(n) for n in range(len(OEIS_A180364))]
    assert terms == OEIS_A180364, "Mismatch with OEIS A180364 data!"
    print(f"[PASS] All {len(OEIS_A180364)} published OEIS A180364 terms (n = 0..20) reproduced exactly.")

    # Extend via direct definition up to N_check and check recurrence
    a = [a_def(n) for n in range(N_check + 2)]
    for n in range(N_check):
        lhs = (
            -(n + 1) * (2 * n**2 + 10 * n + 11) * a[n]
            + (2 * n + 3) * (6 * n**2 + 18 * n - 7) * a[n + 1]
            - (n + 2) * (2 * n**2 + 2 * n - 1) * a[n + 2]
        )
        assert lhs == 0, f"Recurrence failed at n={n}"
    print(f"[PASS] Three-term recurrence verified directly against definition for n = 0..{N_check - 1}.")
    return a


def verify_wz_certificate():
    """Independently expand and verify the WZ polynomial identity (2) and all boundary cases."""
    n, k = sp.symbols("n k")
    c0 = -(n + 1) * (2 * n**2 + 10 * n + 11)
    c1 = (2 * n + 3) * (6 * n**2 + 18 * n - 7)
    c2 = -(n + 2) * (2 * n**2 + 2 * n - 1)
    Q = 2 * (2 * n + 3) * ((8 * n**2 + 24 * n - 4) * k**2 - (8 * n**2 + 24 * n + 8) * k + (2 * n**2 + 6 * n + 7))

    P_lhs = sp.expand(
        (2 * k + 1) ** 2
        * (
            c0 * (n + 1 - k) * (n + 2 - k)
            + c1 * (n + k + 1) * (n + 2 - k)
            + c2 * (n + k + 1) * (n + k + 2)
        )
    )
    P_rhs = sp.expand((n + k + 1) * (n + 2 - k) * Q.subs(k, k + 1) - k**2 * Q)
    assert P_lhs == P_rhs, "WZ polynomial identity (2) failed!"

    # Also verify rational function form R(n, k)
    R = k**2 * Q / ((n + 1 - k) * (n + 2 - k) * (2 * k + 1) ** 2)
    r_n1 = (n + k + 1) / (n + 1 - k)
    r_n2 = (n + k + 1) * (n + k + 2) / ((n + 1 - k) * (n + 2 - k))
    r_k1 = (n - k) * (n + k + 1) * (2 * k + 3) ** 2 / ((k + 1) ** 2 * (2 * k + 1) ** 2)
    assert sp.simplify(c0 + c1 * r_n1 + c2 * r_n2 - (R.subs(k, k + 1) * r_k1 - R)) == 0

    # Explicitly check boundary identities at k = 0, n+1, n+2 as polynomials in n
    assert sp.expand(c0 + c1 + c2 - Q.subs(k, 1)) == 0, "k=0 boundary failed"
    assert sp.expand(
        (2 * n + 3) ** 2 * ((2 * n + 2) * c1 + (2 * n + 2) * (2 * n + 3) * c2)
        - ((2 * n + 2) * Q.subs(k, n + 2) - (n + 1) ** 2 * Q.subs(k, n + 1))
    ) == 0, "k=n+1 boundary failed"
    assert sp.expand(
        (2 * n + 5) ** 2 * (2 * n + 3) * (2 * n + 4) * c2 + (n + 2) ** 2 * Q.subs(k, n + 2)
    ) == 0, "k=n+2 boundary failed"

    # Numerically check telescoping sum (1) term-by-term for n = 0..15
    for nv in range(16):
        c0v = -(nv + 1) * (2 * nv**2 + 10 * nv + 11)
        c1v = (2 * nv + 3) * (6 * nv**2 + 18 * nv - 7)
        c2v = -(nv + 2) * (2 * nv**2 + 2 * nv - 1)

        def F(m, kv):
            if 0 <= kv <= m:
                return math.comb(m, kv) * math.comb(m + kv, kv) * (2 * kv + 1) ** 2
            return 0

        def G(kv):
            if 1 <= kv <= nv + 2:
                Qv = 2 * (2 * nv + 3) * (
                    (8 * nv**2 + 24 * nv - 4) * kv**2
                    - (8 * nv**2 + 24 * nv + 8) * kv
                    + (2 * nv**2 + 6 * nv + 7)
                )
                return math.factorial(nv + kv) * Qv // (math.factorial(kv - 1) ** 2 * math.factorial(nv + 2 - kv))
            return 0

        for kv in range(nv + 3):
            assert c0v * F(nv, kv) + c1v * F(nv + 1, kv) + c2v * F(nv + 2, kv) == G(kv + 1) - G(kv)
    print("[PASS] WZ polynomial identity (2), rational certificate R(n,k), and all boundary cases verified.")


def verify_barriers_and_monotonicity(a):
    """Verify exact polynomial barrier identities and all exact integer inequalities."""
    n, m = sp.symbols("n m")
    alpha = 3 + 2 * sp.sqrt(2)
    A_n = (2 * n + 3) * (6 * n**2 + 18 * n - 7) / ((n + 2) * (2 * n**2 + 2 * n - 1))
    B_n = (n + 1) * (2 * n**2 + 10 * n + 11) / ((n + 2) * (2 * n**2 + 2 * n - 1))
    f = lambda t: alpha * (1 + sp.Rational(3, 2) / t)

    # Lower barrier identity
    lo_expected = (
        (30 + 32 * sp.sqrt(2)) * m**2 + (98 + 144 * sp.sqrt(2)) * m + (112 * sp.sqrt(2) - 11)
    ).subs(m, n - 1)
    lo_diff = sp.simplify(
        (A_n * f(n + 1) - B_n - f(n + 1) * f(n + 2)) * 4 * (n + 1) * (n + 2) * (2 * n**2 + 2 * n - 1)
        - lo_expected
    )
    assert lo_diff == 0, f"Lower barrier numerator mismatch: {lo_diff}"

    # Upper barrier identity
    hi_expected = (
        (162 + 112 * sp.sqrt(2)) * m**3
        + (904 + 616 * sp.sqrt(2)) * m**2
        + (1497 + 992 * sp.sqrt(2)) * m
        + (623 + 380 * sp.sqrt(2))
    ).subs(m, n - 1)
    hi_diff = sp.simplify(
        (f(n) * f(n + 1) - A_n * f(n) + B_n) * 4 * n * (n + 1) * (n + 2) * (2 * n**2 + 2 * n - 1)
        - hi_expected
    )
    assert hi_diff == 0, f"Upper barrier numerator mismatch: {hi_diff}"

    # Verify inequality (8) algebraic identity
    diff_8 = sp.simplify(
        sp.Rational(33, 4) - 3 * (n + 1) * (11 * n + 14) / (2 * n * (2 * n + 7))
        - (81 * n - 84) / (4 * n * (2 * n + 7))
    )
    assert diff_8 == 0
    print("[PASS] Symbolic barrier identities P_lo(m+1), P_hi(m+1) and inequality (8) verified exactly.")

    # Base cases for ratio monotonicity
    assert 2 * 266**2 < 421**2 and 125**2 < 2 * 190**2 and 19**2 > 205
    print("[PASS] Exact integer base cases for ratio monotonicity (n = 0, 1) verified.")

    # Exact integer inequality for n >= 13 tail: 4^33 * a(14)^8 > 11^33 * alpha^112
    lhs_tail = (4**33) * (a[14] ** 8)
    rhs_expr = sp.expand((11**33) * alpha**112)
    P = int(rhs_expr.subs(sp.sqrt(2), 0))
    Q = int(sp.simplify((rhs_expr - P) / sp.sqrt(2)))
    assert P > 0 and Q > 0 and lhs_tail > P and (lhs_tail - P) ** 2 > 2 * Q**2
    print(f"[PASS] Exact integer tail inequality 4^33 * a(14)^8 > 11^33 * alpha^112 verified (P, Q > 0).")

    # Exact integer root-ratio monotonicity for n = 1..50 (proof needs 1..12)
    for nv in range(1, 51):
        lhs = (a[nv + 2] ** (nv * (nv + 1))) * (a[nv] ** ((nv + 1) * (nv + 2)))
        rhs = a[nv + 1] ** (2 * nv * (nv + 2))
        assert lhs > rhs, f"Root-ratio inequality failed at n={nv}"
    print("[PASS] Exact integer root-ratio monotonicity verified for n = 1..50 (proof requires 1..12).")

    # Exact integer ratio strict decrease for n = 0..200
    for nv in range(200):
        assert a[nv + 1] ** 2 > a[nv] * a[nv + 2], f"Strict log-concavity failed at n={nv}"
    print("[PASS] Exact integer ratio strict decrease a(n+1)^2 > a(n)*a(n+2) verified for n = 0..199.")


if __name__ == "__main__":
    a = verify_oeis_and_recurrence(N_check=200)
    verify_wz_certificate()
    verify_barriers_and_monotonicity(a)
    print("ALL CHECKS PASSED.")
