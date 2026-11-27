"""Independent verification of OEIS A360278 Conjectures 1, 2, and 3."""
import sympy as sp

OEIS_A360278 = [
    4, 16, 44, 121, 319, 841, 2204, 5776, 15124, 39601, 103679, 271441,
    710644, 1860496, 4870844, 12752041, 33385279, 87403801, 228826124,
    599074576, 1568397604, 4106118241, 10749957119, 28143753121,
    73681302244, 192900153616, 505019158604, 1322157322201,
    3461452807999, 9062201101801, 23725150497404, 62113250390416,
    162614600673844, 425730551631121, 1114577054219519,
]


def check_general_n_symbolic():
    """Verify the general-n algebraic identities of Sections 3, 4, 5 symbolically."""
    al, X = sp.symbols("alpha X")
    # Case 1 (B = -1): beta = -1/alpha, A = alpha - 1/alpha, alpha^n = X, beta^n = (-1)^n / X
    be1 = -1 / al
    A1 = al + be1
    for parity in (0, 1):
        Y = ((-1) ** parity) / X
        S_a = al * (X**2 - 1) / A1
        S_b = be1 * (Y**2 - 1) / A1
        S_ab = -parity
        det_val = 1 + S_a + S_b + (S_a * S_b - S_ab**2)
        v_np1 = al * X + be1 * Y
        diff = sp.simplify(A1**2 * det_val - (v_np1**2 - (A1**2 + 4) * parity))
        assert diff == 0, f"Conj 1 general-n symbolic check failed (parity={parity}): {diff}"

    # Case 2 (B = +1): beta = 1/alpha, Delta = alpha - 1/alpha, beta^n = 1/X
    be2 = 1 / al
    Delta = al - be2
    n_sym = sp.Symbol("n")
    Y2 = 1 / X
    S_a = al * (X**2 - 1) / Delta
    S_b = -be2 * (Y2**2 - 1) / Delta
    S_ab = n_sym
    det_val = 1 + S_a + S_b + (S_a * S_b - S_ab**2)
    u_np1 = (al * X - be2 * Y2) / Delta
    diff2 = sp.simplify(det_val - (u_np1**2 - n_sym**2))
    assert diff2 == 0, f"Conj 2 general-n symbolic check failed: {diff2}"

    # Case 3 (Fibonacci: A = 1, B = -1, alpha = (1+sqrt(5))/2, beta = (1-sqrt(5))/2)
    al3 = (1 + sp.sqrt(5)) / 2
    be3 = (1 - sp.sqrt(5)) / 2
    c1, c2 = 1 / sp.sqrt(5), -1 / sp.sqrt(5)
    for parity in (0, 1):
        Y3 = ((-1) ** parity) / X
        S_a = al3 * (X**2 - 1)
        S_b = be3 * (Y3**2 - 1)
        S_ab = -parity
        det_val = 1 + c1 * S_a + c2 * S_b + c1 * c2 * (S_a * S_b - S_ab**2)
        F_np1 = (al3 * X - be3 * Y3) / sp.sqrt(5)
        diff3 = sp.simplify(det_val - (F_np1**2 + parity))
        assert diff3 == 0, f"Conj 3 general-n symbolic check failed (parity={parity}): {diff3}"
    print("[PASS] General-n symbolic identities for Conjectures 1, 2, 3 verified exactly.")


def check_polynomial_and_degenerate(N_poly=12, N_deg=10):
    """Verify Conjectures 1 and 2 as exact polynomials in Z[A] and at degenerate values."""
    A = sp.Symbol("A")
    # Conj 1 recurrence
    v1 = [sp.Integer(2), A]
    for _ in range(2 * N_poly + 2):
        v1.append(sp.expand(A * v1[-1] + v1[-2]))
    for n in range(1, N_poly + 1):
        M = sp.Matrix(n, n, lambda j, k: v1[j + k + 2] + (1 if j == k else 0))
        lhs = sp.expand(A**2 * M.det())
        rhs = sp.expand(v1[n + 1] ** 2 - (A**2 + 4) * (n % 2))
        assert lhs == rhs, f"Conj 1 Z[A] mismatch at n={n}"
    print(f"[PASS] Conjecture 1 exact Z[A] determinant identity verified for n = 1..{N_poly}.")

    # Conj 2 recurrence
    v2 = [sp.Integer(2), A]
    u2 = [sp.Integer(0), sp.Integer(1)]
    for _ in range(2 * N_poly + 2):
        v2.append(sp.expand(A * v2[-1] - v2[-2]))
        u2.append(sp.expand(A * u2[-1] - u2[-2]))
    for n in range(1, N_poly + 1):
        M = sp.Matrix(n, n, lambda j, k: v2[j + k + 2] + (1 if j == k else 0))
        lhs = sp.expand(M.det())
        rhs = sp.expand(u2[n + 1] ** 2 - n**2)
        assert lhs == rhs, f"Conj 2 Z[A] mismatch at n={n}"
    print(f"[PASS] Conjecture 2 exact Z[A] determinant identity verified for n = 1..{N_poly}.")

    # Degenerate parameter checks
    for Aval in [sp.Integer(0), 2 * sp.I, -2 * sp.I]:
        vs = [sp.Integer(2), Aval]
        for _ in range(2 * N_deg + 2):
            vs.append(sp.expand(Aval * vs[-1] + vs[-2]))
        for n in range(1, N_deg + 1):
            M = sp.Matrix(n, n, lambda j, k: vs[j + k + 2] + (1 if j == k else 0))
            assert sp.simplify(Aval**2 * M.det() - (vs[n + 1] ** 2 - (Aval**2 + 4) * (n % 2))) == 0
    for Aval in [sp.Integer(2), sp.Integer(-2)]:
        vs = [sp.Integer(2), Aval]
        us = [sp.Integer(0), sp.Integer(1)]
        for _ in range(2 * N_deg + 2):
            vs.append(Aval * vs[-1] - vs[-2])
            us.append(Aval * us[-1] - us[-2])
        for n in range(1, N_deg + 1):
            M = sp.Matrix(n, n, lambda j, k: vs[j + k + 2] + (1 if j == k else 0))
            assert M.det() == us[n + 1] ** 2 - n**2
    print(f"[PASS] Degenerate parameter values A in {{0, +-2, +-2i}} verified for n = 1..{N_deg}.")


def check_oeis_and_extended(N_ext=40):
    """Reproduce all 35 OEIS terms of A360278 and check Conj 1 (A=1) & Conj 3 up to N_ext."""
    L = [2, 1]
    F = [0, 1]
    for _ in range(2 * N_ext + 4):
        L.append(L[-1] + L[-2])
        F.append(F[-1] + F[-2])

    computed_L = []
    for n in range(1, N_ext + 1):
        ML = sp.Matrix(n, n, lambda j, k: L[j + k + 2] + (1 if j == k else 0))
        dL = int(ML.det())
        assert dL == L[n + 1] ** 2 - 5 * (n % 2), f"A360278 mismatch at n={n}"
        computed_L.append(dL)

        MF = sp.Matrix(n, n, lambda j, k: F[j + k + 2] + (1 if j == k else 0))
        dF = int(MF.det())
        assert dF == F[n + 1] ** 2 + (n % 2), f"Conj 3 mismatch at n={n}"

    assert computed_L[: len(OEIS_A360278)] == OEIS_A360278, "OEIS A360278 data mismatch!"
    print(f"[PASS] All {len(OEIS_A360278)} published OEIS A360278 terms reproduced exactly from det.")
    print(f"[PASS] Exact integer determinants for A360278 (Conj 1, A=1) and Conj 3 verified for n = 1..{N_ext}.")


if __name__ == "__main__":
    check_general_n_symbolic()
    check_polynomial_and_degenerate(N_poly=12, N_deg=10)
    check_oeis_and_extended(N_ext=40)
    print("ALL CHECKS PASSED.")
