#!/usr/bin/env python3
"""Independent verification for OEIS A093669, A093670, and A025052."""
import math
from sympy import factorint, kronecker_symbol

EULER_65 = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
    30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102,
    105, 112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273,
    280, 312, 330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848,
]

EXPECTED_A093669 = [
    11, 14, 17, 19, 20, 27, 32, 34, 36, 43, 46, 49, 52, 64, 67, 73, 82,
    97, 100, 142, 148, 163, 193,
]
EXPECTED_A093670 = [
    3, 5, 7, 8, 9, 12, 13, 14, 16, 25, 28, 34, 37, 46, 82, 142,
]
EXPECTED_A025052 = [
    1, 2, 4, 6, 10, 18, 22, 30, 42, 58, 70, 78, 102, 130, 190, 210, 330, 462,
]


def is_fund_disc(D: int) -> bool:
    m = -D
    if m % 4 == 3:
        return all(e == 1 for e in factorint(m).values())
    if m % 4 == 0:
        n = m // 4
        if n % 4 in (1, 2):
            return all(e == 1 for e in factorint(n).values())
    return False


def reduced_forms(D: int):
    """Return (h_prim, g_prim, H_all, H_amb) for discriminant D < 0."""
    hp = gp = ha = ga = 0
    lim = int(math.isqrt((-D) // 3)) + 1
    for a in range(1, lim + 1):
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a) != 0:
                continue
            c = (b * b - D) // (4 * a)
            if c < a or (a == c and b < 0):
                continue
            is_amb = (b == 0) or (b == a) or (a == c)
            ha += 1
            if is_amb:
                ga += 1
            if math.gcd(a, math.gcd(abs(b), c)) == 1:
                hp += 1
                if is_amb:
                    gp += 1
    return hp, gp, ha, ga


def r_strict_and_eq(N: int):
    s_cnt = e_cnt = 0
    for a in range(1, N + 1):
        if 3 * a * a > N:
            break
        for b in range(a, N + 1):
            p, s = a * b, a + b
            if p + s * b > N:
                break
            if (N - p) % s == 0:
                c = (N - p) // s
                if c >= b:
                    if a < b < c:
                        s_cnt += 1
                    else:
                        e_cnt += 1
    return s_cnt, e_cnt


def main():
    # 1. Verify exact bijection r_strict(N) == (H(-4N) - H_amb(-4N))/2 for 1 <= N <= 2000
    for N in range(1, 2001):
        s_cnt, _ = r_strict_and_eq(N)
        _, _, ha, ga = reduced_forms(-4 * N)
        assert (ha - ga) % 2 == 0 and s_cnt == (ha - ga) // 2, f"Bijection failed at N={N}"
    print("[PASS] Exact bijection r_strict(N) == (H(-4N) - H_amb(-4N))/2 verified for 1 <= N <= 2000.")

    # 2. Verify all 97 fundamental discriminants with h(D0) <= 4 (checked up to |D0| <= 5000)
    fund_le4 = []
    for m in range(3, 5001):
        D0 = -m
        if not is_fund_disc(D0):
            continue
        h0, g0, _, _ = reduced_forms(D0)
        if h0 <= 4:
            fund_le4.append((D0, h0, g0))
    by_h = {k: [D for D, h, _ in fund_le4 if h == k] for k in (1, 2, 3, 4)}
    assert {k: len(v) for k, v in by_h.items()} == {1: 9, 2: 18, 3: 16, 4: 54}
    print("[PASS] 97 fundamental discriminants with h(D0) <= 4 verified (max |D0| = 1555).")

    # 3. Enumerate ALL orders -4N = f^2 D0 with h(-4N) in {3, 4} (phi(f) <= 12 => f <= 42)
    cand_N = set()
    for D0, h0, _ in fund_le4:
        u_base = 3 if D0 == -3 else (2 if D0 == -4 else 1)
        for f in range(1, 43):
            D = f * f * D0
            if D % 4 != 0:
                continue
            u = u_base if f > 1 else 1
            num, den = h0 * f, u
            for p in factorint(f):
                num *= (p - kronecker_symbol(D0, p))
                den *= p
            assert num % den == 0
            hD = num // den
            if hD in (3, 4):
                cand_N.add(-D // 4)
    cand_list = sorted(cand_N)
    print(f"[PASS] Exactly {len(cand_list)} orders with h(-4N) in {{3, 4}} (max N = {max(cand_list)}):")
    print("       ", cand_list)

    # 4. Exact classification of A093669, A025052, A093670
    a093669 = [N for N in cand_list if r_strict_and_eq(N)[0] == 1]
    assert a093669 == EXPECTED_A093669
    print(f"[PASS] A093669 complete ({len(a093669)} terms): {a093669}")

    for N in EULER_65:
        assert r_strict_and_eq(N)[0] == 0, f"Idoneal {N} has strict rep!"
    a025052 = [N for N in EULER_65 if sum(r_strict_and_eq(N)) == 0]
    assert a025052 == EXPECTED_A025052
    print(f"[PASS] A025052 complete ({len(a025052)} terms): {a025052}")

    a093670 = sorted(
        [N for N in a093669 if r_strict_and_eq(N) == (1, 0)]
        + [N for N in EULER_65 if r_strict_and_eq(N) == (0, 1)]
    )
    assert a093670 == EXPECTED_A093670
    print(f"[PASS] A093670 complete ({len(a093670)} terms): {a093670}")

    # 5. Direct brute-force cross-check up to N = 5000
    s_arr = [0] * 5001
    e_arr = [0] * 5001
    for a in range(1, 5001):
        if 3 * a * a > 5000:
            break
        for b in range(a, 5001):
            p, s = a * b, a + b
            if p + s * b > 5000:
                break
            for c in range(b, 5001):
                v = p + s * c
                if v > 5000:
                    break
                if a < b < c:
                    s_arr[v] += 1
                else:
                    e_arr[v] += 1
    assert [n for n in range(1, 5001) if s_arr[n] == 1] == EXPECTED_A093669
    assert [n for n in range(1, 5001) if s_arr[n] + e_arr[n] == 1] == EXPECTED_A093670
    assert [n for n in range(1, 5001) if s_arr[n] + e_arr[n] == 0] == EXPECTED_A025052
    assert [n for n in range(1, 5001) if s_arr[n] == 0] == EULER_65
    print("[PASS] Brute-force cross-check on 1 <= N <= 5000 matches all four sequences identically.")


if __name__ == "__main__":
    main()
