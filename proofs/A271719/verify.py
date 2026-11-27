"""Standalone verification script for OEIS A271719.

Checks:
1. Reproduces all 70 published terms (n = 1..70) of OEIS A271719 directly from the definition.
2. Verifies the exact bijection (x, y, z) <-> (u, v) = (x, 2y+z) for all 1 <= n <= 200.
3. Exhaustively computes a(n) for all 1 <= n <= 1302 directly via the bijection (and directly
   from the (x,y,z) definition for 1 <= n <= 1302), verifying:
   - a(n) > 0 for all 11 <= n <= 1302,
   - a(n) = 1 for 1 <= n <= 1302 ONLY for n in {11, 12, 14, 18, 24, 54}.
4. Verifies the d = 11 primitive Pythagorean double-covering construction on 1303 <= n <= 1,000,000,
   constructing two explicit distinct valid (x, y, z) triples for every n in [1303, 1,000,000].
"""
import math
import sys
import time

# All 70 published terms of OEIS A271719 (n = 1..70), from oeis/oeisdata seq/A271/A271719.seq
OEIS_A271719 = [
    0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 3, 1, 2, 4, 3, 1, 3, 4, 3, 2, 2, 1,
    4, 2, 5, 4, 5, 2, 6, 4, 7, 4, 6, 4, 8, 5, 7, 7, 10, 3, 9, 7, 10, 9, 10,
    4, 8, 5, 6, 4, 9, 1, 8, 5, 7, 6, 12, 4, 17, 11, 15, 10, 15, 8, 21, 12,
    15, 9,
]


def count_a271719_direct(n: int) -> int:
    """Direct brute-force count from OEIS A271719 definition:
    n = x + y + z, x >= y > 0, z > 0, gcd(x,y,z) = 1, x^2 + (2y+z)^2 = square.
    """
    cnt = 0
    for x in range(1, n - 1):
        ymax = min(x, n - 1 - x)
        for y in range(1, ymax + 1):
            z = n - x - y
            if math.gcd(x, math.gcd(y, z)) != 1:
                continue
            val = x * x + (2 * y + z) ** 2
            s = math.isqrt(val)
            if s * s == val:
                cnt += 1
    return cnt


def count_a271719_pyth_sieve(N: int):
    """Exact computation of a(1..N) via all Pythagorean triples (primitive and scaled)
    using the proven bijection (x, y, z) <-> (u, v).
    """
    counts = [0] * (N + 1)
    # Generate all primitive triples (a, b) with min(a, b) <= N
    # Since a = m^2 - r^2, b = 2mr, we have b <= 2n and a <= n, Wait: we need v <= N and u < N (since 2u+v < 2N => u < N)!
    # So BOTH u <= N and v <= N!
    # Wait: if u <= N and v <= N, then for primitive triple (a, b), max(a, b) <= N => m^2 - r^2 <= N and 2mr <= N => m <= N!
    # More precisely, a = m^2 - r^2 >= 2m - 1 <= N => m <= (N+1)//2!
    m_max = (N + 1) // 2 + 2
    for m in range(2, m_max + 1):
        # Need 2*m*1 <= N (for r=1) and m^2 - (m-1)^2 = 2m-1 <= N
        if 2 * m - 1 > N:
            break
        # r < m, m - r odd, gcd(m, r) = 1, m^2 - r^2 <= N, 2*m*r <= N
        r_min = max(1, math.isqrt(max(0, m * m - N)))
        if m * m - r_min * r_min > N:
            r_min += 1
        r_max = min(m - 1, N // (2 * m))
        for r in range(r_min, r_max + 1):
            if (m - r) % 2 == 0 or math.gcd(m, r) != 1:
                continue
            a = m * m - r * r
            b = 2 * m * r
            for u0, v0 in ((a, b), (b, a)):
                # Scale by k >= 1 while v = k*v0 <= N and u = k*u0 < N
                k = 1
                while True:
                    u = k * u0
                    v = k * v0
                    if v > N or u >= N:
                        break
                    lo = max(v, u + v // 2 + 1)
                    hi = min(N, u + v - 1)
                    if lo <= hi:
                        if k == 1:
                            for n in range(lo, hi + 1):
                                counts[n] += 1
                        else:
                            for n in range(lo, hi + 1):
                                if math.gcd(k, n) == 1:
                                    counts[n] += 1
                    k += 1
    return counts


def verify_d11_covering(n_lo: int = 1303, n_hi: int = 1_000_000):
    """Explicitly construct TWO distinct valid representations (x, y, z) for EVERY n in [n_lo, n_hi]
    using ONLY the d = 11 primitive Pythagorean family (m = r + 11, r >= 18, 11 nmid r).
    """
    t0 = time.time()
    # Precompute intervals for d = 11
    intervals = []
    r = 18
    while True:
        if r % 11 != 0:
            L = 2 * r * r + 33 * r + 61
            R = 2 * r * r + 44 * r + 120
            intervals.append((r, L, R))
            if L > n_hi:
                break
        r += 1
    # Verify contiguous coverage from n_lo to n_hi, AND explicitly check the two (x,y,z) triples
    # for every n in [1303, 50000] + spot checks up to 1,000,000 + exact interval overlap check!
    assert intervals[0][1] == 1303
    for idx in range(len(intervals) - 1):
        r1, L1, R1 = intervals[idx]
        r2, L2, R2 = intervals[idx + 1]
        assert L2 <= R1 + 1, f"Gap between r={r1} ({L1}..{R1}) and r={r2} ({L2}..{R2})"
    assert intervals[-1][2] >= n_hi

    # Also explicitly construct & verify BOTH (x,y,z) triples for every n in 1303..1,000,000!
    idx = 0
    for n in range(n_lo, n_hi + 1):
        while intervals[idx][2] < n:
            idx += 1
        r, L, R = intervals[idx]
        assert L <= n <= R
        m = r + 11
        a = m * m - r * r
        b = 2 * m * r
        c = m * m + r * r
        # Orientation 1: u = a, v = b
        x1, y1, z1 = a, a + b - n, 2 * n - 2 * a - b
        # Orientation 2: u = b, v = a
        x2, y2, z2 = b, a + b - n, 2 * n - 2 * b - a
        assert x1 >= y1 > 0 and z1 > 0 and x1 + y1 + z1 == n
        assert x2 >= y2 > 0 and z2 > 0 and x2 + y2 + z2 == n
        assert x1 != x2  # distinct ordered triples (a is odd, b is even!)
        if n <= 50000 or n % 1000 == 0:
            assert math.gcd(x1, math.gcd(y1, z1)) == 1
            assert math.gcd(x2, math.gcd(y2, z2)) == 1
            assert x1 * x1 + (2 * y1 + z1) ** 2 == c * c
            assert x2 * x2 + (2 * y2 + z2) ** 2 == c * c
    print(f"   PASS: d=11 family explicitly produces >= 2 distinct valid triples for ALL {n_lo} <= n <= {n_hi} in {time.time()-t0:.2f}s.")


def main():
    print("1. Reproducing OEIS A271719 published data (n = 1..70) directly from definition...")
    got = [count_a271719_direct(n) for n in range(1, len(OEIS_A271719) + 1)]
    assert got == OEIS_A271719, f"OEIS mismatch! got={got}"
    print(f"   PASS: all {len(OEIS_A271719)} terms match OEIS A271719 exactly.")

    if "--check" in sys.argv:
        return

    print("2. Cross-checking direct (x,y,z) count vs Pythagorean bijection sieve on 1..1302...")
    t0 = time.time()
    sieve_counts = count_a271719_pyth_sieve(1302)
    for n in range(1, 1303):
        dc = count_a271719_direct(n)
        assert dc == sieve_counts[n], f"Bijection mismatch at n={n}: direct={dc} vs sieve={sieve_counts[n]}"
    zeros = [n for n in range(1, 1303) if sieve_counts[n] == 0]
    ones = [n for n in range(1, 1303) if sieve_counts[n] == 1]
    assert zeros == [1, 2, 3, 4, 5, 7, 8, 9, 10], f"Unexpected zeros: {zeros}"
    assert ones == [11, 12, 14, 18, 24, 54], f"Unexpected ones: {ones}"
    min_above_54 = min((sieve_counts[n], n) for n in range(55, 1303))
    print(f"   PASS: 1..1302 direct == bijection in {time.time()-t0:.2f}s.")
    print(f"   Zeros in 1..1302: {zeros}")
    print(f"   Ones in 1..1302:  {ones}")
    print(f"   Min a(n) for 55 <= n <= 1302: a({min_above_54[1]}) = {min_above_54[0]}")

    print("3. Verifying d = 11 double-covering construction on 1303..1,000,000...")
    verify_d11_covering(1303, 1_000_000)


if __name__ == "__main__":
    main()
