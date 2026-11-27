"""Standalone verification script for OEIS A256132.

Checks:
1. Reproduces all 101 published terms (n = 0..100) of OEIS A256132 directly from the definition.
2. Verifies the finite base cases 0 <= n <= 5459 directly from the definition.
3. Verifies the constructive Hadamard + Gauss-Legendre proof for all 5460 <= n <= 20000.
4. Verifies a(n) > 0 for all 0 <= n <= 1,000,000 (recording the hardest case).
"""
import math
import sys
import time

# All 101 published terms of OEIS A256132 (n = 0..100), from oeis/oeisdata seq/A256/A256132.seq
OEIS_A256132 = [
    1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 1, 3, 3, 3, 3, 2, 4, 3, 2, 3, 2, 4, 1,
    5, 4, 4, 4, 3, 6, 3, 4, 4, 2, 3, 3, 5, 6, 4, 6, 4, 5, 5, 6, 4, 3, 4, 6,
    5, 4, 6, 7, 6, 5, 6, 5, 4, 4, 7, 7, 6, 5, 7, 8, 8, 4, 5, 5, 6, 4, 6, 9,
    8, 6, 6, 9, 6, 9, 8, 8, 6, 6, 10, 6, 7, 9, 6, 8, 5, 9, 6, 5, 10, 8, 11,
    6, 7, 10, 7, 9, 8,
]


def count_a256132_direct(n: int) -> int:
    """Direct brute-force count from OEIS A256132 definition:
    w(3w+1)/2 + x(3x-1)/2 + y(3y-1)/2 + z(3z-1)/2 = n, w,x,y,z >= 0, x <= y <= z.
    """
    cnt = 0
    x = 0
    while True:
        px = x * (3 * x - 1) // 2
        if 3 * px > n:
            break
        y = x
        while True:
            pxy = px + y * (3 * y - 1) // 2
            if pxy + y * (3 * y - 1) // 2 > n:
                break
            z = y
            while True:
                pxyz = pxy + z * (3 * z - 1) // 2
                if pxyz > n:
                    break
                rem = n - pxyz
                # w(3w+1)/2 = rem <=> (6w+1)^2 = 24*rem + 1
                disc = 24 * rem + 1
                s = math.isqrt(disc)
                if s * s == disc and s % 6 == 1:
                    cnt += 1
                z += 1
            y += 1
        x += 1
    return cnt


def find_witness_direct(n: int):
    """Find a nonnegative (w, x, y, z) with x <= y <= z directly."""
    x = 0
    while True:
        px = x * (3 * x - 1) // 2
        if 3 * px > n:
            break
        y = x
        while True:
            pxy = px + y * (3 * y - 1) // 2
            if pxy + y * (3 * y - 1) // 2 > n:
                break
            z = y
            while True:
                pxyz = pxy + z * (3 * z - 1) // 2
                if pxyz > n:
                    break
                rem = n - pxyz
                disc = 24 * rem + 1
                s = math.isqrt(disc)
                if s * s == disc and s % 6 == 1:
                    w = (s - 1) // 6
                    return (w, x, y, z)
                z += 1
            y += 1
        x += 1
    return None


def three_squares(M: int):
    r = math.isqrt(M)
    for a in range(r + 1):
        rem1 = M - a * a
        for b in range(a, math.isqrt(rem1) + 1):
            rem2 = rem1 - b * b
            c = math.isqrt(rem2)
            if c >= b and c * c == rem2:
                return (a, b, c)
    return None


def verify_constructive(n_lo: int, n_hi: int):
    """Verify the constructive Hadamard + Gauss-Legendre proof for n_lo <= n <= n_hi."""
    for n in range(n_lo, n_hi + 1):
        # Strictly < (sqrt(24n+4) + 1)/3
        s = math.isqrt(24 * n + 4)
        # If s^2 == 24n+4, we need 3B-1 < s; if s^2 < 24n+4, we need 3B-1 <= s.
        B_hi = (s if s * s == 24 * n + 4 else s + 1) // 3
        while (3 * B_hi - 1) ** 2 >= 24 * n + 4:
            B_hi -= 1
        # Target residue mod 8
        if n % 4 == 1:
            r8 = 7
        elif n % 4 == 3:
            r8 = 3
        else:
            r8 = 3  # actually any B == 3 mod 4 works, using r8=3 mod 8 is even more uniform!
        # Largest B <= B_hi with B == r8 (mod 8)
        B1 = B_hi - ((B_hi - r8) % 8)
        B = B1 if (2 * n + 1 + 2 * B1) % 3 != 0 else B1 - 8
        assert B >= 105, f"B={B} < 105 at n={n}"
        assert B % 8 == r8 and (2 * n + 1 + 2 * B) % 3 != 0
        M = 24 * n + 4 - (3 * B - 1) ** 2
        assert M > 0 and M % 4 == 0 and M % 3 == 0 and M % 9 != 0
        assert 3 * M <= (3 * B - 3) ** 2, f"Cauchy-Schwarz bound fail at n={n}"
        m4 = M // 4
        assert m4 % 2 == 1 and m4 % 8 != 7
        sol = three_squares(m4)
        assert sol is not None
        vals = []
        for t in sol:
            assert t % 3 != 0
            x = 2 * t if (2 * t) % 3 == 1 else -2 * t
            vals.append((x - 1) // 3)
        U, V, W = vals
        assert B % 2 == 1 and U % 2 == 1 and V % 2 == 1 and W % 2 == 1
        assert (B + U + V + W) % 4 == 0
        w = (B + U + V + W) // 4
        x = (B + U - V - W) // 4
        y = (B - U + V - W) // 4
        z = (B - U - V + W) // 4
        assert min(w, x, y, z) >= 0, f"Negative at n={n}: {(w,x,y,z)}"
        assert w * (3 * w + 1) // 2 + x * (3 * x - 1) // 2 + y * (3 * y - 1) // 2 + z * (3 * z - 1) // 2 == n


def verify_range_1e6(N: int = 1_000_000):
    t0 = time.time()
    P = []
    k = 0
    while True:
        v = k * (3 * k - 1) // 2
        if v > N:
            break
        P.append(v)
        k += 1
    Q = []
    k = 0
    while True:
        v = k * (3 * k + 1) // 2
        if v > N:
            break
        Q.append(v)
        k += 1
    # Bitset of P + P
    hasPP = bytearray(N + 1)
    for i, v1 in enumerate(P):
        for j in range(i, len(P)):
            s = v1 + P[j]
            if s > N:
                break
            hasPP[s] = 1
    # Bitset of P + Q
    hasPQ = bytearray(N + 1)
    for v1 in P:
        for v2 in Q:
            s = v1 + v2
            if s > N:
                break
            hasPQ[s] = 1
    listPQ = [s for s in range(N + 1) if hasPQ[s]]
    hardest = (0, 0)
    for n in range(N + 1):
        found = -1
        for s in listPQ:
            if s > n:
                break
            if hasPP[n - s]:
                found = s
                break
        assert found >= 0, f"A256132 FAILED at n={n}!"
        if found > hardest[0]:
            hardest = (found, n)
    dt = time.time() - t0
    print(f"   PASS: 0..{N} all represented in {dt:.2f}s | hardest min(P+Q) = {hardest[0]} at n = {hardest[1]}")


def main():
    print("1. Reproducing OEIS A256132 published data (n = 0..100)...")
    got = [count_a256132_direct(n) for n in range(len(OEIS_A256132))]
    assert got == OEIS_A256132, f"OEIS mismatch! got={got}"
    print(f"   PASS: all {len(OEIS_A256132)} terms match OEIS A256132 exactly.")

    if "--check" in sys.argv:
        return

    print("2. Checking finite base cases 0 <= n <= 5459 directly from definition...")
    t0 = time.time()
    for n in range(0, 5460):
        w = find_witness_direct(n)
        assert w is not None, f"Direct witness failed at n={n}"
        assert w[0]*(3*w[0]+1)//2 + w[1]*(3*w[1]-1)//2 + w[2]*(3*w[2]-1)//2 + w[3]*(3*w[3]-1)//2 == n
    print(f"   PASS: 0 <= n <= 5459 verified directly in {time.time()-t0:.2f}s.")

    print("3. Verifying constructive Hadamard + Gauss-Legendre proof on 5460 <= n <= 20000...")
    t0 = time.time()
    verify_constructive(5460, 20000)
    print(f"   PASS: constructive proof verified on 5460..20000 in {time.time()-t0:.2f}s.")

    print("4. Verifying a(n) > 0 for all 0 <= n <= 1,000,000...")
    verify_range_1e6(1_000_000)


if __name__ == "__main__":
    main()
