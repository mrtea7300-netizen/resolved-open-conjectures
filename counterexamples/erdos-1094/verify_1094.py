"""Standalone brute-force verifier & reproducer for Erdős Problem #1094
(Erdős-Lacampagne-Selfridge 1988, 1993; Selfridge 1977).

Checks directly from Kummer's theorem AND exact math.comb factorization for small n
to confirm all conventions and reproduce all 14 published exceptions.
"""
import argparse
import math
import time


def sieve_primes(limit):
    is_p = bytearray(b"\x01") * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if is_p[i]:
            is_p[i * i : limit + 1 : i] = b"\x00" * len(range(i * i, limit + 1, i))
    return [i for i in range(2, limit + 1) if is_p[i]]


def p_divides_binom(n, k, p):
    """By Kummer's theorem: p | C(n, k) iff there is a carry in base p when adding k + (n-k)."""
    m = n - k
    carry = 0
    kk = k
    while kk > 0 or m > 0:
        s = (kk % p) + (m % p) + carry
        if s >= p:
            return True
        carry = 0
        kk //= p
        m //= p
    return False


def lpf_binom(n, k, primes):
    """Exact least prime factor of C(n, k) for 1 <= k <= n//2."""
    for p in primes:
        if p > n:
            break
        if p_divides_binom(n, k, p):
            return p
    return n + 1  # shouldn't happen since C(n,k) has a prime factor <= n


def exact_lpf_comb(n, k):
    """Completely independent check using exact math.comb(n, k)."""
    val = math.comb(n, k)
    d = 2
    while d * d <= val and d <= n:
        if val % d == 0:
            return d
        d += 1 if d == 2 else 2
    return val


PUBLISHED_14 = {
    (7, 3), (13, 4), (23, 5), (14, 4), (44, 8), (46, 10), (47, 10),
    (47, 11), (62, 6), (74, 10), (94, 10), (95, 10), (241, 16), (284, 28),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=2000)
    args = ap.parse_args()

    t0 = time.time()
    primes = sieve_primes(args.max_n)

    exc_max_nk_k = []
    exc_max_nk_13 = []
    exc_selfridge_k2m1 = []
    exc_selfridge_17125 = []

    for n in range(4, args.max_n + 1):
        for k in range(2, n // 2 + 1):
            # Fast test: check if any prime <= max(n/k, k) divides C(n, k)
            lim_k = max(n // k, k)
            # Check max(n/k, 13) too (note: if n/k is non-integer, p <= n/k iff p <= floor(n/k)!)
            lim_13 = max(n // k, 13)
            need = max(lim_k, lim_13)

            # Quick check against smallest bound min(lim_k, lim_13)
            lpf = None
            for p in primes:
                if p > need:
                    break
                if p_divides_binom(n, k, p):
                    lpf = p
                    break
            if lpf is None:
                lpf = lpf_binom(n, k, primes)

            if lpf > lim_k:
                exc_max_nk_k.append((n, k, lpf))
            if lpf > lim_13:
                exc_max_nk_13.append((n, k, lpf))
            if n >= k * k - 1 and lpf > n // k:
                exc_selfridge_k2m1.append((n, k, lpf))
            if 8 * n > 137 * k and lpf > n // k:
                exc_selfridge_17125.append((n, k, lpf))

    dt = time.time() - t0
    print(f"Brute-force verified all 2 <= k <= n/2 for n <= {args.max_n} in {dt:.2f}s:")
    print(f"\n1. Exceptions to lpf(C(n,k)) <= max(n/k, k) [{len(exc_max_nk_k)} found]:")
    for n, k, p in exc_max_nk_k:
        if n <= 300:
            assert exact_lpf_comb(n, k) == p
        print(f"   C({n}, {k}): lpf = {p} > max({n/k:.3f}, {k})")
    found_set = {(n, k) for n, k, _ in exc_max_nk_k}
    assert found_set == PUBLISHED_14, f"Mismatch! diff={found_set ^ PUBLISHED_14}"
    print("   EXACT MATCH with all 14 published [ELS88] exceptions!")

    print(f"\n2. Exceptions to lpf(C(n,k)) <= max(n/k, 13) [{len(exc_max_nk_13)} found]:")
    for n, k, p in exc_max_nk_13:
        print(f"   C({n}, {k}): lpf = {p} > max({n/k:.3f}, 13)")

    print(f"\n3. Exceptions to Selfridge (1977): n >= k^2 - 1 => lpf <= n/k [{len(exc_selfridge_k2m1)} found]:")
    for n, k, p in exc_selfridge_k2m1:
        print(f"   C({n}, {k}): lpf = {p} > {n/k:.3f} (k^2-1 = {k*k-1})")

    print(f"\n4. Exceptions to Guy B31/B33: n > 17.125*k => lpf <= n/k [{len(exc_selfridge_17125)} found]:")
    for n, k, p in exc_selfridge_17125:
        print(f"   C({n}, {k}): lpf = {p} > {n/k:.3f} (n/k = {n/k:.4f})")


if __name__ == "__main__":
    main()
