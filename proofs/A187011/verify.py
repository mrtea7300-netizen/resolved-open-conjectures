"""Independent verification of the proof of Zhi-Wei Sun's conjecture for OEIS A187011."""
import math
import sympy as sp

OEIS_A187011 = [
    1, 0, -1, 12, -80, 1152, -5632, 61440, -278528, 2752512, -42467328,
    182452224, -2642411520, 23555211264, -99052683264, 869730877440,
    -11828339933184, 158638912045056, -656820758642688, 8683393080360960,
    -73742045851680768, 303517985824309248, -3950008716924813312,
]


def verify_symbolic_det(N_sym: int = 7):
    """Verify Proposition 1 symbolically for general ordered variables x_1 < ... < x_n."""
    for n in range(2, N_sym + 1):
        d = sp.symbols(f"d1:{n}")
        # x_1 = 0, x_{k+1} = d_1 + ... + d_k so |x_i - x_j| = sum_{k=min(i,j)}^{max(i,j)-1} d_k
        x = [sp.Integer(0)]
        for dk in d:
            x.append(x[-1] + dk)
        M = sp.Matrix(n, n, lambda i, j: x[j] - x[i] if j >= i else x[i] - x[j])
        lhs = sp.expand(M.det())
        prod_d = sp.Integer(1)
        for dk in d:
            prod_d *= dk
        rhs = sp.expand(((-1) ** (n - 1)) * (2 ** (n - 2)) * (x[-1] - x[0]) * prod_d)
        assert lhs == rhs, f"Symbolic Proposition 1 failed at n={n}"
    print(f"[PASS] Proposition 1 verified symbolically for general x_1 <= ... <= x_n (n = 2..{N_sym}).")


def verify_oeis_and_primes(N_det: int = 40):
    primes = list(sp.primerange(2, 1000))
    computed = [1]  # a(0) = 1
    for n in range(1, N_det + 1):
        M = sp.Matrix(n, n, lambda i, j: abs(primes[i] - primes[j]))
        dv = int(M.det())
        if n == 1:
            fv = 0
        else:
            fv = ((-1) ** (n - 1)) * (2 ** (n - 2)) * (primes[n - 1] - primes[0])
            for k in range(n - 1):
                fv *= primes[k + 1] - primes[k]
            assert ((-1) ** (n - 1)) * dv > 0
        assert dv == fv, f"Mismatch at n={n}: {dv} != {fv}"
        computed.append(dv)

    assert computed[: len(OEIS_A187011)] == OEIS_A187011, "OEIS A187011 data mismatch!"
    print(f"[PASS] All {len(OEIS_A187011)} published OEIS A187011 terms (n = 0..22) reproduced exactly.")
    print(f"[PASS] Exact determinant matches Proposition 1 for primes n = 1..{N_det}.")


def verify_selberg_and_growth():
    """Verify Selberg sieve weights |lambda_d| <= 1, G(z) lower bound, p_n < 2*n*log(n), and growth."""
    # Check Selberg sieve inner algebra explicitly for h = 2, 4, 6 and z = 60
    for h in (2, 4, 6):
        z = 60
        primes_P = [p for p in sp.primerange(3, z + 1) if h % p != 0]
        # Generate all squarefree d | P with d <= z
        divs = [1]
        for p in primes_P:
            divs += [d * p for d in divs if d * p <= z]
        divs.sort()

        def f(d):
            val = sp.Rational(1)
            for p in sp.primefactors(d):
                val *= sp.Rational(p, 2)
            return val

        def g(d):
            val = sp.Rational(1)
            for p in sp.primefactors(d):
                val *= sp.Rational(p - 2, 2)
            return val

        G_z = sum(1 / g(r) for r in divs)
        for d in divs:
            # lambda_d = f(d) * sum_{d|r, r in divs} mu(r/d) * mu(r) / (G_z * g(r))
            lam_d = f(d) * sum(
                sp.mobius(r // d) * sp.mobius(r) / (G_z * g(r)) for r in divs if r % d == 0
            )
            if d == 1:
                assert lam_d == 1
            assert abs(lam_d) <= 1, f"|lambda_{d}| > 1 for h={h}"

        # Check G(z) >= (sum_{a <= sqrt(z), gcd(a,h)=1} mu^2(a)/a)^2
        y = int(math.isqrt(z))
        lhs_sq = sum(sp.Rational(1, a) for a in range(1, y + 1) if math.gcd(a, h) == 1 and sp.mobius(a) != 0) ** 2
        assert G_z >= lhs_sq, f"G(z) lower bound failed for h={h}"
    print("[PASS] Selberg sieve weights (lambda_1 = 1, |lambda_d| <= 1) and G(z) lower bound verified exactly for h=2,4,6, z=60.")

    # Check p_n < 2*n*log(n) and empirical |a(n)|^(1/n) up to p_n <= 10^6
    primes = list(sp.primerange(2, 1_000_000))
    for idx in range(2, len(primes)):
        n = idx + 1
        assert primes[idx] < 2 * n * math.log(n), f"p_n < 2*n*log(n) failed at n={n}"
    print(f"[PASS] p_n < 2*n*log(n) verified for all 3 <= n <= {len(primes)} (p_n <= 10^6).")

    # Empirical profile of |a(n)|^(1/n)
    log_prod = 0.0
    milestones = {10, 100, 1000, 10000, len(primes)}
    print("Empirical profile of |a(n)|^(1/n):")
    for k in range(len(primes) - 1):
        log_prod += math.log(primes[k + 1] - primes[k])
        n = k + 2
        if n in milestones:
            log_abs_a = (n - 2) * math.log(2) + math.log(primes[n - 1] - 2) + log_prod
            root_val = math.exp(log_abs_a / n)
            print(f"  n = {n:6d} (p_n = {primes[n-1]:7d}): |a(n)|^(1/n) = {root_val:.6f}")


if __name__ == "__main__":
    verify_symbolic_det(N_sym=7)
    verify_oeis_and_primes(N_det=40)
    verify_selberg_and_growth()
    print("ALL CHECKS PASSED.")
