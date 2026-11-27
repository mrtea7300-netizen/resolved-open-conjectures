# Sun's Conjecture 2.7(i) of arXiv:1402.6641 (= OEIS A238165, part (ii))

**Conjecture (Z.-W. Sun, 2014-02-17).** For every integer n > 4 and every k = 1, ..., n,

    pi(kn)^(1/k) > pi((k+1)n)^(1/(k+1)).

Sources: Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641, Conj. 2.7(i)
(published in: Number Theory: Plowing and Starring through High Wave Forms, World Sci. 2015, 169-187);
OEIS A238165, comment "(ii) For any integer n > 4, the sequence pi(k*n)^(1/k) (k = 1, ..., n) is strictly
decreasing."

We prove a stronger statement: the restriction k <= n is not needed.

**Theorem.** For every integer n >= 5, the sequence pi(kn)^(1/k), k = 1, 2, 3, ..., is strictly
decreasing.

(For n = 1, 2, 4 the statement fails: n = 4, k = 1 gives pi(4)^2 = 4 = pi(8); n = 2, k = 1 gives
pi(2)^2 = 1 < pi(4) = 2; n = 1 fails for infinitely many k. For n = 3 it holds for all k; the check
log records it for k <= 666665. The argument below does not cover n = 3, because (n+1)/(2n) = 2/3 is
not below 1 - 1/e, and n = 3 is not part of the conjecture.)

## Proof

Fix n >= 5 and k >= 1. Write a = pi(kn) and b = pi((k+1)n) - pi(kn). The claimed inequality is
equivalent to (k+1) log a > k log(a+b), that is,

    log(1 + b/a) < (log a)/k.                                            (1)

**Case kn < 17.** There are 17 such pairs (n, k) with n >= 5. The script checks
pi(kn)^(k+1) > pi((k+1)n)^k for each of them in exact integer arithmetic (`check.py`, Part A; no failures).

**Case kn >= 17.** We use two facts.

(F1) Rosser–Schoenfeld [RS, Cor. 1, (3.5)]: pi(x) > x/log x for x >= 17. (The script also re-checks
this on [17, 2*10^6), although the proof does not need that.)

(F2) b <= (n+1)/2. All primes in (kn, kn+n] are odd, since kn >= 17, and an interval of n consecutive
integers contains at most ceil(n/2) <= (n+1)/2 odd numbers.

Put u = log(kn) >= log 17 > 2.8. By (F1), a > kn/u. Since t -> t log t is increasing for t >= 1 and
kn/u > 1, we get

    a log a > (kn/u)·log(kn/u) = kn·(1 - (log u)/u) >= kn·(1 - 1/e),

because max_{u>0} (log u)/u = 1/e. By (F2) and n >= 5,

    k·b <= k(n+1)/2 = kn·(1/2 + 1/(2n)) <= 0.6·kn < (1 - 1/e)·kn < a log a,

because 1 - 1/e = 0.63212... > 0.6. Therefore b/a < (log a)/k. Since log(1+y) <= y for y >= 0,

    log(1 + b/a) <= b/a < (log a)/k,

which is (1). (If b = 0, then (1) reads 0 < (log a)/k, which is true because a >= pi(17) = 7.) QED

In particular Sun's Conjecture 2.7(i), the range 1 <= k <= n, is true.

## Remarks

* The proof needs no Brun–Titchmarsh-type bound and no RH. Inequality (1) only asks for
  b < a(log a)/k, which is about kn/k = n, while b <= (n+1)/2 holds trivially. This is why the problem is
  much easier than Conj. 2.14(ii) (pi(n^2)^(1/n) decreasing).
* Literature: I found no published proof. Searches covered arXiv (API search on Sun/monotonicity/primes)
  and the OEIS entry A238165 (local mirror dated 2026-11-26), which still lists it as a conjecture.
  The argument is short enough that someone may have noticed it informally.

## Files

* `check.py`: Part A, the 17 exact checks that the proof needs. It also re-checks (F1) on [17, 2e6) and
  runs an independent sanity check (Part B) of pi(kn)^(k+1) > pi((k+1)n)^k for all n <= 200 and
  (k+1)n <= 2*10^6, about 1.18*10^7 pairs. Logs are used in floating point; any pair with margin
  < 1e-6 is decided in exact integers (one such pair occurred: n = 4, k = 1, which is the equality case).
* `check.log`: output. Part A has no failures. Part B fails only for n = 1, 2, 4, as described above.

Run: `nice -n 19 python3 check.py 2000000 200` (about 3 minutes, pure Python, no dependencies).

## Reference

[RS] J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers,
Illinois J. Math. 6 (1962), 64–94.
