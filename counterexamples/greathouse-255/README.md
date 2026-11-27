# Greathouse's 255 conjecture (A156695) — odd numbers not of the form p + 2^a + 2^b

- **OEIS:** https://oeis.org/A156695 (related: Erdős problems #9 and #10, Guy A19)
- **Status:** counterexample (confirmed) — n = 275984581255575 (the smallest; every odd n below 285873023221760 was checked, 2026-11-27; found 2026-11-26) and n = 949806618679575 are not of the form p + 2^a + 2^b and are not divisible by 17

## Statement (verbatim from OEIS)

A156695, name (mirror `oeis/oeisdata`, revision #75, Jul 10 2026):

> Odd numbers that are not of the form p + 2^a + 2^b, a, b > 0, p prime.

Comment by the author of the entry (Charles R Greathouse IV, 2009):

> All members above 5 found so far (up to 2.5 * 10^11) are divisible by 255 = 3 * 5 * 17, and many are divisible by 257. I conjecture that all members of this sequence greater than 5 are divisible by 255. This implies that all odd numbers (greater than 7) are the sum of a prime and at most three positive powers of two.

Conventions: offset 1; the sequence starts 1, 3, 5, 6495105, …; a and b are positive integers
(so 2^a and 2^b are even, at least 2), a = b is allowed, p is any prime. Since n is odd and
2^a + 2^b is even, p is odd automatically.

Published verification: the entry says "up to 2.5 * 10^11"; its b-file (G. Resta) lists the 233
terms below 10^12. UNVERIFIED CITATION: Z.-W. Sun's page "Mixed sums of primes and other terms"
is reported (by a web search summary, page not opened by us) to say that D. S. McNeil verified the
conjecture for odd numbers below 10^13.

## Sanity check

`search.exe 1 1 1 100000000 8` (every odd n below 10^8) prints exactly 1, 3, 5, 6495105.
`search.exe 255 0 1 25000000000 8` (every odd multiple of 255 below 2.5·10^10) prints 6495105,
848629545, 1117175145, …, 21468020835 — the same 22 terms as the OEIS data section after 1, 3, 5 —
and then 24358769685, which is past the end of the data section. Reproduces the OEIS data: **yes**.

## Result

**n = 949806618679575 = 3² · 5² · 241 · 257 · 68155751** is odd, greater than 5, and
n − 2^a − 2^b is composite for every 1 ≤ a ≤ b with n − 2^a − 2^b ≥ 2 (1224 pairs). So n is a
term of A156695. But n ≡ 13 (mod 17), so 255 does not divide n (n mod 255 = 30).
This contradicts "all members of this sequence greater than 5 are divisible by 255".

Evidence (three independent checks of the same 1224 numbers):

| Check | Command | Output |
|---|---|---|
| C search (sieve + 7-base deterministic Miller–Rabin) | `search.exe 6503385 5574330 1 9223372036854775807 12 data\ckpt_no17_A.txt` | `HIT 949806618679575  mod17=13 mod255=30` |
| Python, `sympy.isprime` on every pair | `python verify.py 949806618679575` | `pairs (a<=b, m>=2) checked: 1224  primes found: 0` |
| PARI/GP `isprime` (a proof, not a probable-prime test) on every pair | loop in the log below | `gp: pairs 1224 primes 0` |
| Explicit divisor for each of the 1224 numbers | `python certificate.py --check data/certificate_949806618679575.txt` | `OK … 1224 pairs, each m has the listed proper divisor` |

The certificate needs no primality test at all: it lists a proper divisor of each
n − 2^a − 2^b (600 of them are divisible by 3, 300 by 5, the largest least prime factor is 20641351).

Further terms not divisible by 17 from the same class search (each verified the same three ways,
certificates in `data/`), as of the search reaching 4.12·10^17:

| n | factorization | n mod 17 | pairs checked |
|---|---|---|---|
| 275984581255575 (from the 3855 search, see below) | 3 · 5² · 241 · 257 · 59411893 | 15 | 1127 |
| 949806618679575 | 3² · 5² · 241 · 257 · 68155751 | 13 | 1224 |
| 31376079494071815 | 3 · 5 · 241 · 257 · 43651 · 773683 | 15 | 1484 |
| 34680815917336875 | 3 · 5⁴ · 11 · 13 · 241 · 257 · 2088343 | 4 | 1484 |
| 72319213470435315 | 3 · 5 · 241 · 257 · 77841692333 | 1 | 1587 |
| 384368597849371365 | 3² · 5 · 241 · 257 · 313 · 440596337 | 13 | 1709 |
| 399332799094755105 | 3³ · 5 · 241 · 257 · 5827 · 8196077 | 4 | 1709 |

In the same range the class contains 2779 exceptions divisible by 17 (2785 hits in all).

What this does **not** show:

- It does not contradict the weaker statement in the same comment: n = 949806618679561 + 2 + 4 + 8
  with 949806618679561 prime, so n is a prime plus three positive powers of two.
- It says nothing about Erdős #9 or #10.
- **We do not know that this is the smallest counterexample.** Only one residue class was searched
  (see below). Between the published bound and 9.5·10^14 other classes are unchecked.

## A smaller counterexample (2026-11-26)

**n = 275984581255575 = 3 · 5² · 241 · 257 · 59411893** is a term of A156695 with n ≡ 15 (mod 17)
(n mod 255 = 15). It is smaller than 949806618679575. It was found by the search over all odd
multiples of 3855 = 3·5·257 between 10^13 and 949806618679576; it was missed by the class search
above because n ≡ 2 (mod 7), not 6.

| Check | Command | Output |
|---|---|---|
| C search | `search.exe 3855 0 10000000000000 949806618679576 6 data\ckpt_3855_below.txt` | `HIT 275984581255575  mod17=15 mod255=15` |
| `sympy.isprime` on every pair | `python verify.py 275984581255575` | `pairs (a<=b, m>=2) checked: 1127  primes found: 0` |
| PARI/GP `isprime` on every pair | loop as in the log | `gp: pairs 1127 primes 0` |
| Explicit divisors | `python certificate.py --check data/certificate_275984581255575.txt` | `OK … 1127 pairs, each m has the listed proper divisor` |

It is the only hit with 17 ∤ n among the odd multiples of 3855 in [10^13, 328724154329205).
**Still not known to be the smallest counterexample**: numbers that are not multiples of 3855 are
only covered by the exhaustive run, which had reached 9.0·10^13 at the time of writing.

**Update 2026-11-27: it is the smallest.** The exhaustive run passed n < 285873023221760
(2.8587·10^14) and was stopped there. Its hit file `data/hits_exh.txt` has 18097 lines; the only
hits not divisible by 255 are 1, 3, 5 (the trivial terms) and 275984581255575. So every term n
with 5 < n < 275984581255575 is divisible by 255. This rests on `exhaustive.c` alone for n not
divisible by 3855; `search.c` (a separate program) covers the multiples of 3855 in the same range
and agrees. `exhaustive.c` was checked against the OEIS data section (see the log).

## Open follow-ups (model estimates, not results)

`python optimize_class.py`, lines for L = 63 (n < 2^63), best small-modulus class per variant:

| Variant | Best class | E (expected primes per n) | ln(candidates below 2^63) | ln(expected exceptions in the class) |
|---|---|---|---|---|
| 17 ∤ n (done) | 0 mod 3·5·241·257, 6 mod 7 | 23.43 | 27.29 | +3.86 |
| 5 ∤ n | 0 mod 3·13·17·257, 6 mod 7 | 31.12 | 28.98 | −2.14 |
| 3 ∤ n | 0 mod 5·11·17·19·43·257, 6 mod 7 | 46.16 | 21.93 | −24.22 |

Calibration: for 17 ∤ n the model predicts about e^3.86 ≈ 47 exceptions in the class below 2^63;
the search found 6 in the first 5% of the range, so the model is low by a factor of about 2–3.
Reading the table with that correction: a term not divisible by 5 below 2^63 has maybe a 30%
chance of existing in the best class, and scanning that class (about 4·10^12 candidates) would
take roughly 17 days on this machine. A term not divisible by 3 is not expected below 2^63 at all.
So "every term > 5 is divisible by 15" is still consistent with everything known. Not started.

## How it was found

Heuristic (not a proof; `optimize_class.py`): for a fixed residue of n modulo a prime q, the pairs
(a, b) with q | n − 2^a − 2^b are those with 2^a + 2^b ≡ n (mod q), which depends only on a, b
modulo the order of 2 mod q. For n ≡ 0 modulo 3, 5, 17, 257 the killed sets are disjoint
(a − b odd; ≡ 2 mod 4; ≡ 4 mod 8; ≡ 8 mod 16), which is why multiples of 255 dominate. The script
minimises the expected number of prime values, E, over residue classes with 17 ∤ n. The best class
found with a small modulus is

    n ≡ 0 (mod 3·5·241·257),  n ≡ 6 (mod 7)     i.e.  n ≡ 5574330 (mod 6503385),

where 241 (order 24) takes over part of the role of 17. The model gave E ≈ 23 near 2^63 and
predicted that the class contains exceptions with 17 ∤ n below 2^63. The search then scans every
odd n in that class.
