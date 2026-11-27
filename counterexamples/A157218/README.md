# A157218 — odd m = p + 2ˣ + 7·2ʸ with p ≡ 1 (mod 6)

- **OEIS:** https://oeis.org/A157218
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-prime-plus-sparse/`](../family-prime-plus-sparse/)

## Statement (verbatim from OEIS)

> Number of ways to write the n-th positive odd integer in the form p+2^x+7*2^y with p a prime
> congruent to 1 mod 6 and x,y positive integers.
>
> On Feb 24 2009, Zhi-Wei Sun conjectured that a(n)>0 for all n=18,19,...; in other words, any odd
> integer greater than 34 can be written as the sum of a prime congruent to 1 mod 6, a positive
> power of 2 and seven times a positive power of 2. Sun verified the conjecture for odd integers
> below 5*10^7, and Qing-Hu Hou continued the verification for odd integers below 1.5*10^8.

Conventions: offset 1, the n-th positive odd integer is 2n − 1, x ≥ 1, y ≥ 1, p prime with p mod 6 = 1.

## Result

**The conjecture is false.** The odd number

> **m = 445466268731** (n = 222733134366, m = 11³ · 2999 · 111599)

has no representation p + 2ˣ + 7·2ʸ with p a prime ≡ 1 (mod 6) and x, y ≥ 1, so a(222733134366) = 0.

It is the **only** counterexample below 10¹³: every other odd m with 34 < m < 10¹³ has a representation (the search was extended from 10¹² to 10¹³ on 2026-11-26; `conjectures/family-prime-plus-sparse/RESULTS.md`).

### Why it fails (the certificate)

There are 1329 pairs (x, y) with p = m − 2ˣ − 7·2ʸ > 1.

- For 987 of them p is not ≡ 1 (mod 6). Indeed m ≡ 5 (mod 6) forces 2ˣ + 7·2ʸ ≡ 4 (mod 6), which
  happens only when x and y are both odd.
- For the other 342, p is composite. An explicit prime factor of each is listed in
  [`A157218_445466268731.certificate.txt`](../family-prime-plus-sparse/data/A157218_445466268731.certificate.txt).
  5 divides 90 of them, 7 divides 81 more, 11 another 34; the hardest one has least prime factor 566999.

So the failure is checkable by hand-sized arithmetic: 342 divisions.

## How to check it yourself (1 minute, plain Python, no installs)

```
cd conjectures/family-prime-plus-sparse
python verify.py 445466268731 7 1                 # -> COUNTEREXAMPLE CONFIRMED
python verify.py --certificate 445466268731 7 1   # -> prints a prime factor for all 342 candidates
```

`verify.py` shares no code with the search engine: it is a double loop over (x, y) written from the
OEIS definition, with its own deterministic Miller–Rabin test, and it first re-derives the first 50
terms of the OEIS data section.

PARI/GP one-liner, also straight from the definition:

```
cnt(m)=my(c=0,q);for(x=1,logint(m,2),for(y=1,logint(m,2),q=m-2^x-7*2^y;if(q>1&&q%6==1&&isprime(q),c++)));c;
vector(50,n,cnt(2*n-1))   \\ matches the OEIS data section
cnt(445466268731)         \\ 0
```

## Independent confirmations

| # | Implementation | Primality | Result |
|---|---|---|---|
| 1 | `sparse3.c` bit-sieve search engine | segmented sieve (+ Miller–Rabin for large shifts) | no representation; unique below 10¹³ |
| 2 | `families.py` brute force | `sympy.isprime` | no representation |
| 3 | PARI/GP 2.17 one-liner above | `isprime` (proven) | count = 0; first 50 terms match OEIS |
| 4 | `verify.py` | own deterministic Miller–Rabin; trial division for the certificate | count = 0; 342 explicit factors |

The engine is validated separately (`test_engine.py`): it agrees with brute force on [1, 200000)
for every family, and it rediscovers the published counterexamples of the sister conjectures
(A157225: 1433987797; A154364: 169421772576 and three more).

## Why this number, and how many more?

`python structure.py table | rank | predict` (this folder).

- Since m ≡ 5 (mod 6), the candidates are m − 2·4ᵃ − 14·4ᵇ. For a prime q the proportion of
  candidates divisible by q depends only on m mod q, and m sits in the **worst** residue class for
  5, 7, 11, 13, 31 and 41 at once (11 divides m, which makes 1 candidate in 5 divisible by 11).
- The resulting local factor is S(m) ≈ 0.615; only about 1% of all m ≡ 5 (mod 6) are that low.
  The heuristic expected number of representations drops from 38 to about 24, and the 41 candidates
  with no prime factor below 500 all happen to be composite.
- An independent-primes model predicts about 1.6 counterexamples per conjecture in [1.5·10⁸, 10¹²)
  and about 0.6 more per decade after that, growing slowly — so heuristically there are infinitely
  many. Observed: 1 for A157218 and 4 for the sister A157225 (see below). The model is exponentially
  sensitive to second-order choices; trust the order of magnitude only.
- **Not proved:** we have no proof that there are infinitely many counterexamples. Crocker's trick
  for p + 2ᵃ + 2ᵇ does not transfer, and a covering-congruence proof would need to cover all pairs (a, b).

## Sister results from the same search (all below 10¹²)

| Entry | Result |
|---|---|
| A157225 (p ≡ 5 mod 6, c = 7) | counterexamples are exactly 1433987797 (Adamczewski 2026), **45483661477, 85305551767, 367084269651** (new; each verified with `verify.py N 7 5`) |
| A157237 (p ≡ 1 mod 6, c = 11) | holds with exactly Sun's exceptions (previous bound 1.5·10⁸) |
| A155904 (any odd prime, c = 5) | no exception for odd m ≥ 15 (previous bound 10⁸) |
| A154258, A154263 (p + F_s + F_t², F_t³) | no exception for n > 4 (previous bound 3·10⁷) |

## Novelty check (2026-11-25)

- The OEIS entry (revision of 2026-05-30) lists no counterexample and no verification past 1.5·10⁸.
- A157218 is not among the 492 conjectures of the 2026 OEIS Open / AlphaProof Nexus benchmarks.
  Its sister A157225 (p ≡ 5 mod 6) was disproved there (Adamczewski, 2026, m = 1433987797).
- Web searches for the number and for the conjecture found no prior report.

## Reporting

What was posted, published and sent, and the OEIS edits proposed: [`report.md`](report.md).
