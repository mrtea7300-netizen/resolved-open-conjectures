# A157225 — odd m = p + 2ˣ + 7·2ʸ with p ≡ 5 (mod 6)

- **OEIS:** https://oeis.org/A157225
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-prime-plus-sparse/`](../family-prime-plus-sparse/)

## Statement (verbatim from OEIS)

> Number of ways to write the n-th positive odd integer in the form p+2^x+7*2^y with p a prime
> congruent to 5 mod 6 and x,y positive integers.
>
> On Feb. 24, 2009, Zhi-Wei Sun conjectured that a(n)=0 if and only if n<11 or n=13,16,992; in
> other words, except for 25, 31, 1983, any odd integer greater than 20 can be written as the sum
> of a prime congruent to 5 mod 6, a positive power of 2 and seven times a positive power of 2.
> Sun verified the conjecture for odd integers below 5*10^7, and Qing-Hu Hou continued the
> verification for odd integers below 1.5*10^8 (on Sun's request). Compare the conjecture with
> Crocker's result that there are infinitely many positive odd integers not of the form p+2^x+2^y
> with p an odd prime and x,y positive integers.
>
> Adamczewski disproved the above conjecture using n = 716993899, a(n) = 0, in linked article. -
> _Michael De Vlieger_, Aug 20 2026

Conventions: offset 1, the n-th positive odd integer is m = 2n − 1; x ≥ 1, y ≥ 1; p prime, p mod 6 = 5.

## Result

Sun's conjecture (a(n) = 0 only for n < 11 and n = 13, 16, 992) was refuted by T. Adamczewski in
2026 with n = 716993899 (m = 1433987797). We found **four further counterexamples**:

| m = 2n − 1 | n |
|---|---|
| 45483661477 | 22741830739 |
| 85305551767 | 42652775884 |
| 367084269651 | 183542134826 |
| 1572650032347 | 786325016174 |

Together with Adamczewski's value these are **all** odd m with 1983 < m < 10¹³ that have no
representation (exhaustive search, 1001 chunks, no gaps).

## How it was checked

1. Search engine `sparse3` (C, bit-parallel sieve), validated against brute force and the OEIS data section (`test_engine.py`).
2. Standalone `verify.py` (own Miller–Rabin, no shared code): no representation for each of the four values.
3. sympy and PARI/GP (`isprime`), each run separately: 0 representations for each value.
4. Factor certificate for the largest value: `data/A157225_1572650032347.certificate.txt`.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-prime-plus-sparse/verify.py 1572650032347 7 5
python conjectures/family-prime-plus-sparse/verify.py --certificate 1572650032347 7 5
```

## Reporting

Proposed to OEIS on 2026-11-26 from the account "Yotam Moshe" (comment + PARI program); see `../A157218/report.md`.
