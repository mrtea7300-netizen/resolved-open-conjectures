# A303932 — 2n = p + 2ᵏ + 3ᵐ with 11 a quadratic residue (or nonresidue) mod p

- **OEIS:** https://oeis.org/A303932
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-prime-plus-sparse-2018/`](../family-prime-plus-sparse-2018/)

## Statement (verbatim from OEIS)

> Number of ways to write 2*n as p + 2^k + 3^m, where p is a prime with 11 a quadratic residue
> modulo p, and k and m are nonnegative integers.
>
> Conjecture 1. a(n) > 0 for all n > 1, i.e., any even number greater than two can be written as
> the sum of a power 2, a power of 3 and a prime p with 11 a quadratic residue modulo p.
>
> Conjecture 2. For any integer n > 2, we can write 2*n as p + 2^k + 3^m, where p is a prime with
> 11 a quadratic nonresidue modulo p, and k and m are nonnegative integers.
>
> We have verified Conjectures 1 and 2 for n up to 5*10^8.

Conventions: k, m ≥ 0. Conjecture 1: p = 2 counts and p = 11 does not (as in the entry's Mathematica program). Conjecture 2: p odd with (11/p) = −1. For the numbers below neither p = 2 nor p = 11 occurs at all, so the result does not depend on that reading. Sun verified both for n ≤ 5·10⁸.

## Result

**Both conjectures are false.**

| | smallest counterexample 2n | n | all counterexamples with 2n < 10¹² |
|---|---|---|---|
| Conjecture 1 (residue) | **257558146370** | 128779073185 | 257558146370, 749360555468, 799324864730 |
| Conjecture 2 (nonresidue) | **68211369278** | 34105684639 | 68211369278, 273299806988 |

For 2n = 257558146370 there are 19 primes of the form 2n − 2ᵏ − 3ᵐ, and 11 is a nonresidue modulo
every one of them; for 2n = 68211369278 there are 20, and 11 is a residue modulo every one.

## How it was checked

1. Search engine `sparse4` (C), validated against brute force and OEIS data (`test_engine.py`).
2. Standalone `verify.py` (own Miller–Rabin and Jacobi symbol).
3. PARI/GP script `verify.gp`.
4. `coordinator_check_A303932.py` (sympy, written from the OEIS wording): reproduces the first 40 terms and lists the prime candidates with their Jacobi symbols.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-prime-plus-sparse-2018/verify.py A303932 257558146370
python conjectures/family-prime-plus-sparse-2018/verify.py A303932nr 68211369278
python conjectures/family-prime-plus-sparse-2018/coordinator_check_A303932.py
```

## Reporting

Not reported outside the repository yet (next OEIS batch).
