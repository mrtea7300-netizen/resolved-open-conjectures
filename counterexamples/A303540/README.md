# A303540 — n = a² + b² + C(2c,c) + C(2d,d)

- **OEIS:** https://oeis.org/A303540
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-binary-form-plus-sparse/`](../family-binary-form-plus-sparse/)

## Statement (verbatim from OEIS)

> Number of ways to write n as a^2 + b^2 + binomial(2*c,c) + binomial(2*d,d), where a,b,c,d are
> nonnegative integers with a <= b and c <= d.
>
> Conjecture: a(n) > 0 for all n > 1. In other words, any integer n > 1 can be written as the sum
> of two squares and two central binomial coefficients.
>
> It has been verified that a(n) > 0 for all n = 2..10^10.
>
> Jiao-Min Lin (a student at Nanjing University) has verified a(n) > 0 for all 1 < n <= 10^11. -
> _Zhi-Wei Sun_, Jul 30 2022

Conventions: a, b, c, d ≥ 0, counted with a ≤ b and c ≤ d; claimed for n > 1. A303539 states the same conjecture as "n − C(2k,k) − C(2m,m) is a sum of two squares for some k, m", so it fails at the same n.

## Result

**The conjecture is false.** The numbers

> **210107364447** and **654217254627**

are not the sum of two squares and two central binomial coefficients. They are the only such n with
1 < n < 10¹² (the entry records a verification to 10¹¹ by Jiao-Min Lin, 2022).

## How it was checked

1. Search engine `bfsparse` (C), validated against brute force and OEIS data (`test_engine.py`).
2. Standalone `verify.py` (exhaustive from the definition), and its `--two-squares` mode, which prints for every remainder a prime q ≡ 3 (mod 4) dividing it to an odd power.
3. PARI/GP script `verify.gp` (third implementation).
4. `coordinator_check.py`, written separately from the OEIS wording.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-binary-form-plus-sparse/verify.py A303540 210107364447 654217254627
python conjectures/family-binary-form-plus-sparse/verify.py A303540 210107364447 --two-squares
```

## Reporting

Not reported outside the repository yet (next OEIS batch).
