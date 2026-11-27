# A308656 — n = (2ᵃ9ᵇ)² + c(4c+1) + d(3d+1)/2 (Conjecture 2)

- **OEIS:** https://oeis.org/A308656
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-binary-form-plus-sparse/`](../family-binary-form-plus-sparse/)

## Statement (verbatim from OEIS)

> Number of ways to write n as (2^a*9^b)^2 + c*(2c+1) + d*(3d+1), where a and b are nonnegative
> integers, and c and d are integers.
>
> Conjecture 1: a(n) > 0 for all n > 0.
>
> Conjecture 2: If f(x) is one of the polynomials x*(4x+1), x*(5x+2), x*(5x+4), x*(7x+3)/2 and
> x(7x+5)/2, then any positive integer n can be written as (2^a*9^b)^2 + f(c) + d*(3d+1)/2, where
> a and b are nonnegative integers, and c and d are integers.
>
> Conjecture 3: Let r be 1 or 2. Then any positive integer n can be written as (2^a*7^b)^2 +
> c*(2c+1) + d*(3d+r), where a and b are nonnegative integers, and c and d are integers.
>
> Conjecture 4: If g(x) is one of the polynomials x*(x+1), x*(4x+3), x*(7x+1)/2, x*(7x+3)/2 and
> x*(7x+5)/2, then any positive integer n can be written as (2^a*7^b)^2 + g(c) + d*(3d+1)/2, where
> a and b are nonnegative integers, and c and d are integers.
>
> We have verified a(n) > 0 for all n = 1..10^8, and Conjectures 2-4 for all n = 1..10^6.
>
> See also A308640, A308641, and A308644 for similar conjectures.
>
> Jiao-Min Lin (a student at Nanjing University) has found a counterexample to Conjecture 1:
> a(2109982225) = 0. - _Zhi-Wei Sun_, Jul 30 2022

Conventions: a, b ≥ 0; c, d any integers. Conjecture 1 (the sequence itself) was already refuted by Jiao-Min Lin in 2022 (n = 2109982225).

## Result

**Conjecture 2 is false for f(x) = x(4x+1).** The smallest counterexample is

> **n = 235644514**

and 9974943843 is the only other one below 10¹⁰ (Sun verified n ≤ 10⁶). The other four polynomials
of Conjecture 2, and Conjectures 3 and 4, have no counterexample below 10¹¹. Conjecture 2 is listed
as unsettled in the "OEIS Open" benchmark table (arXiv:2608.11941) as downloaded on 2026-11-25.

For Conjecture 1 we also found a second zero, a(2657795568) = 0.

## How it was checked

1. Search engine `bfsparse` (C), validated against brute force and OEIS data, including Lin's published zero.
2. Standalone `verify.py` (exhaustive from the definition).
3. `coordinator_check_A308644_A308656.py`: reproduces the 100 OEIS terms of A308656 and Lin's zero, then finds 0 representations; control n + 1 has 25.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-binary-form-plus-sparse/verify.py A308656_2_4x1 235644514
python conjectures/family-binary-form-plus-sparse/coordinator_check_A308644_A308656.py
```

## Reporting

Not reported outside the repository yet.
