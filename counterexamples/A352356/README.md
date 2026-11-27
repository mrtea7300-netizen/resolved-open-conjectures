# A352356 — 12n + 5 = 2x² + 5y² + 9z² + xyz

- **OEIS:** https://oeis.org/A352356
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-polynomial-uniqueness/`](../family-polynomial-uniqueness/)

## Statement (verbatim from OEIS)

> Number of ways to write 12*n + 5 as 2*x^2 + 5*y^2 + 9*z^2 + x*y*z, where x, y and z are
> nonnegative integers.
>
> Conjecture: For each n = 0,1,2,... we can write 12*n + 5 as 2*x^2 + 5*y^2 + 9*z^2 + x*y*z with
> x,y,z nonnegative integers.
>
> This has been verified for all n = 0..10^6.
>
> It seems that a(n) = 1 only for n = 0, 2, 5, 12, 65, 86, 155, 338, 21030.

Conventions: x, y, z ≥ 0. The entry says "It seems that a(n) = 1 only for …".

## Result

**The list of n with a(n) = 1 is incomplete.** a(n) = 1 also for

> **n = 874830**

These are all the missing values for n ≤ 3·10⁸. The other half of the conjecture, a(n) > 0, has no
counterexample in that range.

## How it was checked

1. Search engine `polyrep` (C), which reproduces the OEIS data section.
2. Standalone `verify.py` (brute force from the definition): lists the single representation for each new n.
3. PARI/GP script `verify.gp`.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-polynomial-uniqueness/verify.py
```

## Reporting

Not reported outside the repository yet (next OEIS batch).
