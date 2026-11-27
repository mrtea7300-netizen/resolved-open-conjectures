# A300448 — n² = 4ᵏ·m + x² + y² with m ∈ {1, 5, 17} (Conjecture 2)

- **OEIS:** https://oeis.org/A300448
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-binary-form-plus-sparse/`](../family-binary-form-plus-sparse/)

## Statement (verbatim from OEIS)

> Number of the integers 4^k*m with k >= 0 and m = 1, 2, 5 such that n^2 - 4^k*m can be written as
> the sum of two squares.
>
> Conjecture 1: a(n) > 0 for all n > 0.
>
> Conjecture 2: Each positive square n^2 can be written as 4^k*m + x^2 + y^2 with k,x,y
> nonnegative integers and m among 1, 5 17.
>
> Conjecture 3: For each n = 1,2,3,... we can write n^2 as 4^k*m + x^2 + y^2 with k,x,y
> nonnegative integers and m among 1, 5, 65.
>
> Conjecture 3 implies that A300441(n) > 0 for all n > 0 since  4*A001353(0)^2 + 1 = 1,
> 4*A001353(1)^2 + 1 = 5 and 4*A001353(2)^2 + 1 = 65.
>
> We have verified Conjectures 1-3 for all n = 1..2*10^7.

Conventions: k, x, y ≥ 0. The sequence itself counts Conjecture 1 (m ∈ {1, 2, 5}); Conjectures 2 and 3 are stated in the comments. Sun verified all three for n ≤ 2·10⁷.

## Result

**Conjecture 2 is false.** The smallest counterexample is

> **n = 239694783** = 3 · 47 · 179 · 9497

For each of the 81 numbers n² − 4ᵏ·m (m ∈ {1, 5, 17}) some prime ≡ 3 (mod 4) divides it to an odd
power. The other counterexamples below 10⁹ are 2n and 4n (479389566, 958779132).
Conjectures 1 and 3 have no counterexample for n < 10⁹.

## How it was checked

1. Search engine `sqform` (C), validated against the OEIS data of A300448, A301452 and the published counterexample of A302641.
2. `coordinator_check_A302984_A300448.py` (sympy): reproduces the first 33 terms of A300448 by brute force, then finds 0 good values for n = 239694783 by the two-squares theorem. Control n + 1 has 12.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-binary-form-plus-sparse/coordinator_check_A302984_A300448.py
```

## Reporting

Not reported outside the repository yet (next OEIS batch).
