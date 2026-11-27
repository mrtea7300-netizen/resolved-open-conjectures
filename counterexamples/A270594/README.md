# A270594 — n = triangular + positive square + (generalized pentagonal)²

- **OEIS:** https://oeis.org/A270594
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-polynomial-uniqueness/`](../family-polynomial-uniqueness/)

## Statement (verbatim from OEIS)

> Number of ordered ways to write n as the sum of a triangular number, a positive square and the
> square of a generalized pentagonal number (A001318).
>
> Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 3, 21, 24, 48, 90, 138,
> 213, 283, 462, 468, 567, 573, 1998, 2068, 2488, 2687, 5208, 5547, 5638, 6093, 6492, 6548, 6717,
> 7538, 7731, 8522, 14763, 16222, 17143, 24958, 26148.
>
> See also A270566 for a similar conjecture involving four powers.

Conventions: ordered; the square is positive; generalized pentagonal numbers are A001318.

## Result

**The list of n with a(n) = 1 is incomplete.** a(n) = 1 also for

> **n = 66738, 67518, 77143, 131218 and 183543**

These are all the missing values for n ≤ 10⁹. The other half of the conjecture, a(n) > 0, has no
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
