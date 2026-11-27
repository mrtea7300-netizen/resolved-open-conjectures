# A262945 — pairs (x, y) with n − x⁴ − 2y² triangular or pentagonal

- **OEIS:** https://oeis.org/A262945
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-polynomial-uniqueness/`](../family-polynomial-uniqueness/)

## Statement (verbatim from OEIS)

> Number of ordered pairs (x,y) with x >= 0 and y >= 0 such that n - x^4 - 2*y^2 is a triangular
> number or a pentagonal number.
>
> Conjecture: a(n) > 0 for every n = 0,1,2,..., and a(n) = 1 only for the following 55 values of
> n: 0, 26, 27, 32, 41, 42, 50, 65, 80, 97, 112, 122, 130, 160, 196, 227, 239, 272, 322, 371, 612,
> 647, 736, 967, 995, 1007, 1106, 1127, 1205, 1237, 1240, 1262, 1637, 1657, 1757, 2912, 2987,
> 3062, 3107, 3524, 3647, 3902, 5387, 5587, 5657, 6047, 6107, 11462, 13427, 14717, 15002, 17132,
> 20462, 30082, 35750.
>
> See also A262941, A262944, A262954 and A262955 for similar conjectures.

Conventions: x, y ≥ 0, ordered pairs.

## Result

**The list of n with a(n) = 1 is incomplete.** a(n) = 1 also for

> **n = 254702 and 283457**

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
