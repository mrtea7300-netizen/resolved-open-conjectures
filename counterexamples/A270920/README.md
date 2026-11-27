# A270920 — n = positive triangular + positive square + fifth power

- **OEIS:** https://oeis.org/A270920
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-polynomial-uniqueness/`](../family-polynomial-uniqueness/)

## Statement (verbatim from OEIS)

> Number of ordered ways to write n as the sum of a positive triangular number, a positive square,
> and a fifth power whose absolute value does not exceed n.
>
> Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 112, 770, 801, 1593, 1826,
> 2320, 2334, 2849, 7561.

Conventions: the fifth power z⁵ has |z⁵| ≤ n; the OEIS data count z = 0 twice (as Sun's program does), and we follow the data.

## Result

**The list of n with a(n) = 1 is incomplete.** a(n) = 1 also for

> **n = 265295**

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
