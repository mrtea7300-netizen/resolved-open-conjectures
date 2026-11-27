# A302984 — n = x² + 2y² + 2ᶻ + 5·2ʷ

- **OEIS:** https://oeis.org/A302984
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-binary-form-plus-sparse/`](../family-binary-form-plus-sparse/)

## Statement (verbatim from OEIS)

> Number of ways to write n as x^2 + 2*y^2 + 2^z + 5*2^w with x,y,z,w nonnegative integers.
>
> Conjecture: a(n) > 0 for all n > 5.
>
> Clearly, a(2*n) > 0 if a(n) > 0. We have verified a(n) > 0 for all n = 6...10^9.
>
> See also A302982 and A302983 for similar conjectures.

Conventions: x, y, z, w ≥ 0; claimed for n > 5; Sun verified n ≤ 10⁹.

## Result

**The conjecture is false.** The smallest counterexample is

> **n = 4375339279** = 139 · 1601 · 19661

(983 pairs (z, w), none leaves a number of the form x² + 2y²). There are 219 counterexamples
below 10¹²; the list is in `data/A302984.exceptions.txt` of the family folder. The sister entry
A302983 (3·2ʷ instead of 5·2ʷ) has no counterexample below 10¹².

## How it was checked

1. Search engine `bfsparse` (C), validated against brute force and OEIS data.
2. `coordinator_check_A302984_A300448.py` (sympy, written from the OEIS wording): reproduces the first 32 terms, then finds 0 representations two ways — by brute force over y, and by the criterion "no prime ≡ 5, 7 (mod 8) to an odd power". Control n + 1 has 331 good pairs.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-binary-form-plus-sparse/coordinator_check_A302984_A300448.py
```

## Reporting

Not reported outside the repository yet (next OEIS batch).
