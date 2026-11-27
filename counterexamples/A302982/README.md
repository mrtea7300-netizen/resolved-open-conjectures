# A302982 — n = x² + 5y² + 2ᶻ + 3·2ʷ

- **OEIS:** https://oeis.org/A302982
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-binary-form-plus-sparse/`](../family-binary-form-plus-sparse/)

## Statement (verbatim from OEIS)

> Number of ways to write n as x^2 + 5*y^2 + 2^z + 3*2^w with x,y,z,w nonnegative integers.
>
> Conjecture: a(n) > 0 for all n > 3.
>
> Clearly, a(4*n) > 0 if a(n) > 0. We have verified a(n) > 0 for all n = 4..2*10^8.
>
> See also A302983 and A302984 for similar conjectures.

Conventions: x, y, z, w ≥ 0; claimed for n > 3; Sun verified n ≤ 2·10⁸.

## Result

**The conjecture is false.** The smallest counterexample is

> **n = 558556427**

and there are 200 counterexamples below 4·10¹⁰ (all ≡ 3 mod 8); the full list is in
`data/A302982.exceptions.txt` of the family folder.

## How it was checked

1. Search engine `bfsparse` (C), validated against brute force and OEIS data.
2. Standalone `verify.py` (exhaustive from the definition).
3. PARI/GP script `verify.gp`.
4. `coordinator_check.py`, written separately from the OEIS wording.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-binary-form-plus-sparse/verify.py A302982 558556427
```

## Reporting

Not reported outside the repository yet (next OEIS batch).
