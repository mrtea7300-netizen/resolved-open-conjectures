# A308644 — n = (3ᵃ5ᵇ)² + c(3c+1)/2 + d(7d+3)/2 and the 3ᵃ4ᵇ variant

- **OEIS:** https://oeis.org/A308644
- **Status:** counterexample (confirmed)
- **Code and data:** [`../family-binary-form-plus-sparse/`](../family-binary-form-plus-sparse/)

## Statement (verbatim from OEIS)

> Number of ways to write n as (3^a*5^b)^2 + c*(3c+1)/2 + d*(7d+1)/2, where a and b are
> nonnegative integers, and c and d are integers.
>
> Conjecture 1: a(n) > 0 for all n > 0. Also, any positive integer n can be written as (3^a*5^b)^2
> + c*(3c+1)/2 + d*(7d+3)/2, where a and b are nonnegative integers, and c and d are integers.
>
> Conjecture 2: Let r be 1 or 3. Then, any positive integer n can be written as (3^a*4^b)^2 +
> c*(3c+1)/2 + d*(7d+r)/2, where a and b are nonnegative integers, and c and d are integers.
>
> We have verified Conjectures 1-2 for all n = 1..10^6.
>
> See also A308640, A308641 and A308656 for similar conjectures.

Conventions: a, b ≥ 0; c, d any integers. The sequence counts the form with d(7d+1)/2; the failing statements are in the comments.

## Result

Two of the statements in the comments are false:

- **Conjecture 1, second sentence** (n = (3ᵃ5ᵇ)² + c(3c+1)/2 + d(7d+3)/2): fails at **n = 108011768**, and at 442043442 (searched to 10¹⁰).
- **Conjecture 2 with r = 3** (n = (3ᵃ4ᵇ)² + c(3c+1)/2 + d(7d+3)/2): fails at **n = 7654105** (the only one below 10¹⁰).

Sun had verified these for n ≤ 10⁶. The main statement a(n) > 0 and Conjecture 2 with r = 1 have no
counterexample below 10¹¹.

## How it was checked

1. Search engine `bfsparse` (C), validated against brute force and OEIS data.
2. Standalone `verify.py` (exhaustive from the definition).
3. `coordinator_check_A308644_A308656.py`: reproduces the 100 OEIS terms of A308644, then finds 0 representations; controls n + 1 have 38 and 54.

"Confirmed" here means: reproduced by at least two programs that share no code. Statements of the
kind "no other counterexample below N" rest on the search engine alone.

## Reproduce

```
python conjectures/family-binary-form-plus-sparse/verify.py A308644_1b 108011768
python conjectures/family-binary-form-plus-sparse/verify.py A308644_2_r3 7654105
python conjectures/family-binary-form-plus-sparse/coordinator_check_A308644_A308656.py
```

## Reporting

Not reported outside the repository yet.
