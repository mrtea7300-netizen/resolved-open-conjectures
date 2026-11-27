# OEIS A224210

- **Status:** `counterexample (confirmed)` (first bound conjecture disproved at $n = 63$; two independent CAS implementations: `python-flint` and `SymPy`)

## Verbatim statement

From OEIS `A224210.seq` (retrieved from the GitHub mirror `oeis/oeisdata`, dated Apr 01 2013):

> **Name:** Least prime p such that sum_{k=0}^n (k+1)^2*x^{n-k} is irreducible modulo p.
>
> **Conjecture:** a(n) does not exceed the (4n-3)-th prime for each n>0. Moreover, for any integers m>1 and n>0 the polynomial sum_{k=0}^n (k+1)^m*x^{n-k} is irreducible modulo some prime, and its Galois group over the rationals is isomorphic to the symmetric group S_n. Also, for m,n=2,3,... there are infinitely many integers b > n^m such that [n^m,...,2^m,1^m] in base b is prime.
>
> **Offset:** `1,1`
> **Published terms (`n = 1..50`):** `2, 11, 7, 17, 11, 3, 7, 97, 3, 89, 31, 113, 43, 7, 23, 23, 17, 67, 23, 109, 17, 277, 103, 283, 59, 101, 157, 127, 29, 79, 23, 223, 73, 269, 433, 137, 5, 659, 109, 401, 419, 7, 373, 131, 89, 269, 149, 61, 829, 881`

## Counterexample

The bound conjecture $a(n) \le p_{4n-3}$ for all $n > 0$ is **false**.

At **$n = 63$**:
- The polynomial is $f_{63}(x) = \sum_{k=0}^{63} (k+1)^2 x^{63-k} = x^{63} + 4x^{62} + 9x^{61} + \dots + 4096$.
- The conjectured upper bound is $p_{4 \cdot 63 - 3} = p_{249} = 1579$.
- $f_{63}(x)$ is **reducible modulo every prime $p \le 1621$** (the first 257 primes, including all 249 primes $\le 1579$).
- The least prime modulo which $f_{63}(x)$ is irreducible is **$a(63) = 1627 = p_{258} > 1579 = p_{249}$**.

$n = 63$ is the **smallest** counterexample and the only counterexample in $1 \le n \le 200$.

### Why Sun's original check missed $n = 63$

In the `%t` Mathematica program recorded in `A224210.seq`:
```mathematica
Do[Do[If[IrreduciblePolynomialQ[A[n,x],Modulus->Prime[k]]==True,Print[n," ",Prime[k]];Goto[aa]],{k,1,Prime[4n-3]}];
Print[n," ",counterexample];Label[aa];Continue,{n,1,100}]
```
The inner loop upper limit was written as `Prime[4n-3]` instead of `4n-3`, so at $n = 63$ it searched up to the $1579$-th prime ($13297$) rather than the $249$-th prime ($1579$) and never triggered the counterexample branch.

### Heuristic note

By Chebotarev's density theorem (assuming $\mathrm{Gal}(f_n/\mathbb{Q}) \cong S_n$), the density of primes $p$ for which $f_n(x)$ is irreducible mod $p$ is $1/n$, so the probability that all of the first $4n-3$ primes fail is approximately $(1 - 1/n)^{4n-3} \approx e^{-4} \approx 1.83\%$ per $n$. Thus infinitely many counterexamples are expected.

## Verification

1. **`search.py`** (`python-flint`): reproduces all 50 published OEIS terms `n = 1..50` and scans `n = 1..200`, finding `n = 63` (`a(63) = 1627 = p_258 > p_249 = 1579`).
2. **`verify_counterexample.py`** (`SymPy`, completely independent implementation directly from the OEIS definition): reproduces all 50 published OEIS terms `n = 1..50` and confirms `a(63) = 1627 = p_258 > p_249 = 1579`.

Commands:
```bash
python conjectures/A224210/search.py
python conjectures/A224210/verify_counterexample.py
```

## Novelty check (2026-11-26)

- Checked `A224210.seq` in `oeis/oeisdata`: the conjecture is still listed as open with no counterexample comment.
- Checked `https://tadamcz.com/oeis-open/`: `A224210` is not listed.
- Web search for `"A224210"` and `"does not exceed the (4n-3)-th prime"`: no prior disproof found.
