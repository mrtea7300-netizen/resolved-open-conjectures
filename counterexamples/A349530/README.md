# OEIS A349530 (Conjecture 3)

- **Status:** `counterexample (confirmed)` (infinite family of counterexamples proved & formally verified in Lean 4, and smallest new counterexamples $n = 1{,}953{,}126\dots 1{,}953{,}130$ directly verified by brute force)

## Verbatim statement

From OEIS `A349530.seq` (retrieved from `oeis/oeisdata`):

> **Name:** Least positive integer m such that the n numbers k*(k^4+1) (k=1..n) are pairwise distinct modulo m^2.
>
> **Conjecture 3:** Let n be a positive integer not among 26, 27, 28, 626, 627, 628, 629, 630, and define D(n) as the least positive integer m such that the n numbers k*(k^4+1) (k=1..n) are pairwise distinct modulo m. If 5^a < n <= 3*5^a, then D(n) = 3*5^a. If 3*5^a < n <= 5^(a+1), then D(n) = 5^(a+1).
>
> We have verified the above conjectures for n up to 10^5.

## Infinite family of counterexamples

**Conjecture 3 is false for infinitely many $n$.**

For every integer $k \ge 1$, set $a = 5k + 4$ ($a = 9, 14, 19, \dots$). Then for all five integers
$$n \in \{5^a + 1,\; 5^a + 2,\; 5^a + 3,\; 5^a + 4,\; 5^a + 5\},$$
we have $5^a < n \le 3 \cdot 5^a$, so Conjecture 3 predicts $D(n) = 3 \cdot 5^a = 15 \cdot 5^{a-1}$. However,
$$D(n) \le 11 \cdot 5^{a-1} < 3 \cdot 5^a.$$

The **smallest new counterexamples** ($k = 1$, $a = 9$, just beyond Sun's $10^5$ search bound) are:
$$n = 1{,}953{,}126,\; 1{,}953{,}127,\; 1{,}953{,}128,\; 1{,}953{,}129,\; 1{,}953{,}130,$$
for which all $n$ values $j(j^4 + 1)$ ($1 \le j \le n$) are pairwise distinct modulo $m = 11 \cdot 5^8 = 4{,}296{,}875 < 5{,}859{,}375 = 3 \cdot 5^9$.

### Proof (why Sun's exception at $n = 626..630$ repeats every 5 powers of 5)

1. **Bijectivity mod $5^{a-1}$:** Let $f(x) = x(x^4 + 1)$. Modulo $5$, $f(x) \equiv 2x \pmod 5$ is bijective and $f'(x) = 5x^4 + 1 \equiv 1 \not\equiv 0 \pmod 5$, so by Hensel's lemma $f$ is injective modulo $5^e$ for every $e \ge 1$.
2. **Reduction mod $11$:** If $1 \le i < j \le 5^a + 5$ satisfy $f(i) \equiv f(j) \pmod{11 \cdot 5^{a-1}}$, then $i \equiv j \pmod{5^{a-1}}$. Writing $i = r + t_1 \cdot 5^{a-1}$ and $j = r + t_2 \cdot 5^{a-1}$ with $1 \le r \le 5^{a-1}$, we have $0 \le t_1 < t_2 \le 5$ when $1 \le r \le 5$ and $0 \le t_1 < t_2 \le 4$ when $r > 5$.
3. **Periodicity:** Since $5^5 \equiv 1 \pmod{11}$, for every $a = 5k + 4$ we have $5^{a-1} = 5^{5k+3} \equiv 5^3 \equiv 4 \pmod{11}$ — the exact same shift as at $a = 4$ ($n = 626..630$). Direct check mod $11$ confirms that $f(r + 4t) \bmod 11$ is pairwise distinct for $t \in \{0, 1, 2, 3, 4\}$ (all $r \bmod 11$) and for $t \in \{0, 1, 2, 3, 4, 5\}$ ($r \in \{1, 2, 3, 4, 5\}$), contradicting $f(i) \equiv f(j) \pmod{11}$.

## Verification

1. **Formal Lean 4 proof of the entire infinite family** ([`A349530.lean`](A349530.lean), zero external dependencies, zero `sorry`, standard axioms only):
   ```bash
   lean conjectures/A349530/A349530.lean
   ```
2. **Standalone brute-force Python verifier** ([`verify_counterexample.py`](verify_counterexample.py)): reproduces published OEIS A349530 `n = 1..30`, confirms Sun's `n = 626..630`, and directly hashes all $1{,}953{,}130$ values $k(k^4+1) \bmod 4{,}296{,}875$ in `1.51s`.
   ```bash
   python conjectures/A349530/verify_counterexample.py
   ```

## Novelty check (2026-11-26)

- Checked `A349530.seq` in `oeis/oeisdata`: Conjecture 3 is still listed as open (verified only to $10^5$).
- Checked `https://tadamcz.com/oeis-open/`: `A349530` is not listed.
- Web search for `"A349530"` and `"k*(k^4+1)"`: no prior disproof found.
