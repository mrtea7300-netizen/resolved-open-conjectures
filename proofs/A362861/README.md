# A362861 — Complete Lean 4 Proof of Conjecture 1(i) and Conjecture 1(ii) (First Part)

**Status:** `proof (formalized)` (zero-dependency Lean 4.36.0, zero `sorry`, standard axioms only)  
**Primary source:** OEIS [A362861](https://oeis.org/A362861) (read from `oeis/oeisdata`, revision `#12`, May 16 2023).

---

## Verbatim Conjecture Statement

From `A362861.seq`:
> `Positive integers n such that 2*n cannot be written as a sum of distinct elements of the set {5^a + 5^b: a,b = 0,1,2,...}.`
>
> `2, 7, 10, 11, 12, 27, 35, 50, 51, 52, 55, 60, 135, 255`
>
> **Conjecture 1:**
> - **(i)** The current sequence only has the listed 14 terms. Also, each positive even number can be written as a sum of distinct elements of the set $\{3^a + 3^b : a, b = 0, 1, 2, \dots\}$.
> - **(ii)** Each positive even number can be written as a sum of distinct elements of the set $\{3^a + 7^b : a, b = 0, 1, 2, \dots\}$. Also, any positive even number not equal to 12 can be written as a sum of numbers of the form $3^a + 5^b$ ($a, b \ge 0$) with no summand dividing another.

---

## Proof Summary

Working in half-units $h = (k^a + m^b)/2$ (since $k, m$ are odd, every $k^a + m^b$ is even), we formally prove all three distinct-summand claims in `A362861.lean`:

1. **Conjecture 1(i), Part A (`5^a + 5^b`, exact characterization of A362861):**
   For every $n \ge 1$, $2n$ is a sum of distinct elements of $\{5^a + 5^b : a, b \ge 0\}$ if and only if
   $$n \notin \{2, 7, 10, 11, 12, 27, 35, 50, 51, 52, 55, 60, 135, 255\}.$$
   - The 15 half-values for $0 \le b \le a \le 4$ cover $[256, 2087]$ (and every non-exception in $[1, 255]$).
   - Adjoining block $t = 5$, namely $\{(5^5 + 5^b)/2 : 0 \le b \le 4\} = \{1563, 1565, 1575, 1625, 1875\}$, extends coverage via Brown's interval-merging lemma to $[256, 10290]$ (span $10035 \ge (5^6 + 625)/2 = 8125$).
   - Block induction for all $t \ge 6$ using $B_t = \{(5^t + 5^b)/2 : 0 \le b \le 4\} \subset (5^t/2, 5^{t+1}/2)$ adds $(5^{t+1} + 781)/2 > (5^{t+1} + 625)/2$ per step, proving all $n \ge 256$.
   - Any $5^a + 5^b \le 510$ has $a, b \le 3$, so its half-value lies in $\{1, 3, 5, 13, 15, 25, 63, 65, 75, 125\}$; exact bitset verification rules out all 14 exceptions.

2. **Conjecture 1(i), Part B (`3^a + 3^b`):**
   Every positive even integer $2n$ ($n \ge 1$) is a sum of distinct elements of $\{3^a + 3^b : a, b \ge 0\}$.
   - The 6 half-values $\{1, 2, 3, 5, 6, 9\}$ ($0 \le b \le a \le 2$) cover $[1, 25]$ (span $25 \ge (3^3 + 9)/2 = 18$).
   - Block induction for all $t \ge 3$ using $B_t = \{(3^t + 3^b)/2 : 0 \le b \le 2\}$ adds $(3^{t+1} + 13)/2 > (3^{t+1} + 9)/2$ per step.

3. **Conjecture 1(ii), Part A (`3^a + 7^b`):**
   Every positive even integer $2n$ ($n \ge 1$) is a sum of distinct elements of $\{3^a + 7^b : a, b \ge 0\}$.
   - The 11 distinct half-values for $0 \le a \le 3, 0 \le b \le 2$, namely $\{1, 2, 4, 5, 8, 14, 17, 25, 26, 29, 38\}$, cover $[1, 168]$ (span $168 \ge (3^4 + 49)/2 = 65$).
   - Block induction for all $t \ge 4$ using $B_t = \{(3^t + 7^b)/2 : 0 \le b \le 2\}$ adds $(3^{t+1} + 57)/2 > (3^{t+1} + 49)/2$ per step.

Note: The second sentence of Conjecture 1(ii) (the $d$-complete antichain condition for $3^a + 5^b$) and Conjectures 2–3 remain open.

---

## Verification

- **Python verification & OEIS data reproduction:**
  ```powershell
  python conjectures/A362861/verify.py
  ```
- **Zero-dependency Lean 4 formal proof (Lean 4.36.0, zero `sorry`, standard axioms only):**
  ```powershell
  lean conjectures/A362861/A362861.lean
  ```
