# A362743 — Complete Lean 4 Proof of Conjecture 1 (First Part)

**Status:** `proof (formalized)` (zero-dependency Lean 4.36.0, zero `sorry`, standard axioms only)  
**Primary source:** OEIS [A362743](https://oeis.org/A362743) (read from `oeis/oeisdata`, revision `#35`, Nov 02 2023).

---

## Verbatim Conjecture Statement

From `A362743.seq`:
> `Positive integers which cannot be written as a sum of distinct numbers of the form 4^a + 5^b (a,b >= 0).`
>
> `1, 3, 4, 10, 12, 18`
>
> **Conjecture 1:** The only terms of the current sequence are `1, 3, 4, 10, 12, 18`. Moreover, any positive integer not among `1, 3, 4, 8, 10, 12, 13, 18, 25, 39, 42` can be written as a sum of numbers of the form $4^a + 5^b$ ($a, b \ge 0$) with no one summand dividing another.

---

## Proof Summary (Conjecture 1, First Part)

We prove that for every integer $n \ge 1$:
$$n \text{ is a sum of distinct numbers of the form } 4^a + 5^b \; (a, b \ge 0) \iff n \notin \{1, 3, 4, 10, 12, 18\}.$$

1. **Base interval ($[19, 531]$):**
   - The 9 distinct elements of $\{4^a + 5^b : 0 \le a \le 2,\, 0 \le b \le 2\}$,
     $$L_0 = \{2, 5, 6, 9, 17, 21, 26, 29, 41\},$$
     have subset sums covering every integer in $[19, 137]$ (span $119$), as well as every integer in $\{2, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17\}$.
   - Adjoining the four elements of block $t = 3$, namely $4^3 + 1 = 65$, $4^3 + 5 = 69$, $4^3 + 25 = 89$, and $4^3 + 125 = 189$ (each $\le$ the current span), extends the covered interval via Brown's interval-merging lemma to $[19, 531]$, which has span $513 \ge 4^4 + 125 = 381$.

2. **Block induction ($t \ge 4$):**
   For each $t \ge 4$, form the 4-element block
   $$B_t = \{4^t + 1,\; 4^t + 5,\; 4^t + 25,\; 4^t + 125\} \subset (4^t, 4^{t+1}).$$
   Since $125 < 3 \cdot 4^t$, all elements of $B_t$ are strictly greater than $4^t$ and strictly less than $4^{t+1}$, so the blocks $B_4, B_5, \dots$ are pairwise disjoint and disjoint from the base list ($\max = 189 < 256 = 4^4$).
   If the chain up to $t - 1$ covers $[19, B]$ with span $B - 18 \ge 4^t + 125$, then adjoining the four elements of $B_t$ one by one extends the covered interval to $[19, B + 4^{t+1} + 156]$, whose new span satisfies
   $$(B + 4^{t+1} + 156) - 18 \ge 4^{t+1} + 156 > 4^{t+1} + 125.$$
   By induction, every integer $n \ge 19$ is a sum of distinct numbers of the form $4^a + 5^b$.

3. **Exact exclusion of $\{1, 3, 4, 10, 12, 18\}$:**
   Any element $4^a + 5^b \le 18$ must have $a \le 2$ and $b \le 1$, hence belongs to $\{2, 5, 6, 9, 17\}$. Exhaustive subset-sum verification over $\{2, 5, 6, 9, 17\}$ shows none of $\{1, 3, 4, 10, 12, 18\}$ is a subset sum.

Note: The second sentence of Conjecture 1 (the antichain / $d$-complete condition that no summand divides another) and Conjectures 2–3 remain open.

---

## Verification

- **Python verification & OEIS data reproduction:**
  ```powershell
  python conjectures/A362743/verify.py
  ```
- **Zero-dependency Lean 4 formal proof (Lean 4.36.0, zero `sorry`, standard axioms only):**
  ```powershell
  lean conjectures/A362743/A362743.lean
  ```
