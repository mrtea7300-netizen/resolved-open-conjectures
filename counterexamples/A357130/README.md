# A357130 — Counterexamples to Conjecture 2(ii) (Wang–Sun E-JC 2026 Conjecture 1(1))

**Status:** `counterexample (confirmed)` (formally proved in zero-dependency Lean 4, zero `sorry`)  
**Primary sources:**
- OEIS [A357130](https://oeis.org/A357130) (read from `oeis/oeisdata`, revision `#52`, Nov 05 2025)
- Han Wang and Zhi-Wei Sun, *"On Two New Kinds of Restricted Sumsets"*, *The Electronic Journal of Combinatorics* **33(2)** (2026), #P2.64, p. 2 ([doi:10.37236/13831](https://doi.org/10.37236/13831); preprint [arXiv:2210.12044](https://arxiv.org/abs/2210.12044)).

---

## Verbatim Conjecture Statement

From `A357130.seq`:
> `a(n) = 2*n - (-1)^n*(1+(n mod 2)).`
>
> **Conjecture 2:** Let $G$ be an additive group with $|G| > 1$, and let $p(G)$ be the minimum of those orders of nonzero elements of $G$ (which is the positive infinity if each nonzero element of $G$ has infinite order). Let $A_1, \dots, A_n$ ($n > 1$) be finite subsets of $G$ with $|A_i| > 1$ for all $i = 1..n$.
> - **(i)** For the set $C = \{a_1 + \dots + a_n : a_1, \dots, a_n \text{ are elements of } A_1, \dots, A_n \text{ respectively, with } a_i \ne a_{i+1} \text{ for all } 0 < i < n, \text{ and } a_n \ne a_1\}$, we have $|C| \ge \min\{p(G), |A_1| + \dots + |A_n| - a(n)\}$.
> - **(ii)** For the set $D = \{a_1 + \dots + a_n : a_1, \dots, a_n \text{ are elements of } A_1, \dots, A_n \text{ respectively, with } a_i \ne a_{i+1} \text{ for all } 0 < i < n\}$, we have $|D| \ge \min\{p(G), |A_1| + \dots + |A_n| - 2n + 1 + (n \bmod 2)\}$.

In Wang & Sun (*E-JC* **33(2)** (2026), #P2.64, p. 2), this is stated verbatim as **Conjecture 1 (Sun)**, equations **(1)** and **(2)**, writing $L(A_1, \dots, A_n)$ for $D$.

---

## Disproof of Conjecture 2(ii) / Wang–Sun Conjecture 1(1)

We give two independent elementary counterexamples showing that Conjecture 2(ii) fails both in torsion-free groups (for **every odd $n \ge 3$**) and in finite prime fields (even when $|A_2| > |A_1|, |A_3|$).

### 1. Universal counterexample ($n = 3$, every additive group $G$ with $p(G) \ge 4$)

Let $G$ be any additive group with $p(G) \ge 4$ (including $G = \mathbb{Z}$, $G = \mathbb{R}$, and $G = \mathbb{Z}/p\mathbb{Z}$ for every prime $p \ge 5$). Pick any nonzero $g \in G$ (so $0, g, 2g$ are pairwise distinct) and take
$$A_1 = \{0, g, 2g\}, \qquad A_2 = \{0, 2g\}, \qquad A_3 = \{0, g, 2g\}.$$
Then $|A_1| = 3$, $|A_2| = 2$, $|A_3| = 3$ (all $> 1$), and every valid triple $(a_1, a_2, a_3)$ with $a_1 \ne a_2$ and $a_2 \ne a_3$ satisfies:
- if $a_2 = 0$, then $a_1, a_3 \in \{g, 2g\}$, so $a_1 + a_2 + a_3 \in \{2g, 3g, 4g\}$;
- if $a_2 = 2g$, then $a_1, a_3 \in \{0, g\}$, so $a_1 + a_2 + a_3 \in \{2g, 3g, 4g\}$.

Hence
$$|L(A_1, A_2, A_3)| = |\{2g, 3g, 4g\}| = 3 < 4 = \min\{p(G),\, 3 + 2 + 3 - 2\cdot 3 + 1 + (3 \bmod 2)\}.$$

### 2. Infinite family for every odd $n = 2m + 1 \ge 3$ in $\mathbb{Z}$ (and any torsion-free group)

For any integer $m \ge 1$ and $n = 2m + 1$, take in $G = \mathbb{Z}$:
$$A_1 = \{0, 1, 2\}, \quad A_2 = \{0, 2\}, \quad A_3 = \{0, 1, 2\}, \quad A_{2j} = A_{2j+1} = \{3j, 3j+1\} \quad (2 \le j \le m).$$
Every set has size $\ge 2$, and for each $j \in \{2, \dots, m\}$, the constraint $a_{2j} \ne a_{2j+1}$ forces $\{a_{2j}, a_{2j+1}\} = \{3j, 3j+1\}$, contributing the constant sum $6j + 1$, while $A_{2j-1} \cap A_{2j} = \emptyset$ makes $a_{2j-1} \ne a_{2j}$ automatic. Therefore
$$L(A_1, \dots, A_{2m+1}) = \{C_m + 2,\, C_m + 3,\, C_m + 4\}, \qquad C_m = \sum_{j=2}^{m}(6j+1) = 3m^2 + 4m - 7,$$
so $|L(A_1, \dots, A_{2m+1})| = 3$, whereas the conjectured lower bound is
$$\sum_{i=1}^{2m+1} |A_i| - 2(2m+1) + 1 + ((2m+1) \bmod 2) = (4m + 4) - 4m = 4 > 3.$$

### 3. Modular counterexample with $|A_2| > |A_1|, |A_3|$ ($n = 3$, $G = \mathbb{Z}/5\mathbb{Z}$)

Even when the middle set is strictly larger than the outer sets, Conjecture 2(ii) still fails in $G = \mathbb{Z}/5\mathbb{Z}$ ($p(G) = 5$):
$$A_1 = \{0, 1\}, \qquad A_2 = \{0, 1, 2, 3, 4\}, \qquad A_3 = \{2, 4\}.$$
Here $|A_1| = 2$, $|A_2| = 5$, $|A_3| = 2$, so the conjectured lower bound is $\min\{5, 2+5+2-4\} = 5$. Yet $4 \notin L(A_1, A_2, A_3)$: for every $(a_1, a_3) \in A_1 \times A_3$, the unique $a_2 \in \mathbb{Z}/5\mathbb{Z}$ with $a_1 + a_2 + a_3 \equiv 4 \pmod 5$ satisfies $a_2 \in \{a_1, a_3\}$:
- $(0, 2) \implies a_2 = 2 = a_3$,
- $(0, 4) \implies a_2 = 0 = a_1$,
- $(1, 2) \implies a_2 = 1 = a_1$,
- $(1, 4) \implies a_2 = 4 = a_3$.

Thus $L(A_1, A_2, A_3) = \{0, 1, 2, 3\}$ has cardinality $4 < 5$.

### Connection to Wang–Sun (2026), Lemma 10

In Wang & Sun (*E-JC* **33(2)** (2026), #P2.64, Lemma 10, eq. (12)), the polynomial-method coefficient for $n = 3$ is
$$[x_1^{k_1} x_2^{k_2} x_3^{k_3}](x_1 - x_2)(x_2 - x_3)(x_1 + x_2 + x_3)^{k_1+k_2+k_3-2} = \frac{(k_1+k_2+k_3-2)!}{k_1!k_2!k_3!}\bigl(k_2 + (k_2 - k_1)(k_3 - k_2)\bigr)$$
where $k_i = |A_i| - 1$. Both counterexamples sit precisely on the vanishing locus of $k_2 + (k_2 - k_1)(k_3 - k_2)$:
- $(|A_1|, |A_2|, |A_3|) = (3, 2, 3) \implies (k_1, k_2, k_3) = (2, 1, 2) \implies 1 + (-1)(1) = 0$;
- $(|A_1|, |A_2|, |A_3|) = (2, 5, 2)$ in $\mathbb{F}_5 \implies (k_1, k_2, k_3) = (1, 4, 1) \implies 4 + (3)(-3) = -5 \equiv 0 \pmod 5$.

Note that Wang & Sun's **Theorem 2** (which requires $|A_2| - |A_1| \in \{0, 1\}$ in part (i) and $2 \le |A_1| \le |A_2| \le |A_3|$ in part (ii)) is unaffected; our counterexamples show that removing those size-ordering hypotheses from Theorem 2 (as in Conjecture 1(1) / A357130 Conjecture 2(ii)) is impossible. Conjecture 1 (where $A_1 = \dots = A_n = A$) and Conjecture 2(i) remain open in general.

---

## Verification

- **Python verification & OEIS data reproduction:**
  ```powershell
  python conjectures/A357130/verify_counterexample.py
  ```
- **Zero-dependency Lean 4 formal proof (Lean 4.36.0, zero `sorry`, standard axioms only):**
  ```powershell
  lean conjectures/A357130/A357130.lean
  ```
