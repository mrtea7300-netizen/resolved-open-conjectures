# Proof of Completeness for OEIS A093669, A093670, and A025052

**Status:** `proof (draft)`, assuming the Riemann Hypothesis for Dirichlet $L$-functions (`DirichletLNonvanishingRightOfHalf`), which has a Lean-checked proof (Alpöge 2026, not yet refereed). Only real quadratic Dirichlet $L$-functions $L(s, \chi_D)$ are used.

---

## 1. Notation

For every integer $N \ge 1$, define:
- $\mathcal{R}_{\mathrm{strict}}(N) = \{(a, b, c) \in \mathbb{Z}^3 : 0 < a < b < c,\; ab + bc + ca = N\}$, $r_{\mathrm{strict}}(N) = |\mathcal{R}_{\mathrm{strict}}(N)|$;
- $\mathcal{R}_{\mathrm{eq}}(N) = \{(a, b, c) \in \mathbb{Z}^3 : 1 \le a \le b \le c,\; (a = b \lor b = c),\; ab + bc + ca = N\}$, $r_{\mathrm{eq}}(N) = |\mathcal{R}_{\mathrm{eq}}(N)|$;
- $r_{\mathrm{all}}(N) = r_{\mathrm{strict}}(N) + r_{\mathrm{eq}}(N)$.

Thus:
- $N \in \mathrm{A025052} \iff r_{\mathrm{all}}(N) = 0$;
- $N \in \mathrm{A093669} \iff r_{\mathrm{strict}}(N) = 1$;
- $N \in \mathrm{A093670} \iff r_{\mathrm{all}}(N) = 1$.

---

## 2. Exact Bijection with Reduced Binary Quadratic Forms

Let $\mathcal{F}^+(-4N) = \{(A, 2k, C) \in \mathbb{Z}^3 : AC - k^2 = N,\; 0 < 2k < A < C\}$.

**Lemma 1 (Bijection; formalized in `A093669.lean`).**
The map $\Phi(a, b, c) = (a + b,\; 2a,\; a + c)$ is a bijection $\mathcal{R}_{\mathrm{strict}}(N) \xrightarrow{\sim} \mathcal{F}^+(-4N)$ with inverse $\Psi(A, 2k, C) = (k,\; A - k,\; C - k)$.

*Proof.*
- If $(a, b, c) \in \mathcal{R}_{\mathrm{strict}}(N)$, then $0 < a < b < c$ gives $0 < 2a < a + b < a + c$, and $(a + b)(a + c) - a^2 = ab + bc + ca = N$, so $\Phi(a, b, c) \in \mathcal{F}^+(-4N)$.
- If $(A, 2k, C) \in \mathcal{F}^+(-4N)$, then $0 < 2k < A < C$ gives $0 < k < A - k < C - k$, and $k(A - k) + (A - k)(C - k) + (C - k)k = AC - k^2 = N$, so $\Psi(A, 2k, C) \in \mathcal{R}_{\mathrm{strict}}(N)$.
- Clearly $\Psi(\Phi(a, b, c)) = (a, b, c)$ and $\Phi(\Psi(A, 2k, C)) = (A, 2k, C)$. $\blacksquare$

---

## 3. Content Decomposition & Class-Group Reduction

Recall that a positive-definite binary quadratic form $A x^2 + B xy + C y^2$ of discriminant $\Delta = B^2 - 4AC < 0$ is **reduced** if $-A < B \le A \le C$ and $B \ge 0$ whenever $A = C$. A reduced form is **ambiguous** (of order dividing $2$ in the class group when primitive) if and only if $B = 0$, $B = A$, or $A = C$. Every non-ambiguous reduced form has $0 < |B| < A < C$, so non-ambiguous reduced forms come in conjugate pairs $\{(A, +|B|, C), (A, -|B|, C)\}$ of equal cardinality.

**Lemma 2 (Content Decomposition).**
For every $N \ge 1$,
$$r_{\mathrm{strict}}(N) = \sum_{\substack{d \ge 1 \\ d^2 \mid 4N,\; -4N/d^2 \equiv 0, 1 \pmod 4}} \frac{h(-4N/d^2) - g(-4N/d^2)}{2},$$
where $h(\Delta) = |\mathrm{Cl}(\mathcal{O}_\Delta)|$ is the number of primitive reduced forms of discriminant $\Delta < 0$, and $g(\Delta) = |\mathrm{Cl}(\mathcal{O}_\Delta)[2]|$ is the number of primitive ambiguous reduced forms of discriminant $\Delta$.

*Proof.* For each $(A, 2k, C) \in \mathcal{F}^+(-4N)$, let $d = \gcd(A, 2k, C) \ge 1$ and write $(A, 2k, C) = d(A', B', C')$. Then $\gcd(A', B', C') = 1$, $0 < B' < A' < C'$, and $(B')^2 - 4A'C' = -4N/d^2 =: \Delta' \equiv 0, 1 \pmod 4$. Conversely, if $(A', B', C')$ is a primitive reduced non-ambiguous form of discriminant $\Delta' = -4N/d^2$ with $B' > 0$, then $d^2 (B')^2 = d^2 \Delta' + 4d^2 A'C' = -4N + 4(dA')(dC') \equiv 0 \pmod 4$, so $2 \mid dB'$, and $(dA', dB', dC') \in \mathcal{F}^+(-4N)$. Since primitive non-ambiguous reduced forms of discriminant $\Delta'$ pair up under $B' \leftrightarrow -B'$, there are exactly $(h(\Delta') - g(\Delta'))/2$ with $B' > 0$. Summing over $d$ gives the formula. $\blacksquare$

**Theorem 1 (Reduction for A093669).**
For every $N \ge 1$, if $r_{\mathrm{strict}}(N) = 1$, then $h(-4N) \in \{3, 4\}$ (specifically $(h(-4N), g(-4N)) \in \{(3, 1), (4, 2)\}$).

*Proof.* Every summand $(h(\Delta') - g(\Delta'))/2$ in Lemma 2 is a nonnegative integer. Suppose for contradiction that the $d = 1$ summand is $0$, i.e., $h(-4N) = g(-4N)$. Then every element of $\mathrm{Cl}(\mathcal{O}_{-4N})$ has order dividing $2$. For any $d > 1$ with $d^2 \mid 4N$ and $\Delta' = -4N/d^2 \equiv 0, 1 \pmod 4$, $\mathcal{O}_{-4N} \subseteq \mathcal{O}_{\Delta'}$ is a suborder of index $d$, and the extension map $[\mathfrak{a}] \mapsto [\mathfrak{a}\mathcal{O}_{\Delta'}]$ is a **surjective** group homomorphism $\mathrm{Cl}(\mathcal{O}_{-4N}) \twoheadrightarrow \mathrm{Cl}(\mathcal{O}_{\Delta'})$ (D. A. Cox, *Primes of the Form $x^2 + ny^2$*, 2nd ed., Prop. 7.20 & Thm. 7.24). Hence every quotient $\mathrm{Cl}(\mathcal{O}_{\Delta'})$ also has exponent dividing $2$, so $h(\Delta') = g(\Delta')$ for every $d$, giving $r_{\mathrm{strict}}(N) = 0 \ne 1$, contradiction.

Therefore the $d = 1$ summand must equal $1$ (and all $d > 1$ summands equal $0$), so $h(-4N) - g(-4N) = 2$. Since $\mathrm{Cl}(\mathcal{O}_{-4N})[2]$ is a subgroup of $\mathrm{Cl}(\mathcal{O}_{-4N})$, Lagrange's theorem gives $g(-4N) \mid h(-4N)$, hence $g(-4N) \mid (h(-4N) - g(-4N)) = 2$. Thus $g(-4N) \in \{1, 2\}$, so $(h(-4N), g(-4N)) \in \{(3, 1), (4, 2)\}$. $\blacksquare$

---

## 4. Complete Finite Determination of A093669, A093670, and A025052

### 4.1 Complete List of Orders with $h(-4N) \in \{3, 4\}$ (A093669)

Write $-4N = f^2 D_0$ with $D_0 < 0$ a fundamental discriminant and conductor $f \ge 1$. By Cox, Theorem 7.24:
$$h(-4N) = \frac{h(D_0) \cdot f}{u} \prod_{p \mid f} \left(1 - \left(\frac{D_0}{p}\right)\frac{1}{p}\right), \qquad u = \begin{cases} 3 & D_0 = -3,\; f > 1,\\ 2 & D_0 = -4,\; f > 1,\\ 1 & \text{otherwise.} \end{cases}$$
Since $h(D_0) \mid h(-4N)$, we have $h(D_0) \le 4$. Moreover, since $1 - \left(\frac{D_0}{p}\right)\frac{1}{p} \ge 1 - \frac{1}{p}$, we have $h(-4N) \ge h(D_0)\varphi(f)/u \ge \varphi(f)/3$, so $h(-4N) \le 4 \implies \varphi(f) \le 12 \implies f \le 42$.

The complete list of imaginary quadratic fundamental discriminants $D_0 < 0$ with $h(D_0) \le 4$ consists of **97** discriminants ($9$ with $h = 1$, max $|D_0| = 163$; $18$ with $h = 2$, max $|D_0| = 427$; $16$ with $h = 3$, max $|D_0| = 907$; $54$ with $h = 4$, max $|D_0| = 1555$):
- **Unconditionally:** M. Watkins, *Class numbers of imaginary quadratic fields*, Math. Comp. 73 (2004), 907–938 (and S. Arno, *The imaginary quadratic fields of class number 4*, Acta Arith. 60 (1992), 321–334).
- **Directly under Dirichlet GRH (`DirichletLNonvanishingRightOfHalf`):** By Lamzouri–Li–Soundararajan (*Math. Comp.* 84 (2015), `arXiv:1309.3595`, Theorem 1.5), for every primitive real character $\chi_{D_0}$ with $|D_0| \ge 10^{10}$,
  $$L(1, \chi_{D_0}) \ge \frac{\pi^2}{12 e^\gamma \left(\log\log|D_0| - \log 2 + \tfrac{1}{2} + \tfrac{1}{\log\log|D_0|} + \tfrac{14\log\log|D_0|}{\log|D_0|}\right)},$$
  which gives $h(D_0) = \frac{\sqrt{|D_0|}}{\pi} L(1, \chi_{D_0}) > 4 \cdot 10^3 \gg 4$ for all $|D_0| \ge 10^{10}$ (and direct class-number computation up to $|D_0| < 10^{10}$ — or Watkins 2004 — yields the exact 97 discriminants, all with $|D_0| \le 1555$).

Enumerating all pairs $(D_0, f)$ with $h(D_0) \le 4$, $1 \le f \le 42$, $4 \mid f^2 D_0$, and $h(f^2 D_0) \in \{3, 4\}$ (`verify.py`) yields exactly **52** candidate integers $N$ (with $\max N = 253$). Testing $r_{\mathrm{strict}}(N) = 1$ on these 52 integers (`verify.py` and `A093669.lean`) yields **exactly the 23 listed terms of A093669**:
$$\{11, 14, 17, 19, 20, 27, 32, 34, 36, 43, 46, 49, 52, 64, 67, 73, 82, 97, 100, 142, 148, 163, 193\}.$$

### 4.2 Complete Lists for A025052 and A093670 (assuming Dirichlet GRH)

By Lemma 2, $r_{\mathrm{strict}}(N) = 0 \iff h(-4N) = g(-4N) \iff \mathrm{Cl}(\mathcal{O}_{-4N})$ has exponent dividing $2$, i.e., $N$ is an **Euler idoneal number** (OEIS A000926).
Assuming Dirichlet GRH (`DirichletLNonvanishingRightOfHalf` for real quadratic Dirichlet $L$-functions $L(s, \chi_D)$), P. J. Weinberger (*Acta Arith.* 22 (1973), 117–124, Theorem 1; see also E. Kani, *Idoneal numbers and some generalizations*, Ann. Sci. Math. Québec 35 (2011), Cor. 23) proves that Euler's list of **65 idoneal numbers** ($\max = 1848$) is complete.

- **A025052 ($r_{\mathrm{all}}(N) = 0$):** Since $r_{\mathrm{all}}(N) = r_{\mathrm{strict}}(N) + r_{\mathrm{eq}}(N) = 0 \implies r_{\mathrm{strict}}(N) = 0$, every term of A025052 belongs to Euler's 65 idoneal numbers. Exact evaluation of $r_{\mathrm{all}}(N)$ on all 65 idoneal numbers (`verify.py` and `A093669.lean`) gives **exactly the 18 listed terms of A025052** (max $462$).
- **A093670 ($r_{\mathrm{all}}(N) = 1$):** Since $r_{\mathrm{strict}}(N) + r_{\mathrm{eq}}(N) = 1$, either:
  - **Case A:** $r_{\mathrm{strict}}(N) = 1$ and $r_{\mathrm{eq}}(N) = 0$. By §4.1, $N$ belongs to the 23 terms of A093669; checking $r_{\mathrm{eq}}(N) = 0$ yields the 5 terms $\{14, 34, 46, 82, 142\}$.
  - **Case B:** $r_{\mathrm{strict}}(N) = 0$ and $r_{\mathrm{eq}}(N) = 1$. Then $N$ is one of Euler's 65 idoneal numbers; checking $r_{\mathrm{eq}}(N) = 1$ yields the 11 terms $\{3, 5, 7, 8, 9, 12, 13, 16, 25, 28, 37\}$.
  Combining Cases A and B gives **exactly the 16 listed terms of A093670**:
  $$\{3, 5, 7, 8, 9, 12, 13, 14, 16, 25, 28, 34, 37, 46, 82, 142\}. \qquad \blacksquare$$
