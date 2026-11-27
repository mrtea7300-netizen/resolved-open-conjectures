# Proof of Conjectures 1, 2, and 3 of OEIS A360278

## 1. Exact Statement (verbatim from OEIS A360278)

Let $L(n)$ denote the Lucas numbers (`A000032`: $L(0)=2, L(1)=1, L(m+1)=L(m)+L(m-1)$), let $F(n)$ denote the Fibonacci numbers (`A000045`: $F(0)=0, F(1)=1, F(m+1)=F(m)+F(m-1)$), and let $\delta_{jk}$ (written `d(j,k)` in OEIS) be the Kronecker delta ($1$ if $j=k$, $0$ otherwise). The sequence `A360278` is defined for $n \ge 1$ by
$$a(n) = \det\bigl[L(j+k) + \delta_{jk}\bigr]_{1 \le j,k \le n}.$$

> **Conjecture 1:** Let $v(0) = 2$, $v(1) = A$, and $v(n+1) = A v(n) + v(n-1)$ for $n > 0$. Then
> $$A^2 \det\bigl[v(j+k) + \delta_{jk}\bigr]_{1 \le j,k \le n} = v(n+1)^2 - (A^2 + 4)(n \bmod 2)$$
> for any positive integer $n$. In particular, $a(n) = L(n+1)^2 - 5(n \bmod 2)$ for all $n > 0$.
>
> **Conjecture 2:** Let $v(0) = 2$, $v(1) = A$, and $v(n+1) = A v(n) - v(n-1)$ for $n > 0$. Then
> $$\det\bigl[v(j+k) + \delta_{jk}\bigr]_{1 \le j,k \le n} = u(n+1)^2 - n^2$$
> for any positive integer $n$, where $u(0) = 0$, $u(1) = 1$, and $u(n+1) = A u(n) - u(n-1)$ for all $n > 0$.
>
> **Conjecture 3:** Let $F(n)$ denote the Fibonacci number A000045(n). Then, for any positive integer $n$, we have
> $$\det\bigl[F(j+k) + \delta_{jk}\bigr]_{1 \le j,k \le n} = F(n+1)^2 + (n \bmod 2).$$

Here $(n \bmod 2) \in \{0,1\}$ is the remainder of $n$ upon division by $2$. Conjectures 1 and 2 hold identically in the polynomial ring $\mathbb{Z}[A]$ (hence for every $A \in \mathbb{C}$, including degenerate values $A \in \{0, \pm 2, \pm 2i\}$).

*(Context: In `arXiv:2302.08315v2`, Zhi-Wei Sun proved Conjectures 1 and 3 for even $n$, and explicitly posed the odd-$n$ cases of Conjectures 1 and 3 and all $n \ge 1$ of Conjecture 2 as Conjectures 4.2–4.4. The proof below settles all three conjectures uniformly for all $n \ge 1$.)*

---

## 2. Preliminaries: Rank-2 Matrix Determinant Lemma

**Lemma 1 (Sylvester's Determinant Identity).** *Let $U, V \in \mathbb{C}^{n \times 2}$ be any $n \times 2$ complex matrices. Then*
$$\det(I_n + U V^T) = \det(I_2 + V^T U).$$

*Proof.* Consider the $(n+2) \times (n+2)$ block matrices
$$P = \begin{pmatrix} I_n & -U \\ 0 & I_2 \end{pmatrix}, \qquad M = \begin{pmatrix} I_n & U \\ -V^T & I_2 \end{pmatrix}.$$
Direct block multiplication gives two block-triangular matrices:
$$P M = \begin{pmatrix} I_n + U V^T & 0 \\ -V^T & I_2 \end{pmatrix}, \qquad M P = \begin{pmatrix} I_n & 0 \\ -V^T & I_2 + V^T U \end{pmatrix}.$$
Since $\det P = 1$, taking determinants yields
$$\det(I_n + U V^T) = \det(P M) = \det(M) = \det(M P) = \det(I_2 + V^T U). \qquad \square$$

**Lemma 2 (Reduction of $[w_{j+k} + \delta_{jk}]$ to a $2 \times 2$ determinant).** *Let $\alpha, \beta, c_1, c_2 \in \mathbb{C}$, and set $w_m = c_1 \alpha^m + c_2 \beta^m$ for $m \ge 0$. For every integer $n \ge 1$,*
$$\det\bigl[w_{j+k} + \delta_{jk}\bigr]_{1 \le j,k \le n} = 1 + c_1 S_\alpha + c_2 S_\beta + c_1 c_2 \bigl(S_\alpha S_\beta - S_{\alpha\beta}^2\bigr),$$
*where*
$$S_\alpha = \sum_{j=1}^n \alpha^{2j}, \qquad S_\beta = \sum_{j=1}^n \beta^{2j}, \qquad S_{\alpha\beta} = \sum_{j=1}^n (\alpha\beta)^j.$$

*Proof.* Define $U, V \in \mathbb{C}^{n \times 2}$ by $U_{j,1} = c_1 \alpha^j$, $U_{j,2} = c_2 \beta^j$, $V_{k,1} = \alpha^k$, $V_{k,2} = \beta^k$ for $1 \le j,k \le n$. Then
$$(U V^T)_{j,k} = c_1 \alpha^j \alpha^k + c_2 \beta^j \beta^k = w_{j+k},$$
so $[w_{j+k} + \delta_{jk}]_{1 \le j,k \le n} = I_n + U V^T$. Moreover,
$$V^T U = \begin{pmatrix} c_1 \sum_{j=1}^n \alpha^{2j} & c_2 \sum_{j=1}^n (\alpha\beta)^j \\ c_1 \sum_{j=1}^n (\alpha\beta)^j & c_2 \sum_{j=1}^n \beta^{2j} \end{pmatrix} = \begin{pmatrix} c_1 S_\alpha & c_2 S_{\alpha\beta} \\ c_1 S_{\alpha\beta} & c_2 S_\beta \end{pmatrix}.$$
By Lemma 1,
$$\det(I_n + U V^T) = \det\begin{pmatrix} 1 + c_1 S_\alpha & c_2 S_{\alpha\beta} \\ c_1 S_{\alpha\beta} & 1 + c_2 S_\beta \end{pmatrix} = (1 + c_1 S_\alpha)(1 + c_2 S_\beta) - c_1 c_2 S_{\alpha\beta}^2,$$
which expands to the stated formula. $\square$

---

## 3. Proof of Conjecture 1

Fix $n \ge 1$. From $v(0) = 2$, $v(1) = A$, and $v(m+1) = A v(m) + v(m-1)$, every $v(m)$ is a polynomial in $A$ with integer coefficients, so both sides of Conjecture 1 are polynomials in $A \in \mathbb{C}$. Therefore it suffices to prove the identity for all $A \in \mathbb{C} \setminus \{0, 2i, -2i\}$ (an infinite set).

Let $A \in \mathbb{C} \setminus \{0, 2i, -2i\}$, and let $\alpha, \beta \in \mathbb{C}$ be the two roots of $t^2 - A t - 1 = 0$. Then
$$\alpha + \beta = A, \qquad \alpha\beta = -1, \qquad (\alpha - \beta)^2 = A^2 + 4 \ne 0.$$
In particular $\alpha \ne \beta$, and since $\alpha^2 - 1 = \alpha(\alpha - \alpha^{-1}) = \alpha(\alpha + \beta) = A\alpha \ne 0$ (as $\alpha\beta = -1 \implies \alpha \ne 0$ and $A \ne 0$), we have $\alpha^2 \ne 1$ and symmetrically $\beta^2 - 1 = A\beta \ne 0$.

By Binet's formula, $v(m) = \alpha^m + \beta^m$ for all $m \ge 0$ (verified at $m=0$: $\alpha^0+\beta^0=2$; $m=1$: $\alpha+\beta=A$; and both sides satisfy $x_{m+1} = A x_m + x_{m-1}$). Applying Lemma 2 with $c_1 = c_2 = 1$, we compute the three geometric sums:
$$S_\alpha = \frac{\alpha^2(\alpha^{2n} - 1)}{\alpha^2 - 1} = \frac{\alpha^2(\alpha^{2n} - 1)}{A\alpha} = \frac{\alpha(\alpha^{2n} - 1)}{A}, \qquad S_\beta = \frac{\beta(\beta^{2n} - 1)}{A},$$
$$S_{\alpha\beta} = \sum_{j=1}^n (-1)^j = -(n \bmod 2), \qquad S_{\alpha\beta}^2 = (n \bmod 2).$$
Multiplying Lemma 2 by $A^2$, we obtain
$$A^2 \det\bigl[v(j+k) + \delta_{jk}\bigr]_{1\le j,k\le n} = A^2 + A^2(S_\alpha + S_\beta) + A^2 S_\alpha S_\beta - A^2 S_{\alpha\beta}^2.$$
We simplify each piece using $\alpha + \beta = A$ and $\alpha\beta = -1$:
1. $A^2(S_\alpha + S_\beta) = A(\alpha^{2n+1} + \beta^{2n+1} - \alpha - \beta) = A(\alpha^{2n+1} + \beta^{2n+1}) - A^2$.
   Substituting $A = \alpha + \beta$ into the first term gives
   $$A(\alpha^{2n+1} + \beta^{2n+1}) = \alpha^{2n+2} + \beta^{2n+2} + \alpha\beta(\alpha^{2n} + \beta^{2n}) = \alpha^{2n+2} + \beta^{2n+2} - (\alpha^{2n} + \beta^{2n}).$$
   Hence $A^2 + A^2(S_\alpha + S_\beta) = \alpha^{2n+2} + \beta^{2n+2} - (\alpha^{2n} + \beta^{2n})$.
2. Since $(\alpha\beta)^{2n} = (-1)^{2n} = 1$,
   $$A^2 S_\alpha S_\beta = (\alpha\beta)(\alpha^{2n} - 1)(\beta^{2n} - 1) = -\bigl(1 - \alpha^{2n} - \beta^{2n} + 1\bigr) = (\alpha^{2n} + \beta^{2n}) - 2.$$
3. Adding (1) and (2), the $\alpha^{2n} + \beta^{2n}$ terms cancel identically:
   $$A^2 \det\bigl[v(j+k) + \delta_{jk}\bigr]_{1\le j,k\le n} = \alpha^{2n+2} + \beta^{2n+2} - 2 - A^2(n \bmod 2).$$

Finally, $v(n+1)^2 = (\alpha^{n+1} + \beta^{n+1})^2 = \alpha^{2n+2} + \beta^{2n+2} + 2(\alpha\beta)^{n+1} = \alpha^{2n+2} + \beta^{2n+2} + 2(-1)^{n+1}$.
Since $(-1)^{n+1} = -1 + 2(n \bmod 2)$ for every integer $n$ (check: $-1$ for $n$ even, $+1$ for $n$ odd), we have
$$-2 = 2(-1)^{n+1} - 4(n \bmod 2),$$
and therefore
$$A^2 \det\bigl[v(j+k) + \delta_{jk}\bigr]_{1\le j,k\le n} = v(n+1)^2 - 4(n \bmod 2) - A^2(n \bmod 2) = v(n+1)^2 - (A^2 + 4)(n \bmod 2).$$
Because this polynomial identity holds for all $A \in \mathbb{C} \setminus \{0, \pm 2i\}$, it holds in $\mathbb{Z}[A]$ and thus for every $A \in \mathbb{C}$.

Specializing to $A = 1$ gives $v(m) = L(m)$ and
$$a(n) = \det\bigl[L(j+k) + \delta_{jk}\bigr]_{1\le j,k\le n} = L(n+1)^2 - 5(n \bmod 2) \qquad (n \ge 1). \qquad \square$$

---

## 4. Proof of Conjecture 2

Fix $n \ge 1$. Again, both sides of Conjecture 2 are polynomials in $A$ with integer coefficients, so it suffices to prove the identity for all $A \in \mathbb{C} \setminus \{2, -2\}$.

Let $A \in \mathbb{C} \setminus \{2, -2\}$, and let $\alpha, \beta \in \mathbb{C}$ be the two roots of $t^2 - A t + 1 = 0$. Then
$$\alpha + \beta = A, \qquad \alpha\beta = 1, \qquad \Delta := \alpha - \beta \ne 0 \quad (\Delta^2 = A^2 - 4 \ne 0).$$
Since $\alpha\beta = 1$, we have $\alpha^{-1} = \beta$ and $\beta^{-1} = \alpha$, so
$$\alpha^2 - 1 = \alpha(\alpha - \alpha^{-1}) = \alpha(\alpha - \beta) = \alpha\Delta \ne 0, \qquad \beta^2 - 1 = \beta(\beta - \alpha) = -\beta\Delta \ne 0.$$
By Binet's formula, for all $m \ge 0$,
$$v(m) = \alpha^m + \beta^m, \qquad u(m) = \frac{\alpha^m - \beta^m}{\Delta}$$
(check $m=0$: $v(0)=2, u(0)=0$; $m=1$: $v(1)=\alpha+\beta=A, u(1)=\Delta/\Delta=1$; and both satisfy $x_{m+1} = A x_m - x_{m-1}$).

Applying Lemma 2 with $c_1 = c_2 = 1$, the three geometric sums are:
$$S_\alpha = \frac{\alpha^2(\alpha^{2n} - 1)}{\alpha^2 - 1} = \frac{\alpha(\alpha^{2n} - 1)}{\Delta}, \qquad S_\beta = \frac{\beta^2(\beta^{2n} - 1)}{\beta^2 - 1} = -\frac{\beta(\beta^{2n} - 1)}{\Delta}, \qquad S_{\alpha\beta} = \sum_{j=1}^n 1^j = n.$$
Therefore:
1. $S_\alpha + S_\beta = \frac{\alpha^{2n+1} - \beta^{2n+1} - (\alpha - \beta)}{\Delta} = \frac{\alpha^{2n+1} - \beta^{2n+1}}{\Delta} - 1$, so
   $$1 + S_\alpha + S_\beta = \frac{\Delta(\alpha^{2n+1} - \beta^{2n+1})}{\Delta^2} = \frac{(\alpha - \beta)(\alpha^{2n+1} - \beta^{2n+1})}{\Delta^2} = \frac{\alpha^{2n+2} + \beta^{2n+2} - \alpha\beta(\alpha^{2n} + \beta^{2n})}{\Delta^2}.$$
   Using $\alpha\beta = 1$, this simplifies to
   $$1 + S_\alpha + S_\beta = \frac{\alpha^{2n+2} + \beta^{2n+2} - (\alpha^{2n} + \beta^{2n})}{\Delta^2}.$$
2. Since $\alpha\beta = 1$,
   $$S_\alpha S_\beta = -\frac{(\alpha\beta)(\alpha^{2n} - 1)(\beta^{2n} - 1)}{\Delta^2} = -\frac{1 - \alpha^{2n} - \beta^{2n} + 1}{\Delta^2} = \frac{(\alpha^{2n} + \beta^{2n}) - 2}{\Delta^2}.$$
3. Adding (1) and (2) and subtracting $S_{\alpha\beta}^2 = n^2$, the $\alpha^{2n} + \beta^{2n}$ terms cancel identically:
   $$\det\bigl[v(j+k) + \delta_{jk}\bigr]_{1\le j,k\le n} = \frac{\alpha^{2n+2} + \beta^{2n+2} - 2}{\Delta^2} - n^2.$$

Since $(\alpha^{n+1} - \beta^{n+1})^2 = \alpha^{2n+2} + \beta^{2n+2} - 2(\alpha\beta)^{n+1} = \alpha^{2n+2} + \beta^{2n+2} - 2$, we have
$$\frac{\alpha^{2n+2} + \beta^{2n+2} - 2}{\Delta^2} = \left(\frac{\alpha^{n+1} - \beta^{n+1}}{\Delta}\right)^2 = u(n+1)^2.$$
Hence $\det[v(j+k) + \delta_{jk}]_{1\le j,k\le n} = u(n+1)^2 - n^2$ for all $A \in \mathbb{C} \setminus \{\pm 2\}$, and by polynomial identity for all $A \in \mathbb{C}$. $\square$

---

## 5. Proof of Conjecture 3

Let $\alpha = \frac{1+\sqrt{5}}{2}$ and $\beta = \frac{1-\sqrt{5}}{2}$ be the roots of $t^2 - t - 1 = 0$, so $\alpha + \beta = 1$, $\alpha\beta = -1$, $\alpha - \beta = \sqrt{5}$, and $F(m) = \frac{1}{\sqrt{5}}\alpha^m - \frac{1}{\sqrt{5}}\beta^m$ for all $m \ge 0$.

Apply Lemma 2 with $c_1 = \frac{1}{\sqrt{5}}$ and $c_2 = -\frac{1}{\sqrt{5}}$. As in Section 3 (with $A = 1$), $\alpha^2 - 1 = \alpha$, $\beta^2 - 1 = \beta$, and
$$S_\alpha = \alpha(\alpha^{2n} - 1), \qquad S_\beta = \beta(\beta^{2n} - 1), \qquad S_{\alpha\beta} = -(n \bmod 2).$$
Computing each term in Lemma 2:
1. $c_1 S_\alpha + c_2 S_\beta = \frac{\alpha^{2n+1} - \beta^{2n+1} - (\alpha - \beta)}{\sqrt{5}} = F(2n+1) - 1$, so
   $$1 + c_1 S_\alpha + c_2 S_\beta = F(2n+1) = \frac{(\alpha - \beta)(\alpha^{2n+1} - \beta^{2n+1})}{5} = \frac{\alpha^{2n+2} + \beta^{2n+2} - \alpha\beta(\alpha^{2n} + \beta^{2n})}{5} = \frac{L(2n+2) + L(2n)}{5}.$$
2. Since $c_1 c_2 = -\frac{1}{5}$ and $S_\alpha S_\beta = (\alpha\beta)(\alpha^{2n}-1)(\beta^{2n}-1) = L(2n) - 2$,
   $$c_1 c_2 \bigl(S_\alpha S_\beta - S_{\alpha\beta}^2\bigr) = -\frac{L(2n) - 2}{5} + \frac{n \bmod 2}{5}.$$
3. Adding (1) and (2), the $L(2n)$ terms cancel identically:
   $$\det\bigl[F(j+k) + \delta_{jk}\bigr]_{1\le j,k\le n} = \frac{L(2n+2) + 2 + (n \bmod 2)}{5}.$$

Finally, $5 F(n+1)^2 = (\alpha^{n+1} - \beta^{n+1})^2 = L(2n+2) - 2(-1)^{n+1}$. Using $-2(-1)^{n+1} = 2 - 4(n \bmod 2)$ (check: $+2$ when $n$ is even, $-2$ when $n$ is odd), we have
$$L(2n+2) + 2 + (n \bmod 2) = \bigl(L(2n+2) + 2 - 4(n \bmod 2)\bigr) + 5(n \bmod 2) = 5 F(n+1)^2 + 5(n \bmod 2).$$
Dividing by $5$ gives
$$\det\bigl[F(j+k) + \delta_{jk}\bigr]_{1\le j,k\le n} = F(n+1)^2 + (n \bmod 2) \qquad (n \ge 1). \qquad \square$$

---

## 6. Adversarial Self-Check & Computational Verification

We checked all potential failure modes:
- **Small $n$ ($n = 1, 2, 3$):**
  - $n = 1$: Conj. 1 gives $A^2(A^2+3) = (A^2+2)^2 - (A^2+4)$; Conj. 2 gives $A^2 - 1 = A^2 - 1^2$; Conj. 3 gives $F(2)+1 = 2 = F(2)^2 + 1$.
  - $n = 2$: Conj. 1 at $A = 1$ gives $\det\begin{pmatrix}4&4\\4&8\end{pmatrix} = 16 = L(3)^2$; Conj. 2 gives $(A^2-1)(A^4-4A^2+3)-(A^3-3A)^2 = A^4-2A^2-3 = (A^2-1)^2-4$; Conj. 3 gives $\det\begin{pmatrix}2&2\\2&4\end{pmatrix} = 4 = F(3)^2$.
- **Degenerate parameters ($A = 0, \pm 2, \pm 2i$):**
  - Conj. 1 at $A = 0$: $v(2m)=2, v(2m+1)=0$, so $v(n+1)^2 - 4(n\bmod 2) = 0 = 0^2 \det(\dots)$ for every $n \ge 1$.
  - Conj. 2 at $A = 2$: $v(m) = 2$, $u(m) = m$, and $\det(I_n + 2 J_n) = 2n+1 = (n+1)^2 - n^2$.
  - Conj. 2 at $A = -2$: $v(m) = 2(-1)^m$, $u(m) = (-1)^{m-1} m$, and $\det(I_n + 2 w w^T) = 2n+1 = (n+1)^2 - n^2$ where $w_j = (-1)^j$.
- **Independent computer verification** ([`verify.py`](verify.py), output in [`data/verify_output.txt`](data/verify_output.txt)):
  1. Reproduces all 35 published OEIS terms of A360278 directly from the matrix determinant.
  2. Verifies the general-$n$ symbolic algebra of Lemma 2 and Sections 3–5 in the polynomial ring $\mathbb{Q}(\alpha, \beta, X, Y)$ (where $X = \alpha^n, Y = \beta^n$ with $XY = B^n$), independently confirming exact zero difference for both even and odd $n$.
  3. Verifies Conjectures 1 and 2 symbolically as exact polynomials in $\mathbb{Z}[A]$ for $n = 1, \dots, 12$, explicitly evaluates degenerate cases $A \in \{0, 2, -2, 2i, -2i\}$ for $n = 1, \dots, 10$, and checks Conjecture 1 ($A = 1$, i.e. A360278) and Conjecture 3 by exact integer determinant computation for $n = 1, \dots, 40$.
