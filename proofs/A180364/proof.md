# Proof of Zhi-Wei Sun's Monotonicity Conjecture for OEIS A180364

## 1. Exact Statement (verbatim from OEIS A180364)

For every integer $n \ge 0$, define
$$a(n) = \sum_{k=0}^{n} \binom{n}{k}\binom{n+k}{k}(2k+1)^2.$$

> **Conjecture (Zhi-Wei Sun, Aug 29 2014):** The sequence $a(n+1)/a(n)$ ($n = 0, 1, \dots$) is strictly decreasing to the limit $3 + 2\sqrt{2}$, and the sequence $a(n+1)^{1/(n+1)} / a(n)^{1/n}$ ($n = 1, 2, 3, \dots$) is strictly increasing to the limit $1$.

Throughout this proof, set $\alpha := 3 + 2\sqrt{2}$ (which satisfies $\alpha^2 - 6\alpha + 1 = 0$, $\alpha > 0$) and $r_n := a(n+1)/a(n)$ for $n \ge 0$. Clearly $a(n)$ is a positive integer for all $n \ge 0$, with $a(0) = 1$, $a(1) = 19$, $a(2) = 205$.

---

## 2. Step 1: Certified Three-Term Recurrence (WZ Telescoping)

**Proposition 1.** *For every integer $n \ge 0$,*
$$c_0(n)\, a(n) + c_1(n)\, a(n+1) + c_2(n)\, a(n+2) = 0,$$
*where*
$$c_0(n) = -(n+1)(2n^2+10n+11), \quad c_1(n) = (2n+3)(6n^2+18n-7), \quad c_2(n) = -(n+2)(2n^2+2n-1).$$

*Proof.* For integers $m \ge 0$ and $k \in \mathbb{Z}$, set
$$F(m, k) := \begin{cases} \displaystyle\binom{m}{k}\binom{m+k}{k}(2k+1)^2 = \frac{(m+k)!}{k!^2\,(m-k)!}(2k+1)^2 & \text{if } 0 \le k \le m, \\ 0 & \text{otherwise,} \end{cases}$$
so that $a(m) = \sum_{k=0}^{m} F(m, k) = \sum_{k=0}^{n+2} F(m, k)$ for $m \in \{n, n+1, n+2\}$.

Define the polynomial
$$Q(n, k) := 2(2n+3)\Bigl((8n^2+24n-4)k^2 - (8n^2+24n+8)k + (2n^2+6n+7)\Bigr),$$
and define the certificate function $G(n, k)$ for $n \ge 0$ and $k \in \mathbb{Z}$ by
$$G(n, k) := \begin{cases} \displaystyle\frac{(n+k)!}{(k-1)!^2\,(n+2-k)!}\, Q(n, k) & \text{if } 1 \le k \le n+2, \\ 0 & \text{otherwise.} \end{cases}$$
We claim that for every $n \ge 0$ and every integer $k \in \{0, 1, \dots, n+2\}$,
$$c_0(n) F(n, k) + c_1(n) F(n+1, k) + c_2(n) F(n+2, k) = G(n, k+1) - G(n, k). \tag{1}$$

Let $P_{\mathrm{lhs}}(n, k)$ and $P_{\mathrm{rhs}}(n, k)$ be the polynomials obtained by multiplying the interior ratios by $(n+1-k)(n+2-k)$:
$$P_{\mathrm{lhs}}(n, k) := (2k+1)^2\Bigl(c_0(n)(n+1-k)(n+2-k) + c_1(n)(n+k+1)(n+2-k) + c_2(n)(n+k+1)(n+k+2)\Bigr),$$
$$P_{\mathrm{rhs}}(n, k) := (n+k+1)(n+2-k)\,Q(n, k+1) - k^2\,Q(n, k).$$
Direct expansion in $\mathbb{Z}[n, k]$ (verified symbolically in [`verify.py`](verify.py)) shows the **exact polynomial identity**
$$P_{\mathrm{lhs}}(n, k) = P_{\mathrm{rhs}}(n, k) \qquad \text{in } \mathbb{Z}[n, k]. \tag{2}$$

We now verify (1) across every index $k \in \{0, 1, \dots, n+2\}$ from (2):
- **Case $1 \le k \le n$:** Since $n+2-k \ge 2$ and $k \ge 1$, the common positive factorial factor $W(n,k) := \frac{(n+k)!}{k!^2\,(n+2-k)!}$ is well-defined and finite. Direct comparison of factorials gives:
  $$F(n,k) = (n+1-k)(n+2-k)(2k+1)^2 W(n,k),$$
  $$F(n+1,k) = (n+k+1)(n+2-k)(2k+1)^2 W(n,k),$$
  $$F(n+2,k) = (n+k+1)(n+k+2)(2k+1)^2 W(n,k),$$
  $$G(n,k) = k^2 Q(n,k) W(n,k), \qquad G(n,k+1) = (n+k+1)(n+2-k) Q(n,k+1) W(n,k).$$
  Multiplying (2) by $W(n,k)$ immediately yields (1). (Equivalently, on $1 \le k \le n$, $G(n,k) = R(n,k) F(n,k)$ with rational WZ certificate $R(n,k) = \frac{k^2 Q(n,k)}{(n+1-k)(n+2-k)(2k+1)^2}$.)
- **Case $k = 0$:** Here $G(n, 0) = 0$, $F(m, 0) = 1$ for $m \in \{n, n+1, n+2\}$, and $G(n, 1) = Q(n, 1)$. Setting $k = 0$ in (2) gives $(n+1)(n+2)\bigl(c_0(n) + c_1(n) + c_2(n)\bigr) = (n+1)(n+2) Q(n, 1)$; dividing by $(n+1)(n+2) > 0$ yields $c_0(n) + c_1(n) + c_2(n) = Q(n, 1) = G(n, 1) - G(n, 0)$.
- **Case $k = n+1$:** Here $F(n, n+1) = 0$, while
  $$F(n+1, n+1) = \frac{(2n+2)!}{(n+1)!^2}(2n+3)^2, \quad F(n+2, n+1) = \frac{(2n+3)!}{(n+1)!^2}(2n+3)^2,$$
  $$G(n, n+1) = \frac{(2n+1)!}{n!^2} Q(n, n+1), \quad G(n, n+2) = \frac{(2n+2)!}{(n+1)!^2} Q(n, n+2).$$
  Setting $k = n+1$ in (2) gives $(2n+3)^2\bigl((2n+2) c_1(n) + (2n+2)(2n+3) c_2(n)\bigr) = (2n+2) Q(n, n+2) - (n+1)^2 Q(n, n+1)$. Multiplying by $\frac{(2n+1)!}{(n+1)!^2}$ yields (1) at $k = n+1$.
- **Case $k = n+2$:** Here $F(n, n+2) = F(n+1, n+2) = G(n, n+3) = 0$, while $F(n+2, n+2) = \frac{(2n+4)!}{(n+2)!^2}(2n+5)^2$ and $G(n, n+2) = \frac{(2n+2)!}{(n+1)!^2} Q(n, n+2)$. Setting $k = n+2$ in (2) gives $(2n+5)^2 (2n+3)(2n+4) c_2(n) = -(n+2)^2 Q(n, n+2)$. Multiplying by $\frac{(2n+2)!}{(n+2)!^2}$ yields $c_2(n) F(n+2, n+2) = -G(n, n+2) = G(n, n+3) - G(n, n+2)$.

Summing (1) over $k = 0, 1, \dots, n+2$ telescopes the right-hand side to $G(n, n+3) - G(n, 0) = 0 - 0 = 0$, proving Proposition 1. $\square$

---

## 3. Step 2: Strict Ratio Monotonicity ($r_{n+1} < r_n \to 3 + 2\sqrt{2}$)

For every $n \ge 1$, notice that $2n^2 + 2n - 1 \ge 3 > 0$, so $-c_2(n) = (n+2)(2n^2+2n-1) > 0$. Dividing Proposition 1 by $-c_2(n)\, a(n+1) > 0$ gives the exact ratio recurrence for all $n \ge 1$:
$$r_{n+1} = A(n) - \frac{B(n)}{r_n}, \tag{3}$$
where
$$A(n) := \frac{(2n+3)(6n^2+18n-7)}{(n+2)(2n^2+2n-1)}, \qquad B(n) := \frac{(n+1)(2n^2+10n+11)}{(n+2)(2n^2+2n-1)} > 0.$$
Because $B(n) > 0$, the right-hand side of (3) is a **strictly increasing** function of $r_n > 0$.

Define the strictly decreasing barrier function
$$f(n) := \alpha\left(1 + \frac{3}{2n}\right) = (3 + 2\sqrt{2})\,\frac{2n+3}{2n} \qquad (n \ge 1).$$

**Theorem 2 (Interlacing Bounds and Ratio Monotonicity).** *For every integer $n \ge 1$,*
$$f(n+1) < r_n < f(n). \tag{4}$$
*Consequently, the sequence $\{r_n\}_{n \ge 0}$ is strictly decreasing and satisfies $\lim_{n\to\infty} r_n = 3 + 2\sqrt{2}$.*

*Proof.* We prove (4) by induction on $n \ge 1$.

**Base case ($n = 1$):** We have $r_1 = \frac{a(2)}{a(1)} = \frac{205}{19}$, while $f(2) = \frac{7}{4}(3+2\sqrt{2})$ and $f(1) = \frac{5}{2}(3+2\sqrt{2})$.
- Lower inequality $f(2) < r_1$:
  $$\frac{7}{4}(3 + 2\sqrt{2}) < \frac{205}{19} \iff 133(3 + 2\sqrt{2}) < 820 \iff 266\sqrt{2} < 421 \iff 2 \cdot 266^2 = 141512 < 177241 = 421^2,$$
  which holds strictly.
- Upper inequality $r_1 < f(1)$:
  $$\frac{205}{19} < \frac{5}{2}(3 + 2\sqrt{2}) \iff 410 < 95(3 + 2\sqrt{2}) \iff 125 < 190\sqrt{2} \iff 125^2 = 15625 < 72200 = 2 \cdot 190^2,$$
  which holds strictly.

**Inductive step:** Assume $f(n+1) < r_n < f(n)$ for some $n \ge 1$. Since $B(n) > 0$, equation (3) gives
$$A(n) - \frac{B(n)}{f(n+1)} < r_{n+1} < A(n) - \frac{B(n)}{f(n)}.$$
Thus it suffices to prove, for every integer $n \ge 1$,
$$A(n) - \frac{B(n)}{f(n+1)} > f(n+2) \qquad\text{and}\qquad A(n) - \frac{B(n)}{f(n)} < f(n+1). \tag{5}$$

Since $f(m) > 0$ and $(n+2)(2n^2+2n-1) > 0$ for all $n \ge 1$, clearing denominators (and using $\alpha^2 = 17 + 12\sqrt{2}$) turns the two inequalities in (5) into exact polynomial positivity claims (verified symbolically in [`verify.py`](verify.py)):

1. **Lower barrier:**
   $$A(n) f(n+1) - B(n) - f(n+1) f(n+2) = \frac{P_{\mathrm{lo}}(n)}{4(n+1)(n+2)(2n^2+2n-1)},$$
   where, setting $n = m + 1$ ($m \ge 0$),
   $$P_{\mathrm{lo}}(m + 1) = (30 + 32\sqrt{2}) m^2 + (98 + 144\sqrt{2}) m + (112\sqrt{2} - 11).$$
   Every coefficient is strictly positive (for the constant term, $(112\sqrt{2})^2 = 25088 > 121 = 11^2$), and the denominator is strictly positive for $m \ge 0$. Hence $A(n) - B(n)/f(n+1) > f(n+2)$ for all $n \ge 1$.

2. **Upper barrier:**
   $$f(n) f(n+1) - A(n) f(n) + B(n) = \frac{P_{\mathrm{hi}}(n)}{4n(n+1)(n+2)(2n^2+2n-1)},$$
   where, setting $n = m + 1$ ($m \ge 0$),
   $$P_{\mathrm{hi}}(m + 1) = (162 + 112\sqrt{2}) m^3 + (904 + 616\sqrt{2}) m^2 + (1497 + 992\sqrt{2}) m + (623 + 380\sqrt{2}).$$
   Every coefficient is strictly positive and the denominator is strictly positive for $m \ge 0$. Hence $A(n) - B(n)/f(n) < f(n+1)$ for all $n \ge 1$.

This closes the induction and proves (4) for all $n \ge 1$.

**Deduction of Part 1 of the Conjecture:**
- For $n = 0$: $r_0 = \frac{a(1)}{a(0)} = 19 > \frac{205}{19} = r_1$ (since $361 > 205$).
- For every $n \ge 1$: by (4) at $n+1$ and at $n$,
  $$r_{n+1} < f(n+1) < r_n.$$
  Hence $\{r_n\}_{n \ge 0}$ is strictly decreasing.
- Since $\lim_{n\to\infty} f(n) = \lim_{n\to\infty} f(n+1) = \alpha = 3 + 2\sqrt{2}$, the squeeze theorem applied to (4) yields $\lim_{n\to\infty} r_n = 3 + 2\sqrt{2}$. $\square$

---

## 4. Step 3: Strict Root-Ratio Monotonicity ($a(n+1)^{1/(n+1)} / a(n)^{1/n} \nearrow 1$)

For $n \ge 1$, set $\rho_n := \frac{a(n+1)^{1/(n+1)}}{a(n)^{1/n}}$. We must show that $\rho_{n+1} > \rho_n$ for all $n \ge 1$ and $\lim_{n\to\infty} \rho_n = 1$.

Define $u_k := \log(r_k / \alpha)$ for $k \ge 0$. Since $r_0 = 19 > \alpha$ and $r_k > f(k+1) > \alpha$ for all $k \ge 1$ by Theorem 2, we have $u_k > 0$ for every $k \ge 0$. Moreover, since $a(0) = 1$,
$$\log a(m) = \sum_{k=0}^{m-1} \log r_k = m \log \alpha + \sum_{k=0}^{m-1} u_k \qquad (m \ge 1). \tag{6}$$

### 4.1. Proof of $\lim_{n\to\infty} \rho_n = 1$

Using (6),
$$\log \rho_n = \frac{\log a(n+1)}{n+1} - \frac{\log a(n)}{n} = \frac{n \log a(n+1) - (n+1) \log a(n)}{n(n+1)} = \frac{n u_n - \sum_{k=0}^{n-1} u_k}{n(n+1)}.$$
Since $r_k$ is strictly decreasing and $r_k > \alpha$, we have $0 < u_k \le u_0$ for all $k \ge 0$. Hence
$$|\log \rho_n| \le \frac{n u_0 + n u_0}{n(n+1)} = \frac{2 u_0}{n+1} \xrightarrow[n\to\infty]{} 0,$$
and therefore $\lim_{n\to\infty} \rho_n = e^0 = 1$.

### 4.2. Proof of $\rho_{n+1} > \rho_n$ for all $n \ge 1$

Taking logarithms and multiplying by $n(n+1)(n+2) > 0$:
$$\rho_{n+1} > \rho_n \iff S_n := n(n+1)\log a(n+2) - 2n(n+2)\log a(n+1) + (n+1)(n+2)\log a(n) > 0.$$
Substituting $\log a(n+2) = \log a(n+1) + \log r_{n+1}$ and $\log a(n) = \log a(n+1) - \log r_n$, and noting that $n(n+1) - 2n(n+2) + (n+1)(n+2) = 2$, we obtain
$$S_n = n(n+1)\log r_{n+1} - (n+1)(n+2)\log r_n + 2\log a(n+1).$$
Substituting $\log r_k = \log \alpha + u_k$ and (6) for $\log a(n+1)$, the coefficient of $\log \alpha$ is $n(n+1) - (n+1)(n+2) + 2(n+1) = 0$, leaving the exact identity
$$S_n = n(n+1) u_{n+1} - (n+1)(n+2) u_n + 2 \sum_{k=0}^{n} u_k \qquad (n \ge 1). \tag{7}$$

**Case $n \ge 13$:** For any $x > 0$, the standard elementary inequalities $\frac{x}{1+x} < \log(1+x) < x$ hold (since $\frac{d}{dx}[\log(1+x) - x] = \frac{-x}{1+x} < 0$ and $\frac{d}{dx}[\log(1+x) - \frac{x}{1+x}] = \frac{x}{(1+x)^2} > 0$, both vanishing at $x = 0$). Applying these to Theorem 2 ($1 + \frac{3}{2(k+1)} < \frac{r_k}{\alpha} < 1 + \frac{3}{2k}$ for $k \ge 1$) yields:
$$u_n < \log\!\left(1 + \frac{3}{2n}\right) < \frac{3}{2n}, \qquad u_{n+1} > \log\!\left(1 + \frac{3}{2(n+2)}\right) > \frac{\frac{3}{2(n+2)}}{1 + \frac{3}{2(n+2)}} = \frac{3}{2n+7}.$$
Therefore, for every $n \ge 2$,
$$n(n+1) u_{n+1} - (n+1)(n+2) u_n > \frac{3n(n+1)}{2n+7} - \frac{3(n+1)(n+2)}{2n} = -\frac{3(n+1)(11n+14)}{2n(2n+7)}.$$
Moreover, for every $n \ge 2$,
$$\frac{33}{4} - \frac{3(n+1)(11n+14)}{2n(2n+7)} = \frac{33n(2n+7) - 6(n+1)(11n+14)}{4n(2n+7)} = \frac{81n - 84}{4n(2n+7)} > 0,$$
so
$$n(n+1) u_{n+1} - (n+1)(n+2) u_n > -\frac{33}{4} \qquad \text{for all } n \ge 2. \tag{8}$$

On the other hand, because $u_k > 0$ for all $k \ge 0$, for every $n \ge 13$ we have
$$2 \sum_{k=0}^{n} u_k \ge 2 \sum_{k=0}^{13} u_k = 2 \log\!\left(\frac{a(14)}{\alpha^{14}}\right).$$
Recall the elementary bound $e = \sum_{j=0}^{\infty} \frac{1}{j!} < 1 + 1 + \frac{1}{2} + \frac{1}{6} + \frac{1}{24}\sum_{j=0}^{\infty} 5^{-j} = \frac{87}{32} < \frac{11}{4}$. Hence $e^{33/8} < (11/4)^{33/8}$, so
$$2 \log\!\left(\frac{a(14)}{\alpha^{14}}\right) > \frac{33}{4} \iff \frac{a(14)}{\alpha^{14}} > e^{33/8} \Longleftarrow 4^{33}\, a(14)^8 > 11^{33}\, \alpha^{112}.$$
Expanding $11^{33} \alpha^{112} = P + Q\sqrt{2}$ in $\mathbb{Z}[\sqrt{2}]$ (with $P, Q > 0$), the inequality $4^{33} a(14)^8 > P + Q\sqrt{2}$ is equivalent to the exact integer inequalities $4^{33} a(14)^8 > P$ and $(4^{33} a(14)^8 - P)^2 > 2 Q^2$, which are verified directly by exact integer arithmetic in [`verify.py`](verify.py). Combining this with (7) and (8) gives
$$S_n > -\frac{33}{4} + \frac{33}{4} = 0 \qquad \text{for all } n \ge 13.$$

**Case $1 \le n \le 12$:** Note that $S_n > 0$ is equivalent to the exact integer inequality
$$a(n+2)^{n(n+1)}\, a(n)^{(n+1)(n+2)} > a(n+1)^{2n(n+2)}.$$
All 12 inequalities for $n = 1, 2, \dots, 12$ are verified by exact arbitrary-precision integer arithmetic in [`verify.py`](verify.py) (with no floating-point approximations).

Thus $\rho_{n+1} > \rho_n$ for all $n \ge 1$ and $\lim_{n\to\infty} \rho_n = 1$, completing the proof of both parts of the conjecture. $\square$

---

## 5. Adversarial Self-Check & Verification Summary

- **Boundary indices in WZ telescoping:** Verified $k = 0$, $1 \le k \le n$, $k = n+1$, and $k = n+2$ separately without dividing by $(n+1-k)(n+2-k)$ where it vanishes; also verified $n = 0$ explicitly ($c_0(0) a(0) + c_1(0) a(1) + c_2(0) a(2) = -11(1) - 21(19) + 2(205) = 0$).
- **Denominator sign in ratio recurrence:** $2n^2 + 2n - 1 = -1$ at $n = 0$ (negative!), which is why equation (3) and Theorem 2 are carefully stated and proved only for $n \ge 1$ (where $2n^2 + 2n - 1 \ge 3 > 0$), and $r_0 > r_1$ is checked directly ($19 > 205/19$).
- **Inequality threshold in (8):** $81n - 84$ is negative at $n = 1$ ($-3$), positive for all $n \ge 2$ ($81 \cdot 2 - 84 = 78 > 0$). We apply (8) only for $n \ge 13 \ge 2$.
- **Exactness:** Every symbolic identity (Proposition 1's polynomial identity (2), boundary identities, and the barrier numerators $P_{\mathrm{lo}}$ and $P_{\mathrm{hi}}$) and every finite numerical check ($n = 1..12$ and $4^{33} a(14)^8 > 11^{33} \alpha^{112}$) is verified with exact integer / symbolic arithmetic in [`verify.py`](verify.py) (output saved in [`data/verify_output.txt`](data/verify_output.txt)).
