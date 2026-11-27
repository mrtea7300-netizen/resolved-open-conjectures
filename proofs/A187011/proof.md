# Proof of Zhi-Wei Sun's Conjecture for OEIS A187011

## 1. Exact Statement (verbatim from OEIS A187011)

Let $p_1 = 2 < p_2 = 3 < p_3 = 5 < \dots$ be the sequence of prime numbers (`A000040`). For $n \ge 1$, define
$$a(n) = \det\bigl[|p_i - p_j|\bigr]_{1 \le i,j \le n},$$
with $a(0) = 1$ (empty determinant).

> **Conjecture (Zhi-Wei Sun, Aug 30 2013):** $(-1)^{n-1}\, a(n) > 0$ for all $n > 1$, and $|a(n)|^{1/n}$ tends to infinity as $n \to \infty$.

---

## 2. Step 1: Exact Closed-Form Determinant (Sign and Factorization)

**Proposition 1.** *Let $n \ge 2$ and let $x_1 \le x_2 \le \dots \le x_n$ be any real numbers. Then*
$$\det\bigl[|x_i - x_j|\bigr]_{1 \le i,j \le n} = (-1)^{n-1}\, 2^{n-2}\, (x_n - x_1) \prod_{k=1}^{n-1} (x_{k+1} - x_k). \tag{1}$$

*Proof.* Set $d_k := x_{k+1} - x_k \ge 0$ for $1 \le k \le n - 1$, and let $A = [|x_i - x_j|]_{1 \le i,j \le n}$.

1. **Row differencing:** Replace row $i$ by $R_i - R_{i-1}$ sequentially for $i = n, n-1, \dots, 2$. This preserves the determinant. For each $2 \le i \le n$ and $1 \le j \le n$:
   - if $j \le i - 1$, then $x_j \le x_{i-1} \le x_i$, so $|x_i - x_j| - |x_{i-1} - x_j| = (x_i - x_j) - (x_{i-1} - x_j) = d_{i-1}$;
   - if $j \ge i$, then $x_{i-1} \le x_i \le x_j$, so $|x_i - x_j| - |x_{i-1} - x_j| = (x_j - x_i) - (x_j - x_{i-1}) = -d_{i-1}$.

2. **Factor out row multipliers:** Factoring $d_{i-1}$ out of row $i$ for each $i = 2, \dots, n$ yields
   $$\det(A) = \left(\prod_{k=1}^{n-1} d_k\right) \det(B),$$
   where $B$ has first row $(0,\, x_2 - x_1,\, x_3 - x_1,\, \dots,\, x_n - x_1)$, and for $2 \le i \le n$, row $i$ of $B$ is $B_{i,j} = +1$ for $j < i$ and $B_{i,j} = -1$ for $j \ge i$.

3. **Column differencing:** Replace column $j$ of $B$ by $C_j - C_{j-1}$ sequentially for $j = n, n-1, \dots, 2$. This preserves $\det(B)$ and produces the matrix $D$ with entries:
   - Row $1$: $D_{1,1} = 0$, and $D_{1,j} = (x_j - x_1) - (x_{j-1} - x_1) = d_{j-1}$ for $2 \le j \le n$.
   - Row $i$ ($2 \le i \le n$): $D_{i,1} = 1$; for $2 \le j \le n$, $D_{i,j} = B_{i,j} - B_{i,j-1}$ equals $-2$ when $j = i$ and $0$ when $j \ne i$.

   Explicitly,
   $$D = \begin{pmatrix} 0 & d_1 & d_2 & \cdots & d_{n-1} \\ 1 & -2 & 0 & \cdots & 0 \\ 1 & 0 & -2 & \cdots & 0 \\ \vdots & \vdots & \vdots & \ddots & \vdots \\ 1 & 0 & 0 & \cdots & -2 \end{pmatrix}.$$

4. **Elimination of the first row:** Add $\sum_{k=1}^{n-1} \frac{d_k}{2} R_{k+1}$ to Row $1$ of $D$. This preserves $\det(D)$: every entry in columns $2, \dots, n$ of Row $1$ becomes $d_{j-1} + \frac{d_{j-1}}{2}(-2) = 0$, while the $(1,1)$-entry becomes
   $$0 + \frac{1}{2} \sum_{k=1}^{n-1} d_k = \frac{x_n - x_1}{2}.$$
   The resulting matrix is lower triangular with diagonal entries $\bigl(\frac{x_n - x_1}{2},\, -2,\, -2,\, \dots,\, -2\bigr)$ ($n - 1$ copies of $-2$). Hence
   $$\det(B) = \det(D) = \frac{x_n - x_1}{2} \cdot (-2)^{n-1} = (-1)^{n-1}\, 2^{n-2}\, (x_n - x_1),$$
   and multiplying by $\prod_{k=1}^{n-1} d_k$ gives (1). $\square$

**Proof of Part 1 of the Conjecture:** Applying Proposition 1 to $x_k = p_k$ ($1 \le k \le n$) for any $n > 1$, we have $p_n - p_1 = p_n - 2 \ge 1$ and $g_k := p_{k+1} - p_k \ge 1$ for all $1 \le k \le n - 1$, so
$$(-1)^{n-1}\, a(n) = 2^{n-2}\, (p_n - 2) \prod_{k=1}^{n-1} (p_{k+1} - p_k) > 0. \qquad \square$$

---

## 3. Step 2: Self-Contained Selberg Sieve Upper Bound for Bounded Prime Gaps

For any even integer $h \ge 2$ and real $x \ge 1$, define
$$\pi_2(x; h) := \#\bigl\{p \le x : p \text{ and } p + h \text{ are both prime}\bigr\}.$$

**Theorem 2 (Selberg Sieve Upper Bound).** *For every even integer $h \ge 2$ and every real $x \ge h^{16}$,*
$$\pi_2(x; h) \le x^{1/4} + \frac{1024\, h^2\, x}{(\log x)^2} + x^{1/2}\!\left(\frac{1}{4}\log x + 1\right)^2. \tag{2}$$

*Proof.* Set $z := x^{1/4}$ and $y := \sqrt{z} = x^{1/8}$. Since $h \ge 2$ and $x \ge h^{16}$, we have $y \ge h^2 \ge 4$ and $z \ge 16$. Let
$$P := \prod_{\substack{p \le z \\ p \nmid h}} p.$$
Because $h$ is even, $2 \mid h$, so every prime factor $p$ of $P$ is an odd prime ($p \ge 3$) with $p \nmid h$.

If $p \le x$ is a prime with $p > z$ such that $p + h$ is also prime, then neither $p$ nor $p + h$ is divisible by any prime $\le z$, hence $\gcd(p(p+h), P) = 1$. Accounting for the at most $z$ primes $p \le z$, we have
$$\pi_2(x; h) \le z + S(x; h, z), \qquad S(x; h, z) := \#\bigl\{1 \le m \le x : \gcd(m(m+h), P) = 1\bigr\}. \tag{3}$$

Let $\{\lambda_d\}$ be any real numbers supported on $\{d \mid P : d \le z\}$ with $\lambda_1 = 1$. Whenever $\gcd(m(m+h), P) = 1$, we have $\sum_{d \mid m(m+h)} \lambda_d = \lambda_1 = 1$; for all $m$, the square is nonnegative. Therefore
$$S(x; h, z) \le \sum_{1 \le m \le x} \left(\sum_{\substack{d \mid m(m+h) \\ d \mid P,\, d \le z}} \lambda_d\right)^2 = \sum_{\substack{d_1, d_2 \mid P \\ d_1, d_2 \le z}} \lambda_{d_1} \lambda_{d_2} \sum_{\substack{1 \le m \le x \\ [d_1, d_2] \mid m(m+h)}} 1.$$

For any $D \mid P$ (so $D$ is squarefree and $\gcd(D, h) = 1$), each prime $p \mid D$ satisfies $p \nmid h$, so the congruence $m(m+h) \equiv 0 \pmod{p}$ has exactly $2$ distinct solutions ($m \equiv 0, -h \pmod{p}$). By the Chinese Remainder Theorem, $m(m+h) \equiv 0 \pmod{D}$ has exactly $\nu(D) := 2^{\omega(D)}$ residue classes modulo $D$. Each residue class modulo $D$ contains $\frac{x}{D} + \theta$ integers in $[1, x]$ with $|\theta| \le 1$, so
$$\left|\sum_{\substack{1 \le m \le x \\ D \mid m(m+h)}} 1 - \frac{\nu(D)}{D}\, x\right| \le \nu(D).$$
Applying this to $D = [d_1, d_2]$ gives
$$S(x; h, z) \le x\, Q(\lambda) + R(\lambda), \tag{4}$$
where
$$Q(\lambda) := \sum_{\substack{d_1, d_2 \mid P \\ d_1, d_2 \le z}} \lambda_{d_1} \lambda_{d_2}\, \frac{\nu([d_1, d_2])}{[d_1, d_2]}, \qquad R(\lambda) := \sum_{\substack{d_1, d_2 \mid P \\ d_1, d_2 \le z}} |\lambda_{d_1}|\, |\lambda_{d_2}|\, \nu([d_1, d_2]).$$

**Diagonalizing $Q(\lambda)$:** For $d \mid P$, define the multiplicative functions
$$f(d) := \frac{d}{\nu(d)} = \prod_{p \mid d} \frac{p}{2}, \qquad g(d) := \prod_{p \mid d} \frac{p - 2}{2}.$$
Since every $p \mid P$ satisfies $p \ge 3$, we have $g(d) > 0$, and $f(d) = \prod_{p \mid d} \bigl(1 + g(p)\bigr) = \sum_{r \mid d} g(r)$. Using $\frac{1}{f([d_1, d_2])} = \frac{f(\gcd(d_1, d_2))}{f(d_1) f(d_2)} = \frac{1}{f(d_1) f(d_2)} \sum_{r \mid \gcd(d_1, d_2)} g(r)$, we obtain
$$Q(\lambda) = \sum_{\substack{r \mid P \\ r \le z}} g(r)\, y_r^2, \qquad\text{where } y_r := \sum_{\substack{d \mid P,\, d \le z \\ r \mid d}} \frac{\lambda_d}{f(d)}.$$
By Möbius inversion on the poset of divisors of $P$ not exceeding $z$,
$$\frac{\lambda_d}{f(d)} = \sum_{\substack{r \mid P,\, r \le z \\ d \mid r}} \mu(r/d)\, y_r \qquad (d \mid P,\; d \le z).$$
(Check: substituting $y_r$ gives $\sum_{d \mid r \mid d' \le z} \mu(r/d)\,\frac{\lambda_{d'}}{f(d')} = \sum_{d \mid d' \le z} \frac{\lambda_{d'}}{f(d')} \sum_{s \mid (d'/d)} \mu(s) = \frac{\lambda_d}{f(d)}$.)

Now set
$$G(z) := \sum_{\substack{r \mid P \\ r \le z}} \frac{1}{g(r)}, \qquad y_r := \frac{\mu(r)}{G(z)\, g(r)} \quad (r \mid P,\; r \le z).$$
Since $\mu(r)^2 = 1$ for $r \mid P$, we check:
1. $\lambda_1 = \sum_{r \mid P,\, r \le z} \mu(r) y_r = \frac{1}{G(z)} \sum_{r \mid P,\, r \le z} \frac{1}{g(r)} = 1$.
2. $Q(\lambda) = \sum_{r \mid P,\, r \le z} g(r)\, y_r^2 = \frac{1}{G(z)}$.
3. **$|\lambda_d| \le 1$ for all $d \mid P$, $d \le z$:** Writing $r = d s$ with $s \mid (P/d)$ and $s \le z/d$ (so $\gcd(d, s) = 1$, $\mu(s)\mu(ds) = \mu(d)$, and $g(ds) = g(d) g(s)$),
   $$\lambda_d = \frac{\mu(d)\, f(d)}{g(d)\, G(z)} \sum_{\substack{s \mid (P/d) \\ s \le z/d}} \frac{1}{g(s)}.$$
   Since $\frac{f(p)}{g(p)} = \frac{p}{p-2} = 1 + \frac{2}{p-2} = 1 + \frac{1}{g(p)}$ for each prime $p \mid d$, expanding the product gives $\frac{f(d)}{g(d)} = \sum_{t \mid d} \frac{1}{g(t)}$. Hence
   $$\frac{f(d)}{g(d)} \sum_{\substack{s \mid (P/d) \\ s \le z/d}} \frac{1}{g(s)} = \sum_{t \mid d} \sum_{\substack{s \mid (P/d) \\ s \le z/d}} \frac{1}{g(t s)} \le \sum_{\substack{r \mid P \\ r \le z}} \frac{1}{g(r)} = G(z),$$
   because every product $r = t s$ divides $P$, satisfies $r \le d \cdot (z/d) = z$, and uniquely determines $(t, s) = (\gcd(r, d),\, r/\gcd(r, d))$. Thus $|\lambda_d| \le 1$.

**Bounding $R(\lambda)$:** Since $|\lambda_d| \le 1$ and $\nu([d_1, d_2]) \le \nu(d_1)\nu(d_2)$,
$$R(\lambda) \le \left(\sum_{\substack{d \mid P \\ d \le z}} 2^{\omega(d)}\right)^2 \le \left(\sum_{d \le z} \tau(d)\right)^2,$$
where $\tau(d) = \sum_{a \mid d} 1 \ge 2^{\omega(d)}$. Using $\sum_{d \le z} \tau(d) = \sum_{a \le z} \lfloor z/a \rfloor \le z \sum_{a \le z} \frac{1}{a} \le z(\log z + 1)$, we get
$$R(\lambda) \le z^2 (\log z + 1)^2 = x^{1/2}\!\left(\frac{1}{4}\log x + 1\right)^2. \tag{5}$$

**Lower-bounding $G(z)$:** Consider all pairs of squarefree positive integers $(a, b)$ with $a \le y$, $b \le y$, and $\gcd(a b, h) = 1$ (where $y = \sqrt{z}$). For each such pair, set $r := \mathrm{lcm}(a, b)$ and $c := \gcd(a, b)$; then $r \mid P$ (as $r$ is squarefree, $\gcd(r, h) = 1$, and $r \le ab \le y^2 = z$), $c \mid r$, and $ab = r c$. For a fixed $r \mid P$ and $c \mid r$, the number of pairs $(a, b)$ with $\mathrm{lcm}(a, b) = r$ and $\gcd(a, b) = c$ is $2^{\omega(r/c)}$ (each prime $p \mid c$ divides both $a$ and $b$; each prime $p \mid (r/c)$ divides exactly one of $a, b$). Therefore
$$\left(\sum_{\substack{a \le y \\ \gcd(a, h) = 1}} \frac{\mu^2(a)}{a}\right)^2 \le \sum_{\substack{r \mid P \\ r \le z}} \sum_{c \mid r} \frac{2^{\omega(r/c)}}{r c} = \sum_{\substack{r \mid P \\ r \le z}} \frac{1}{r} \prod_{p \mid r} \left(2 + \frac{1}{p}\right).$$
For every odd prime $p \ge 3$, we have $(2p + 1)(p - 2) = 2p^2 - 3p - 2 < 2p^2$, so $2 + \frac{1}{p} < \frac{2p}{p-2} = \frac{p}{g(p)}$, and thus $\frac{1}{r}\prod_{p \mid r}(2 + \frac{1}{p}) \le \frac{1}{g(r)}$. Hence
$$G(z) \ge \left(\sum_{\substack{a \le y \\ \gcd(a, h) = 1}} \frac{\mu^2(a)}{a}\right)^2. \tag{6}$$

Next, every positive integer $m \le y$ with $\gcd(m, h) = 1$ factors uniquely as $m = a b^2$ with $a$ squarefree ($a \le y$, $\gcd(a, h) = 1$) and $b \ge 1$. Using $\sum_{b=1}^{\infty} b^{-2} \le 1 + \sum_{b=2}^{\infty} \frac{1}{b(b-1)} = 2$, we obtain
$$\sum_{\substack{m \le y \\ \gcd(m, h) = 1}} \frac{1}{m} \le \left(\sum_{\substack{a \le y \\ \gcd(a, h) = 1}} \frac{\mu^2(a)}{a}\right)\left(\sum_{b=1}^{\infty} \frac{1}{b^2}\right) \le 2 \sum_{\substack{a \le y \\ \gcd(a, h) = 1}} \frac{\mu^2(a)}{a}.$$
Keeping only integers of the form $m = h k + 1 \le y$ ($0 \le k \le K := \lfloor (y - 1)/h \rfloor$), each of which is coprime to $h$ and satisfies $h k + 1 \le h(k + 1)$, we have
$$\sum_{\substack{m \le y \\ \gcd(m, h) = 1}} \frac{1}{m} \ge \sum_{k=0}^{K} \frac{1}{h k + 1} \ge \frac{1}{h} \sum_{j=1}^{K+1} \frac{1}{j} > \frac{1}{h} \int_{1}^{K+2} \frac{dt}{t} = \frac{\log(K+2)}{h}.$$
Since $K + 2 = \lfloor (y - 1)/h \rfloor + 2 > \frac{y - 1}{h} + 1 = \frac{y + h - 1}{h} > \frac{y}{h}$, and $y = x^{1/8} \ge h^2$ implies $\frac{y}{h} \ge \sqrt{y} = x^{1/16}$, we get
$$\sum_{\substack{a \le y \\ \gcd(a, h) = 1}} \frac{\mu^2(a)}{a} \ge \frac{1}{2h} \log\!\left(\frac{y}{h}\right) \ge \frac{\log x}{32 h}.$$
Substituting this into (6) yields $G(z) \ge \frac{(\log x)^2}{1024\, h^2}$, and combining (3), (4), and (5) proves (2). $\square$

---

## 4. Step 3: Proof that $|a(n)|^{1/n} \to \infty$

**Theorem 3.** *$\lim_{n \to \infty} |a(n)|^{1/n} = +\infty$.*

*Proof.* By Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. **6** (1962), Theorem 3, Corollary 1 (see also Chebyshev's theorem in Hardy & Wright, *An Introduction to the Theory of Numbers*, Theorem 8), we have $p_n < n(\log n + \log\log n)$ for all $n \ge 6$. Since $\log\log n < \log n$ for all $n \ge 2$ (as $\log t < t$ for $t > 0$), this yields $p_n < 2 n \log n$ for all $n \ge 6$ (and direct check gives $p_3 = 5 < 6\log 3$, $p_4 = 7 < 8\log 4$, $p_5 = 11 < 10\log 5$, so $p_n < 2 n \log n$ for all $n \ge 3$). Also clearly $p_n \ge n$ for all $n \ge 1$.

Fix an arbitrary integer $M \ge 1$. Let $g_k := p_{k+1} - p_k$ ($k \ge 1$), and let
$$N_{\le 2M}(n) := \#\bigl\{1 \le k \le n - 1 : g_k \le 2M\bigr\}.$$
The only odd prime gap is $g_1 = p_2 - p_1 = 1$; every gap $g_k$ with $k \ge 2$ is a positive even integer $2m$. For each $m \in \{1, \dots, M\}$, every index $k \le n - 1$ with $p_{k+1} - p_k = 2m$ contributes a prime $p = p_k \le p_n$ for which $p + 2m$ is also prime, so there are at most $\pi_2(p_n; 2m)$ such indices.

For all $n$ large enough that $p_n \ge (2M)^{16}$ (and $n \ge 3$), Theorem 2 applies to every $h = 2m \in \{2, 4, \dots, 2M\}$:
$$N_{\le 2M}(n) \le 1 + \sum_{m=1}^{M} \pi_2(p_n; 2m) \le 1 + M\!\left(p_n^{1/4} + \frac{4096\, M^2\, p_n}{(\log p_n)^2} + p_n^{1/2}\!\left(\frac{1}{4}\log p_n + 1\right)^2\right).$$
Using $n \le p_n < 2 n \log n$, we have:
- $\dfrac{p_n}{(\log p_n)^2} < \dfrac{2 n \log n}{(\log n)^2} = \dfrac{2 n}{\log n} = o(n)$,
- $p_n^{1/4} = o(n)$ and $p_n^{1/2}\bigl(\frac{1}{4}\log p_n + 1\bigr)^2 = O\bigl(n^{1/2}(\log n)^{5/2}\bigr) = o(n)$.

Therefore $\lim_{n\to\infty} \frac{N_{\le 2M}(n)}{n} = 0$. In particular, there exists $N_M \ge 3$ such that for all $n \ge N_M$, we have $N_{\le 2M}(n) \le \frac{n - 1}{2}$, which means that at least $\frac{n - 1}{2}$ of the gaps $g_1, \dots, g_{n-1}$ satisfy $g_k > 2M$, while every remaining gap satisfies $g_k \ge 1$.

Applying Proposition 1 to $x_k = p_k$ for all $n \ge N_M$ (where $p_n - 2 \ge 1$), we obtain
$$|a(n)| = 2^{n-2}\, (p_n - 2) \prod_{k=1}^{n-1} g_k \ge 2^{n-2} \cdot (2M)^{(n-1)/2},$$
and taking $n$-th roots gives
$$\liminf_{n \to \infty} |a(n)|^{1/n} \ge \lim_{n \to \infty} 2^{1 - 2/n}\, (2M)^{(n-1)/(2n)} = 2\sqrt{2M}.$$
Since $M \ge 1$ is arbitrary, $\lim_{n \to \infty} |a(n)|^{1/n} = +\infty$. $\square$

---

## 5. Adversarial Self-Check & Computational Verification

- **Small $n$ ($n = 0, 1, 2, 3$):**
  - $n = 0$: empty determinant $a(0) = 1$; $n = 1$: $a(1) = \det[0] = 0$ (conjecture explicitly states $n > 1$).
  - $n = 2$: $(-1)^1 2^0 (3-2)(1) = -1$; $(-1)^1 a(2) = 1 > 0$.
  - $n = 3$: $(-1)^2 2^1 (5-2)(1 \cdot 2) = 12$; $(-1)^2 a(3) = 12 > 0$.
- **Parity / prime $2$ edge case:**
  - $g_1 = p_2 - p_1 = 1$ is the unique odd gap, explicitly accounted for by the $+1$ term in $N_{\le 2M}(n) \le 1 + \sum_{m=1}^{M} \pi_2(p_n; 2m)$.
  - In Theorem 2, $h$ is even, so $2 \mid h$ and hence $2 \nmid P$; thus every prime $p \mid P$ satisfies $p \ge 3$, ensuring $g(p) = (p-2)/2 > 0$ and $(2 + 1/p) < 2p/(p-2)$.
- **Independent computer verification** ([`verify.py`](verify.py), output in [`data/verify_output.txt`](data/verify_output.txt)):
  1. Reproduces all 23 published terms of OEIS A187011 (`n = 0..22`) directly from $\det[|p_i - p_j|]$.
  2. Verifies Proposition 1 symbolically for generic indeterminates $x_1 < \dots < x_n$ ($n = 2..7$) and checks exact equality against $\det[|p_i - p_j|]$ for $n = 1..40$.
  3. Verifies Rosser–Schoenfeld's $p_n < 2 n \log n$ for $3 \le n \le 78{,}498$ ($p_n \le 10^6$), verifies the Selberg sieve step-by-step inequalities ($|\lambda_d| \le 1$, $G(z)$ lower bound, and Theorem 2) numerically on sample parameters, and tracks the empirical growth of $|a(n)|^{1/n}$ up to $n = 78{,}498$.
