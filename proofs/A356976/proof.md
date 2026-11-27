# Proof of A356976, Conjecture 2

**Status:** `proof (draft)` — awaiting independent adversarial review (see `CONTRIBUTING.md`).

## Statement (A356976, Conjecture 2)

> **Theorem.** Let $f(k) = 2k^3 + k$. For every positive integer $n$, the least positive integer $m$ such that $f(1), f(2), \dots, f(n)$ are pairwise distinct modulo $m$ is $2^{\lceil \log_2 n \rceil}$ (the least power of $2$ not smaller than $n$).

Equivalently, let $D_f(n)$ denote this least modulus. We prove $D_f(n) = 2^{\lceil \log_2 n \rceil}$ for all $n \ge 1$.

---

## 1. Upper bound: $D_f(n) \le 2^{\lceil \log_2 n \rceil}$

**Lemma 1.** *For every integer $r \ge 0$, the map $k \mapsto f(k) = 2k^3 + k$ is a bijection on $\mathbb{Z}/2^r\mathbb{Z}$.*

*Proof.* For any integers $x, y$,
$$f(y) - f(x) = (y - x)\bigl(2(x^2 + xy + y^2) + 1\bigr).$$
Since $2(x^2 + xy + y^2) + 1$ is odd, we have $2^r \mid (f(y) - f(x))$ if and only if $2^r \mid (y - x)$. Hence $f$ is injective (and therefore bijective) on $\mathbb{Z}/2^r\mathbb{Z}$. $\square$

Taking $m = 2^{\lceil \log_2 n \rceil} \ge n$, the values $f(1), \dots, f(n)$ are pairwise distinct modulo $m$, so $D_f(n) \le 2^{\lceil \log_2 n \rceil}$.

---

## 2. Reduction of the lower bound

To prove $D_f(n) = 2^{\lceil \log_2 n \rceil}$ for all $n \ge 1$, it is necessary and sufficient to show that for every positive integer $m$ that is **not** a power of $2$, $f(1), \dots, f(n)$ are *not* pairwise distinct modulo $m$ whenever $n > 2^{\lfloor \log_2 m \rfloor}$. Equivalently:

> **Target Claim.** For every positive integer $m$ that is not a power of $2$, there exist integers $1 \le x < y \le 2^{\lfloor \log_2 m \rfloor} + 1$ such that $f(x) \equiv f(y) \pmod m$.

Note that if $2^r < m < 2^{r+1}$, then $m \le 2^{r+1} - 1$, so $2^r \ge \frac{m+1}{2} > \frac{m}{2}$. Thus any pair $1 \le x < y \le \lfloor m/2 \rfloor + 1$ automatically satisfies $y \le 2^{\lfloor \log_2 m \rfloor} + 1$.

---

## 3. Case 1: $3 \mid m$

Write $m = 3^e d'$ with $e \ge 1$ and $3 \nmid d'$. For every integer $k$, $f(k) = 2k^3 + k \equiv 2k + k = 3k \equiv 0 \pmod 3$, so $f(k) \bmod 3^e$ always lies in $3\mathbb{Z}/3^e\mathbb{Z}$, a set of size $3^{e-1}$.

Consider the $3^{e-1} + 1$ integers $k_j = 1 + j d'$ for $j = 0, 1, \dots, 3^{e-1}$. By the pigeonhole principle, there exist $0 \le i < j \le 3^{e-1}$ such that $f(k_i) \equiv f(k_j) \pmod{3^e}$. Since $d' \mid (k_j - k_i)$, we also have $f(k_i) \equiv f(k_j) \pmod{d'}$. Because $\gcd(3^e, d') = 1$, it follows that $f(k_i) \equiv f(k_j) \pmod{m}$. Finally,
$$1 \le k_i < k_j \le 1 + 3^{e-1} d' = 1 + \frac{m}{3} < 1 + \frac{m}{2} \le 2^{\lfloor \log_2 m \rfloor} + 1.$$
Thus the Target Claim holds whenever $3 \mid m$. $\square$

---

## 4. The Conic Box Lemma and Pigeonhole Hensel Lifting

For any odd prime $p \ge 5$, write $m = p^e d$ with $e \ge 1$ and $p \nmid d$. If we choose $x = u d$ and $y = v d$ with $1 \le u < v \le \frac{p^e - 1}{2}$, then:
1. $1 \le x < y \le \frac{p^e - 1}{2} d < \frac{m}{2} < 2^{\lfloor \log_2 m \rfloor} + 1$.
2. $d \mid (y - x)$, hence $d \mid (f(y) - f(x))$.
3. $p^e \mid (f(y) - f(x))$ holds if $p^e \mid \bigl(2(u^2 d^2 + uv d^2 + v^2 d^2) + 1\bigr)$, i.e.,
   $$u^2 + uv + v^2 \equiv c \pmod{p^e}, \qquad \text{where } c \equiv -(2d^2)^{-1} \pmod{p^e}.$$

Note that $\gcd(c, p) = 1$.

### Lemma 2 (Pigeonhole Hensel Lifting)
*Let $p \ge 5$ be a prime, $e_0 \ge 1$, and suppose that for every integer $c$ with $p \nmid c$, there exist integers $u_0, v_0$ satisfying:*
1. $1 \le u_0 < v_0 \le \frac{p^{e_0} - 1}{2}$,
2. $u_0^2 + u_0 v_0 + v_0^2 \equiv c \pmod{p^{e_0}}$,
3. $p \nmid (2u_0 + v_0)$ and $p \nmid (u_0 + 2v_0)$.

*Then the same conclusion holds for every $e \ge e_0$.*

*Proof.* We induct on $e \ge e_0$. The base case $e = e_0$ is the hypothesis. For the inductive step $e - 1 \to e$ ($e > e_0$), let $1 \le u_1 < v_1 \le \frac{p^{e-1} - 1}{2}$ satisfy $u_1^2 + u_1 v_1 + v_1^2 \equiv c \pmod{p^{e-1}}$ with $a := 2u_1 + v_1 \not\equiv 0 \pmod p$ and $b := u_1 + 2v_1 \not\equiv 0 \pmod p$.

Set $u = u_1 + k p^{e-1}$ and $v = v_1 + \ell p^{e-1}$ with $k, \ell \in \{0, 1, \dots, \frac{p-1}{2}\}$. Since $2(e-1) \ge e$,
$$u^2 + uv + v^2 \equiv u_1^2 + u_1 v_1 + v_1^2 + p^{e-1}(a k + b \ell) \pmod{p^e}.$$
Let $w := -\frac{u_1^2 + u_1 v_1 + v_1^2 - c}{p^{e-1}} \in \mathbb{Z}$. As $k$ runs over $\{0, 1, \dots, \frac{p-1}{2}\}$, the residues $a k \pmod p$ form a set $A \subseteq \mathbb{F}_p$ of size $\frac{p+1}{2}$. As $\ell$ runs over $\{0, 1, \dots, \frac{p-1}{2}\}$, the residues $w - b \ell \pmod p$ form a set $B \subseteq \mathbb{F}_p$ of size $\frac{p+1}{2}$. Since $|A| + |B| = p + 1 > p$, by the pigeonhole principle $A \cap B \neq \emptyset$, so there exist $k, \ell \in \{0, 1, \dots, \frac{p-1}{2}\}$ with $ak + b\ell \equiv w \pmod p$.

Then:
- $u^2 + uv + v^2 \equiv c \pmod{p^e}$.
- $1 \le u \le \frac{p^{e-1} - 1}{2} + \frac{p-1}{2} p^{e-1} = \frac{p^e - 1}{2}$, and similarly $1 \le v \le \frac{p^e - 1}{2}$.
- Since $1 \le u_1 < v_1 < p^{e-1}$, we have $u \equiv u_1 \not\equiv v_1 \equiv v \pmod{p^{e-1}}$, so $u \neq v$.
- $2u + v \equiv 2u_1 + v_1 \not\equiv 0 \pmod p$ and $u + 2v \equiv u_1 + 2v_1 \not\equiv 0 \pmod p$.

Swapping $u$ and $v$ if $u > v$ completes the induction. $\square$

### Lemma 3 (Conic Box Lemma for $p \ge 17$)
*For every prime $p \ge 17$ and every $c \in \mathbb{F}_p^\times$, there exist integers $1 \le u < v \le \frac{p-1}{2}$ such that $u^2 + uv + v^2 \equiv c \pmod p$ and $p \nmid (2u + v)(u + 2v)$.*

*Proof.* We split into $p \ge 35{,}000$ (analytic) and $17 \le p < 35{,}000$ (finite computation).

**Analytic proof for $p \ge 35{,}000$.** Let $H = \frac{p-1}{2}$, and let $C_c(\mathbb{F}_p) = \{(u, v) \in \mathbb{F}_p^2 : u^2 + uv + v^2 = c\}$. Under the linear bijection $X = 2u + v$, $Y = v$ on $\mathbb{F}_p^2$, $C_c(\mathbb{F}_p)$ becomes the affine conic $X^2 + 3Y^2 = 4c$.

1. *Point count:* For $p \ge 5$ and $c \in \mathbb{F}_p^\times$,
   $$|C_c(\mathbb{F}_p)| = \sum_{Y \in \mathbb{F}_p} \left(1 + \left(\frac{4c - 3Y^2}{p}\right)\right) = p - \left(\frac{-3}{p}\right),$$
   using the standard quadratic character sum identity $\sum_{Y \in \mathbb{F}_p} \left(\frac{\alpha Y^2 + \beta}{p}\right) = -\left(\frac{\alpha}{p}\right)$ for $p \nmid \alpha\beta$.

2. *Exponential sum bound:* For any $(a, b) \in \mathbb{F}_p^2 \setminus \{(0, 0)\}$, define
   $$S_c(a, b) = \sum_{(u, v) \in C_c(\mathbb{F}_p)} e_p(a u + b v), \qquad e_p(z) := e^{2\pi i z / p}.$$
   In $(X, Y)$-coordinates, $a u + b v = \alpha X + \beta Y$ with $(\alpha, \beta) = (a/2, b - a/2) \neq (0, 0)$. Since $|C_c(\mathbb{F}_p)| \ge p - 1 > 0$, pick a point $(X_0, Y_0) \in C_c(\mathbb{F}_p)$. Stereographic projection from $(X_0, Y_0)$ gives a rational parametrization
   $$X(t) = X_0 \frac{t^2 - 3}{t^2 + 3} - \frac{6 Y_0 t}{t^2 + 3}, \qquad Y(t) = Y_0 \frac{3 - t^2}{t^2 + 3} - \frac{2 X_0 t}{t^2 + 3},$$
   which is a bijection from $\mathbb{P}^1(\mathbb{F}_p) \setminus \{t : t^2 + 3 = 0\}$ onto $C_c(\mathbb{F}_p)$ (sending $t = \infty$ to $(X_0, -Y_0)$). Thus
   $$S_c(a, b) = \sum_{\substack{t \in \mathbb{P}^1(\mathbb{F}_p) \\ t^2 + 3 \neq 0}} e_p\bigl(R(t)\bigr), \qquad R(t) = \alpha X(t) + \beta Y(t) = \frac{P(t)}{t^2 + 3},$$
   where $\deg P \le 2$ and $R(t)$ is non-constant (since $1, X(t), Y(t)$ are linearly independent over $\mathbb{F}_p$ and $(\alpha, \beta) \neq (0,0)$).
   - If $P(t)$ shares a root with $t^2 + 3$ over $\overline{\mathbb{F}}_p$: this can only happen when $t^2 + 3$ splits over $\mathbb{F}_p$ (if it were irreducible, $P$ would be a constant multiple of $t^2 + 3$, contradicting non-constancy). Then $R(t)$ simplifies to a degree-$1$ rational function with a single simple pole in $\mathbb{P}^1(\mathbb{F}_p)$, and the sum over the remaining $p - 1$ points (excluding both roots of $t^2 + 3$) equals $-1$, so $|S_c(a, b)| = 1 \le 2\sqrt{p}$.
   - Otherwise, $R(t)$ has two distinct simple poles at $\pm\sqrt{-3}$ over $\overline{\mathbb{F}}_p$ (and no pole at $\infty$), so $\deg(R)_\infty = 2$ and the number of distinct poles is $s = 2$. By the Weil–Bombieri bound for exponential sums of rational functions on $\mathbb{P}^1(\mathbb{F}_p)$ (A. Weil, *On some exponential sums*, Proc. Nat. Acad. Sci. U.S.A. **34** (1948), 204–207; E. Bombieri, *On exponential sums in finite fields*, Amer. J. Math. **88** (1966), Theorem 6, p. 88),
     $$|S_c(a, b)| \le (\deg(R)_\infty + s - 2)\sqrt{p} = 2\sqrt{p}.$$
   (In the split case $p \equiv 1 \pmod 3$, this is also directly Weil's bound for the classical Kloosterman sum after factoring $X^2 + 3Y^2 = (X - \delta Y)(X + \delta Y) = 4c$.)

3. *Fourier count in $[1, H]^2$:* Let $N(H) = |C_c(\mathbb{F}_p) \cap \{1, \dots, H\}^2|$ and $T_H(a) = \sum_{u=1}^H e_p(au)$. By discrete Fourier inversion on $\mathbb{F}_p^2$,
   $$N(H) = \frac{1}{p^2} \sum_{a=0}^{p-1} \sum_{b=0}^{p-1} S_c(a, b) \overline{T_H(a)} \overline{T_H(b)}.$$
   Separating $(a, b) = (0, 0)$ (where $S_c(0, 0) = p - \left(\frac{-3}{p}\right) \ge p - 1$ and $T_H(0) = H$):
   $$N(H) \ge \frac{H^2 (p - 1)}{p^2} - \frac{2\sqrt{p}}{p^2} \left( \left(\sum_{a=0}^{p-1} |T_H(a)|\right)^2 - H^2 \right) \ge \frac{(p-1)^3}{4p^2} - 2\sqrt{p}\, L(p)^2,$$
   where $L(p) := \frac{1}{p}\sum_{a=0}^{p-1} |T_H(a)|$.

4. *Elementary bound on $L(p)$:* For $1 \le a \le p - 1$, since $H = \frac{p-1}{2}$,
   $$|T_H(a)| = \frac{|\sin(\pi a (p-1) / (2p))|}{\sin(\pi a / p)} = \begin{cases} \dfrac{1}{2\sin(\pi a / (2p))} & a \text{ odd}, \\[6pt] \dfrac{1}{2\cos(\pi a / (2p))} & a \text{ even}. \end{cases}$$
   Pairing $a$ with $p - a$ (which swaps parity and maps $\cos(\pi(p-a)/(2p)) = \sin(\pi a/(2p))$),
   $$\sum_{a=1}^{p-1} |T_H(a)| = \sum_{j=0}^{(p-3)/2} \frac{1}{\sin\!\left(\frac{\pi(2j+1)}{2p}\right)}.$$
   For $j = 0$, $\sin\!\left(\frac{\pi}{2p}\right) \ge \frac{2}{\pi}\cdot\frac{\pi}{2p} = \frac{1}{p}$, so the $j = 0$ term is at most $p$. For $1 \le j \le \frac{p-3}{2}$, since $x \mapsto \frac{1}{\sin x}$ is convex on $(0, \pi/2]$, Jensen's inequality on the interval $\left[\frac{\pi j}{p}, \frac{\pi(j+1)}{p}\right]$ gives
   $$\frac{1}{\sin\!\left(\frac{\pi(2j+1)}{2p}\right)} \le \frac{p}{\pi} \int_{\pi j / p}^{\pi(j+1)/p} \frac{dx}{\sin x}.$$
   Summing over $j = 1, \dots, \frac{p-3}{2}$ and noting $\tan\theta \ge \theta$ on $(0, \pi/2)$,
   $$\sum_{j=1}^{(p-3)/2} \frac{1}{\sin\!\left(\frac{\pi(2j+1)}{2p}\right)} \le \frac{p}{\pi} \int_{\pi/p}^{\pi/2} \frac{dx}{\sin x} = \frac{p}{\pi} \ln \cot\!\left(\frac{\pi}{2p}\right) \le \frac{p}{\pi} \ln\!\left(\frac{2p}{\pi}\right).$$
   Including $a = 0$ (contributing $H/p < 1/2$) and $j = 0$ (contributing $\le 1$),
   $$L(p) < \frac{1}{2} + 1 + \frac{1}{\pi}\ln\!\left(\frac{2p}{\pi}\right) = \frac{1}{\pi}\ln p + \frac{3}{2} - \frac{\ln(\pi/2)}{\pi} < \frac{1}{\pi}\ln p + 1.36.$$

5. *Excluding bad points:* A point $(u, v) \in C_c(\mathbb{F}_p) \cap [1, H]^2$ fails our requirements only if:
   - $u = v$: then $3u^2 \equiv c \pmod p$, at most $2$ solutions in $\mathbb{F}_p$ (at most $1$ in $[1, H]$);
   - $2u + v \equiv 0 \pmod p$: then $3u^2 \equiv c \pmod p$, at most $2$ solutions in $\mathbb{F}_p$;
   - $u + 2v \equiv 0 \pmod p$: then $3v^2 \equiv c \pmod p$, at most $2$ solutions in $\mathbb{F}_p$.

   Thus at most $5$ points in $C_c(\mathbb{F}_p) \cap [1, H]^2$ are excluded. If $N(H) \ge 6$, there exists a valid pair $(u, v) \in [1, H]^2$ with $u \neq v$ and $p \nmid (2u+v)(u+2v)$; swapping $u, v$ if $u > v$ yields $1 \le u < v \le H$.

   For $p = 35{,}000$: $\frac{(p-1)^3}{4p^2} - 6 > 8743$, while $2\sqrt{p}\left(\frac{\ln p}{\pi} + 1.36\right)^2 < 8233 < 8743$. Since $\frac{(p-1)^3}{4p^2} - 2\sqrt{p}\left(\frac{\ln p}{\pi} + 1.36\right)^2$ is strictly increasing for $p \ge 35{,}000$ (its derivative is positive as $\frac{1}{4}p^{1/2}$ dominates $\left(\frac{\ln p}{\pi} + 1.36\right)^2$), we have $N(H) \ge 6$ for all primes $p \ge 35{,}000$.

**Finite verification for $17 \le p < 35{,}000$.** Verified exhaustively (in fact for all $9{,}586$ primes $17 \le p \le 100{,}000$) by `verify_conj2.c` with $0$ failures. $\square$

---

## 5. Completing the proof for all non-powers of $2$

Let $m$ be any positive integer that is not a power of $2$.

- **Case 1 ($3 \mid m$):** Proved in Section 3.
- **Case 2 (some prime $p \ge 17$ divides $m$):** Write $m = p^e d$ with $p \nmid d$, $e \ge 1$. By Lemmas 3 and 2, there exist $1 \le u < v \le \frac{p^e - 1}{2}$ with $u^2 + uv + v^2 \equiv -(2d^2)^{-1} \pmod{p^e}$. Setting $x = ud$, $y = vd$ gives $1 \le x < y < \frac{m}{2} < 2^{\lfloor \log_2 m \rfloor} + 1$ and $m \mid (f(y) - f(x))$.
- **Case 3 (any of $5^3, 7^3, 11^2, 13^2$ divides $m$):** Direct computation (`verify_conj2.c`, Check 2) confirms the hypothesis of Lemma 2 holds at $e_0 = 3$ for $p \in \{5, 7\}$ and at $e_0 = 2$ for $p \in \{11, 13\}$. By Lemma 2, it holds for all $e \ge e_0$, and setting $x = ud$, $y = vd$ finishes this case exactly as in Case 2.
- **Case 4 (remaining moduli):** Every remaining $m$ has the form
  $$m = 2^a \cdot s, \qquad s \mid 5^2 \cdot 7^2 \cdot 11 \cdot 13, \quad s > 1.$$
  - **Subcase 4a ($a \ge 7$, so $2^a \ge 128$):** Pick any prime $p \in \{5, 7, 11, 13\}$ dividing $s$, and write $m = p^e d$ with $p \nmid d$ (so $e \in \{1, 2\}$ for $p \in \{5, 7\}$, $e = 1$ for $p \in \{11, 13\}$, and $d \ge 2^a \ge 128 > 2 p^e - 2$ since $p^e \le 49$).
    We seek $y = x + t d$ with $1 \le t \le \frac{p^e - 1}{2}$, $1 \le x \le p^e$, and $p^e \mid \bigl(2(x^2 + xy + y^2) + 1\bigr)$.
    Completing the square (valid since $\gcd(6, p) = 1$), $2(x^2 + x(x+td) + (x+td)^2) + 1 \equiv 0 \pmod{p^e}$ is equivalent to
    $$(6x + 3td)^2 \equiv -3(td)^2 - 6 \pmod{p^e}.$$
    For each $p \in \{5, 7, 11, 13\}$, we check directly that there exists $t_0 \in \{1, \dots, (p-1)/2\}$ such that $-3(t_0 d)^2 - 6$ is a **nonzero** quadratic residue modulo $p$ (independently of $d \not\equiv 0 \pmod p$, since $\{ (t d)^2 \bmod p : 1 \le t \le (p-1)/2 \} = (\mathbb{F}_p^\times)^2$):
    - $p = 5$: taking $u = (t_0 d)^2 \equiv 1 \pmod 5$ gives $-3(1) - 6 = -9 \equiv 1 = 1^2 \pmod 5$.
    - $p = 7$: taking $u \equiv 2 \pmod 7$ gives $-3(2) - 6 = -12 \equiv 2 = 3^2 \pmod 7$.
    - $p = 11$: taking $u \equiv 1 \pmod{11}$ gives $-3(1) - 6 = -9 \equiv 2$ (non-QR); taking $u \equiv 3 \pmod{11}$ gives $-3(3) - 6 = -15 \equiv 7$ (non-QR); taking $u \equiv 4 \pmod{11}$ gives $-3(4) - 6 = -18 \equiv 4 = 2^2 \pmod{11}$.
    - $p = 13$: taking $u \equiv 1 \pmod{13}$ gives $-3(1) - 6 = -9 \equiv 4 = 2^2 \pmod{13}$.

    Thus in all four cases there is a $t \in \{1, \dots, \frac{p-1}{2}\} \subseteq \{1, \dots, \frac{p^e-1}{2}\}$ such that $-3(td)^2 - 6 \equiv s_0^2 \not\equiv 0 \pmod p$. By Hensel's lemma, there exists $s \in \mathbb{Z}$ with $s^2 \equiv -3(td)^2 - 6 \pmod{p^e}$, and since $\gcd(6, p^e) = 1$ there is a unique $x \in \{1, \dots, p^e\}$ with $6x + 3td \equiv s \pmod{p^e}$. Setting $y = x + td$ gives $m \mid (f(y) - f(x))$ and
    $$1 \le x < y = x + td \le p^e + \frac{p^e - 1}{2} d \le \frac{p^e d}{2} + 1 = \frac{m}{2} + 1 \le 2^{\lfloor \log_2 m \rfloor} + 1,$$
    since $d \ge 2p^e - 2$.
  - **Subcase 4b ($0 \le a \le 6$):** There are exactly $7 \times (3 \cdot 3 \cdot 2 \cdot 2 - 1) = 245$ such moduli $m$. All $245$ are verified directly by `verify_conj2.c` (Check 3) to have a collision $1 \le x < y \le 2^{\lfloor \log_2 m \rfloor} + 1$.

This exhausts all positive integers $m$ that are not powers of $2$, completing the proof of Conjecture 2. $\blacksquare$
