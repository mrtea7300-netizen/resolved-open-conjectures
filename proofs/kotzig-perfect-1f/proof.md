# Proof (draft): A perfect 1-factorization of $K_{1682}$ and symmetry obstructions for $K_{64}$

- **Status:** `proof (reviewed)` for the theorem "$K_{1682}$ has a perfect 1-factorization" (Claude Opus 5.5 review, `reviews/`) (verified by two independent brute-force verifiers over all $1{,}412{,}040$ pairs of matchings; awaits independent adversarial review per `CONTRIBUTING.md`). Kotzig's conjecture for $K_{64}$ remains `open`.

---

## 1. Generalized finite-ring multiplier reduction

Let $R$ be a finite commutative ring with unity $1 \ne 0$ of odd order $n = |R|$.
A **starter** in the additive group $(R, +)$ is a set $S$ of $(n - 1)/2$ pairwise disjoint unordered pairs $\{x, y\} \subset R \setminus \{0\}$ such that the differences $\{\pm(x - y) : \{x, y\} \in S\}$ cover $R \setminus \{0\}$ exactly once.

Given a starter $S$ in $R$, define a 1-factorization $\mathcal{F}(S) = \{F_a : a \in R\}$ of $K_{n + 1}$ on vertex set $V = R \cup \{\infty\}$ by
$$F_a = (S + a) \cup \{\{a, \infty\}\}, \qquad a \in R,$$
where $S + a = \{\{x + a, y + a\} : \{x, y\} \in S\}$.

**Proposition 1.1 (Translation and multiplier orbit reduction).**
*Let $U \le R^\times$ be a subgroup of the unit group of $R$ such that $|U|$ is odd and $u - 1 \in R^\times$ for every $u \in U \setminus \{1\}$ (we call such $U$ **admissible**). Let $G = \langle -1, U \rangle \le R^\times$. Suppose $S$ is a $U$-invariant starter in $R$ (i.e., $uS = S$ for all $u \in U$). Then:*
1. *$G = U \cup (-U)$ with $U \cap (-U) = \emptyset$, so $|G| = 2|U|$.*
2. *Both $U$ and $G$ act freely on $R \setminus \{0\}$, partitioning $R \setminus \{0\}$ into $2c$ free $U$-orbits of size $|U|$ and $c = \frac{n - 1}{2|U|}$ free $G$-orbits of size $2|U|$.*
3. *For every $u \in U$, the map $\varphi_u : V \to V$ defined by $\varphi_u(x) = ux$ ($x \in R$) and $\varphi_u(\infty) = \infty$ is an automorphism of $\mathcal{F}(S)$ satisfying $\varphi_u(F_a) = F_{ua}$.*
4. *Let $D \subset R \setminus \{0\}$ contain one representative from each $G$-orbit ($|D| = c$). Then $\mathcal{F}(S)$ is a perfect 1-factorization of $K_{n+1}$ if and only if $F_0 \cup F_d$ is a Hamiltonian cycle of length $n + 1$ for every $d \in D$.*

*Proof.*
1. Since $R$ is commutative and $(-1)^2 = 1$, $U \cup (-U)$ is a subgroup containing $-1$ and $U$, so $G = U \cup (-U)$. Since $|U|$ is odd and $-1$ has order $2$ ($n$ is odd so $1 \ne -1$), $-1 \notin U$. If $u = -v$ for $u, v \in U$, then $-1 = u v^{-1} \in U$, contradiction. Hence $U \cap (-U) = \emptyset$ and $|G| = 2|U|$.
2. Let $x \in R \setminus \{0\}$. If $ux = x$ for $u \in U \setminus \{1\}$, then $(u - 1)x = 0$; multiplying by $(u - 1)^{-1} \in R^\times$ gives $x = 0$, contradiction. If $-ux = x$ for $u \in U$, then $(-u)^{|U|} x = x$; since $|U|$ is odd, $(-u)^{|U|} = -u^{|U|} = -1$, so $-x = x$, i.e., $2x = 0$. Since $|R| = n$ is odd, $2 \in R^\times$, so $x = 0$, contradiction. Thus $U$ and $G$ act freely on $R \setminus \{0\}$, so by orbit-stabilizer every $U$-orbit has size $|U|$ and every $G$-orbit has size $2|U|$, giving $2c = (n-1)/|U|$ $U$-orbits and $c = (n-1)/(2|U|)$ $G$-orbits.
3. Since $u \in R^\times$, $\varphi_u$ is a bijection of $V$. For any $a \in R$ and $\{x, y\} \in S$, $\varphi_u(\{x + a, y + a\}) = \{ux + ua, uy + ua\} = u\{x, y\} + ua \in uS + ua = S + ua$, and $\varphi_u(\{a, \infty\}) = \{ua, \infty\}$. Hence $\varphi_u(F_a) = F_{ua}$.
4. For any distinct $a, b \in R$, the translation $\tau_{-a}(x) = x - a$ ($\tau_{-a}(\infty) = \infty$) is a graph automorphism sending $F_a \cup F_b$ to $F_0 \cup F_{b - a}$, and $\tau_{-(b - a)}$ sends $F_0 \cup F_{b - a}$ to $F_{a - b} \cup F_0 = F_0 \cup F_{-(b - a)}$. By (3), $\varphi_u(F_0 \cup F_d) = F_0 \cup F_{ud}$ for all $u \in U$. Hence the set $H = \{d \in R \setminus \{0\} : F_0 \cup F_d \text{ is a Hamilton cycle}\}$ is closed under multiplication by $-1$ and $U$, so $H$ is a union of $G$-orbits. Therefore $H = R \setminus \{0\}$ if and only if $D \subseteq H$. $\square$

*Remark.* When $R = \mathbb{Z}_n$, Proposition 1.1 recovers Maciosowski (arXiv:2610.20408, Lemmas 2.3, 2.4, 2.13–2.15). When $R = \mathbb{F}_{p^r}$ is a finite field, every non-zero element is a unit, so **every** odd-order subgroup $U \le \mathbb{F}_{p^r}^\times$ is automatically admissible (recovering the quotient coset starters of Dinitz–Stinson 1989 and symmetric cyclotomic orthomorphisms of Wanless 2005). When $R = \prod_i \mathbb{F}_{p_i^{a_i}}$ is a product of finite fields, an odd-order subgroup $U \le \prod_i \mathbb{F}_{p_i^{a_i}}^\times$ is admissible iff no non-identity element has coordinate $1$ in any factor, giving $|U| \mid \gcd_i \mathrm{odd}(p_i^{a_i} - 1)$ (which strictly extends $\mathbb{Z}_n^*$ whenever some $a_i \ge 2$, e.g. $R = \mathbb{F}_{25} \times \mathbb{F}_7$ for $K_{176}$).

---

## 2. Theorem A (draft): $K_{1682}$ has a perfect 1-factorization

**Theorem A.** *The complete graph $K_{1682}$ admits a perfect 1-factorization.*

*Proof (constructive certificate + independent brute-force verifiers).*
Let $R = \mathbb{F}_{41^2} = \mathbb{F}_{41}[t] / (t^2 + t + 12)$.
1. **Field verification.** For every $r \in \mathbb{F}_{41}$, $r^2 + r + 12 \not\equiv 0 \pmod{41}$ (its discriminant is $1 - 48 = -47 \equiv 35 \pmod{41}$, and $35^{20} \equiv -1 \pmod{41}$), so $t^2 + t + 12$ is irreducible over $\mathbb{F}_{41}$ and $R$ is a finite field of order $q = 41^2 = 1681$.
   We encode each element $a + bt \in R$ ($a, b \in \{0, \dots, 40\}$) as the integer $v = a + 41b \in \{0, \dots, 1680\}$, and label the vertex at infinity by $\infty = 1681$.
2. **Admissible subgroup.** The element $t$ (encoded as $41$) is a primitive root of $R^\times$ of order $1680 = 2^4 \cdot 3 \cdot 5 \cdot 7$: direct calculation confirms $t^{1680} = 1$ and $t^{1680/p} \ne 1$ for $p \in \{2, 3, 5, 7\}$.
   Let $u_0 = t^{16} = 6 + 32t$ (encoded as $1318$) and $U = \langle u_0 \rangle \le R^\times$. Then $|U| = 105$ (odd), and since $R$ is a field, $u - 1 \in R^\times$ for all $u \in U \setminus \{1\}$, so $U$ is admissible with $c = 1680 / (2 \cdot 105) = 8$ orbits of $G = \langle -1, U \rangle$ on $R \setminus \{0\}$.
3. **Explicit $U$-invariant starter.** Let $S$ be the union of the $U$-orbits of the $8$ representative pairs:
   $$\{1, 328\},\; \{3, 813\},\; \{15, 1532\},\; \{43, 387\},\; \{4, 1300\},\; \{6, 781\},\; \{2, 650\},\; \{11, 728\}.$$
   The $8$ $U$-orbits consist of $8 \times 105 = 840$ pairwise disjoint pairs partitioning $R \setminus \{0\}$, whose $1680$ signed differences $\pm(x - y)$ cover $R \setminus \{0\}$ exactly once (saved explicitly in [`data/k1682_starter.txt`](data/k1682_starter.txt)).
4. **Full 1-factorization and verification.** Define $F_a = (S + a) \cup \{\{a, 1681\}\}$ for $a \in \{0, \dots, 1680\}$ (saved explicitly in [`data/k1682_matchings.txt.xz`](data/k1682_matchings.txt.xz), 3,537,784 bytes).
   - **Algebraic orbit check (pure Python, [`verify_k1682_independent.py`](verify_k1682_independent.py)):** Checks that $S$ is a $U$-invariant starter and that $F_0 \cup F_d$ is a single 1682-cycle for all $8$ $G$-orbit representatives $d \in \{1, 2, 3, 6, 41, 43, 45, 48\}$. By Proposition 1.1(4), this already implies $\mathcal{F}(S)$ is perfect.
   - **Independent brute-force verification #1 ([`verify_p1f.c`](verify_p1f.c), standalone C, no shared code, no symmetry assumed):** Decompresses `data/k1682_matchings.txt.xz` and directly checks all $1681$ matchings, all $1{,}413{,}721$ edges, and all $\binom{1681}{2} = 1{,}412{,}040$ unordered pairs $(F_i, F_j)$:
     ```
     VERIFIED PERFECT 1-FACTORIZATION OF K_1682: 1681 perfect matchings, 1413721 edges partitioned, all 1412040 pairs form a single Hamiltonian 1682-cycle (3.571 s).
     ```
   - **Independent brute-force verification #2 ([`verify_k1682_independent.py`](verify_k1682_independent.py), standalone Python + Numba, no shared code):** Independently reconstructs $\mathbb{F}_{41}[t]/(t^2+t+12)$ from scratch and brute-force checks all $1{,}412{,}040$ pairs:
     ```
     [4] Independent Numba brute-force check PASSED: all 1412040 unordered pairs of 1-factors of K_1682 form a single 1682-cycle (brute-force 5.132 s, total 6.377 s).
     ```
   Hence $\mathcal{F}(S)$ is a perfect 1-factorization of $K_{1682}$. $\square$

*Corollaries (following Pike 2019, Corollaries 1–2).* By Laufer (1980, *Ars Combin.* 9, 43–46; cited via Pike 2019), a perfect 1-factorization of $K_{1681, 1681}$ exists; by Xu et al. (1999, *IEEE Trans. Inform. Theory* 45, 1817–1826; cited via Pike 2019), a B-code $B_{1681}$ exists. (Note: original Laufer 1980 and Xu et al. 1999 papers were not opened; both implications are secondary citations via Pike 2019, p. 4.)

---

## 3. Symmetry obstruction theorems for $K_{64}$

We establish that neither starters in **any** of the four groups of order $63$ nor even starters in $\mathbb{Z}_{62}$ admit any non-trivial multiplier or affine symmetry reduction for $K_{64}$.

**Lemma 3.1 (At most two fixed points; cf. Ihrig 1989, Remark 1.3(d)).**
*If $\alpha$ is a non-identity automorphism of a perfect 1-factorization $\mathcal{F}$ of $K_{2n}$, then $\alpha$ fixes at most two vertices.*

*Proof.* Suppose $\alpha$ fixes three distinct vertices $a, b, c$. Let $F \in \mathcal{F}$ be the unique 1-factor containing the edge $\{a, b\}$, and $F' \in \mathcal{F}$ the unique 1-factor containing $\{a, c\}$. Since $b \ne c$, $F \ne F'$. Because $\alpha$ fixes $a, b, c$, it fixes the edges $\{a, b\}$ and $\{a, c\}$, hence $\alpha(F) = F$ and $\alpha(F') = F'$. Therefore $\alpha$ restricts to an automorphism of the Hamiltonian cycle $F \cup F'$ fixing the vertex $a$ and both of its neighbors $b$ and $c$. The only automorphism of a cycle fixing a vertex and both its neighbors is the identity, so $\alpha$ fixes every vertex of $K_{2n}$, contradiction. $\square$

**Theorem 3.2 (No automorphism reduction for starters in any group of order 63).**
*Up to isomorphism there are four groups of order $63$: $\mathbb{Z}_{63}$, $\mathbb{Z}_3 \times \mathbb{Z}_{21}$, $\mathbb{Z}_7 \rtimes \mathbb{Z}_9$, and $F_{21} \times \mathbb{Z}_3 = (\mathbb{Z}_7 \rtimes \mathbb{Z}_3) \times \mathbb{Z}_3$. For every group $G$ of order $63$, no starter $S$ in $G$ (with left differences $xy^{-1}$ and factors $F_g = Sg \cup \{\{g, \infty\}\}$) can satisfy $\alpha(S) = S$ for a non-identity group automorphism $\alpha \in \mathrm{Aut}(G)$ and induce a perfect 1-factorization of $K_{64}$.*

*Proof.*
If $\alpha \in \mathrm{Aut}(G)$ satisfies $\alpha(S) = S$, then $\varphi_\alpha : G \cup \{\infty\} \to G \cup \{\infty\}$ given by $\varphi_\alpha(g) = \alpha(g)$ and $\varphi_\alpha(\infty) = \infty$ satisfies $\varphi_\alpha(F_g) = \alpha(S)\alpha(g) \cup \{\{\alpha(g), \infty\}\} = F_{\alpha(g)}$, so $\varphi_\alpha$ is a non-identity automorphism of $\mathcal{F}(S)$ fixing both $1_G$ and $\infty$.
By Lemma 3.1, every non-identity power $\beta = \alpha^k$ in the cyclic subgroup $\langle \alpha \rangle$ must fix **no** element of $G \setminus \{1_G\}$ (i.e., $\langle \alpha \rangle$ acts fixed-point-freely on $G \setminus \{1_G\}$).

*Case 1: $|\alpha|$ is divisible by an odd prime $q$.*
Choose a power $\beta \in \langle \alpha \rangle$ of prime order $q$. Since $63 = 3^2 \cdot 7$, by Sylow's theorem $G$ has a unique (hence characteristic) Sylow $7$-subgroup $P_7 \cong \mathbb{Z}_7$. Thus $\beta(P_7) = P_7$, so $\beta$ acts fixed-point-freely on $P_7 \setminus \{1_G\}$ (size $6$), forcing $q \mid 6$, hence $q = 3$.
Now $\beta$ induces an automorphism $\bar{\beta}$ of the quotient group $G / P_7$ (order $9$). Since $\bar{\beta}$ fixes the identity coset $P_7$, the remaining $8$ cosets partition into orbits of sizes dividing $3$. Because $8 \equiv 2 \pmod 3$, at least two non-identity cosets $C \ne P_7$ are fixed setwise by $\beta$ ($\beta(C) = C$). On any such coset $C$ (which has $|C| = 7 \equiv 1 \pmod 3$ elements), $\beta$ must fix at least one element $g \in C \subseteq G \setminus \{1_G\}$, contradicting Lemma 3.1.

*Case 2: $|\alpha|$ is a power of $2$ (so $2 \mid |\alpha|$).*
Choose a power $\beta \in \langle \alpha \rangle$ of order $2$. Then $\beta$ is a fixed-point-free involution of $G$. Define $f : G \to G$ by $f(x) = x^{-1}\beta(x)$. If $f(x) = f(y)$, then $\beta(x)\beta(y)^{-1} = xy^{-1}$, so $\beta(xy^{-1}) = xy^{-1}$; since $\beta$ fixes only $1_G$, $x = y$. Thus $f$ is injective, hence surjective. For any $z \in G$, writing $z = x^{-1}\beta(x)$ gives $\beta(z) = \beta(x)^{-1} x = z^{-1}$. Since inversion $z \mapsto z^{-1}$ is a group automorphism if and only if $G$ is abelian, $G$ cannot be $\mathbb{Z}_7 \rtimes \mathbb{Z}_9$ or $F_{21} \times \mathbb{Z}_3$.
When $G$ is abelian ($\mathbb{Z}_{63}$ or $\mathbb{Z}_3 \times \mathbb{Z}_{21}$), $\beta(x) = -x$, so $-S = S$. For any pair $\{x, y\} \in S$, the pair $\{-x, -y\} \in S$ has the same differences $\pm(x - y)$; since every difference occurs once in $S$, we must have $\{-x, -y\} = \{x, y\}$. As $n = 63$ is odd and $x \ne 0$, $-x \ne x$, forcing $y = -x$. Thus $S = P = \{\{x, -x\} : x \in G \setminus \{0\}\}$ is the patterned starter. Taking $d \in P_7 \setminus \{0\}$, every neighbor of a vertex in $P_7 \cup \{\infty\}$ under $F_0 \cup F_d$ lies in $P_7 \cup \{\infty\}$ (in $F_0$: $y \mapsto -y$, $0 \leftrightarrow \infty$; in $F_d$: $y \mapsto 2d - y$, $d \leftrightarrow \infty$). Thus the cycle through $\infty$ in $F_0 \cup F_d$ has length at most $|P_7| + 1 = 8 < 64$, so $\mathcal{F}(P)$ is not perfect. $\square$

*Computational cross-check:* [`verify_k64_obstructions.py`](verify_k64_obstructions.py) enumerates all elements of $\mathrm{Aut}(G)$ for all four groups ($|\mathrm{Aut}| = 36, 288, 126, 252$ respectively) and confirms `0` non-trivial admissible cyclic subgroups $\langle \alpha \rangle$ in every case.

**Theorem 3.3 (No affine symmetry reduction for even starters in $\mathbb{Z}_{62}$).**
*Let $E$ be an even starter in $\mathbb{Z}_{62}$ (a set of $30$ disjoint pairs covering $\mathbb{Z}_{62} \setminus \{a, b\}$ whose differences $\pm(x-y)$ cover $\mathbb{Z}_{62} \setminus \{0, 31\}$ once), inducing the 1-factorization $\mathcal{F}(E) = \{M, F_0, \dots, F_{61}\}$ of $K_{64}$ on $\mathbb{Z}_{62} \cup \{\infty_1, \infty_2\}$ where $F_i = (E + i) \cup \{\{a+i, \infty_1\}, \{b+i, \infty_2\}\}$ and $M = \{\{x, x+31\} : 0 \le x < 31\} \cup \{\{\infty_1, \infty_2\}\}$. No non-identity affine map $\psi(x) = ux + c$ ($u \in \mathbb{Z}_{62}^\times$, $c \in \mathbb{Z}_{62}$) preserving $E$ can extend (either fixing or swapping $\{\infty_1, \infty_2\}$) to an automorphism of a perfect 1-factorization $\mathcal{F}(E)$.*

*Proof.*
Suppose $\psi(x) = ux + c$ preserves $E$ ($\psi(E) = E$) and extends to an automorphism $\tilde{\psi}$ of $\mathcal{F}(E)$ preserving $\{\infty_1, \infty_2\}$ setwise. Since $\psi$ is not the identity, consider three exhaustive cases on the unit $u \in \mathbb{Z}_{62}^\times \cong \mathbb{Z}_{31}^\times$ (order $30$):

*Case 1: $u = 1$ and $c \ne 0$.*
Since $\psi(E) = E$, $\psi$ maps the uncovered pair $\{a, b\}$ to $\{a + c, b + c\} = \{a, b\}$. As $c \ne 0$, we must have $a + c \equiv b$ and $b + c \equiv a \pmod{62}$, so $2c \equiv 0 \pmod{62}$, forcing $c = 31$ and $b \equiv a + 31 \pmod{62}$. Then $F_0$ contains $\{a, \infty_1\}$ and $\{a + 31, \infty_2\}$, while $F_{31}$ contains $\{a + 31, \infty_1\}$ and $\{a, \infty_2\}$. Their union $F_0 \cup F_{31}$ contains the $4$-cycle $\infty_1 - a - \infty_2 - (a + 31) - \infty_1$, so $\mathcal{F}(E)$ is not perfect.

*Case 2: $u \ne 1$ and $\mathrm{ord}(u)$ has an odd prime divisor $q \in \{3, 5\}$.*
Let $\tilde{\beta} = \tilde{\psi}^k$ be a power of $\tilde{\psi}$ of odd prime order $q$, acting on $\mathbb{Z}_{62}$ as $\beta(x) = vx + c'$ where $v \in \mathbb{Z}_{62}^\times$ has order $q \in \{3, 5\}$.
Because $q$ is odd, $\tilde{\beta}$ cannot swap $\{\infty_1, \infty_2\}$, so $\tilde{\beta}$ fixes both $\infty_1$ and $\infty_2$.
Modulo $2$, every unit $v \in \mathbb{Z}_{62}^\times$ satisfies $v \equiv 1 \pmod 2$, so $\beta^q(x) \equiv x + q c' \pmod 2$. Since $\beta^q = \mathrm{id}$ and $q$ is odd, $c' \equiv 0 \pmod 2$, so $\beta(x) \equiv x \pmod 2$ for all $x$.
Modulo $31$, $v \not\equiv 1 \pmod{31}$ (since $\mathrm{ord}(v) = q > 1$), so $v - 1$ is invertible modulo $31$, and $(v - 1)x + c' \equiv 0 \pmod{31}$ has a unique solution $x_0 \pmod{31}$.
By CRT, $x \equiv x_0 \pmod{31}$ paired with $x \equiv 0 \pmod 2$ and $x \equiv 1 \pmod 2$ yields **two** fixed points of $\beta$ in $\mathbb{Z}_{62}$. Together with $\infty_1$ and $\infty_2$, $\tilde{\beta}$ fixes **four** vertices of $K_{64}$, contradicting Lemma 3.1.

*Case 3: $u \ne 1$ and $\mathrm{ord}(u)$ is a power of $2$.*
Since $\mathbb{Z}_{62}^\times \cong \mathbb{Z}_{31}^\times$ is cyclic of order $30 = 2 \cdot 15$, the unique element of order $2$ is $u = -1 \equiv 61 \pmod{62}$, so $\psi(x) = c - x$.
For every pair $\{x, y\} \in E$, the image $\psi(\{x, y\}) = \{c - x, c - y\} \in E$ has the exact same differences $\pm(x - y)$ as $\{x, y\}$. Since every non-half difference in $\mathbb{Z}_{62} \setminus \{0, 31\}$ occurs exactly once in $E$, we must have $\{c - x, c - y\} = \{x, y\}$ for every $\{x, y\} \in E$. Because $x \ne y$, we cannot have $c - x = x$ and $c - y = y$ for the same pair unless both $2x \equiv c$ and $2y \equiv c \pmod{62}$, which would make $x - y \equiv 31 \pmod{62}$ (the excluded half-difference!). Hence $c - x = y$ for **every** pair $\{x, y\} \in E$, so $x + y \equiv c \pmod{62}$ and therefore $x - y \equiv 2x - c \equiv c \pmod 2$ has constant parity for all $30$ pairs in $E$. This contradicts the fact that $E$ must cover both odd and even differences in $\{1, \dots, 30\}$. $\square$

*Computational cross-check:* [`verify_k64_obstructions.py`](verify_k64_obstructions.py) directly checks all $30 \times 62 - 1 = 1859$ non-identity affine maps on $\mathbb{Z}_{62}$ (for both fixing and swapping $\{\infty_1, \infty_2\}$) and confirms every one is obstructed.

**Corollary 3.4 (2-Sylow bound for any P1F of $K_{64}$).**
*For any perfect 1-factorization $\mathcal{F}$ of $K_{64}$, $|\mathrm{Syl}_2(\mathrm{Aut}(\mathcal{F}))| \le 2$.*

*Proof (using Ihrig 1989 T2–T3 as summarized in Ivanov & Tertitski, arXiv:2611.01807v2, p. 2).*
Since $64 \equiv 0 \pmod 4$, by Ihrig (1989) no automorphism of $\mathcal{F}$ has order $4$ and no involution is fixed-point-free. Hence every involution fixes exactly $2$ vertices (by Lemma 3.1 and parity of $64$) and any $2$-subgroup $P \le \mathrm{Aut}(\mathcal{F})$ is elementary abelian. If $|P| \ge 4$, let $V_4 = \{1, \sigma_1, \sigma_2, \sigma_3\} \le P$ be a Klein four-group acting on the $64$ vertices. By Burnside's lemma, the number of $V_4$-orbits on $V(K_{64})$ would be $\frac{1}{4}(64 + 2 + 2 + 2) = \frac{70}{4} = 17.5 \notin \mathbb{Z}$, a contradiction. Thus $|P| \le 2$. $\square$
*(`UNVERIFIED CITATION:` Corollary 3.4 relies on Ihrig 1989 T2–T3 via the secondary summary in Ivanov & Tertitski 2026, p. 2; the original Ihrig 1989 PDF was not opened. Theorems 3.2 and 3.3 are completely self-contained and do not use T2–T3.)*
