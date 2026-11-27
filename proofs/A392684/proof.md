# Proof of Zhi-Wei Sun's Conjecture in OEIS A392684 ($k = 3$)

## Theorem

Every integer $n \ge 6$ can be written as $n = x + y + z$ with integers $x \ge y \ge z \ge 1$ such that
$$\mathrm{lcm}(x, y, z) = m(m+1)(m+2)$$
for some positive integer $m$. Moreover, no integer $1 \le n \le 5$ has such a representation.

This proves Conjecture (i) of OEIS [A392684](https://oeis.org/A392684) for $k = 3$ and establishes $N(3) = 6$ in Conjecture (ii).

## Proof

### 1. Impossibility for $1 \le n \le 5$

If $x + y + z = n \le 5$ with $x \ge y \ge z \ge 1$, then $x, y, z \in \{1, 2, 3\}$ and at most one of them can exceed $2$, so $\mathrm{lcm}(x, y, z) \in \{1, 2, 3, 4\} < 6 = 1 \cdot 2 \cdot 3$. Since $m(m+1)(m+2) \ge 6$ for all $m \ge 1$, no representation exists for $1 \le n \le 5$.

### 2. Master LCM Lemmas

For any positive integer $m$ and positive integers $a, b, c$ satisfying
$$a \mid (m+1)(m+2), \qquad b \mid m(m+2), \qquad c \mid m(m+1),$$
we immediately have $\mathrm{lcm}(a m, b(m+1), c(m+2)) \mid m(m+1)(m+2)$. Equality holds in each of the following four cases:

1. **Case A ($m$ odd):** $m, m+1, m+2$ are pairwise coprime, so $m(m+1)(m+2) \mid \mathrm{lcm}(a m, b(m+1), c(m+2))$.
2. **Case B1 ($m = 2k$ even, $2 \mid a$ and $2 \mid c$):** $4k \mid a m$ and $4(k+1) \mid c(m+2)$, so $\mathrm{lcm}(4k, 4(k+1)) = 4 \mathrm{lcm}(k, k+1) = 4k(k+1) = m(m+2)$ divides the lcm; since $\gcd(m(m+2), m+1) = 1$, $m(m+1)(m+2)$ divides the lcm.
3. **Case B2 ($m = 4k$, $2 \mid a$):** $8k \mid a m$ and $2k+1 \mid (m+2)$, with $\gcd(8k, 2k+1) = 1$, so $8k(2k+1) = 4k(4k+2) = m(m+2)$ divides the lcm; since $\gcd(m(m+2), m+1) = 1$, $m(m+1)(m+2)$ divides the lcm.
4. **Case B3 ($m = 4k + 2$, $2 \mid c$):** $2k+1 \mid m$ and $8(k+1) \mid c(m+2)$, with $\gcd(2k+1, 8(k+1)) = 1$, so $8(k+1)(2k+1) = (4k+2)(4k+4) = m(m+2)$ divides the lcm; since $\gcd(m(m+2), m+1) = 1$, $m(m+1)(m+2)$ divides the lcm.

### 3. Explicit 24-Template Covering System Modulo 240

Every integer $n \ge 6$ except $n = 14$ falls into at least one of the following 24 arithmetic progressions, which together cover **all 240 residue classes modulo 240**. In each row, setting $x = a m, y = b(m+1), z = c(m+2)$ (and sorting $x, y, z$ in non-increasing order) gives $x + y + z = n$ and $\mathrm{lcm}(x, y, z) = m(m+1)(m+2)$ by the indicated Master Lemma:

| # | Congruence for $n$ | Min $n$ | $(a, b, c)$ | Congruence for $m$ | Case |
|---|---|---|---|---|---|
| 1 | $n \equiv 0 \pmod{6}$ | $6$ | $(1, 1, 1)$ | $m \equiv 1 \pmod 2$ | A |
| 2 | $n \equiv 1 \pmod{8}$ | $9$ | $(1, 1, 2)$ | $m \equiv 1 \pmod 2$ | A |
| 3 | $n \equiv 7 \pmod{8}$ | $7$ | $(2, 1, 1)$ | $m \equiv 1 \pmod 2$ | A |
| 4 | $n \equiv 0 \pmod{10}$ | $10$ | $(2, 1, 2)$ | $m \equiv 1 \pmod 2$ | A |
| 5 | $n \equiv 5 \pmod{10}$ | $15$ | $(2, 1, 2)$ | $m \equiv 0 \pmod 2$ | B1 |
| 6 | $n \equiv 3 \pmod{16}$ | $19$ | $(2, 1, 1)$ | $m \equiv 0 \pmod 4$ | B2 |
| 7 | $n \equiv 8 \pmod{16}$ | $24$ | $(2, 4, 2)$ | $m \equiv 0 \pmod 2$ | B1 |
| 8 | $n \equiv 13 \pmod{16}$ | $13$ | $(1, 1, 2)$ | $m \equiv 2 \pmod 4$ | B3 |
| 9 | $n \equiv 4 \pmod{20}$ | $24$ | $(2, 2, 1)$ | $m \equiv 0 \pmod 4$ | B2 |
| 10 | $n \equiv 16 \pmod{20}$ | $16$ | $(1, 2, 2)$ | $m \equiv 2 \pmod 4$ | B3 |
| 11 | $n \equiv 3 \pmod{24}$ | $27$ | $(1, 1, 4)$ | $m \equiv 3 \pmod 4$ | A |
| 12 | $n \equiv 21 \pmod{24}$ | $21$ | $(4, 1, 1)$ | $m \equiv 3 \pmod 4$ | A |
| 13 | $n \equiv 2 \pmod{30}$ | $32$ | $(1, 1, 3)$ | $m \equiv 5 \pmod 6$ | A |
| 14 | $n \equiv 8 \pmod{30}$ | $8$ | $(3, 1, 1)$ | $m \equiv 1 \pmod 6$ | A |
| 15 | $n \equiv 22 \pmod{30}$ | $22$ | $(1, 1, 3)$ | $m \equiv 3 \pmod 6$ | A |
| 16 | $n \equiv 28 \pmod{30}$ | $28$ | $(3, 1, 1)$ | $m \equiv 5 \pmod 6$ | A |
| 17 | $n \equiv 5 \pmod{48}$ | $53$ | $(1, 1, 6)$ | $m \equiv 5 \pmod 6$ | A |
| 18 | $n \equiv 11 \pmod{48}$ | $11$ | $(6, 1, 1)$ | $m \equiv 1 \pmod 6$ | A |
| 19 | $n \equiv 37 \pmod{48}$ | $37$ | $(1, 1, 6)$ | $m \equiv 3 \pmod 6$ | A |
| 20 | $n \equiv 43 \pmod{48}$ | $43$ | $(6, 1, 1)$ | $m \equiv 5 \pmod 6$ | A |
| 21 | $n \equiv 14 \pmod{60}$ | $74$ | $(2, 2, 6)$ | $m \equiv 0 \pmod 6$ | B1 |
| 22 | $n \equiv 26 \pmod{60}$ | $26$ | $(6, 2, 2)$ | $m \equiv 2 \pmod 6$ | B1 |
| 23 | $n \equiv 34 \pmod{60}$ | $34$ | $(2, 2, 6)$ | $m \equiv 2 \pmod 6$ | B1 |
| 24 | $n \equiv 46 \pmod{60}$ | $46$ | $(6, 2, 2)$ | $m \equiv 4 \pmod 6$ | B1 |

### 4. The Lone Finite Case ($n = 14$)

The only integer $n \ge 6$ not covered by the 24 templates above (since Template 21 starts at $n = 74$ for $m = 6$) is $n = 14$, which is represented by
$$14 = 6 + 6 + 2, \qquad \mathrm{lcm}(6, 6, 2) = 6 = 1 \cdot 2 \cdot 3.$$

Hence every integer $n \ge 6$ has a valid representation. $\blacksquare$

## Formal Verification

The entire proof above — including all 4 Master LCM Lemmas, all 24 templates, the complete covering mod 240, the finite case $n = 14$, and the impossibility for $1 \le n \le 5$ — is formally verified with zero `sorry` and zero external dependencies in [`A392684.lean`](A392684.lean).
