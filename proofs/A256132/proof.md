# Proof of OEIS A256132

## Statement

From OEIS [A256132](https://oeis.org/A256132) (Zhi-Wei Sun, Mar 15 2015):

> Number of ways to write $n$ as $w(3w+1)/2 + x(3x-1)/2 + y(3y-1)/2 + z(3z-1)/2$, where $w,x,y,z$ are nonnegative integers with $x \le y \le z$.
>
> **Conjecture:** $a(n) > 0$ for all $n$. In other words, any nonnegative integer $n$ can be expressed as the sum of three pentagonal numbers and a second pentagonal number.

Here $w, x, y, z \in \mathbb{Z}_{\ge 0}$ (with $0$ allowed). Because the sum of the three pentagonal terms $\frac{x(3x-1)}{2} + \frac{y(3y-1)}{2} + \frac{z(3z-1)}{2}$ is symmetric in $(x, y, z)$, any representation in nonnegative integers $(w, x, y, z)$ yields one with $x \le y \le z$ upon sorting $(x, y, z)$.

---

## 1. Hadamard Transform Lemma

**Lemma 1.** Let $B, U, V, W \in \mathbb{Z}$ be four odd integers satisfying
$$B + U + V + W \equiv 0 \pmod 4.$$
Define
$$w = \frac{B + U + V + W}{4}, \quad x = \frac{B + U - V - W}{4}, \quad y = \frac{B - U + V - W}{4}, \quad z = \frac{B - U - V + W}{4}.$$
Then:
1. $w, x, y, z \in \mathbb{Z}$.
2. $w^2 + x^2 + y^2 + z^2 = \frac{1}{4}(B^2 + U^2 + V^2 + W^2)$ and $w - x - y - z = \frac{1}{2}(-B + U + V + W)$.
3. Consequently,
   $$\frac{w(3w+1)}{2} + \frac{x(3x-1)}{2} + \frac{y(3y-1)}{2} + \frac{z(3z-1)}{2} = \frac{(3B - 1)^2 + (3U + 1)^2 + (3V + 1)^2 + (3W + 1)^2 - 4}{24}.$$
4. If $|U| + |V| + |W| \le B$, then $w, x, y, z \ge 0$.

*Proof.*
1. By assumption $w \in \mathbb{Z}$. Since $U, V, W$ are odd, $V + W$, $U + W$, and $U + V$ are even, so
   $$x = w - \frac{V + W}{2}, \quad y = w - \frac{U + W}{2}, \quad z = w - \frac{U + V}{2}$$
   are integers.
2. Direct expansion gives $16(w^2 + x^2 + y^2 + z^2) = 4(B^2 + U^2 + V^2 + W^2)$ and
   $$4(w - x - y - z) = (B + U + V + W) - (3B - U - V - W) = 2(-B + U + V + W).$$
3. Substituting (2) into the left-hand side:
   $$\frac{3(w^2 + x^2 + y^2 + z^2) + (w - x - y - z)}{2} = \frac{3(B^2 + U^2 + V^2 + W^2) + 2(-B + U + V + W)}{8} = \frac{9(B^2 + U^2 + V^2 + W^2) + 6(-B + U + V + W) + 4 - 4}{24} = \frac{(3B-1)^2 + (3U+1)^2 + (3V+1)^2 + (3W+1)^2 - 4}{24}.$$
4. Each numerator is at least $B - |U| - |V| - |W| \ge 0$. $\square$

---

## 2. Main Theorem

**Theorem.** *Every integer $n \ge 0$ can be written as $n = \frac{w(3w+1)}{2} + \frac{x(3x-1)}{2} + \frac{y(3y-1)}{2} + \frac{z(3z-1)}{2}$ with $w, x, y, z \in \mathbb{Z}_{\ge 0}$.*

*Proof.* For $0 \le n \le 5459$, direct verification in [`verify.py`](verify.py) constructs an explicit nonnegative solution $(w, x, y, z)$ for every $n$. Now assume $n \ge 5460$.

Set
$$R := \frac{\sqrt{24n + 4} + 1}{3}.$$
Since $n \ge 5460$, we have $24n + 4 \ge 131044 = 362^2$, so $R \ge \frac{362 + 1}{3} = 121$.

Define the target residue class $r_8 \in \{3, 7\}$ by
$$r_8 := \begin{cases} 7 & \text{if } n \equiv 1 \pmod 4, \\ 3 & \text{otherwise.} \end{cases}$$
Let $B_1$ be the largest integer strictly less than $R$ with $B_1 \equiv r_8 \pmod 8$, and let $B_2 := B_1 - 8$. Then
$$R - 8 \le B_1 < R \qquad \text{and} \qquad R - 16 \le B_2 < R - 8.$$
Since $B_1 - B_2 = 8 \equiv 2 \not\equiv 0 \pmod 3$, we have $B_1 \not\equiv B_2 \pmod 3$, so at least one $B \in \{B_1, B_2\}$ satisfies
$$2n + 1 + 2B \not\equiv 0 \pmod 3.$$
Fix such a $B$. Then:
- $B \ge R - 16 \ge 121 - 16 = 105$;
- $B < R$, so $3B - 1 < \sqrt{24n + 4}$ and hence $M := 24n + 4 - (3B - 1)^2 > 0$;
- $B \equiv r_8 \equiv 3 \pmod 4$.

Check the divisibility of $M$ by $3$, $9$, and $4$:
1. **Mod 9:** Expanding $(3B - 1)^2 = 9B^2 - 6B + 1$,
   $$M = 24n + 4 - (9B^2 - 6B + 1) = 3(8n + 1 + 2B - 3B^2) \equiv 3(2n + 1 + 2B) \pmod 9.$$
   Since $2n + 1 + 2B \not\equiv 0 \pmod 3$, we have $3 \mid M$ and $9 \nmid M$.
2. **Mod 4 and Mod 32:** Since $B \equiv 3 \pmod 4$, we have $3B - 1 \equiv 0 \pmod 4$, so $4 \mid M$ and $m_4 := M / 4 = 6n + 1 - \bigl(\frac{3B-1}{2}\bigr)^2 \ge 1$.
   - If $B = 8t + 3$, then $\frac{3B - 1}{2} = 12t + 4 \equiv 4 \pmod 8$, so $\bigl(\frac{3B-1}{2}\bigr)^2 \equiv 0 \pmod 8$.
   - If $B = 8t + 7$, then $\frac{3B - 1}{2} = 12t + 10 \equiv 2 \pmod 8$, so $\bigl(\frac{3B-1}{2}\bigr)^2 \equiv 4 \pmod 8$.

   Therefore:
   - if $n \equiv 1 \pmod 4$, then $B \equiv 7 \pmod 8$ and $m_4 \equiv 6n + 1 - 4 \equiv 7 - 4 = 3 \pmod 8$;
   - if $n \equiv 3 \pmod 4$, then $B \equiv 3 \pmod 8$ and $m_4 \equiv 6n + 1 \equiv 19 \equiv 3 \pmod 8$;
   - if $n$ is even, then $B \equiv 3 \pmod 8$ and $m_4 \equiv 6n + 1 \equiv 1$ or $5 \pmod 8$.

   In every case $m_4$ is a positive odd integer with $m_4 \not\equiv 7 \pmod 8$, and $3 \mid m_4$, $9 \nmid m_4$.

By the Gauss–Legendre three-squares theorem (Legendre 1798; Gauss, *Disquisitiones Arithmeticae*, 1801, Art. 291), there exist integers $x_0, y_0, z_0$ such that
$$x_0^2 + y_0^2 + z_0^2 = m_4.$$

**Claim:** None of $x_0, y_0, z_0$ is divisible by $3$.
*Proof of Claim.* Modulo $3$, every square is $0$ or $1$. If $3 \mid x_0$, then $y_0^2 + z_0^2 \equiv m_4 \equiv 0 \pmod 3$, which forces $3 \mid y_0$ and $3 \mid z_0$, hence $9 \mid (x_0^2 + y_0^2 + z_0^2) = m_4$, contradicting $9 \nmid m_4$. $\square$

Hence $2x_0, 2y_0, 2z_0 \not\equiv 0 \pmod 3$. Choose the unique signs $X \in \{2x_0, -2x_0\}$, $Y \in \{2y_0, -2y_0\}$, $Z \in \{2z_0, -2z_0\}$ satisfying $X \equiv Y \equiv Z \equiv 1 \pmod 3$, and set
$$U := \frac{X - 1}{3}, \qquad V := \frac{Y - 1}{3}, \qquad W := \frac{Z - 1}{3} \in \mathbb{Z}.$$
Then
$$(3B - 1)^2 + (3U + 1)^2 + (3V + 1)^2 + (3W + 1)^2 = (3B - 1)^2 + 4(x_0^2 + y_0^2 + z_0^2) = (3B - 1)^2 + M = 24n + 4.$$

Check parity and mod 4:
- Since $X, Y, Z$ are even, $3U = X - 1$, $3V = Y - 1$, and $3W = Z - 1$ are odd, so $U, V, W$ are all odd (matching $B \equiv 3 \pmod 4$).
- Since $3U + 1 = \pm 2x_0 \equiv 2x_0 \pmod 4$ and $2x_0 \equiv 2x_0^2 \pmod 4$ (as $x_0 \equiv x_0^2 \pmod 2$), we have
  $$U \equiv -3U = 1 - (3U + 1) \equiv 1 - 2x_0 \equiv 1 + 2x_0^2 \pmod 4.$$
  Similarly $V \equiv 1 + 2y_0^2 \pmod 4$ and $W \equiv 1 + 2z_0^2 \pmod 4$. Since $B \equiv 3 \pmod 4$ and $m_4$ is odd,
  $$B + U + V + W \equiv 3 + (1 + 2x_0^2) + (1 + 2y_0^2) + (1 + 2z_0^2) = 6 + 2m_4 \equiv 6 + 2 = 8 \equiv 0 \pmod 4.$$

Thus $B, U, V, W$ satisfy the hypotheses of Lemma 1. Let $w, x, y, z \in \mathbb{Z}$ be defined by Lemma 1; by Lemma 1(3),
$$\frac{w(3w+1)}{2} + \frac{x(3x-1)}{2} + \frac{y(3y-1)}{2} + \frac{z(3z-1)}{2} = n.$$

Finally, verify $w, x, y, z \ge 0$. By the triangle inequality and Cauchy–Schwarz,
$$|U| + |V| + |W| \le \frac{|X| + 1}{3} + \frac{|Y| + 1}{3} + \frac{|Z| + 1}{3} = 1 + \frac{|X| + |Y| + |Z|}{3} \le 1 + \frac{\sqrt{3(X^2 + Y^2 + Z^2)}}{3} = 1 + \sqrt{\frac{M}{3}}.$$
Since $B \ge R - 16$, we have $\sqrt{24n + 4} = 3R - 1 \le (3B - 1) + 48$, so
$$M = 24n + 4 - (3B - 1)^2 \le \bigl((3B - 1) + 48\bigr)^2 - (3B - 1)^2 = 96(3B - 1) + 2304 = 288B + 2208.$$
Therefore, for all $B \ge 105$,
$$(3B - 3)^2 - 3M \ge (9B^2 - 18B + 9) - (864B + 6624) = 9(B^2 - 98B - 735) = 9(B - 105)(B + 7) \ge 0.$$
Hence $3M \le (3B - 3)^2$, so $1 + \sqrt{M/3} \le B$, which gives $|U| + |V| + |W| \le B$. By Lemma 1(4), $w, x, y, z \ge 0$. $\square$

---

## 3. Computational Verification Summary

Running `python conjectures/A256132/verify.py` verifies:
1. All $101$ published terms ($n = 0, \dots, 100$) of OEIS A256132 match the direct definition.
2. All finite base cases $0 \le n \le 5459$ have explicit nonnegative witnesses directly from the definition.
3. The constructive proof above succeeds without exception on $5460 \le n \le 20{,}000$.
4. Exhaustive verification confirms $a(n) > 0$ for all $0 \le n \le 10^6$.
