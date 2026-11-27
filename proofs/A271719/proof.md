# Proof of OEIS A271719

## Statement

From OEIS [A271719](https://oeis.org/A271719) (Zhi-Wei Sun, Apr 12 2016):

> Number of ordered ways to write $n$ as $x + y + z$ with $x \ge y > 0$, $z > 0$ and $\gcd(x,y,z) = 1$ such that $x^2 + (2y+z)^2$ is a square.
>
> **Conjecture:** $a(n) > 0$ for all $n > 10$, and $a(n) = 1$ only for $n = 11, 12, 14, 18, 24, 54$.

Conventions: offset $= 1$; $(x, y, z)$ are ordered triples of positive integers with $x \ge y \ge 1$, $z \ge 1$, $x + y + z = n$, $\gcd(x, y, z) = 1$, and $x^2 + (2y + z)^2 = w^2$ for some integer $w$.

---

## 1. Exact Bijection to Pythagorean Leg Pairs

**Lemma 1.** *For every positive integer $n$, $a(n)$ equals the number of ordered pairs $(u, v)$ of positive integers such that:*
1. *$u^2 + v^2$ is a square,*
2. *$\gcd(u, v, n) = 1$, and*
3. *$\max\!\bigl(v,\; u + \lfloor v/2 \rfloor + 1\bigr) \le n \le u + v - 1$.*

*Proof.* Define $\Phi(x, y, z) = (u, v) := (x,\, 2y + z)$ and $\Psi(u, v) = (x, y, z) := (u,\, u + v - n,\, 2n - 2u - v)$.

- **Inverse maps:** If $x + y + z = n$ and $(u, v) = (x, 2y + z)$, then
  $$u + v - n = x + (2y + z) - (x + y + z) = y, \qquad 2n - 2u - v = 2(x + y + z) - 2x - (2y + z) = z.$$
  Conversely, for any $(u, v)$, setting $(x, y, z) = \Psi(u, v)$ gives $x + y + z = n$ and $2y + z = v$. Thus $\Phi$ and $\Psi$ are mutually inverse bijections on $\mathbb{Z}^3 \cap \{x+y+z=n\} \leftrightarrow \mathbb{Z}^2$.
- **Square condition:** $x^2 + (2y+z)^2 = u^2 + v^2$.
- **Inequalities:** Under $(x, y, z) = \Psi(u, v)$:
  - $x \ge y \iff u \ge u + v - n \iff v \le n$;
  - $y > 0 \iff u + v - n \ge 1 \iff n \le u + v - 1$;
  - $z > 0 \iff 2n > 2u + v \iff n \ge u + \lfloor v/2 \rfloor + 1$ (since $2n$ is even: if $v = 2k$ then $2n > 2u + 2k \iff n \ge u + k + 1$; if $v = 2k + 1$ then $2n > 2u + 2k + 1 \iff 2n \ge 2u + 2k + 2 \iff n \ge u + k + 1$).
  - Finally, $x \ge y > 0$ and $z > 0$ imply $u = x > 0$ and $v = 2y + z > 0$; conversely, $u > 0$, $v > 0$ and the three inequalities above imply $x = u > 0$, $y > 0$, $z > 0$, and $x \ge y$.
- **Coprimality:** Any common divisor $g$ of $(x, y, z)$ divides $u = x$, $v = 2y + z$, and $n = x + y + z$. Conversely, any common divisor $g$ of $(u, v, n)$ divides $x = u$, $y = u + v - n$, and $z = 2n - 2u - v$. Hence $\gcd(x, y, z) = \gcd(u, v, n)$. $\square$

In particular, every **primitive** Pythagorean leg pair $(a, b)$ (i.e., $a, b > 0$, $a^2 + b^2 = c^2$, $\gcd(a, b) = 1$) automatically satisfies $\gcd(a, b, n) = 1$ for every $n$, and since $a \ne b$ (as $\sqrt{2}$ is irrational), $(a, b)$ and $(b, a)$ are **two distinct** ordered pairs contributing to $a(n)$ whenever $n$ lies in both of their intervals:
$$I(a, b) := \bigl[\max(b,\; a + \lfloor b/2 \rfloor + 1),\; a + b - 1\bigr] \cap \mathbb{Z}, \qquad I(b, a) := \bigl[\max(a,\; b + \lfloor a/2 \rfloor + 1),\; a + b - 1\bigr] \cap \mathbb{Z}.$$

---

## 2. Single-Family Double Covering for $n \ge 1303$

**Lemma 2.** *For every integer $n \ge 1303$, we have $a(n) \ge 2$.*

*Proof.* Consider the set of indices $S := \{r \in \mathbb{Z} : r \ge 18,\; 11 \nmid r\}$. For each $r \in S$, put $m := r + 11$, and define
$$a(r) := m^2 - r^2 = 22r + 121, \qquad b(r) := 2mr = 2r^2 + 22r, \qquad c(r) := m^2 + r^2.$$

1. **Primitive Pythagorean triple:** Clearly $a(r), b(r) > 0$ and $a(r)^2 + b(r)^2 = (m^2 - r^2)^2 + (2mr)^2 = (m^2 + r^2)^2 = c(r)^2$. Since $11$ is prime and $11 \nmid r$, we have $\gcd(m, r) = \gcd(r + 11, r) = \gcd(11, r) = 1$. Moreover, $m - r = 11$ is odd, so $a(r) = (m-r)(m+r)$ is odd while $b(r)$ is even. Any prime $p$ dividing $\gcd(a(r), b(r))$ must therefore be odd and divide $mr$, so $p \mid m$ or $p \mid r$; since $p \mid (m^2 - r^2)$, $p$ divides both $m$ and $r$, contradicting $\gcd(m, r) = 1$. Thus $\gcd(a(r), b(r)) = 1$ and $a(r) \ne b(r)$ (opposite parities).

2. **Common double-covered interval:** Define
   $$L(r) := 2r^2 + 33r + 61, \qquad R(r) := 2r^2 + 44r + 120.$$
   Notice $a(r) + b(r) - 1 = 2r^2 + 44r + 120 = R(r)$. For every $r \ge 18$:
   - For the orientation $(u, v) = (a(r), b(r))$: since $b(r) = 2r^2 + 22r$ is even,
     $$b(r) - \bigl(a(r) + \lfloor b(r)/2 \rfloor + 1\bigr) = (2r^2 + 22r) - (r^2 + 33r + 122) = r^2 - 11r - 122.$$
     At $r = 18$, $18^2 - 11(18) - 122 = 4 > 0$, and the derivative $2r - 11 > 0$ for $r \ge 18$, so $I(a(r), b(r)) = [2r^2 + 22r,\; R(r)] \cap \mathbb{Z}$.
   - For the orientation $(u, v) = (b(r), a(r))$: since $a(r) = 22r + 121$ is odd, $\lfloor a(r)/2 \rfloor + 1 = 11r + 61$, so $b(r) + \lfloor a(r)/2 \rfloor + 1 = 2r^2 + 33r + 61 = L(r)$. Moreover,
     $$L(r) - a(r) = 2r^2 + 11r - 60 > 0 \quad (r \ge 18),$$
     so $I(b(r), a(r)) = [L(r),\; R(r)] \cap \mathbb{Z}$.
   - Since $L(r) - (2r^2 + 22r) = 11r + 61 > 0$, we have the inclusion
     $$[L(r),\; R(r)] \cap \mathbb{Z} = I(b(r), a(r)) \subseteq I(a(r), b(r)).$$
   Hence by Lemma 1, every integer $n \in [L(r), R(r)]$ receives at least **two** distinct valid representations, corresponding to $(u, v) = (a(r), b(r))$ and $(u, v) = (b(r), a(r))$.

3. **Contiguous coverage of all $n \ge 1303$:** The smallest element of $S$ is $r = 18$, with
   $$L(18) = 2(18)^2 + 33(18) + 61 = 648 + 594 + 61 = 1303.$$
   For any $r \in S$, the next element $r' \in S$ is either $r + 1$ (if $11 \nmid (r + 1)$) or $r + 2$ (if $11 \mid (r + 1)$, since then $11 \nmid (r + 2)$). Because $L(r)$ is strictly increasing for $r \ge 1$,
   $$L(r') \le L(r + 2) = 2(r + 2)^2 + 33(r + 2) + 61 = 2r^2 + 41r + 135.$$
   Comparing with $R(r) + 1 = 2r^2 + 44r + 121$:
   $$\bigl(R(r) + 1\bigr) - L(r + 2) = 3r - 14 \ge 3(18) - 14 = 40 > 0 \qquad \text{for all } r \ge 18.$$
   Thus $L(r') \le R(r) + 1$ for every consecutive pair $r < r'$ in $S$, and $R(r) \to \infty$ as $r \to \infty$. Therefore $\bigcup_{r \in S} ([L(r), R(r)] \cap \mathbb{Z}) = \{n \in \mathbb{Z} : n \ge 1303\}$, so $a(n) \ge 2$ for every integer $n \ge 1303$. $\square$

---

## 3. Completion of the Conjecture

**Theorem.** *For the sequence $a(n)$ of OEIS A271719:*
1. *$a(n) > 0$ for every integer $n > 10$, and*
2. *$a(n) = 1$ if and only if $n \in \{11, 12, 14, 18, 24, 54\}$.*

*Proof.* By Lemma 2, $a(n) \ge 2$ for all $n \ge 1303$. For $1 \le n \le 1302$, exhaustive computation in [`verify.py`](verify.py) (both directly from the $(x, y, z)$ definition and independently via the Pythagorean bijection of Lemma 1) yields exact values of $a(n)$ for every $n \in [1, 1302]$:
- $a(n) = 0$ precisely for $n \in \{1, 2, 3, 4, 5, 7, 8, 9, 10\}$ (note $a(6) = 2$); hence $a(n) > 0$ for all $11 \le n \le 1302$.
- $a(n) = 1$ precisely for $n \in \{11, 12, 14, 18, 24, 54\}$.
- For $55 \le n \le 1302$, $a(n) \ge 2$.

Combining $1 \le n \le 1302$ with Lemma 2 ($n \ge 1303$) proves both claims for all positive integers $n$. $\square$

---

## 4. Computational Verification Summary

Running `python conjectures/A271719/verify.py` verifies:
1. All $70$ published terms ($n = 1, \dots, 70$) of OEIS A271719 match the direct definition.
2. Direct $(x, y, z)$ brute force agrees term-for-term with the Pythagorean bijection sieve on all $1 \le n \le 1302$, confirming $a(n) > 0$ for $11 \le n \le 1302$ and $a(n) = 1 \iff n \in \{11, 12, 14, 18, 24, 54\}$.
3. The $d = 11$ construction explicitly produces two distinct valid triples $(x, y, z)$ for every $n \in [1303, 10^6]$.
