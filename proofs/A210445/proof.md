# Proof of Zhi-Wei Sun's Conjecture in OEIS A210445

## Theorem

Let $a(n)$ be the least positive integer $k$ such that $k n$ is a practical number (OEIS [A005153](https://oeis.org/A005153)): a positive integer $m$ is **practical** if every integer $r$ with $1 \le r \le m$ can be written as a sum of distinct positive divisors of $m$.

1. For every integer $n > 1$, $a(n) < n$.
2. For every integer $n > 47$, $a(n) < n / 2$ (equivalently, $2 a(n) < n$).

Both bounds are sharp: $a(2) = 1$, $a(3) = 2$, and $a(47) = 24 = (47 + 1)/2$.

## Proof

We say that a positive integer $m$ is **$B$-practical** if every integer $r$ with $0 \le r \le B$ can be written as a sum of distinct positive divisors of $m$. Clearly, if $m$ is $B$-practical and $m \le B$, then $m$ is practical.

For $p \ge 2$ and $e \ge 0$, write $\sigma(p^e) = \sum_{i=0}^{e} p^i = \frac{p^{e+1} - 1}{p - 1}$. Notice that $(p - 1)\sigma(p^e) + 1 = p^{e+1}$.

### Lemma 1 (Coprime prime-power extension)

Suppose $u \ge 1$ is $B$-practical, and $p$ is a prime such that $p \nmid u$ and $p \le B + 1$. Then for every $e \ge 0$, $p^e u$ is $\bigl(\sigma(p^e) B\bigr)$-practical.

**Proof.** We induct on $e$. The base case $e = 0$ is immediate since $\sigma(p^0) = 1$.

For the inductive step $e \to e + 1$, assume $m = p^e u$ is $B_e$-practical, where $B_e = \sigma(p^e) B$. Since $p - 1 \le B$, we have
$$p^{e+1} = (p - 1)\sigma(p^e) + 1 \le B \sigma(p^e) + 1 = B_e + 1.$$
Now let $0 \le r \le \sigma(p^{e+1}) B = B_e + p^{e+1} B$. Set
$$q = \min\!\left(\left\lfloor \frac{r}{p^{e+1}} \right\rfloor,\, B\right), \qquad s = r - p^{e+1} q.$$
Then $0 \le q \le B$ and $0 \le s \le B_e$:
- If $\lfloor r / p^{e+1} \rfloor \le B$, then $s = r \bmod p^{e+1} \le p^{e+1} - 1 \le B_e$.
- If $\lfloor r / p^{e+1} \rfloor > B$, then $q = B$ and $s = r - p^{e+1} B \le B_e$.

By hypothesis, $q$ is a sum of a set $A$ of distinct divisors of $u$, and by the inductive hypothesis $s$ is a sum of a set $C$ of distinct divisors of $p^e u$. Consider
$$S = \{p^{e+1} a : a \in A\} \cup C.$$
Every element of $S$ divides $p^{e+1} u$. Moreover, the two sets are **disjoint**: every element $p^{e+1} a$ is divisible by $p^{e+1}$, whereas no divisor of $p^e u$ is divisible by $p^{e+1}$ (since $p \nmid u$ and $p$ is prime). Thus $S$ consists of distinct divisors of $p^{e+1} u$ whose sum is $p^{e+1} q + s = r$. $\blacksquare$

### Lemma 2 (Closure under bounded multiplication)

Call a list $L = [(p_t, e_t), \dots, (p_1, e_1)]$ of prime-exponent pairs ($p_1 < p_2 < \dots < p_t$, $e_i \ge 1$) **Stewart-valid** with bound $B(L) = \prod_{i=1}^t \sigma(p_i^{e_i})$ if for each $i = 1, \dots, t$,
$$p_i \le 1 + \prod_{j=1}^{i-1} \sigma(p_j^{e_j})$$
(with the empty product equal to $1$). Let $k = \prod_{i=1}^t p_i^{e_i}$.

1. By repeated application of Lemma 1, $k$ is $B(L)$-practical (and $k \le B(L)$).
2. If $q$ is any prime with $q \le B(L) + 1$, then inserting $q$ into the prime factorization of $k$ produces a Stewart-valid list $L'$ with value $q k$ and $B(L') \ge B(L)$.
   - *Proof:* Induct on the length of $L$. If $L = []$, then $q \le 2$ forces $q = 2$, giving $[(2, 1)]$. Otherwise, let $(p_t, e_t)$ be the largest prime in $L$, with tail $L_0$ and bound $B_0$:
     - If $q > p_t$, prepend $(q, 1)$; validity holds since $q \le B(L) + 1$.
     - If $q = p_t$, increment $e_t$ to $e_t + 1$; validity holds unchanged and $\sigma(q^{e_t+1}) \ge \sigma(q^{e_t})$.
     - If $q < p_t$, then $q < p_t \le B_0 + 1$, so by the inductive hypothesis we insert $q$ into $L_0$ to obtain $L_0'$ with $B(L_0') \ge B_0$ and all primes $< p_t$; prepending $(p_t, e_t)$ preserves $p_t \le B_0 + 1 \le B(L_0') + 1$.
3. Consequently, for **every** integer $n$ with $1 \le n \le B(L) + 1$, the product $k n$ is **practical** (by strong induction on $n$, peeling off the smallest prime factor $q \mid n$, which satisfies $q \le n \le B(L) + 1$). $\blacksquare$

### Proof of Part 1 ($a(n) < n$ for all $n > 1$)

For any $n > 1$, choose the unique integer $a \ge 0$ such that
$$2^a < n \le 2^{a+1}.$$
Take $k = 2^a$. Then $k$ is represented by the Stewart-valid list $[]$ (if $a = 0$) or $[(2, a)]$ (if $a \ge 1$), with bound $B = \sigma(2^a) = 2^{a+1} - 1$. Since $1 \le n \le 2^{a+1} = B + 1$, Lemma 2 implies that $k n$ is practical. Because $1 \le k = 2^a < n$, we have $a(n) \le 2^a < n$. $\blacksquare$

### Proof of Part 2 ($a(n) < n / 2$ for all $n > 47$)

If $n = 48 = 2^4 \cdot 3$, then $48$ is itself practical (take $k = 1 < 48 / 2$).

Now suppose $n > 48$. Choose the unique integer $a \ge 0$ such that
$$48 \cdot 2^a < n \le 96 \cdot 2^a.$$
Consider the four Stewart-valid templates (for every $a \ge 0$):

| Case | Range of $n$ | Choice of $k$ | Factorization of $k$ | $B(k) + 1 = \sigma(k) + 1$ | Check $n \le B(k) + 1$ for all $a \ge 0$ |
|---|---|---|---|---|---|
| 1 | $48 \cdot 2^a < n \le 60 \cdot 2^a$ | $24 \cdot 2^a$ | $2^{a+3} \cdot 3$ | $64 \cdot 2^a - 3$ | $60 \cdot 2^a \le 64 \cdot 2^a - 3 \iff 4 \cdot 2^a \ge 3$ |
| 2 | $60 \cdot 2^a < n \le 72 \cdot 2^a$ | $30 \cdot 2^a$ | $2^{a+1} \cdot 3 \cdot 5$ | $96 \cdot 2^a - 23$ | $72 \cdot 2^a \le 96 \cdot 2^a - 23 \iff 24 \cdot 2^a \ge 23$ |
| 3 | $72 \cdot 2^a < n \le 84 \cdot 2^a$ | $36 \cdot 2^a$ | $2^{a+2} \cdot 3^2$ | $104 \cdot 2^a - 12$ | $84 \cdot 2^a \le 104 \cdot 2^a - 12 \iff 20 \cdot 2^a \ge 12$ |
| 4 | $84 \cdot 2^a < n \le 96 \cdot 2^a$ | $42 \cdot 2^a$ | $2^{a+1} \cdot 3 \cdot 7$ | $128 \cdot 2^a - 31$ | $96 \cdot 2^a \le 128 \cdot 2^a - 31 \iff 32 \cdot 2^a \ge 31$ |

In every case:
- $k$ is Stewart-valid (for $a \ge 0$: $3 \le \sigma(2^{a+1}) + 1 = 4 \cdot 2^a$, $5 \le \sigma(2^{a+1} \cdot 3) + 1 = 16 \cdot 2^a - 3$, and $7 \le 16 \cdot 2^a - 3$);
- $2 k < n$ (equivalently $k < n / 2$);
- $1 \le n \le B(k) + 1$, so by Lemma 2, $k n$ is practical.

Hence $a(n) \le k < n / 2$ for every $n > 47$. $\blacksquare$

## Formal Verification

The entire proof above (including the textbook subset-sum definition of `IsPractical`, Lemmas 1 and 2, and both parts of the theorem) is formalized with zero `sorry` and zero external dependencies in [`A210445.lean`](A210445.lean).
