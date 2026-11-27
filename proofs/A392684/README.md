# OEIS A392684

- **Status:** `proof (formalized)` (Lean 4.36.0, zero external dependencies, zero `sorry`, standard axioms only — proves Conjecture (i) for $k = 3$ and $N(3) = 6$ in Conjecture (ii))

## Verbatim statement

From OEIS `A392684.seq` (retrieved from `oeis/oeisdata`, dated Jan 19–23, 2026):

> **Name:** Number of ways to write n as x + y + z with x >= y >= z >= 1 such that lcm(x,y,z) is a product of three consecutive integers.
>
> **Conjecture:** (i) For any integer k > 2, each integer n >= 2^k - 2 can be written as x_1 + ... + x_k with x_1,...,x_k positive integers such that lcm(x_1,...,x_k) is a product of k consecutive integers.
>
> (ii) For each integer k > 2, let N(k) be the least positive integer N such that any integer n >= N can be written as x_1 + ... + x_k with x_1,...,x_k positive integers such that lcm(x_1,...,x_k) is a product of k consecutive integers. Then N(3) = 6, N(4) = 13, N(5) = 18, N(6) = 33, N(7) = 40, N(8) = 153 and N(9) = 226.
>
> **Offset:** `1,8`
> **Published terms (`n = 1..20`):** `0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 2, 4, 3, 5`

## Result

We prove and formally verify in Lean 4 the complete $k = 3$ theorem (the exact statement for the sequence `A392684` itself):
- `A392684.a392684_pos`: for every $n \ge 6$, $a(n) > 0$ (i.e., there exist $x \ge y \ge z \ge 1$ and $m \ge 1$ with $x + y + z = n$ and $\operatorname{lcm}(x, y, z) = m(m+1)(m+2)$).
- `A392684.a392684_zero_lt_six`: for every $1 \le n \le 5$, $a(n) = 0$.

Together these prove Conjecture (i) for $k = 3$ and $N(3) = 6$ in Conjecture (ii). The proof uses a 24-template integer covering system modulo 240 where every integer $n \ge 6$ except $n = 14 = 6 + 6 + 2$ is handled directly by a linear template $(a m, b(m+1), c(m+2))$.

See [`proof.md`](proof.md) for the human-readable proof and [`A392684.lean`](A392684.lean) for the self-contained Lean 4 formalization.

## Reproducing the verification

```bash
lean conjectures/A392684/A392684.lean
```

## Novelty check (2026-11-26)

- Checked `A392684.seq` in `oeis/oeisdata` (submitted Jan 19, 2026; last edited Jan 23, 2026): conjecture is still open.
- Checked `https://tadamcz.com/oeis-open/`: `A392684` is not listed.
- Web search for `"A392684"` and `"Zhi-Wei Sun"`: no prior proof found.
