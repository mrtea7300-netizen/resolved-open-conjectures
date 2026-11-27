# OEIS A389880 and A321651 (Conjecture 2)

- **Status:** `counterexample (confirmed)` (both conjectures disproved at $n = 146$ via an explicit Hall's Marriage Theorem witness $|S| = 72 > |N(S)| = 71$, independently verified directly from the subset-sum definition of practical numbers)

## Verbatim statements

### OEIS A389880 (from `oeis/oeisdata`, dated Nov 15–18, 2025)

> **Name:** Number of permutations f of {1,...,n} with f(1) = 1 such that k*f(k) (k = 1..n) are distinct practical numbers.
>
> **Conjecture:** a(n) > 0 except for n = 3, 5, 7.
>
> This is stronger than Conjecture 2 in A321651.
>
> **Offset:** `1,4`
> **Published terms (`n = 1..10`):** `1, 1, 0, 2, 0, 4, 0, 44, 24, 106`

### OEIS A321651, Conjecture 2 (from `oeis/oeisdata`, dated Nov 15, 2018; updated Nov 13, 2025)

> **Conjecture 2:** For any positive integer n, there is a permutation f of {1,...,n} such that k*f(k) is practical for every k = 1,...,n.

## Counterexample ($n = 146$)

**Both conjectures are false at $n = 146$** (the smallest counterexample to A321651 Conjecture 2, and the smallest $n > 7$ where even the relaxed permutation condition without distinctness fails for A389880).

In the bipartite graph $G_{146}$ on $\{1, \dots, 146\}$ with an edge $(u, v)$ whenever $u \cdot v$ is practical, the maximum matching has size **$145 < 146$**.

### Explicit pigeonhole / Hall witness

Let $S \subset \{1, \dots, 146\}$ be the **72-element** set:
```
S = {5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 34, 35, 37, 38, 41, 43, 46, 47,
     49, 51, 53, 55, 57, 58, 59, 61, 62, 65, 67, 69, 71, 73, 74, 77, 79, 82,
     83, 85, 86, 87, 89, 91, 93, 94, 95, 97, 101, 103, 106, 107, 109, 111,
     113, 115, 118, 119, 121, 122, 123, 125, 127, 129, 131, 133, 134, 137,
     139, 141, 142, 143, 145, 146}
```
and let $N(S) \subset \{1, \dots, 146\}$ be the **71-element** set:
```
N(S) = {4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 26, 27, 28, 30,
        32, 33, 36, 39, 40, 42, 44, 45, 48, 50, 52, 54, 56, 60, 63, 64, 66,
        68, 70, 72, 75, 76, 78, 80, 81, 84, 88, 90, 92, 96, 98, 99, 100,
        102, 104, 105, 108, 110, 112, 114, 116, 117, 120, 124, 126, 128,
        130, 132, 135, 136, 138, 140, 144}
```

Then:
- $S$ and $N(S)$ are disjoint (with $\{1, \dots, 146\} \setminus (S \cup N(S)) = \{1, 2, 3\}$).
- For every $u \in S$ and every $v \in \{1, \dots, 146\} \setminus N(S)$ (all $72 \times 75 = 5400$ pairs), the product $u \cdot v$ is **not practical**.
- Therefore, in any valid permutation $f$ of $\{1, \dots, 146\}$, all $72$ elements of $S$ must be mapped injectively into the $71$-element set $N(S)$, which is impossible by the pigeonhole principle.

### Structural explanation

The set $S$ consists of:
1. All odd integers $5 \le u \le 146$ with $3 \nmid u$ (48 elements);
2. All odd multiples of $3$ of the form $3p$ with prime $p \ge 17$ (9 elements: $51, 57, 69, 87, 93, 111, 123, 129, 141$);
3. All even integers $2p$ with prime $p \ge 17$ (15 elements: $34, 38, 46, \dots, 146$).

No product of two elements of $S$ (nor any element of $S$ with $1, 2,$ or $3$) can be practical: odd-odd products $> 1$ are odd; an odd $u \in S$ with $3 \nmid u$ multiplied by $2p$ ($p \ge 17$) has $2 \parallel 2pu$ and $3 \nmid 2pu$ (so the smallest odd prime factor is $\ge 5 > \sigma(2) + 1 = 4$); and $(3p)(2q) = 6pq$ ($p, q \ge 17$) has $\sigma(6) + 1 = 13 < 17 \le \min(p, q)$.

## Verification

1. **`search.py`** (Stewart's criterion + Hopcroft-Karp matching): scans $n = 1..250$, confirms $n = 146$ is the smallest counterexample to A321651 Conjecture 2, and extracts $(S, N(S))$.
2. **`verify_counterexample.py`** (pure Python, zero external dependencies, direct subset-sum definition of practical numbers — no Stewart's theorem):
   - Reproduces published OEIS A389880 terms `n = 1..8`: `[1, 1, 0, 2, 0, 4, 0, 44]`.
   - Verifies all $72 \times 75 = 5400$ forbidden pairs $(u, v)$ with $u \in S, v \notin N(S)$ by exhibiting an explicit unrepresentable integer $1 \le r \le u v$.

Commands:
```bash
python conjectures/A389880/search.py
python conjectures/A389880/verify_counterexample.py
```

## Novelty check (2026-11-26)

- Checked `A389880.seq` (created Nov 15, 2025; last edited Nov 18, 2025) and `A321651.seq` (last edited Nov 13, 2025) in `oeis/oeisdata`: both conjectures are still listed as open.
- Checked `https://tadamcz.com/oeis-open/`: neither `A389880` nor `A321651` is listed.
- Web search for `"A321651"`, `"A389880"`, and `"146"` + practical numbers: no prior disproof found.
