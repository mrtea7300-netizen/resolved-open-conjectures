# A356976 — Least modulus m for which k^3 + 3k (k = 1..n) are distinct mod m (and Conjectures 1–4)

- **OEIS:** https://oeis.org/A356976
- **Status:** proof (draft) — Conjecture 2 (`2k^3 + k`); Conjectures 1, 3, 4 open

## Statement (verbatim from OEIS)

> Least positive integer m such that the numbers k^3 + 3*k (k = 1..n) are pairwise distinct modulo m.
>
> Conjecture 1: If n is at least 15, then a(n) is the least power of 3 not smaller than 3*n.
>
> Conjecture 2: For each positive integer n, the least positive integer m such that those numbers 2*k^3 + k (k = 1..n) are pairwise distinct modulo m, is just the least power of 2 not smaller than n.
>
> Conjecture 3: For any positive integer n, the least positive integer m such that those numbers 2*k^3 - 4*k (k = 1..n) are pairwise distinct modulo m, is just the least power of 3 not smaller than n.
>
> Conjecture 4: For each positive integer n not equal to 4, the least positive integer m such that those numbers 16*k^3 - 8*k (k = 1..n) are pairwise distinct modulo m, is just the least power of 3 not smaller than n.
>
> The author formulated Conjectures 1-4 on Nov. 16, 2021, and verified them for n up to 10^5.

Conventions: offset = 1; $k$ runs over $1, \dots, n$; $m \ge 1$.

## Sanity check

`python conjectures/A356976/verify_conj2.py --check` reproduces all 38 published terms of the OEIS A356976 data section (`n = 1..38`): **yes**.

## What is known

- Checked OEIS entry A356976 comments and links, arXiv (discriminator papers by Moree, Faye, Luca, Sun), `epoch-research/LeanOpenProblems-results`, and `google-deepmind/alphaproof-nexus-results`.
- No prior proof or resolution of A356976 Conjectures 1–4 found; not included in the 2026 OEIS Open or AlphaProof Nexus benchmarks.
- Zhi-Wei Sun verified Conjectures 1–4 computationally up to $n = 10^5$.

## Result

- **Conjectures 1, 3, 4:** `open` (same norm-form framework applies, with box width $1/3$ instead of $1/2$).
