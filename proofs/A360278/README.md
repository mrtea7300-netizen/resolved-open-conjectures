# A360278 — Determinant of `[L(j+k) + d(j,k)]_{1<=j,k<=n}` (and Conjectures 1–3)

- **OEIS:** https://oeis.org/A360278
- **Status:** `proof (formalized)` (prose proof reviewed + zero-dependency Lean 4 formalization in [`A360278.lean`](A360278.lean))

## Statement (verbatim from OEIS)

> Determinant of the matrix [L(j+k) + d(j,k)]_{1<=j, k<=n}, where L(n) denotes the Lucas number A000032(n), and d(j,k) is 1 or 0 according as j = k or not.
>
> Conjecture 1: Let v(0) = 2, v(1) = A, and v(n+1) = A*v(n) + v(n-1) for n > 0. Then A^2*det[v(j+k) + d(j,k)]_{1<=j, k<=n} = v(n+1)^2 - (A^2 + 4)*(n mod 2) for any positive integer n. In particular, a(n) = L(n+1)^2 - 5*(n mod 2) for all n > 0.
>
> Conjecture 2: Let v(0) = 2, v(1) = A, and v(n+1) = A*v(n) - v(n-1) for n > 0. Then det[v(j+k) + d(j,k)]_{1<=j, k<=n} = u(n+1)^2 - n^2 for any positive integer n, where u(0) = 0, u(1) = 1, and u(n+1) = A*u(n) - u(n-1) for all n > 0.
>
> Conjecture 3: Let F(n) denote the Fibonacci number A000045(n). Then, for any positive integer n, we have det[F(j+k) + d(j,k)]_{1<=j, k<=n} = F(n+1)^2 + (n mod 2).

Conventions: offset = `1,1`; matrix indices run over $1 \le j, k \le n$ for all positive integers $n \ge 1$; $A$ is an arbitrary complex number (or indeterminate in $\mathbb{Z}[A]$); $L(0)=2, L(1)=1, L(m+1)=L(m)+L(m-1)$ (A000032); $F(0)=0, F(1)=1, F(m+1)=F(m)+F(m-1)$ (A000045); $(n \bmod 2) \in \{0, 1\}$.

## Sanity check

`python conjectures/A360278/verify.py` reproduces all 35 published terms of the OEIS A360278 data section (`n = 1..35`) directly from the determinant definition: **yes**.

## What is known (Novelty check, 2026-11-27)

- Checked the full OEIS entry A360278 (from the official GitHub mirror `github.com/oeis/oeisdata`, revision `#20 Mar 19 2026`), Zhi-Wei Sun's linked paper H. Wang and Z.-W. Sun, *Evaluations of some Toeplitz-type determinants* (`arXiv:2206.12317v8`, Feb 2023; published in *Linear Multilinear Algebra* 72 (2024), 2504–2515), and Z.-W. Sun's follow-up preprint *On determinants involving second-order recurrent sequences* (`arXiv:2302.08315v2`, Feb 16 2023).
- In `arXiv:2302.08315v2` (Theorem 1.4 and its corollaries), Sun proved the **even-$n$ cases** of Conjectures 1 and 3 by diagonalizing $[w_{j+k}]$ when $B = -1$ and $2 \mid n$, and explicitly posed the **odd-$n$ cases** of Conjectures 1 and 3 as well as **all $n \ge 1$ of Conjecture 2** as open conjectures (Conjectures 4.2, 4.3, and 4.4 of `arXiv:2302.08315v2`).
- Searched arXiv (`all:"A360278"`, `all:"Zhi-Wei Sun" AND all:"determinant" AND (all:"Lucas" OR all:"Fibonacci")`, `"2302.08315"`) and the web (`"det[v(j+k)"`, `"u_{n+1}(A,1)^2"`, `"2302.08315"`), plus cross-referenced `OEIS Open` (`results.json`, 2026-09-16) and `AlphaProof Nexus` (`google-deepmind/alphaproof-nexus-results`). No prior proof of the odd-$n$ cases of Conjectures 1 and 3 or of Conjecture 2 was found.
- Note: G. C. Greubel added `a(n) = A000032(n+1)^2 - 5*(n mod 2)` in the `%F` section of A360278 on Jun 10 2025 without proof or citation.

## Lean 4 Formalization (`A360278.lean`)

- **Command:** `lean conjectures/A360278/A360278.lean`
- **Dependencies:** None (pure Lean 4.36.0 core, zero `sorry`, standard axioms `[propext, Classical.choice, Quot.sound]` only).
- **What is formalized:** Defines `det` from scratch via recursive Laplace expansion along column 0, proves column multilinearity, alternatingness, and the rank-2 Matrix Determinant Lemma (`det_id_add_rank2`), applies the purely integral rank-2 factorization $w_{j+k} = w_{j+1} u_k - B w_j u_{k-1}$ (`w_add_decomp`), and proves `conjecture1`, `conjecture1_lucas`, `conjecture2`, and `conjecture3` for all $n \ge 0$ and all $A \in \mathbb{Z}$ (hence identically in $\mathbb{Z}[A]$ and over $\mathbb{C}$).

## Result

- **Status:** `proof (formalized)` — Complete, self-contained prose proof in [`proof.md`](proof.md) and complete zero-dependency Lean 4 formalization in [`A360278.lean`](A360278.lean), verified by [`verify.py`](verify.py) and `lean conjectures/A360278/A360278.lean`.
