# A187011 — Determinant of `[|p_i - p_j|]_{1 <= i,j <= n}`

- **OEIS:** https://oeis.org/A187011
- **Status:** proof (reviewed)

## Statement (verbatim from OEIS)

> Determinant of the n X n matrix with (i,j)-entry equal to |p_i-p_j|, where p_k denotes the k-th prime.
>
> Conjecture: (-1)^(n-1)*a(n) > 0 for all n > 1, and |a(n)|^{1/n} tends to the infinity.

Conventions: offset = `0,4` (`a(0) = 1` empty determinant prepended by Alois P. Heinz, Aug 15 2026; `a(1) = 0`, `a(2) = -1`, `a(3) = 12`, `a(4) = -80`, ...); $p_1 = 2, p_2 = 3, p_3 = 5, \dots$ are the primes (`A000040`).

## Sanity check

`python conjectures/A187011/verify.py` reproduces all 23 published terms of the OEIS A187011 data section (`n = 0..22`) directly from the determinant definition: **yes**.

## What is known (Novelty check, 2026-11-27)

- Read the full OEIS entry A187011 from the official GitHub mirror (`github.com/oeis/oeisdata`, revision `#19 Aug 16 2026`): contains only Alois P. Heinz's b-file (`n = 0..750`) and Maple/Mathematica programs; no closed-form formula or proof of Sun's conjecture is recorded.
- Searched arXiv (`all:"A187011"`), web (`"A187011"`, `"|p_i - p_j|" determinant "Zhi-Wei Sun"`, `"distance matrix" "primes" "1/n" "infinity"`), and cross-referenced `OEIS Open` (`results.json`, 2026-09-16) and `AlphaProof Nexus`. No prior proof of A187011 was found. (The general linear-algebra identity $\det[|x_i - x_j|] = (-1)^{n-1} 2^{n-2}(x_n - x_1)\prod_{k=1}^{n-1}(x_{k+1} - x_k)$ is a classical special case of the distance-matrix determinant for a path/line, e.g. Graham–Pollak 1971; here we prove it from scratch in 10 lines and combine it with a self-contained Selberg sieve upper bound on bounded prime gaps.)

## Result
