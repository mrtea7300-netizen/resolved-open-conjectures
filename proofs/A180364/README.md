# A180364 — Ratio and root-ratio monotonicity of `sum_{k=0..n} C(n,k)*C(n+k,k)*(2k+1)^2`

- **OEIS:** https://oeis.org/A180364
- **Status:** proof (reviewed)

## Statement (verbatim from OEIS)

> a(n) = sum_{k=0..n} C(n,k)*C(n+k,k)*(2*k+1)^2, where C(m,k) denotes the binomial coefficient m!/(k!*(m-k)!).
>
> Conjecture: The sequence a(n+1)/a(n) (n = 0,1,...) is strictly decreasing to the limit 3+2*sqrt(2), and the sequence a(n+1)^(1/(n+1))/a(n)^(1/n) (n = 1,2,3,..) is strictly increasing to the limit 1.

Conventions: offset = `0,2`; $a(0) = 1$, $a(1) = 19$, $a(n) > 0$ for all $n \ge 0$; ratio sequence $a(n+1)/a(n)$ indexed over $n \ge 0$; root-ratio sequence $a(n+1)^{1/(n+1)}/a(n)^{1/n}$ indexed over $n \ge 1$.

## Sanity check

`python conjectures/A180364/verify.py` reproduces all 21 published terms of the OEIS A180364 data section (`n = 0..20`) directly from the binomial sum definition: **yes**.

## What is known (Novelty check, 2026-11-27)

- Read the full OEIS entry A180364 from the official GitHub mirror (`github.com/oeis/oeisdata`, revision `#29 Nov 05 2025`): lists Sun's Zeilberger recurrence and Vaclav Kotesovec's asymptotic formula, with no proof of the monotonicity conjecture linked.
- Checked Sun's source paper `arXiv:1408.5381v10` (*Two new kinds of numbers and related divisibility results*, 2014–2018), Brian Y. Sun's papers `arXiv:1512.01008` (which proves A245769, $R_n$) and `arXiv:1512.01010` (which proves $S_n = \sum \binom{n}{k}^2\binom{2k}{k}(2k+1)$), Lien-Hung Su's Zenodo preprint (Oct 2026, which proves A246065 and its normalized partial sums), Bian–Yao–Zhang–Zhao (2019, which proves A295112), and Wang–Zhu (`arXiv:1303.5595`, 2013).
- Searched arXiv (`all:"A180364"`, `all:"2k+1" AND all:"C(n,k)" AND all:"monotonic"`, `all:"Zhi-Wei Sun" AND (all:"log-convex" OR all:"log-concave" OR all:"monotonicity")`, `all:"ratio monotonicity" AND all:"Sun"`) and the web (`"A180364"`, `"C(n,k)*C(n+k,k)*(2*k+1)^2"`, `"Brian Y. Sun" "(2k+1)^2"`), and cross-referenced `OEIS Open` (`results.json`, 2026-09-16) and `AlphaProof Nexus`. No prior proof of A180364's monotonicity conjecture was found.

## Result
