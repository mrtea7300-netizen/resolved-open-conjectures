# turan-c4 — upper bounds for ex(n, C4) (OEIS A006855), 45 ≤ n ≤ 56

- **OEIS:** https://oeis.org/A006855 (read from the mirror `oeis/oeisdata`, `seq/A006/A006855.seq`, header `#86 Mar 03 2026`)
- **Status:** proof (reviewed) — new upper bounds for 45 ≤ n ≤ 56

## Statement (verbatim from OEIS A006855)

> `%N A006855 Maximum number of edges in an n-node squarefree graph, or, in a graph containing no 4-cycle, or no C_4.`
>
> `%C A006855 Lower bounds that have a good chance of being exact: a(41) >= 132, a(42) >= 137, a(43) >= 142, a(44) >= 148, a(45) >= 154, a(46) >= 157, a(47) >= 163, a(48) >= 168, a(49) >= 174. - _Brendan McKay_, Mar 08 2022`
>
> `%C A006855 Upper bounds: a(41) <= 133, a(42) <= 139, a(43) <= 145, a(44) <= 151, a(45) <= 158, a(46) <= 165, a(47) <= 171, a(48) <= 176, a(49) <= 182. - _Max Alekseyev_, Jan 26 2023`
>
> `%F A006855 For n > 2, a(n) <= floor(a(n-1) * n / (n-2)). - _Max Alekseyev_, Jan 26 2023`

Conventions: simple graphs; offset 1. The data section gives a(1..40), ending with a(40) = 127.
The open problem is the exact value of a(n) for n ≥ 41. Here we lower the upper bounds.

## Result

| n | McKay lower bound | previous upper bound | **new upper bound (draft)** | constraints used | certificate |
|---:|---:|---:|---:|---|---|
| 45 | 154 | 158 (Alekseyev) | **157** | (I5) + (I6) with ex(44) ≤ 151 | [`data/cert_n45_m158.txt`](data/cert_n45_m158.txt) |
| 46 | 157 | 165 (Alekseyev) | **163** | (I5) | [`data/cert_n46_m164.txt`](data/cert_n46_m164.txt) |
| 47 | 163 | 171 (Alekseyev) | **169** | (I4) + (I5) | [`data/cert_n47_m170.txt`](data/cert_n47_m170.txt) |
| 48 | 168 | 176 (Alekseyev) | **174** | (I5) | [`data/cert_n48_m175.txt`](data/cert_n48_m175.txt) |
| 49 | 174 | 182 (Alekseyev) | **180** | (I4) only, hand-checkable | [`data/cert_n49_m181.txt`](data/cert_n49_m181.txt) |
| 50 | 181 ¹ | 187 (Reiman) ² | **186** | (I4) only, hand-checkable | [`data/cert_n50_m187.txt`](data/cert_n50_m187.txt) |
| 51 | — | 193 (Reiman) | **192** | (I4) only, hand-checkable | [`data/cert_n51_m193.txt`](data/cert_n51_m193.txt) |
| 52 | — | 199 (Reiman) | **197** | (I4) + (I5) | [`data/cert_n52_m198.txt`](data/cert_n52_m198.txt) |
| 53 | — | 204 (Reiman) | **202** | (I4) + (I5) | [`data/cert_n53_m203.txt`](data/cert_n53_m203.txt) |
| 54 | — | 210 (Reiman) | **208** | (I4) + (I5) | [`data/cert_n54_m209.txt`](data/cert_n54_m209.txt) |
| 55 | — | 216 (Reiman) | **214** | (I4) + (I5) | [`data/cert_n55_m215.txt`](data/cert_n55_m215.txt) |
| 56 | — | 222 (Reiman) | **220** | (I4) + (I5) | [`data/cert_n56_m221.txt`](data/cert_n56_m221.txt) |

Rows where the LP gives nothing new:
- n = 41–44: the LP gives nothing below Alekseyev's 133, 139, 145, 151, which come from the
  averaging recurrence.
- n = 57: the LP gives 228, which equals Reiman's bound. The certificate is kept as a check.

which we did not check.
² OEIS records no upper bound for n ≥ 50. The comparison is with Reiman's ⌊n(1 + √(4n − 3))/4⌋
and the recurrence, whichever is smaller (Reiman in every row).

The proof is in [`proof.md`](proof.md). In short:
- Count vertices by degree and edges by the degrees of their ends.
- Three facts hold in every C4-free graph:
  - **(I4)** Reiman's pair count, sharpened by parity. A vertex of odd degree is on an edge
    that lies in no triangle.
  - **(I5)** For every vertex v, Σ_{u∈N(v)} d(u) ≤ n − 1 + d(v) − (d(v) mod 2).
  - **(I6)** Every vertex has degree ≥ m − ex(n − 1). This is used only at n = 45.
- Each bound U(n) is proved by an explicit integer Farkas certificate at m = U(n) + 1.

Every bound except n = 45 is unconditional. The n = 45 bound uses ex(44, C4) ≤ 151, which
follows from the averaging recurrence starting at a(40) = 127. That value is McKay's computer
result (OEIS), the same input behind Alekseyev's bounds.

## Reproduce

```
cd conjectures/turan-c4
python check_certificates.py            # standalone exact check of all data/cert_*.txt (integers only)
python lp_c4.py --run                   # recompute the bounds and certificates (~30 s), writes data/
python lp_c4.py --sanity                # exact feasible points at a(n), n<=40, and McKay's bounds 41..49 (~30 s)
python test_constraints.py --nmax 10 --mckay <dir of McKay c4_*.s6> --random 3000   # ~50 s
```

The McKay–Afzaly graphs are in https://users.cecs.anu.edu.au/~bdm/data/extremal/c4_all.tar.gz
(5162 bytes, downloaded 2026-11-27). They are not committed. Outputs of the four commands are in
`data/*.log`.

## What is known (novelty check, 2026-11-27)

- **OEIS A006855:** upper bounds for 41 ≤ n ≤ 49 only, by Alekseyev (quoted above). Each one
  equals min(averaging recurrence from a(40) = 127, Reiman's bound); we recomputed both.
- **Alekseyev, arXiv:2303.02872v2** (J. Comp. Sys. Sci. 157 (2026) 103735), HTML version read by a
  fetch agent. The only bounds on h(n) = A006855(n) are the recurrence h(n) ≤ ⌊h(n−1)·n/(n−2)⌋
  (Section 7, generalising Theorem 4(II)) and Reiman's bound. There is no table for n ≥ 41 and
  nothing better than the OEIS values.
- **McKay–Afzaly, "Extremal Graphs and Turan numbers"** (page read 2026-11-27): exact values
  for n ≤ 40, and "maybe" lower bounds for 41–49 ("we didn't prove that more edges are
  impossible"). The page states no upper bounds.
- **Ma–Yang, arXiv:2107.11601:** only asymptotic bounds near n = q² + q + 1 for "sufficiently
  large" q, and no numerical bound for any n in 41–60.
- **Web and arXiv searches** ("ex(n,C4)" small n upper bounds; A006855 a(45)–a(49); SAT/SMS
  Turán C4, 2023–2026): no source with bounds as good as ours was found.
  - Not read: a 2026 Springer chapter, "Formally Verified Graph Generation with SAT Modulo
    Symmetries and Lean" (10.1007/978-3-032-32589-1_8). It was behind a login. A search snippet
    says it certifies "m = ex(n, C4) + 1" instances, probably for small n. Someone should check
    its range.
  - Not read: the classical small-n papers (Clapham–Flockhart–Sheehan 1989, n ≤ 21;
    Yuansheng–Rowlinson, n ≤ 31), which may use the same counting arguments. The parity
    sharpening of Reiman's count is elementary and may well be folklore. What we have not found
    anywhere is the resulting numerical bounds.

## Handoff

Next steps:
2. Check the Springer SMS+Lean chapter and the Clapham et al. / Yuansheng–Rowlinson papers for
   prior bounds.
3. For further gains, add constraints to the LP: integrality of t(v); per-vertex parity
   (s(v) ≥ 1 for odd d); counting the pairs of P_0 that are non-edges; or pair-degree classes.

Do not retry `limit_denominator` rounding. Exact vertex reconstruction works for every n here.
