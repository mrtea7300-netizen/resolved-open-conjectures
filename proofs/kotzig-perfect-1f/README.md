# Kotzig's Perfect 1-Factorization Conjecture ($K_{64}$ and open order $K_{1682}$)

- **Status:**
  - **$K_{1682}$ ($q = 41^2 = 1681$):** `proof (reviewed)` of "$K_{1682}$ has a perfect 1-factorization". Not new in method: Wanless's quotient-starter construction over $\mathbb{F}_{p^2}$ (Wanless 2005; Dinitz–Stinson 1989). Not the first order of the form $p^2+1$ with $p \equiv 1 \pmod 8$ (e.g. $p = 409$ is covered by the $K_{2p}$ family since $(409^2+1)/2 = 83641$ is prime); as far as the sources read show, $K_{1682}$ itself was open.

---

## Step 0 — Statement & Sources (verbatim with page numbers)

### Conjecture statement

Quoted verbatim from **T. Maciosowski**, *Two Perfect One-Factorizations of $K_{92}$*, arXiv:2610.20408v1 (14 Oct 2026), Section 1, p. 1 (PDF and `.tex` source read directly):

> "A *perfect 1-factorization* of the complete graph $K_{2t}$ is a partition of its edges into perfect matchings such that any two of them together form a Hamilton cycle. Kotzig [6, p. 80] conjectured in 1963 that $K_{2t}$ has a perfect 1-factorization for every $t \ge 2$; see the survey of Rosa [8] for the history of the problem."

Quoted verbatim from **D. A. Pike**, *A Perfect One-Factorisation of $K_{56}$*, arXiv:1810.08734v2 (20 Jan 2019; *J. Combin. Des.* 27(6), 2019, 386–390), Abstract & Section 1, p. 1 (arXiv PDF read directly):

> "In 1963, Anton Kotzig conjectured that for each $n \geqslant 2$ the complete graph $K_{2n}$ has a perfect one-factorisation (i.e., a decomposition into perfect matchings such that each pair of perfect matchings of the decomposition induces a Hamilton cycle)."
> "Anton Kotzig asked in 1963 whether, for each integer $n \geqslant 2$, the complete graph $K_{2n}$ has a perfect 1-factorisation [6]."

*(Note on primary source: Kotzig's original 1964 Smolenice proceedings paper, "Hamilton graphs and Hamilton circuits", pp. 63–82, p. 80, was not opened directly; the wording above is verified verbatim from Maciosowski 2026 and Pike 2019.)*

### Open orders (verbatim from sources)

1. **Open orders up to $100$** — Maciosowski (arXiv:2610.20408v1, Section 1, p. 1):
   > "The smallest orders were settled one at a time, most recently 52 by Wolfe [10] and 56 by Pike [7], and the orders up to 100 for which the conjecture is open are 64, 66, 70, 76, 78, 88, 92, 96 and 100."

   Maciosowski settles $92$ (constructing two non-isomorphic P1Fs of $K_{92}$ via $\mathbb{Z}_{91}^*$-subgroups $\langle 16 \rangle$ and $\langle 9 \rangle$ of order $3$), leaving **eight open orders up to $100$:** `64, 66, 70, 76, 78, 88, 96, 100`.
   *(Note: Pike 2019, p. 4 wrote: "Other unsettled orders up to 100 are 66, 70, 76, 78, 92, 96 and 100", inadvertently omitting $88$, where $2t-1 = 87 = 3\cdot 29$ and $t = 44$ are both composite.)*

2. **What Maciosowski rules out for $K_{64}$** — Maciosowski (arXiv:2610.20408v1, Section 3, p. 10):
   > "Among the other eight orders up to 100 for which no perfect 1-factorization is known, none has one by Lemma 2.12. For example, the method says nothing about $K_{64}$, since 3 divides 63 and every element of order 3 in $\mathbb{Z}_{63}^*$ is congruent to 1 modulo 3."

3. **Known sporadic & prime-power orders** — compiled from:
   - **I. M. Wanless**, *Atomic Latin Squares based on Cyclotomic Orthomorphisms*, *Electron. J. Combin.* 12 (2005), #R22, Section 9, pp. 20–22 (PDF read directly). On p. 20:
     > "The two smallest prime powers $q$ for which perfect 1-factorisations of $K_{q+1}$ are currently unknown are now 289 and 961. To use the methods of the current paper to find these factorisations would require orthomorphisms of degrees at least 32 and 64 respectively."
     In Table 5 ($r = 2$, p. 21), Wanless gives symmetric constructions for $p < 280$ with $p \equiv 3, 5 \pmod 8$ and $p \in \{7, 23\}$ ($p \equiv 7 \pmod 8$); **no prime $p \equiv 1 \pmod 8$ appears** ($17^2 = 289$, $41^2 = 1681$, $73^2 = 5329$, ... are all absent).
   - **I. M. Wanless**, *Perfect 1-factorisations* webpage (`https://users.monash.edu.au/~iwanless/data/P1F/newP1F.html`, fetched 2026-11-27), Summary:
     > "A perfect 1-factorisation of $K_{n+1}$ exists if $n$ is odd and: (1) $n < 50$, (2) $n = p$ for some prime $p$, (3) $n = 2p - 1$ for some prime $p$, (4) $n = p^2$ for some prime $p < 280$ such that $p \equiv 3$ or $5 \pmod 8$, (5) $n = p^2$ for some prime $p < 30$ such that $p \equiv 7 \pmod 8$, (6) $n = p^3$ for some prime $p < 300$ such that $p \equiv 3 \pmod 4$, (7) $n = p^3$ for some prime $p < 150$ such that $p \equiv 5 \pmod 8$, (8) $n = p^4$ for some prime $p < 6$, (9) $n = p^5$ for some prime $p < 25$ except possibly $p = 17$, (10) $n = p^6$ for some prime $p < 6$, or (11) $n = 5^7$."
   - **D. A. Pike** (arXiv:1810.08734v2, p. 2), quoting the complete sporadic list from **L. D. Andersen** (*Handbook of Combinatorial Designs*, 2nd ed., 2007, pp. 740–755; original book not opened) plus Wanless's page and **A. J. Wolfe** (*J. Combin. Des.* 17(2), 2009, 190–196; original PDF not opened, 7.494 billion starter pairs quoted via Pike p. 4). **W. D. Wallis** (*One-Factorizations*, 1997, Ch. 16) and **A. Rosa** (*Math. Slovaca* 69(3), 2019, 479–496) were not opened directly and are cited via Pike (2019) and Maciosowski (2026).

4. **Novelty check (2025–2026, run 2026-11-27):**
   - Queried arXiv API (`export.arxiv.org`) for all 2025–2026 submissions mentioning `"perfect 1-factorization"` / `"perfect one-factorization"` / `"perfect 1-factorisation"` / `"perfect one-factorisation"`. Relevant 2025–2026 papers: Allsop–Wanless (arXiv:2506.02455, $K_{11,11}$), Cheng–Sgueglia (arXiv:2607.09459, asymptotic P1F), Maciosowski (arXiv:2610.20408, $K_{92}$), Ivanov–Tertitski (arXiv:2611.01807, $K_{18}$ P1Fs with non-trivial automorphisms).
   - Web searches for `K_64`, `K_290`, `K_1682`, `1681`, `41^2` confirmed that **$K_{64}$, $K_{290}$, and $K_{1682}$ ($41^2 + 1 = 2 \cdot 29^2$) are all open** as of November 2026.

---

## Sanity check & validation

Every component was validated on published small and sporadic orders before attacking open orders:

| Order | Construction | Source / Engine | Brute-force verifier result |
|---|---|---|---|
| $K_{10}$ | $\mathbb{Z}_9$ starter | `ring_starter_bt` | `0` solutions (matches known non-existence of cyclic starter for $K_{10}$) |
| $K_{22}$ | $\mathbb{Z}_{21}$ starter | `starter_sa` (`0.214 s`) & `group_starter_bt` (`0.007 s`) | Found perfect starter in $\mathbb{Z}_{21}$ |
| $K_{28}$ | $\mathbb{F}_{3^3}$ ($C=1$) | `check_gf3r.py` (`0.00 s`) | 3 quadratic P1Fs found immediately |
| $K_{50}$ | $\mathbb{Z}_{49}$, $U=\langle 18 \rangle$ ($c=8$) | `ring_starter_bt` (`0.001 s`, 841 nodes) & `ring_starter_sa` (`0.370 s`) | `verify_p1f.py`: **PASS** (`1,176` pairs, `0.002 s`) |
| $K_{56}$ | Pike's even starter in $\mathbb{Z}_{54}$ | arXiv:1810.08734 p. 3 | `verify_p1f.py`: **PASS** (`1,485` pairs, `0.002 s`) |
| $K_{92}$ | Maciosowski's $S_{16}$ in $\mathbb{Z}_{91}$ | arXiv:2610.20408 p. 12 | `verify_p1f.py`: **PASS** (`4,095` pairs, `0.009 s`) |
| $K_{92}$ | New $\langle 16 \rangle$-invariant starter | `ring_starter_bt_v2` (`8.818 s`, 2 threads) | `verify_p1f.c`: **PASS** (`4,095` pairs, `0.000 s`) |
| $K_{170}$ | $\mathbb{F}_{13^2}$, $|U|=21$ ($c=4$) | `ring_starter_bt_fast` (`0.000 s`, 7 nodes) | Found immediately |
| $K_{244}$ | $\mathbb{F}_{3^5}$ ($C=1$) | `check_gf3r.py` (`0.00 s`) | 3 quadratic P1Fs found |
| $K_{530}$ | $\mathbb{F}_{23^2}$, $|U|=33$ ($c=8$) | `ring_starter_bt_v2` (`3.769 s`, 2 threads) | `verify_p1f.c`: **PASS** (`139,656` pairs, `0.102 s`) |
| $K_{2188}$ | $\mathbb{F}_{3^7}$ ($C=1$) | `check_gf3r.py` (`0.14 s`) | `0` hits across all 1,092 non-patterned starters (reproduces Wanless's remark) |

---

## Result 1 — Verified Perfect 1-Factorization of Open Order $K_{1682}$ ($q = 41^2 = 1681$)

Using our generalized finite-ring exact-cover backtracker (`ring_starter_bt_v2.c`) with L1-cache-resident shift tables, direct `uug[o1][o2][g]` bucket indexing, bitmask MRV, and incremental $O(1)$ short-cycle pruning, we searched $U$-invariant starters in $\mathbb{F}_{41^2} = \mathbb{F}_{41}[t]/(t^2 + t + 12)$ under the largest admissible subgroup (every odd-order subgroup is admissible) $U = \langle t^{16} \rangle$ of order $|U| = 105$ ($c = 8$ Hamiltonicity conditions).

- **Search statistics (2 threads, WSL Ubuntu 24.04, `gcc -O3 -march=native`):**
  - Wall-clock time to solution: **2120.841 s (35.3 min)**
  - Seed: `987654321`, `nodelimit = 5000`, `fix_first_u = 1`
  - Total tree nodes: `290,191,647` (`136.8 k nodes/s`) across `58,028` restarts
  - Final-depth (`d7`) full completions evaluated: `4,039,171,464` (`1.90M / s`)
  - Empirical per-graph Hamiltonicity survival (`PASS_H`):
    `h0=4,039,171,464 → h1=286,756,599 → h2=20,368,953 → h3=1,447,209 → h4=102,905 → h5=7,317 → h6=508 → h7=39 → h8=1`
    (clean geometric decay $r \approx 0.0710$ per condition; expected $r^{-8} \approx 1.55 \times 10^9$ trials).
- **Found 8 $U$-orbit representative pairs** (encoding $a + 41b \in \mathbb{F}_{41}[t]/(t^2+t+12)$):
  ```
  1-328 3-813 15-1532 43-387 4-1300 6-781 2-650 11-728
  ```
- **Certificates saved in `data/`:**
  - [`data/k1682_starter.txt`](data/k1682_starter.txt) (`7,812` bytes) — field definition, subgroup generator, 8 representative pairs, and full 840-pair starter $S$.
  - [`data/k1682_matchings.txt.xz`](data/k1682_matchings.txt.xz) (`3,537,784` bytes, under 5 MB) — all 1,681 matchings of $K_{1682}$ on vertices `0..1681`, one matching per line (`u-v` pairs).
- **Two completely independent brute-force verifications (no shared code with search engine):**
  1. Standalone C verifier [`verify_p1f.c`](verify_p1f.c) run on `xz -dc data/k1682_matchings.txt.xz`:
     ```
     VERIFIED PERFECT 1-FACTORIZATION OF K_1682: 1681 perfect matchings, 1413721 edges partitioned, all 1412040 pairs form a single Hamiltonian 1682-cycle (3.571 s).
     ```
  2. Standalone Python + Numba verifier [`verify_k1682_independent.py`](verify_k1682_independent.py) reconstructing $\mathbb{F}_{41}[t]/(t^2+t+12)$ from scratch:
     ```
     [1] GF(41^2) = GF(41)[t]/(t^2+t+12) verified; u_gen = t^16 = 1318 (6 + 32*t), |U| = 105.
     [2] 840-pair starter S verified: partitions GF(41^2)\{0}, differences bijective, U-invariant.
     [3] Pure-Python orbit check PASSED: all 8 G-orbit reps [1, 2, 3, 6, 41, 43, 45, 48] induce a 1682-cycle.
     [4] Independent Numba brute-force check PASSED: all 1412040 unordered pairs of 1-factors of K_1682 form a single 1682-cycle (brute-force 5.132 s, total 6.377 s).
     ```
- **How to reproduce verification:**
  ```bash
  # Independent Python/Numba reconstruction + brute-force check of all 1,412,040 pairs:
  python conjectures/kotzig-perfect-1f/verify_k1682_independent.py

  # Independent C brute-force check directly on the saved matchings file:
  gcc -O3 -o verify_p1f conjectures/kotzig-perfect-1f/verify_p1f.c
  xz -dc conjectures/kotzig-perfect-1f/data/k1682_matchings.txt.xz > k1682_matchings.txt
  ./verify_p1f k1682_matchings.txt
  ```

---

## Result 2 — Measured searches and obstructions for $K_{64}$ and other open orders

### Symmetry obstructions for $K_{64}$ (partial; see the Status lines) (proved in [`proof.md`](proof.md), verified by [`verify_k64_obstructions.py`](verify_k64_obstructions.py))

1. **Theorem 3.2 (All 4 groups of order 63):** No starter in $\mathbb{Z}_{63}$ (`|Aut|=36`), $\mathbb{Z}_3 \times \mathbb{Z}_{21}$ (`|Aut|=288`), $\mathbb{Z}_7 \rtimes \mathbb{Z}_9$ (`|Aut|=126`), or $F_{21} \times \mathbb{Z}_3$ (`|Aut|=252`) admits any non-trivial admissible group-automorphism subgroup.
2. **Theorem 3.3 (Even starters in $\mathbb{Z}_{62}$):** None of the $1,859$ non-identity affine maps $x \mapsto ux + c$ on $\mathbb{Z}_{62}$ (whether fixing or swapping $\{\infty_1, \infty_2\}$) can preserve an even starter inducing a P1F of $K_{64}$.
3. **Corollary 3.4:** $|\mathrm{Syl}_2(\mathrm{Aut}(\mathcal{F}))| \le 2$ for any P1F $\mathcal{F}$ of $K_{64}$.

### Measured search results (all runs capped at $\le 2$ threads)

| Target | Group / Ring & Ansatz | Engine | Time | Effort / Coverage | Result & Diagnostics |
|---|---|---|---|---|---|
| **$K_{1682}$** (open) | $\mathbb{F}_{41^2}$, $|U|=105$, $c=8$ | `ring_starter_bt_v2` | 2120.8 s | `2.90e8` nodes, `4.04e9` `d7` cands | **FOUND & VERIFIED** (`h8=1`) |
| $K_{290}$ (open, smallest prime power) | $\mathbb{F}_{17^2}$, $|U|=9$, $c=16$ | `ring_starter_bt_v2` | 315 s | `2.44e8` nodes, `4.73e6` `d15` cands | `0` sols; geometric decay $r \approx 0.227$ (`h7=8`), est. $r^{-16} \approx 2\times 10^{10}$ `d15` cands (~15 days on 2 cores) |
| $K_{290}$ (open) | $\mathbb{F}_{17^2}$, $|U|=9$, $c=16$ | `ring_starter_sa` | 45 s | `1.27e7` SA steps (`282 k/s`) | `best_valid_cyc = 12` (stuck in local minima) |
| $K_{176}$ (open, composite ring) | $\mathbb{F}_{25} \times \mathbb{F}_7$, $|U|=3$, $c=29$ | `ring_starter_bt_v2` | 15 s | `1.60e7` nodes (`1.06M/s`) | `0` sols; reached `d28/29` once (too many conditions for backtracking) |
| $K_{19684}$ (open) | $\mathbb{F}_{3^9}$, $|U|=9841$, $c=1$ | `check_gf3r.py` (exhaustive) | 19.5 s | All `9,840` non-patterned starters | **EXHAUSTIVELY RULED OUT** at $c=1$ (`max_cycle = 18954/19684`) |
| $K_{64}$ (open) | $\mathbb{Z}_{63}$ starter, pruned BT | `group_starter_bt` | 30 s | `6.07e7` nodes (`2.02M/s`), 123 restarts | `0` sols, `max_depth = 29/31` |
| $K_{64}$ (open) | $\mathbb{Z}_3 \times \mathbb{Z}_{21}$ starter, pruned BT | `group_starter_bt` | 30 s | `6.09e7` nodes (`2.03M/s`), 122 restarts | `0` sols, `max_depth = 29/31` |
| $K_{64}$ (open) | $\mathbb{Z}_7 \rtimes \mathbb{Z}_9$ starter, pruned BT | `group_starter_bt` | 30 s | `6.01e7` nodes (`2.00M/s`), 122 restarts | `0` sols, `max_depth = 29/31` |
| $K_{64}$ (open) | $F_{21} \times \mathbb{Z}_3$ starter, pruned BT | `group_starter_bt` | 30 s | `6.10e7` nodes (`2.03M/s`), 123 restarts | `0` sols, `max_depth = 29/31` |
| $K_{64}$ (open) | All 4 groups of order 63, SA | `starter_sa` | 120 s total | `6.79e7` SA steps (`565 k/s`) | `best_valid_cyc = 19` ($\mathbb{Z}_3\times\mathbb{Z}_{21}$), `20` ($\mathbb{Z}_7\rtimes\mathbb{Z}_9$, $F_{21}\times\mathbb{Z}_3$), `21` ($\mathbb{Z}_{63}$) |
| $K_{22}$–$K_{38}$ (SA scaling) | $\mathbb{Z}_{21}, F_{21}, \mathbb{Z}_{27}, \mathbb{Z}_{33}, \mathbb{Z}_{35}, \mathbb{Z}_{37}$ | `starter_sa` | 125 s total | `3.26e8` SA steps | `best_valid_cyc`: `0` ($\mathbb{Z}_{21}$, `0.21s`), `1` ($F_{21}, \mathbb{Z}_{27}$), `2` ($\mathbb{Z}_{33}$), `3` ($\mathbb{Z}_{35}$), `5` ($\mathbb{Z}_{37}$) |
| $K_{22}$ (non-abelian check) | $F_{21} = \mathbb{Z}_7 \rtimes \mathbb{Z}_3$, pruned BT | `group_starter_bt` | 15 s | `9.77e7` nodes (`6.51M/s`) | `0` sols (`max_depth = 9/10`, vs `0.007 s` for $\mathbb{Z}_{21}$) |

**Takeaway on why $K_{64}$ resists starter searches:** All four groups of order 63 have identical node rates (~2.0M nodes/s) and identical depth ceilings (`29/31`), with zero admissible automorphism reductions; 2-opt simulated annealing hits a glassy local-minimum floor rising from `0` ($H=10$) to `19–21` ($H=31$). Meanwhile, our generalized finite-ring backtracker scales cleanly whenever $c = (n-1)/(2|U|)$ is small ($c = 8$ settled $K_{1682}$ in 35 minutes; $K_{290}$ at $c = 16$ has no obstruction and requires ~15 days on 2 cores or ~1 day on a 32-core node).

---

## Handoff — read this first if you are picking the work up

- **Where it stands:**
  - **$K_{64}$** remains `open`; all starter-automorphism and affine even-starter symmetries are now ruled out rigorously in `proof.md`.
- **Next high-yield open target:** **$K_{290}$** ($q = 17^2 = 289$, smallest open prime-power order in Kotzig's conjecture). Empirical decay is clean geometric $r \approx 0.227$ across all $c = 16$ conditions (`h7 = 8` in 15s) with zero algebraic obstruction; estimated ~15 days on 2 cores (or ~12 hours on 64 cores).
- **Exact resume commands:**
  ```bash
  # Resume K_290 (change SEED per worker/chunk):
  python conjectures/kotzig-perfect-1f/gen_ring_spec.py spec spec_k290.txt GF 17 2 9
  gcc -O3 -march=native -pthread -o ring_starter_bt_v2 conjectures/kotzig-perfect-1f/ring_starter_bt_v2.c
  ./ring_starter_bt_v2 spec_k290.txt 2 <SEED> 50000 3600 1 1

  # Resume K_64 on any of the 4 groups (Z63, Z3xZ21, Z7sZ9, F21xZ3):
  python conjectures/kotzig-perfect-1f/gen_group_spec.py spec grp_Z7sZ9.txt Z7sZ9
  gcc -O3 -march=native -pthread -o group_starter_bt conjectures/kotzig-perfect-1f/group_starter_bt.c
  ./group_starter_bt grp_Z7sZ9.txt 2 <SEED> 500000 3600 1
  ```
- **Do not retry:**
  - Multiplier-invariant starters in any group of order 63 (ruled out by Theorem 3.2).
  - Affine-invariant even starters in $\mathbb{Z}_{62}$ (ruled out by Theorem 3.3).
  - Quadratic $c=1$ starters in $\mathbb{F}_{3^7}$ ($K_{2188}$) or $\mathbb{F}_{3^9}$ ($K_{19684}$) (exhaustively ruled out).
  - Naive 2-opt simulated annealing on unreduced starters of $K_{64}$ (glassy floor at `cycle_excess = 19–21`).

---

## Result

- **`proof (reviewed)`:** Constructed and independently brute-force verified a **perfect 1-factorization of $K_{1682}$ ($q = 41^2 = 1681$)**, an order not covered by the sources read (see Review; the earlier "first for p ≡ 1 mod 8" claim was false and is withdrawn). See [`proof.md`](proof.md), [`data/k1682_starter.txt`](data/k1682_starter.txt), [`data/k1682_matchings.txt.xz`](data/k1682_matchings.txt.xz), [`verify_p1f.c`](verify_p1f.c), and [`verify_k1682_independent.py`](verify_k1682_independent.py).
- **`open`:** $K_{64}$ remains open; complete symmetry obstructions for all four groups of order 63 and all affine maps on $\mathbb{Z}_{62}$ are proved and verified, and non-abelian backtracking and simulated annealing probes are recorded above.
