# Erdős #1094 — Erdős–Lacampagne–Selfridge least prime factor of binomial coefficients

- **Reference:** Erdős Problem #1094 (`https://www.erdosproblems.com/1094`, accessed 2026-11-26); Guy's *Unsolved Problems in Number Theory* B31/B33; Wolfram MathWorld *Exceptional Binomial Coefficient* (`https://mathworld.wolfram.com/ExceptionalBinomialCoefficient.html`); MathOverflow #368183; P. Erdős, C. B. Lacampagne, and J. L. Selfridge (`[ELS88]`, `[ELS93]` *Math. Comp.* 61 (1993), 215–224; `UNVERIFIED CITATION:` original PDFs not opened directly, statements quoted verbatim from `erdosproblems.com/1094` and MathWorld).
- **Status:** open
- **Read first:** [`HEADLINE.md`](HEADLINE.md) is the current statement of what was found. It
  quotes the 1993 paper itself (read on 2026-11-26) and supersedes three things written earlier in
  this file: (1) "primary sources not read" — `[ELS93]` has been read, Guy's book has not;
  (2) the misprint (13277; 900) is in `[ELS93]` itself, MathWorld copied it; (3) the count of new
  pairs above both n/k and 17 is six (ten in all up to 10^36), not the three of the first scan to 10^7.


## Statement (verbatim from `https://www.erdosproblems.com/1094`)

> "For all $n \ge 2k$ the least prime factor of $\binom{n}{k}$ is $\le \max(n/k, k)$, with only finitely many exceptions."
>
> "Selfridge `[Se77]` further conjectured that this always happens if $n \ge k^2 - 1$, except $\binom{62}{6}$."
>
> "More precisely, in `[ELS88]` they conjecture that if $n \ge 2k$ then the least prime factor of $\binom{n}{k}$ is $\le \max(n/k, k)$ with the following 14 exceptions:
> $\binom{7}{3}, \binom{13}{4}, \binom{23}{5}, \binom{14}{4}, \binom{44}{8}, \binom{46}{10}, \binom{47}{10}, \binom{47}{11}, \binom{62}{6}, \binom{74}{10}, \binom{94}{10}, \binom{95}{10}, \binom{241}{16}, \binom{284}{28}$."
>
> "Indeed, in `[ELS93]` they provide some further computational evidence, and point out it is consistent with what they know that in fact this holds with $\le \max(n/k, 13)$, with only 12 exceptions."
>
> "Discussed in problem B31 and B33 of Guy's collection `[Gu04]` - there Guy credits Selfridge with the conjecture that if $n > 17.125k$ then $\binom{n}{k}$ has a prime factor $p \le n/k$."

## Sanity check

`python verify_1094.py --max-n 2000` (0.66s) reproduced:
- All **14** published `[ELS88]` exceptions to $\text{lpf}\binom{n}{k} \le \max(n/k, k)$ (exact match with exact `math.comb` factorization for $n \le 300$).
- All **10** exceptions below $n = 2000$ to $\text{lpf}\binom{n}{k} \le \max(n/k, 13)$ (plus `(14273, 896)` and `(14277, 900)` reproduced by `kummer_1094.c` and `kummer_1094_fast.py`).
- Selfridge's unique exception $\binom{62}{6}$ for $n \ge k^2 - 1$, and $0$ exceptions for $n > 17.125k$.

## Method

We combine two Kummer-theorem structural reductions (implemented in LLVM-compiled Numba `@njit` in `kummer_1094_fast.py`, plus C cross-check `kummer_1094.c` and completely independent verifier `verify_findings.py`):

1. **Exact binary-submask scan for general $(n, k)$ ($2 \le k \le n/2$, $n \le N_{\max}$):**
   By Kummer's theorem, $2 \nmid \binom{n}{k} \iff (k \mathbin{\&} n) = k$. Letting $B = 2^{\lfloor \log_2 n \rfloor}$ be the highest set bit of $n$, we have $2B > n$, so $k \le n/2$ excludes bit $B$; hence
   $$2 \nmid \binom{n}{k} \text{ and } 2 \le k \le n/2 \iff k \ge 2 \text{ is a binary submask of } (n \oplus B).$$
   Enumerating only binary submasks cuts the search space from $\Theta(N^2)$ to $\Theta(N^{\log_2 3}) = \Theta(N^{1.585})$ (470× fewer pairs at $N = 10^7$), and an unrolled bottom-2-digit base-3 check rejects another $5/9$ in $O(1)$ cycles before entering any loop.

2. **Exact Kummer-CRT reduction for Regime 1 ($2k \le n \le k^2$, i.e., Erdős–Selfridge $g(k) > k^2$):**
   Suppose $\text{lpf}\binom{n}{k} > k$, so $p \nmid \binom{n}{k}$ for every prime $p \le k$. For any $c \in \{1, 2, 3, 4\}$ and any prime power $q = p^a \parallel (k + c)$ with $p \le k$, Kummer's theorem requires every base-$p$ digit of $n \bmod q$ to be $\ge$ the corresponding base-$p$ digit of $k \bmod q$, restricting $n \bmod q$ to a subset of $[k \bmod q, q - 1]$ (at most $c$ residues; only **1 residue**, $n \equiv -1 \pmod{k+1}$, whenever $k+1$ is composite!).
   For every $k \ge 20$, at least two coprime composite moduli exist among $\{k+1, k+2, k+3, \text{odd}(k+4)\}$ with all prime factors $< k$:
   - $k+1$ composite, $k+2$ composite $\implies$ CRT modulus $(k+1)(k+2) > k^2$;
   - $k+1$ composite, $k+2$ odd prime $\implies k+1$ odd, $k+3$ even composite, $\gcd(k+1, k+3) = 1$, modulus $(k+1)(k+3) > k^2$;
   - $k+1$ odd prime, $k+3$ odd composite $\implies k+2$ even composite, $\gcd(k+2, k+3) = 1$, modulus $(k+2)(k+3) > k^2$;
   - twin primes $(k+1, k+3) \implies k+2$ even composite, $\text{odd}(k+4)$ coprime to $k+2$, modulus $\ge k^2 / 4$.
   This cuts the $k^2$ candidates per $k$ to $O((\log k)^c)$ exact CRT residues, verifying $2k \le n \le k^2$ for ALL $k \le 20{,}000{,}000$ ($n \le 4 \times 10^{14}$, $\sim 2.67 \times 10^{21}$ binomial coefficients) in **7.50 seconds** on 2 cores!

3. **Kummer phase-transition analysis for $\text{lpf}\binom{n}{k} \le \max(n/k, P)$:**
   Under base-$p$ digit independence across primes $p \le P$, a random pair $0 \le k \le n \le N$ is carry-free in base $p$ with fraction $\left(\frac{p+1}{2p}\right)^{\log_p N} = N^{\ln((p+1)/(2p)) / \ln p}$. Multiplying over $p \le P$ gives expected count $\sim N^{\alpha(P)}$ where $\alpha(P) = 2 + \sum_{p \le P} \frac{\ln((p+1)/(2p))}{\ln p}$:
   - $P = 13$: $\alpha(13) = \mathbf{+0.116789 > 0}$ $\implies$ **diverges** (infinitely many exceptions expected!).
   - $P = 17$: $\alpha(17) = \mathbf{-0.107687 < 0}$ $\implies$ **converges** (finitely many exceptions expected).
   - $P = 19$: $\alpha(19) = -0.325676$; $P = 23$: $\alpha(23) = -0.533167$; $P = 29$: $\alpha(29) = -0.728946$.

   This explains both why the stronger `[ELS93]` remark (`max(n/k, 13)` with 12 exceptions) breaks dramatically (55 exceptions below $10^7$ and still growing in digit-aligned clusters) and why `max(n/k, 17)` appears to terminate quickly (only 7 exceptions below $10^7$, none after $n = 57{,}077$).

## Result

All 66 rows in [`data/exceptions_1094.tsv`](data/exceptions_1094.tsv) were **independently verified** by [`verify_findings.py`](verify_findings.py) using exact `gmpy2.bincoef` (for 55 rows) and exact Legendre factorial valuations (for the 11 largest rows where $\log_{10}\binom{n}{k} > 150{,}000$), with **zero** Kummer or CRT code shared with the search engines.

### 1. New exceptions to the bound `max(n/k, 13)` (a remark in `[ELS93]`, not a formal conjecture)

We found **55 exceptions** to $\text{lpf}\binom{n}{k} \le \max(n/k, 13)$ with $n \le 10{,}000{,}000$ — **43 NEW confirmed exceptions** beyond the 12 listed on `erdosproblems.com/1094` and MathWorld (which stop at `(14273, 896)` and `(14277, 900)`). The first new ones are `C(23799, 3159)` and `C(23799, 3168)` (`lpf = 17`), and they continue in clusters up to `C(5764797, 430137)` (`lpf = 17`, `n/k = 13.4022`).

In particular, we found **3 NEW confirmed exceptions to $\text{lpf}\binom{n}{k} \le \max(n/k, 17)$** (previously only 4 were listed: `(62, 6)`, `(284, 28)`, `(474, 66)`, `(959, 56)`):

| $(n, k)$ | Exact $\text{lpf}\binom{n}{k}$ | $n/k$ | Independent check |
|---|---:|---:|---|
| $(57074, 22050)$ | **23** | $2.5884$ | `gmpy2.bincoef` exact |
| $(57075, 22050)$ | **23** | $2.5884$ | `gmpy2.bincoef` exact |
| $(57077, 22052)$ | **19** | $2.5883$ | `gmpy2.bincoef` exact |

Full list of all 55 exceptions to `max(n/k, 13)` (and all 14 exceptions to `max(n/k, k)`) is in [`data/exceptions_1094.tsv`](data/exceptions_1094.tsv).

### 2. Confirmed MathWorld erratum

Wolfram MathWorld (`ExceptionalBinomialCoefficient.html`) lists `(13277, 900)` as an exceptional binomial coefficient with $\text{lpf} = 17$. Exact `gmpy2.bincoef` confirms this is a typo for `(14277, 900)`:
- $\text{lpf}\binom{13277}{900} = 3$,
- $\text{lpf}\binom{14277}{900} = 17 > 14277/900 = 15.8633$.

### 3. Exhaustive verification bounds pushed

| Sub-conjecture | Verified range | Result | Hardest non-trivial cases |
|---|---|---|---|
| **Regime 1:** $2k \le n \le k^2 \implies \text{lpf}\binom{n}{k} \le k$ (i.e. $g(k) > k^2$ for $k > 28$) | **$2 \le k \le 20{,}000{,}000$, $n \le 4 \times 10^{14}$** ($\sim 2.67 \times 10^{21}$ pairs; 2.41B CRT candidates, 7.50s) | **EXACTLY the 13 known exceptions** (all $k \le 28$) | Last exception: `C(284, 28)` (`lpf = 29`) |
| **Erdős #1094 / `[ELS88]`:** $\text{lpf}\binom{n}{k} \le \max(n/k, k)$ | **ALL $2 \le k \le n/2$, $n \le 10{,}000{,}000$** ($2.5 \times 10^{13}$ pairs; 52.93B submasks, 120.53s) | **EXACTLY the 14 known exceptions** | Last exception: `C(284, 28)` (`lpf = 29`) |
| **`[ELS93]` main conjecture:** $\text{lpf}\binom{n}{k} \le \max(n/k, 29)$ | **ALL $2 \le k \le n/2$, $n \le 10{,}000{,}000$** | **0 exceptions** | Closest: `C(284, 28)` (`lpf = 29`), `C(57074, 22050)` & `C(57075, 22050)` (`lpf = 23`) |
| **Selfridge (1977):** $n \ge k^2 - 1 \implies \text{lpf}\binom{n}{k} \le n/k$ | **ALL $2 \le k \le n/2$, $n \le 10{,}000{,}000$** | **ONLY `C(62, 6)`** | Unique `C(62, 6)` (`lpf = 19`, $n/k = 10.333$) |
| **Guy B31/B33:** $n > 17.125k \implies \text{lpf}\binom{n}{k} \le n/k$ | **ALL $2 \le k \le n/2$, $n \le 10{,}000{,}000$** | **0 exceptions** | Equality `C(959, 56)` ($17.1250$); next highest ratio: `C(56699, 3432)` ($16.5207$), `C(71679, 4401)` ($16.2870$), `C(1405499, 86544)` ($16.2403$) |

## Handoff — read this first if you are picking the work up

- **Where it stands:**
  - Confirmed **43 new exceptions** (55 total below $10^7$) beyond the 12 known for the bound `max(n/k, 13)` (which `[ELS93]` only called "possible"; see `HEADLINE.md`), including **3 new exceptions to `max(n/k, 17)`** (`(57074, 22050)`, `(57075, 22050)`, `(57077, 22052)`), all independently verified via `gmpy2.bincoef` / Legendre.
  - Exhaustively verified Regime 1 ($g(k) > k^2$) up to **$k \le 20{,}000{,}000$ ($n \le 4\times 10^{14}$)** in 7.50s, and ALL $2 \le k \le n/2$ up to **$n \le 10{,}000{,}000$** in 120.53s.
- **Next steps:**
  1. **Push Regime 1 to $k \le 10^8$ ($n \le 10^{16}$)** — at 7.5s per $2\times 10^7$, this takes ~45 seconds (check 64-bit `diff * inv` overflow for $q > 2^{32}$, fine up to $k < 4\times 10^9$).
  2. **Extend Regime 2 (`n > k^2`, Selfridge 1977 & Guy B31/B33) beyond $n = 10^7$ using a base-$2 \times 3$ or base-$2 \times 3 \times 5$ meet-in-the-middle / CRT-Kummer generator** for fixed small $k$ ($k \le 5000$) up to $n \le 10^{12}$, targeting a possible counterexample to Guy's $n > 17.125k$ or Selfridge's $n \ge k^2 - 1$!
  3. **Write a short note on the $P = 13 \to 17$ phase transition** and the 43 new exceptions (plus the `C(13277, 900)` MathWorld erratum); verify against the original `[ELS93]` PDF before any external communication.
- **How to resume:**
  ```powershell
  cd conjectures/erdos-1094
  python verify_1094.py --max-n 2000
  python kummer_1094_fast.py --regime1 20000000 --threads 2
  python kummer_1094_fast.py --scan-n 10000000 --threads 2 --out-tsv data/exceptions_1094.tsv
  python verify_findings.py data/exceptions_1094.tsv
  ```
- **Do not retry:** Naive $O(N^2)$ scanning in Python (already superseded by the $O(N^{1.585})$ binary-submask scanner and $O(K \log^c K)$ Kummer-CRT engine).
