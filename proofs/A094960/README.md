# A094960 — Bernoulli polynomials whose derivative has only integer coefficients

- **OEIS:** https://oeis.org/A094960 (related: A195441, A324370, A366168, A366169)
- **Status:** proof (reviewed)

## Statement (verbatim from OEIS)

Quoted from the mirror `raw.githubusercontent.com/oeis/oeisdata/main/seq/A094/A094960.seq`
(revision #64, Nov 24 2026), fetched 2026-11-26. No request to oeis.org was made.

> %N A094960 Positive integers k such that the derivative of the k-th Bernoulli polynomial B(k,x) contains only integer coefficients.
>
> %S A094960 1,2,4,6,10,12,28,30,36,60
>
> %C A094960 There are no other terms below 10^9. [_Max Alekseyev_, Dec 08 2011]
>
> %C A094960 If for a prime p >= 3, k ends with base-p digits a,b with a+b >= p, then for m = (a+1)*(p-1), the number k*binomial(k-1,m)*Bernoulli(m) is not an integer (it contains p in the denominator). [...]
>
> %C A094960 Conjecture: for every integer k > 78, there exists a prime p >= 3 such that the sum of last two base-p digits of k is at least p. This conjecture would imply that this sequence is finite and 60 is the last term. (End) [_Max Alekseyev_, Jun 04 2012]
>
> %C A094960 The conjecture is true for all k such that k+1 is not a prime, a power of 2, or a Giuga number (A007850). In this case, there exists a prime p >= 3 such that the base-p representation of k ends in a,p-1 with a > 0. - _Max Alekseyev_, Feb 16 2021
>
> %C A094960 The sequence is finite and is a subsequence of A366169. The terms are those numbers k where A324370(k) = 1. It remains to show that 60 is the last term. This is very likely, since the terms depend on the estimation of a product of primes satisfying certain p-adic conditions that is connected with A324370. A proven asymptotic formula related to that product implies that this sequence is finite. See Kellner 2017, 2023, and BLMS 2018. - _Bernd C. Kellner_, Oct 02 2023

Siblings (same mirror, same day):

> %C A195441 The equation a(n-1) = denominator(Bernoulli_n(x) - Bernoulli_n) = rad(n+1) has only finitely many solutions, where rad(n) = A007947(n) is the radical of n. It is conjectured that S = {3, 5, 8, 9, 11, 27, 29, 35, 59} is the full set of all such solutions. [...] - _Bernd C. Kellner_, Oct 18 2023
>
> %C A366169 The sequence is finite and is a supersequence of A094960. The terms are those numbers k where the denominator A366168(k) = 1. It remains to show that 190 is the last term. [...]

Conventions pinned down: offset 1; `k` ranges over positive integers (`k = 0` is excluded,
`k = 1` counts: `B_1(x) = x - 1/2`, derivative 1); "integer coefficients" means all coefficients
of the polynomial `B_k'(x) = k B_{k-1}(x)`; the sign convention for `B_1` does not affect any
denominator. A195441 has offset 0 and `a(n)` uses index `n + 1`, so Kellner's set is about
`n >= 1` with `denominator(B_n(x) - B_n) = rad(n+1)`. Published verification bound: no other
terms below 10^9 (Alekseyev 2011); `> 10^7` in Kellner's paper.

In the papers (statements quoted in `proof.md`, section 7): Kellner, *On the finiteness of
Bernoulli polynomials whose derivative has only integral coefficients*, J. Integer Seq. 27 (2024),
Article 24.2.8, arXiv:2310.01325 — Conjecture 1(ii) (the ten terms are all), Conjecture 2(i)
(= Conjecture 1 of Kellner, *On a product of certain primes*, J. Number Theory 179 (2017): for
`n > 192` there is a prime `p > sqrt(n)` with `s_p(n) >= p`), Conjecture 11 (the set for A195441),
Conjecture 15 (second and third derivatives). The paper proves finiteness from an asymptotic of
Bordellès, Luca, Moree and Shparlinski and says: "Unfortunately, their methods do not lead to an
explicit or computable bound n_0" and "it is still an open task to establish Conjectures 1(ii)
and 2(i)."

## Sanity check

`python check_bernoulli.py` builds `B_k(x)` for `k <= 1100` in exact rational arithmetic and
reproduces the data sections of A094960 (10 terms), A366169 (29 terms), A195441 (60 terms),
A324370 (74 terms), A366168 (76 terms), Kellner's sets `R` and `S_3`: **yes** (all `[ok]`).

## Lean formalization

`#print axioms` output, what is not formalized and how to build are in
[`lean/README.md`](lean/README.md). In short, the Lean kernel checks (no `sorry`, no `axiom`, no
`native_decide` in the proofs; axioms used: `propext`, `Classical.choice`, `Quot.sound`):

- Theorem 1 (a), Kellner's conjecture:
  `∀ n : ℕ, 193 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum`;
  no such prime for `n = 192`; for `1 ≤ n ≤ 192` one exists exactly when `n` is not in `E_0`;
- Theorem 1 (b), (c) for `n ≥ 1081` and (d) for `n ≥ 193`;
- Corollary A, the OEIS statement: for `k ≥ 1`, `B_k'(x)` has only integer coefficients if and
  only if `k` is one of 1, 2, 4, 6, 10, 12, 28, 30, 36, 60

**under two hypotheses that are not proved in Lean** (they are arguments of the theorems):
`m / (ln m - 1) ≤ π(m)` and `π(m) ≤ m / (ln m - 1.107)`, both for integers `m ≥ 468049`. Both
follow, in Lean, from Axler's Corollary 3.5 (2016 paper) and Theorem 2 (2018 paper) as published
(`lean/Kellner/Cited.lean`); those two statements are cited, not formalized.

Proved in Lean, with nothing assumed: Lemmas 2 to 5 and Proposition 6; Proposition 7 for
`F ≥ 468049` from the two hypotheses; the finite check for every `n < 468049^2` (so step (b0) of
`threshold_test.py` and the C program are not needed by the Lean proof); Lemma 1 (ii) for `i = 1`,
with von Staudt-Clausen and Lucas taken from Mathlib. Not formalized: Axler's two cited bounds,
the sets `E_1`, `E_2`, `E_3`, Corollaries B to F. Formalizing found no error in sections 2 to 6
of `proof.md`.

The Lean statements were compared with the OEIS entry, with Kellner's papers and with Axler's two
(8 to 10 minutes on the Ryzen 5 7600X under WSL2, Mathlib from its cache).

## Files

| File | What it does | Time |
|---|---|---|
| `proof.md` | the write-up | |
| `check_bernoulli.py` | exact Bernoulli polynomials to `k = 1100`; OEIS data; small cases of all corollaries; tests Lemma 1 | 25 s |
| `finite_check.c`, `run_finite_check.sh` | for every `n < 60184^2`, smallest prime `p > sqrt(n)` with `s_p(n) >= p` (4 variants), digit sums by division; lists exceptions and hardest cases | 2 × 22 s |
| `verify_small.py` | independent Python version of the same search to `2·10^6`, compared with the C output; small cases of Alekseyev's conjecture | 10 s |
| `lemma_test.py` | tests Lemmas 2–4 and Proposition 6 (43 million pairs `(n, s)`) | 2 min |
| `threshold_test.py` | **proof steps (b0) and (b)**: `pi(x) >= x/(ln x - 1)` on `[5393, 468049)` and `pi(x) <= x/(ln x - 1.107)` on `[60184, 468049)`; constants of Proposition 7; `pi(x)` bounds checked to `2.1·10^7`; actual prime counts against the bound for all `F <= 2·10^7` | 3 s |
| `data/finite_check_*.txt` | outputs of the C program (exceptions, records, histograms, checksums) | |

## Handoff

  objections, pass); all objections applied; all programs run and committed; nothing running.
- Reviewed so far (by the referee, with independent code): Lemmas 1–5 and Proposition 7
  re-derived; the full finite check repeated with a second program; Bernoulli data to `k = 1100`
  repeated; Axler's Corollaries 3.4 and 3.5, Kellner's statements and the journal numbering
  compared with the sources (this comparison missed Axler's 2018 corrigendum to Corollary 3.4,
- Still owed:
  1. a **human review**, ideally by someone who works with explicit prime-counting estimates:
     the two cited bounds (Axler 2016 #A22 Corollary 3.5; Axler 2018 #A52 Theorem 2) are the only
     part of the result that no program here checks in full. The model reviews are done;
  2. a person opens a textbook for von Staudt–Clausen (the only citation the proof uses that is
     still marked `UNVERIFIED CITATION:`);
  3. novelty: MathSciNet, zbMATH and "cited by" lists for Kellner's paper, and the OEIS Open
     results site, have not been checked by anyone;
  4. nobody has audited Axler's proofs of Corollary 3.5 (2016) and Theorem 2 (2018). Two other
     statements of the 2016 paper turned out to have problems (Corollary 3.4 false as printed,
     Theorem 1.3 with a gap in its proof), so this matters. What exists: Corollary 3.5 follows
     from Theorem 1.4 of the 2016 paper above 1332479531 and was "checked with a computer" below;
     A human who knows explicit prime-counting estimates should look at Theorem 1.4 (2016) and
     Theorem 2 (2018).
- To reproduce everything: `python check_bernoulli.py && bash run_finite_check.sh && python
  verify_small.py && python lemma_test.py && python threshold_test.py` (under 4 minutes).
- Do not announce or edit OEIS: results are held (see `CONTRIBUTING.md`).

## Result

`proof (reviewed)` of: A094960 is complete (last term 60); Kellner's Conjecture 2(i) / Conjecture 1
of his 2017 paper; A366169 is complete (last term 190); third-derivative list complete (last term
392); the A195441 set {3, 5, 8, 9, 11, 27, 29, 35, 59} is complete. Status `proof (reviewed)`
since 2026-11-26 (four reviews, the last one a pass), given two cited bounds for `pi(x)`; the
Lean formalization covers Theorem 1 and the A094960 statement from those two bounds.
