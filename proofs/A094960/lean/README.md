# Lean 4 formalization of the A094960 proof draft

checks, in Lean 4 with Mathlib, Theorem 1 and Corollary A of [`../proof.md`](../proof.md).
with Axler's two cited statements, and the last one is a pass. It is not `proof (formalized)`,
because the two prime-counting bounds are hypotheses of the theorems, not proved in Lean.

## What Lean checks, and from what

Everything below is checked by the Lean kernel. There is no `sorry`, no `axiom`, no `admit`, and
the final theorems do not use `native_decide`.

**Two inequalities for `π(x)` are assumed.** They are not in Mathlib and are not proved here. They
enter only as hypotheses of the theorems (`Kellner/Analytic.lean`):

```lean
def AxlerLower : Prop :=
  ∀ m : ℕ, 468049 ≤ m → (m : ℝ) / (Real.log m - 1) ≤ Nat.primeCounting m

def AxlerUpper : Prop :=
  ∀ m : ℕ, 468049 ≤ m → (Nat.primeCounting m : ℝ) ≤ m / (Real.log m - 1.107)
```

Sources: for the lower bound, C. Axler, *New bounds for the prime counting function*, Integers 16
(2016), #A22 (arXiv:1409.1780), Corollary 3.5 (p. 10); for the upper bound, C. Axler, *New
estimates for some functions defined over primes*, Integers 18 (2018), #A52, Theorem 2 (p. 4).
`Kellner/Cited.lean` also states these two as in the papers, for real `x` with
`π(x) = Nat.primeCounting ⌊x⌋₊`, and proves in Lean that they imply the two hypotheses above:

```lean
def AxlerCor35 : Prop :=
  ∀ x : ℝ, 468049 ≤ x → x / (Real.log x - 1 - 1 / Real.log x) < (Nat.primeCounting ⌊x⌋₊ : ℝ)

def Axler18Thm2 : Prop :=
  ∀ x : ℝ, 49 ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / (Real.log x - 1 - 1 / Real.log x - 3.15 / Real.log x ^ 2 - 12.85 / Real.log x ^ 3
        - 71.3 / Real.log x ^ 4 - 463.2275 / Real.log x ^ 5 - 4585 / Real.log x ^ 6)

theorem axlerLower_of_cor35 (h : AxlerCor35) : AxlerLower
theorem axlerUpper_of_thm2 (h : Axler18Thm2) : AxlerUpper
```

**Corrected on 2026-11-26.** Until then the upper bound was the hypothesis `AxlerCor34`
(`π(x) < x / (ln x - 1 - 1.17 / ln x)` for `x ≥ 5.43`, the last statement of Axler's
Corollary 3.4). That statement is false as printed (it fails at `x = 59753`, `10^8`, `10^9`) and
Axler corrected it in 2018 to `x ≥ 2634800823`. A theorem with a false hypothesis says nothing,
this by comparing the Lean text with the paper and its corrigendum
. The same review confirms that `AxlerCor35`
matches the paper symbol for symbol.

**Corrected a second time on 2026-11-26.** The first replacement was `AxlerThm13`, Theorem 1.3 of
confirmed that it matched the paper symbol for symbol and held on every range tested, but pointed
out that Axler's 2018 paper says the published proof of Theorem 1.3 has a mistake and replaces it
by a new Theorem 2. The hypothesis is now that Theorem 2, `Axler18Thm2`. It was compared with p. 4
review.

Kellner's Conjecture 1 (J. Number Theory 179 (2017), p. 2) has two inequalities,
`P(p_n) > √n` and `(n+1)/P(p_n) < √n`. `kellner` is the first; `kellner_partD` (Theorem 1 (d),
a prime `p > (n+1)/√n` with `s_p(n) ≥ p`) gives both.

## The theorems (exact statements)

`s_p(n)` is `(Nat.digits p n).sum`. "`p > √n`" is `n < p ^ 2`. "`p > (n + 1) / √n`" is
`(n + 1) ^ 2 < p ^ 2 * n`. `Polynomial.bernoulli k` is Mathlib's Bernoulli polynomial
`B_k(x) = Σ C(k, i) B_i x^(k-i)` with `B_1 = -1/2`, formula (0.1) of the draft.

`Kellner/Main.lean`:

```lean
-- Theorem 1 (a): Kellner's conjecture
theorem kellner (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ n : ℕ, 193 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum

-- sharpness; no hypotheses
theorem kellner_sharp :
    ¬ ∃ p : ℕ, p.Prime ∧ 192 < p ^ 2 ∧ p ≤ (Nat.digits p 192).sum

-- the exceptional set E_0; no hypotheses
theorem kellner_exceptions :
    ∀ n : ℕ, 1 ≤ n → n ≤ 192 →
      ((∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum) ↔
        n ∉ [1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80,
          174, 190, 191, 192])

-- Theorem 1 (b)
theorem kellner_partB (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ n : ℕ, 1081 ≤ n →
      ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧ ¬ p ∣ n + 1

-- Theorem 1 (c)
theorem kellner_partC (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ n : ℕ, 1081 ≤ n →
      ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧ ¬ p ∣ (n + 1) * (n + 2)

-- Theorem 1 (d)
theorem kellner_partD (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ n : ℕ, 193 ≤ n →
      ∃ p : ℕ, p.Prime ∧ (n + 1) ^ 2 < p ^ 2 * n ∧ p ≤ (Nat.digits p n).sum
```

`Kellner/Bernoulli.lean`:

```lean
-- Corollary A: the OEIS statement of A094960 (Kellner 2023, Conjecture 1 (ii))
theorem A094960_complete (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ k : ℕ, 1 ≤ k →
      ((∀ i : ℕ, ∃ z : ℤ, (derivative (Polynomial.bernoulli k)).coeff i = (z : ℚ)) ↔
        k ∈ [1, 2, 4, 6, 10, 12, 28, 30, 36, 60])

-- the part that needs no hypothesis
theorem A094960_upto_192 :
    ∀ k : ℕ, 1 ≤ k → k ≤ 192 →
      ((∀ i : ℕ, ∃ z : ℤ, (derivative (Polynomial.bernoulli k)).coeff i = (z : ℚ)) ↔
        k ∈ [1, 2, 4, 6, 10, 12, 28, 30, 36, 60])
```

`Kellner/Cited.lean`: `kellner_of_axler`, `kellner_partD_of_axler` and `A094960_complete_of_axler`
are `kellner`, `kellner_partD` and `A094960_complete` with the hypotheses
`(h35 : AxlerCor35) (h2 : Axler18Thm2)` instead.

Pieces of the draft, with no hypotheses unless shown:

| Draft | Lean | File |
|---|---|---|
| Lemma 2 (digits of `n < p^2`) | `digits_sum_of_lt_sq` | `Basic.lean` |
| Lemma 3 | `lemma3` | `Basic.lean` |
| Lemma 4 | `card_failing_le` (with `two_mul_le_div_add`, `div_add_le`) | `Basic.lean` |
| Lemma 5 (i), (ii) | `card_prime_dvd_le_one`, `lemma5_ii` | `Basic.lean` |
| Proposition 6 | `prop6`; then `window_partC`, `window_partD` (section 4) | `Basic.lean` |
| Proposition 7, for `F ≥ 468049` | `prop7 (hLow : AxlerLower) (hUp : AxlerUpper)` | `Analytic.lean` |
| Proposition 9 (finite check), for `n < 468049^2` | `windowOK_of_lt`, `partC_small`, `partD_small`, `exceptions_iff` | `FiniteKernel.lean` |
| Lemma 1 (ii), `i = 1`, `p > √k` | `lemma1`, `not_derivIntegral_of_witness` | `Bernoulli.lean` |
| Facts 1.1, 1.2, 1.3 | Mathlib: `Polynomial.derivative_bernoulli`, `Choose.choose_modEq_choose_mod_mul_choose_div_nat`, `Bernoulli.vonStaudt_clausen` / `Bernoulli.dvd_den_bernoulli` | |

## Axioms

Output of `lake env lean Axioms.lean` (2026-11-26, after the second repair of `Cited.lean`), unedited:

```
'Kellner.kellner' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.kellner_partB' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.kellner_partC' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.kellner_partD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.kellner_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.kellner_exceptions' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.A094960_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.not_derivIntegral_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.A094960_upto_192' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.axlerLower_of_cor35' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.axlerUpper_of_thm2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.kellner_of_axler' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.kellner_partD_of_axler' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.A094960_complete_of_axler' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.lemma3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.card_failing_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.prop6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.prop7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.windowOK_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.partC_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.partD_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.lemma1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Kellner.Native.windowOK_of_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Kellner.Native.finite_window._native.native_decide.ax_1_1]
'Kellner.Native.partC_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Kellner.Native.finite_smallC._native.native_decide.ax_1_1]
'Kellner.Native.partD_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Kellner.Native.finite_smallD._native.native_decide.ax_1_1]
grep: no sorry, axiom or admit in the Lean sources
uses of the native_decide tactic (expected: Kellner/FiniteNative.lean only):
Kellner/FiniteNative.lean:140:  native_decide
Kellner/FiniteNative.lean:144:  native_decide
Kellner/FiniteNative.lean:148:  native_decide
Kellner/FiniteNative.lean:152:  native_decide
```

`propext`, `Classical.choice`, `Quot.sound` are the three standard axioms of Lean and Mathlib.
The last three entries belong to `Kellner/FiniteNative.lean`, a second evaluation of the finite
check with `native_decide` that the final theorems do not use. (In this Lean version
`native_decide` shows up as one axiom per use, named `..._native.native_decide.ax_1_1`, not as
`Lean.ofReduceBool`.)

## How the finite check is done (`Kellner/FiniteKernel.lean`)

The draft checks all `n < 60184^2` with a C program. Here every `n < 468049^2 ≈ 2.19·10^11` is
covered by `decide +kernel`, so the lower bound for `π` is only needed from `468049` on, where it
is exactly Axler's Corollary 3.5; step (b0) of `threshold_test.py` (a floating-point check of the
lower bound on `[5393, 468049)`) is not used by the Lean proof.

- `1361 ≤ F < 468049`: the window criterion (6.1) with `r = 2`, that is at least `K(F, S) + 4`
  primes in `(F, F + S]` for some `S`; by Proposition 6 this settles all `n` with `⌊√n⌋ = F`.
  It is read off from an increasing chain of 12217 primes in `Kellner/Data.lean` (written by
  `gen_data.py`): if `q_0 < q_1 < ... < q_k` are primes with `K(q_0, q_k - q_0) + 4 ≤ k`, then
  every `F` in `[q_0, q_1)` satisfies the criterion with `S = q_k - F` (`K_chain_le`,
  `windowOK_of_goodFrom`, `chainOK_sound`). The chain has about 8 elements per `√F`, and every
  prime wherever that is not enough (near the lower end).
- Primality of the 12217 + 245 listed numbers: `n` is prime if `B < n < (B + 1)^2` and
  `gcd(n, B!) = 1` (`gcdPrime_sound`), with `B = 700`, 40, 6. One gcd per number.
- `193 ≤ n < 1361^2`: for each `F` from 13 to 1360 a sweep over `[F^2, (F + 1)^2)`. If a prime
  `p > F` is a witness at `n = a p + b`, it stays one up to `(a + 1) p - 1` (up to
  `(a + 1) p - 3` when `p ∤ (n + 1)(n + 2)` is required; up to `p^2 - 3` for part (d)), so the
  sweep jumps there (`partC_of_interval`, `partD_of_interval`, `sweep_sound`). 11179 jumps in all.
- `1 ≤ n ≤ 192`: the set `E_0`, directly (`finite_E0`).
- Nothing in the proof trusts `gen_data.py`: the kernel re-checks primality, monotonicity, the
  window inequality for every chain element, and that the pieces of the chain fit together.

## Differences from `proof.md`

- Proposition 7 is proved for `F ≥ 468049` only, with constants recomputed for `ln F ≥ 13`
  (`exp 13 < 468049` from Mathlib's bound on `e`; `ln x ≤ 8 x^(1/8) - 8` instead of the
  monotonicity of `x / ln^2 x`). The range `60184 ≤ F < 468049` is covered by the kernel
  computation, not by the estimate of the draft.
- Lemma 3 is stated without `F`: for any `n` and `p < q`, if `n / p + n % p < p`,
  `n / q + n % q < q` and `n / p + p = n / q + q`, then `q = p + 1`. (`n / p + p = 2F + c` in the
  notation of the draft.)
- Parts (a) and (b) are deduced from (d) and (c).
- Corollary A for `k ≤ 192` does not build the polynomials (`check_bernoulli.py`). It uses von
  Staudt-Clausen both ways: `B_k'` has a non-integral coefficient as soon as some prime `p` and
  even `2j` have `(p - 1) ∣ 2j` and `p ∤ k C(k-1, 2j)` (a table of 182 witnesses), and it is
  integral if every such `p` divides `k C(k-1, 2j)` (checked for the ten terms).

## Not formalized

- Axler's Corollary 3.5 (2016) and Theorem 2 (2018) themselves (they are the hypotheses).
- The exceptional sets `E_1`, `E_2`, `E_3`, and the sharpness of 1081 in parts (b), (c)
  (that `n = 1080` has no such prime). Only `E_0` and the sharpness of 193 are checked.
- Lemma 1 (i), and Lemma 1 (ii) for `i ≥ 2` or for primes `p ≤ √k`.
- Corollaries B, C, D, E, F of the draft.
- The estimate of Proposition 7 on `60184 ≤ F < 468049`, and Proposition 9 in the form of the
  draft (replaced as described above).

## What formalizing found in `proof.md`

No error and no gap in sections 2 to 6: every step went through as written, apart from the
constants of Proposition 7, which were redone for the larger threshold. Small remarks only:
Lemma 3 does not need `F` or `e`; Lemma 4 does not need `S ≥ 1`; the set `E_0` listed in section 0
is confirmed by the kernel.

## Files

| File | Content |
|---|---|
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lean `v4.36.0`, Mathlib `v4.36.0` (commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) |
| `Kellner/Basic.lean` | Lemmas 2 to 5, Proposition 6, window criterion |
| `Kellner/Analytic.lean` | the two hypotheses; Proposition 7 for `F ≥ 468049` |
| `Kellner/Data.lean` | generated data: `700!`, the primes in `[17, 1600)`, the chain of primes |
| `Kellner/FiniteKernel.lean` | the finite check, kernel-checked |
| `Kellner/Main.lean` | Theorem 1 (a) to (d), sharpness, `E_0` |
| `Kellner/Bernoulli.lean` | Corollary A |
| `Kellner/Cited.lean` | the hypotheses from Axler's Corollary 3.5 (2016) and Theorem 2 (2018) as published |
| `Kellner/FiniteNative.lean` | cross-check of the finite check with `native_decide`; not used |
| `Axioms.lean` | `#print axioms` for the theorems above |
| `gen_data.py`, `gen_table.py` | write `Kellner/Data.lean` and the witness table in `Kellner/Bernoulli.lean` (Python 3, standard library only) |
| `build.sh` | `lake exe cache get`, `lake build`, axioms, grep |

## Build

```
bash build.sh
```

Needs [elan](https://github.com/leanprover/elan). Mathlib comes pre-built from its cache
(about 7.4 GB under `.lake/`, which is git-ignored); it is not compiled from source.

Measured on 2026-11-26: AMD Ryzen 5 7600X (6 cores, 12 threads), Windows 11 with WSL2
(Ubuntu 24.04, 7.5 GB of memory for WSL), project on the Linux filesystem, Lean
`4.36.0` (commit `611c117bfaf7`). `lake build` of the eight project files from a clean build
directory, Mathlib already cached, while another job was using all six cores: **8 min 23 s** wall
time (`user` 4 min 33 s); a second run, on a `git archive` of the committed tree unpacked into a
fresh directory, took 9 min 53 s (`user` 4 min 45 s) with the same output. `FiniteNative.lean` (the unused cross-check) accounts for more than
3 minutes of CPU time.
