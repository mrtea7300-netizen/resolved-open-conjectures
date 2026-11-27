# Lean 4 kernel-checked disproofs of [ELS93] Conjectures 1 and 2

with Mathlib (`v4.36.0`), the exact least prime factors of the counterexamples found in
[`../HEADLINE.md`](../HEADLINE.md) and formal disproofs of Conjectures 1 and 2 of:

> P. Erdős, C. B. Lacampagne, J. L. Selfridge, *Estimates of the least prime factor of a binomial
> coefficient*, Math. Comp. 61 (1993), 215–224, Section 2, p. 222.

Everything is kernel-checked with no `sorry`, no `axiom`, no `admit`, and no `native_decide`.
Because the largest binomial coefficients here (`C(31152939, 1772289)`, `C(32634047, 2143377)`,
`C(32634223, 2143531)`) have roughly 10 million bits, `Nat.choose` is never evaluated directly;
instead, `Erdos1094/Lucas.lean` derives base-`p` digit dominance from Mathlib's Lucas's theorem
(`Choose.choose_modEq_choose_mod_mul_choose_div_nat`), and structurally recursive fueled checkers
(`digitsLeFuel`, `hasCarryFuel`) reduce directly in the kernel in `O(log_p k)` divisions.

## Statement versus the paper

From [ELS93], Section 2, p. 222 (quoted verbatim in [`../HEADLINE.md`](../HEADLINE.md)):

> "Definition 3. If `p((N k)) > N/k`, then `(N k)` is said to be exceptional. ... The most unusual
> exception is for `p = 29`: `p((284 28)) = 29`. We have found one exception for `p = 23`:
> `p((474 66)) = 23`. There appear to be exactly two exceptions for `p = 19`: `(62 6)` and
> `(959 56)`.
> We have two further conjectures:
> 1. The only exceptional `(N k)` with `p > 17` are these four.
> 2. `p((N k)) ≤ N/k` if `N > 17⅛ k`."

How each piece of the printed text maps to Lean:

- **Implicit parameter range `k ≥ 2` and `N ≥ 2k`.** Throughout [ELS93] (and [ELS88]), binomial
  coefficients `C(N, k)` are restricted to `2 ≤ k` and `2 * k ≤ N`: symmetry `C(N, k) = C(N, N - k)`
  reduces to `N ≥ 2k`, while `k = 0` gives `C(N, 0) = 1` (no prime factor) and `k = 1` gives
  `C(N, 1) = N` (which has `p(N) ≤ N = N/1`, never exceptional). Every counterexample theorem
  explicitly asserts `2 ≤ k ∧ 2 * k ≤ N` (and the negated universal statements quantify over
  `2 ≤ k → 2 * k ≤ N → ...`).
- **Least prime factor `p((N k))`.** In Mathlib, `(N.choose k).minFac` is the least prime factor
  of `Nat.choose N k` whenever `Nat.choose N k ≠ 1` (with the conventions `Nat.minFac 0 = 2` and
  `Nat.minFac 1 = 1`). Every pair proved here has `(N.choose k).minFac ∈ {3, 17, 19, 23, 29}`,
  which automatically rules out both `N.choose k = 0` and `N.choose k = 1` and guarantees that
  `(N.choose k).minFac` is the genuine least prime divisor of `N.choose k`. To remove even the
  need to trust `Nat.minFac`, the counterexample theorems `els93_conjecture2_counterexample`,
  `els93_conjecture1_counterexample`, and `els93_conjecture1_six_new_counterexamples` also state
  the condition directly as `∀ p : ℕ, p.Prime → p ∣ N.choose k → ...`.
- **The exceptional condition `p((N k)) > N/k`.** Since `k ≥ 2 > 0`, the rational inequality
  `p > N / k` is equivalent to the natural-number inequality `N < p * k`, and its negation
  `p ≤ N / k` is equivalent to `p * k ≤ N`. For Conjecture 2, we prove both the `ℕ` formulation
  (`els93_conjecture2_false`) and the `ℚ` formulation (`els93_conjecture2_false_rat`) written
  literally with `(N : ℚ) / (k : ℚ)`.
- **The threshold `N > 17⅛ k`.** The mixed fraction `17⅛ = 17 + 1/8 = 137/8 = 17.125` equals
  `959 / 56` exactly (confirmed in `classical_four_summary` by `8 * 959 = 137 * 56`), which is
  the ratio of the largest-ratio classical exception `(959, 56)`. Over `ℕ`, `N > (137/8) k` is
  strictly equivalent to `137 * k < 8 * N`; `els93_conjecture2_false_rat` also writes it directly
  as `(17 + 1 / 8 : ℚ) * (k : ℚ) < (N : ℚ)`.
- **Conjecture 1 ("the only exceptional `(N k)` with `p > 17` are these four").** Formalized as
  `els93_conjecture1_false` (negating the claim that every `(N, k)` with `2 ≤ k`, `2 * k ≤ N`,
  `17 < (N.choose k).minFac`, and `N < (N.choose k).minFac * k` is one of `(62, 6)`, `(959, 56)`,
  `(474, 66)`, `(284, 28)`), as the existential `els93_conjecture1_counterexample` (witnessed by
  `(57074, 22050)` with `minFac = 23`), and as `els93_conjecture1_six_new_counterexamples`
  covering all six new pairs.
- **Omissions and erratum on p. 222.** `missing_p17_le_12000` checks all eleven `p = 17`
  exceptional pairs with `k ≤ 12000` missing from [ELS93]'s list, and
  `misprint_13277_900_and_14277_900` verifies that the printed `(13277, 900)` has least prime
  factor `3` while `(14277, 900)` has least prime factor `17`.

## The theorems (exact statements)

### `Erdos1094/Lucas.lean`

```lean
theorem not_dvd_choose_iff_forall_digit_le {p : ℕ} (hp : p.Prime) :
    ∀ n k : ℕ, ¬ p ∣ n.choose k ↔ ∀ i : ℕ, k / p ^ i % p ≤ n / p ^ i % p

theorem not_dvd_choose_of_digitsLeFuel {fuel p n k : ℕ} (hp : p.Prime)
    (h : digitsLeFuel fuel p n k = true) : ¬ p ∣ n.choose k

theorem dvd_choose_of_hasCarryFuel {fuel p n k : ℕ} (hp : p.Prime)
    (h : hasCarryFuel fuel p n k = true) : p ∣ n.choose k

theorem minFac_choose_eq {fuel N k q : ℕ} (hq : q.Prime)
    (hdvd : hasCarryFuel fuel q N k = true)
    (hsmall : allSmallPrimesCarryFree fuel q N k = true) :
    (N.choose k).minFac = q
```

### `Erdos1094/Counterexamples.lean`

```lean
-- Sanity anchor: the four classical exceptional pairs of [ELS93] p. 222
theorem minFac_choose_62_6 : (Nat.choose 62 6).minFac = 19
theorem minFac_choose_959_56 : (Nat.choose 959 56).minFac = 19
theorem minFac_choose_474_66 : (Nat.choose 474 66).minFac = 23
theorem minFac_choose_284_28 : (Nat.choose 284 28).minFac = 29

theorem classical_four_summary :
    (Nat.choose 62 6).minFac = 19 ∧ 62 < 19 * 6 ∧
    (Nat.choose 959 56).minFac = 19 ∧ 959 < 19 * 56 ∧ 8 * 959 = 137 * 56 ∧
    (Nat.choose 474 66).minFac = 23 ∧ 474 < 23 * 66 ∧
    (Nat.choose 284 28).minFac = 29 ∧ 284 < 29 * 28

-- The six new exceptional pairs with least prime factor > 17
theorem minFac_choose_57074_22050 : (Nat.choose 57074 22050).minFac = 23
theorem minFac_choose_57075_22050 : (Nat.choose 57075 22050).minFac = 23
theorem minFac_choose_57077_22052 : (Nat.choose 57077 22052).minFac = 19
theorem minFac_choose_31152939_1772289 : (Nat.choose 31152939 1772289).minFac = 19
theorem minFac_choose_32634047_2143377 : (Nat.choose 32634047 2143377).minFac = 19
theorem minFac_choose_32634223_2143531 : (Nat.choose 32634223 2143531).minFac = 19

-- Disproof of [ELS93] Conjecture 2 (p. 222)
theorem els93_conjecture2_counterexample :
    ∃ N k : ℕ, 2 ≤ k ∧ 2 * k ≤ N ∧ 137 * k < 8 * N ∧
      ∀ p : ℕ, p.Prime → p ∣ N.choose k → N < p * k

theorem els93_conjecture2_false :
    ¬ (∀ N k : ℕ, 2 ≤ k → 2 * k ≤ N → 137 * k < 8 * N →
      (N.choose k).minFac * k ≤ N)

theorem els93_conjecture2_false_rat :
    ¬ (∀ N k : ℕ, 2 ≤ k → 2 * k ≤ N → (17 + 1 / 8 : ℚ) * (k : ℚ) < (N : ℚ) →
      ((N.choose k).minFac : ℚ) ≤ (N : ℚ) / (k : ℚ))

-- Disproof of [ELS93] Conjecture 1 (p. 222)
theorem els93_conjecture1_counterexample :
    ∃ N k : ℕ, 2 ≤ k ∧ 2 * k ≤ N ∧
      (N, k) ∉ ([(62, 6), (959, 56), (474, 66), (284, 28)] : List (ℕ × ℕ)) ∧
      17 < (N.choose k).minFac ∧ N < (N.choose k).minFac * k ∧
      ∀ p : ℕ, p.Prime → p ∣ N.choose k → 17 < p ∧ N < p * k

theorem els93_conjecture1_false :
    ¬ (∀ N k : ℕ, 2 ≤ k → 2 * k ≤ N →
      17 < (N.choose k).minFac → N < (N.choose k).minFac * k →
      (N, k) = (62, 6) ∨ (N, k) = (959, 56) ∨ (N, k) = (474, 66) ∨ (N, k) = (284, 28))

theorem els93_conjecture1_six_new_counterexamples :
    ∀ pair ∈ ([(57074, 22050), (57075, 22050), (57077, 22052),
               (31152939, 1772289), (32634047, 2143377), (32634223, 2143531)] : List (ℕ × ℕ)),
      2 ≤ pair.2 ∧ 2 * pair.2 ≤ pair.1 ∧
      pair ∉ ([(62, 6), (959, 56), (474, 66), (284, 28)] : List (ℕ × ℕ)) ∧
      17 < (pair.1.choose pair.2).minFac ∧
      pair.1 < (pair.1.choose pair.2).minFac * pair.2 ∧
      ∀ p : ℕ, p.Prime → p ∣ pair.1.choose pair.2 → 17 < p ∧ pair.1 < p * pair.2

-- Eleven missing p = 17, k ≤ 12000 exceptional pairs and the (13277, 900) misprint
theorem missing_p17_le_12000 :
    ∀ pair ∈ ([(23799, 3159), (36824, 3160), (23799, 3168),
               (56697, 3432), (56698, 3432), (56699, 3432),
               (56699, 3433), (56699, 3434), (56699, 3435),
               (56779, 3528), (71679, 4401)] : List (ℕ × ℕ)),
      2 ≤ pair.2 ∧ 2 * pair.2 ≤ pair.1 ∧ pair.2 ≤ 12000 ∧
      (pair.1.choose pair.2).minFac = 17 ∧ pair.1 < 17 * pair.2

theorem misprint_13277_900_and_14277_900 :
    (Nat.choose 13277 900).minFac = 3 ∧
    (Nat.choose 14277 900).minFac = 17 ∧ 14277 < 17 * 900
```

## Axioms

Unedited output of `lake env lean Axioms.lean` and the source grep checks from the clean build on
2026-11-27:

```
'Erdos1094.not_dvd_choose_iff_forall_digit_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.not_dvd_choose_of_digitsLeFuel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.dvd_choose_of_hasCarryFuel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_62_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_959_56' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_474_66' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_284_28' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.classical_four_summary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_57074_22050' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_57075_22050' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_57077_22052' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_31152939_1772289' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_32634047_2143377' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.minFac_choose_32634223_2143531' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.els93_conjecture2_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.els93_conjecture2_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.els93_conjecture2_false_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.els93_conjecture1_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.els93_conjecture1_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.els93_conjecture1_six_new_counterexamples' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.missing_p17_le_12000' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1094.misprint_13277_900_and_14277_900' depends on axioms: [propext, Classical.choice, Quot.sound]
grep: no sorry, axiom or admit in the Lean sources
grep: no native_decide in the Lean sources
```

Only Lean and Mathlib's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) appear.

## Files

| File | Content |
|---|---|
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lean `v4.36.0`, Mathlib `v4.36.0` (commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) |
| `Erdos1094.lean` | Library root |
| `Erdos1094/Lucas.lean` | Base-`p` digit dominance from Mathlib's Lucas's theorem and kernel-reducible `minFac_choose_eq` |
| `Erdos1094/Counterexamples.lean` | Classical anchor, six new `p > 17` pairs, Conjecture 1 & 2 disproofs, eleven missing `p = 17` pairs, and `(13277, 900)` erratum |
| `Axioms.lean` | `#print axioms` for every final theorem |
| `build.sh` | Cache fetch (if needed), `lake build`, `Axioms.lean`, and `sorry`/`axiom`/`native_decide` grep checks |

## Build

```bash
bash build.sh
```

Needs [elan](https://github.com/leanprover/elan) on `PATH`. On Windows, copy this folder to a Linux
filesystem (WSL, under `~`, not `/mnt/c`) before running `build.sh`.

Measured on 2026-11-27 from a fresh copy (`~/lean/erdos1094-clean`, `.lake/packages` symlinked to
a pre-cached Mathlib `v4.36.0`), AMD Ryzen 5 7600X (6 cores, 12 threads), WSL2 Ubuntu 24.04, Lean
`4.36.0` (commit `611c117bfaf7`), `LEAN_NUM_THREADS=4`:

- `Erdos1094.Lucas`: **8.4 s**
- `Erdos1094.Counterexamples`: **1.3 s**
- `Erdos1094`: **0.86 s**
- Total `lake build`: **16.617 s** wall time (`user` 6.506 s, `sys` 6.826 s).
