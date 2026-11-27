/-
Kernel-checked disproofs of Conjectures 1 and 2 of Erdős, Lacampagne, and Selfridge (1993), p. 222.

Reference:
  P. Erdős, C. B. Lacampagne, J. L. Selfridge,
  "Estimates of the least prime factor of a binomial coefficient",
  Math. Comp. 61 (1993), 215–224, Section 2, p. 222.

Verbatim from p. 222 (with `p(m)` the least prime factor of `m`, `k ≥ 2`, `N ≥ 2k`,
and `(N k)` called "exceptional" if `p((N k)) > N / k`):
  "The most unusual exception is for p = 29: p((284 28)) = 29. We have found one exception
   for p = 23: p((474 66)) = 23. There appear to be exactly two exceptions for p = 19:
   (62 6) and (959 56).
   We have two further conjectures:
   1. The only exceptional (N k) with p > 17 are these four.
   2. p((N k)) ≤ N/k if N > 17⅛ k."
-/
import Erdos1094.Lucas
import Mathlib.Tactic.NormNum

namespace Erdos1094

/-! ## Sanity anchor: the four classical exceptional pairs with `p > 17` -/

theorem minFac_choose_62_6 : (Nat.choose 62 6).minFac = 19 :=
  minFac_choose_eq (fuel := 16) (by decide) rfl (by decide)

theorem minFac_choose_959_56 : (Nat.choose 959 56).minFac = 19 :=
  minFac_choose_eq (fuel := 16) (by decide) rfl (by decide)

theorem minFac_choose_474_66 : (Nat.choose 474 66).minFac = 23 :=
  minFac_choose_eq (fuel := 16) (by decide) rfl (by decide)

theorem minFac_choose_284_28 : (Nat.choose 284 28).minFac = 29 :=
  minFac_choose_eq (fuel := 16) (by decide) rfl (by decide)

/-- Sanity anchor: all four classical pairs from [ELS93] p. 222 have the claimed least prime
factors (`19, 19, 23, 29`) and are exceptional (`N < p * k`).
Moreover, `(959, 56)` attains exact equality `959 / 56 = 17⅛` (`8 * 959 = 137 * 56`). -/
theorem classical_four_summary :
    (Nat.choose 62 6).minFac = 19 ∧ 62 < 19 * 6 ∧
    (Nat.choose 959 56).minFac = 19 ∧ 959 < 19 * 56 ∧ 8 * 959 = 137 * 56 ∧
    (Nat.choose 474 66).minFac = 23 ∧ 474 < 23 * 66 ∧
    (Nat.choose 284 28).minFac = 29 ∧ 284 < 29 * 28 := by
  refine ⟨minFac_choose_62_6, by decide,
          minFac_choose_959_56, by decide, by decide,
          minFac_choose_474_66, by decide,
          minFac_choose_284_28, by decide⟩

/-! ## The six new exceptional pairs with least prime factor `> 17` -/

theorem minFac_choose_57074_22050 : (Nat.choose 57074 22050).minFac = 23 :=
  minFac_choose_eq (fuel := 20) (by decide) rfl (by decide)

theorem minFac_choose_57075_22050 : (Nat.choose 57075 22050).minFac = 23 :=
  minFac_choose_eq (fuel := 20) (by decide) rfl (by decide)

theorem minFac_choose_57077_22052 : (Nat.choose 57077 22052).minFac = 19 :=
  minFac_choose_eq (fuel := 20) (by decide) rfl (by decide)

theorem minFac_choose_31152939_1772289 : (Nat.choose 31152939 1772289).minFac = 19 :=
  minFac_choose_eq (fuel := 26) (by decide) rfl (by decide)

theorem minFac_choose_32634047_2143377 : (Nat.choose 32634047 2143377).minFac = 19 :=
  minFac_choose_eq (fuel := 26) (by decide) rfl (by decide)

theorem minFac_choose_32634223_2143531 : (Nat.choose 32634223 2143531).minFac = 19 :=
  minFac_choose_eq (fuel := 26) (by decide) rfl (by decide)

/-! ## Disproof of [ELS93] Conjecture 2 (`p(C(N, k)) ≤ N / k` if `N > 17⅛ k`) -/

/-- Counterexample to [ELS93] Conjecture 2 (p. 222), stated without any custom definitions:
there exist `N, k` with `2 ≤ k`, `2k ≤ N`, `N > (137/8) k = 17⅛ k`, such that every prime divisor
`p` of `C(N, k)` satisfies `p > N / k`. Witness: `(N, k) = (31152939, 1772289)` with `minFac = 19`. -/
theorem els93_conjecture2_counterexample :
    ∃ N k : ℕ, 2 ≤ k ∧ 2 * k ≤ N ∧ 137 * k < 8 * N ∧
      ∀ p : ℕ, p.Prime → p ∣ N.choose k → N < p * k := by
  refine ⟨31152939, 1772289, by decide, by decide, by decide, ?_⟩
  intro p hp hdvd
  have h19 : 19 ≤ p := le_of_prime_dvd_of_minFac_eq minFac_choose_31152939_1772289 hp hdvd
  have hlt : 31152939 < 19 * 1772289 := by decide
  have hmul : 19 * 1772289 ≤ p * 1772289 := Nat.mul_le_mul_right 1772289 h19
  exact lt_of_lt_of_le hlt hmul

/-- Direct negation of [ELS93] Conjecture 2 in `ℕ`, using `Nat.minFac`. -/
theorem els93_conjecture2_false :
    ¬ (∀ N k : ℕ, 2 ≤ k → 2 * k ≤ N → 137 * k < 8 * N →
      (N.choose k).minFac * k ≤ N) := by
  intro h
  have hle := h 31152939 1772289 (by decide) (by decide) (by decide)
  rw [minFac_choose_31152939_1772289] at hle
  omega

/-- Direct negation of [ELS93] Conjecture 2 in `ℚ`, written with `17 + 1/8` and `N / k`. -/
theorem els93_conjecture2_false_rat :
    ¬ (∀ N k : ℕ, 2 ≤ k → 2 * k ≤ N → (17 + 1 / 8 : ℚ) * (k : ℚ) < (N : ℚ) →
      ((N.choose k).minFac : ℚ) ≤ (N : ℚ) / (k : ℚ)) := by
  intro h
  have hle := h 31152939 1772289 (by decide) (by decide) (by norm_num)
  rw [minFac_choose_31152939_1772289] at hle
  norm_num at hle

/-! ## Disproof of [ELS93] Conjecture 1 (the only exceptional `(N, k)` with `p > 17` are the four) -/

/-- Counterexample to [ELS93] Conjecture 1 (p. 222), stated without any custom definitions:
there exist `N, k` with `2 ≤ k`, `2k ≤ N`, `(N, k)` not among the four classical pairs
`(62, 6), (959, 56), (474, 66), (284, 28)`, whose least prime factor exceeds both `17` and `N / k`.
Witness: `(N, k) = (57074, 22050)` with `minFac = 23`. -/
theorem els93_conjecture1_counterexample :
    ∃ N k : ℕ, 2 ≤ k ∧ 2 * k ≤ N ∧
      (N, k) ∉ ([(62, 6), (959, 56), (474, 66), (284, 28)] : List (ℕ × ℕ)) ∧
      17 < (N.choose k).minFac ∧ N < (N.choose k).minFac * k ∧
      ∀ p : ℕ, p.Prime → p ∣ N.choose k → 17 < p ∧ N < p * k := by
  refine ⟨57074, 22050, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [minFac_choose_57074_22050]; decide
  · rw [minFac_choose_57074_22050]; decide
  · intro p hp hdvd
    have h23 : 23 ≤ p := le_of_prime_dvd_of_minFac_eq minFac_choose_57074_22050 hp hdvd
    exact ⟨by omega, lt_of_lt_of_le (by decide : 57074 < 23 * 22050) (Nat.mul_le_mul_right 22050 h23)⟩

/-- Direct negation of [ELS93] Conjecture 1 in `ℕ`, using `Nat.minFac`. -/
theorem els93_conjecture1_false :
    ¬ (∀ N k : ℕ, 2 ≤ k → 2 * k ≤ N →
      17 < (N.choose k).minFac → N < (N.choose k).minFac * k →
      (N, k) = (62, 6) ∨ (N, k) = (959, 56) ∨ (N, k) = (474, 66) ∨ (N, k) = (284, 28)) := by
  intro h
  have hmem := h 57074 22050 (by decide) (by decide)
    (by rw [minFac_choose_57074_22050]; decide)
    (by rw [minFac_choose_57074_22050]; decide)
  norm_num at hmem

/-- All six new pairs are counterexamples to [ELS93] Conjecture 1. -/
theorem els93_conjecture1_six_new_counterexamples :
    ∀ pair ∈ ([(57074, 22050), (57075, 22050), (57077, 22052),
               (31152939, 1772289), (32634047, 2143377), (32634223, 2143531)] : List (ℕ × ℕ)),
      2 ≤ pair.2 ∧ 2 * pair.2 ≤ pair.1 ∧
      pair ∉ ([(62, 6), (959, 56), (474, 66), (284, 28)] : List (ℕ × ℕ)) ∧
      17 < (pair.1.choose pair.2).minFac ∧
      pair.1 < (pair.1.choose pair.2).minFac * pair.2 ∧
      ∀ p : ℕ, p.Prime → p ∣ pair.1.choose pair.2 → 17 < p ∧ pair.1 < p * pair.2 := by
  intro pair hmem
  have aux : ∀ {N k q : ℕ}, (N.choose k).minFac = q →
      2 ≤ k → 2 * k ≤ N →
      (N, k) ∉ ([(62, 6), (959, 56), (474, 66), (284, 28)] : List (ℕ × ℕ)) →
      17 < q → N < q * k →
      2 ≤ k ∧ 2 * k ≤ N ∧
      (N, k) ∉ ([(62, 6), (959, 56), (474, 66), (284, 28)] : List (ℕ × ℕ)) ∧
      17 < (N.choose k).minFac ∧ N < (N.choose k).minFac * k ∧
      ∀ p : ℕ, p.Prime → p ∣ N.choose k → 17 < p ∧ N < p * k := by
    intro N k q hmin hk h2k hnot h17 hlt
    refine ⟨hk, h2k, hnot, hmin ▸ h17, hmin ▸ hlt, fun p hp hdvd => ?_⟩
    have hqp : q ≤ p := le_of_prime_dvd_of_minFac_eq hmin hp hdvd
    exact ⟨lt_of_lt_of_le h17 hqp, lt_of_lt_of_le hlt (Nat.mul_le_mul_right k hqp)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact aux minFac_choose_57074_22050 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact aux minFac_choose_57075_22050 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact aux minFac_choose_57077_22052 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact aux minFac_choose_31152939_1772289 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact aux minFac_choose_32634047_2143377 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact aux minFac_choose_32634223_2143531 (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Eleven missing `p = 17, k ≤ 12000` exceptional pairs and the `(13277, 900)` misprint -/

/-- The eleven exceptional pairs with `p = 17` and `k ≤ 12000` omitted from [ELS93] p. 222. -/
theorem missing_p17_le_12000 :
    ∀ pair ∈ ([(23799, 3159), (36824, 3160), (23799, 3168),
               (56697, 3432), (56698, 3432), (56699, 3432),
               (56699, 3433), (56699, 3434), (56699, 3435),
               (56779, 3528), (71679, 4401)] : List (ℕ × ℕ)),
      2 ≤ pair.2 ∧ 2 * pair.2 ≤ pair.1 ∧ pair.2 ≤ 12000 ∧
      (pair.1.choose pair.2).minFac = 17 ∧ pair.1 < 17 * pair.2 := by
  have hcheck :
      ([(23799, 3159), (36824, 3160), (23799, 3168),
        (56697, 3432), (56698, 3432), (56699, 3432),
        (56699, 3433), (56699, 3434), (56699, 3435),
        (56779, 3528), (71679, 4401)] : List (ℕ × ℕ)).all
        (fun pair =>
          decide (2 ≤ pair.2) && decide (2 * pair.2 ≤ pair.1) && decide (pair.2 ≤ 12000) &&
          hasCarryFuel 20 17 pair.1 pair.2 && allSmallPrimesCarryFree 20 17 pair.1 pair.2 &&
          decide (pair.1 < 17 * pair.2)) = true := by
    decide
  intro pair hmem
  have h := List.all_eq_true.1 hcheck pair hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, minFac_choose_eq (by decide) h4 h5, h6⟩

/-- Erratum in [ELS93] p. 222: `(13277, 900)` has least prime factor `3` (not `17`);
the intended exceptional pair is `(14277, 900)`, which has least prime factor `17`. -/
theorem misprint_13277_900_and_14277_900 :
    (Nat.choose 13277 900).minFac = 3 ∧
    (Nat.choose 14277 900).minFac = 17 ∧ 14277 < 17 * 900 :=
  ⟨minFac_choose_eq (fuel := 16) (by decide) rfl (by decide),
   minFac_choose_eq (fuel := 16) (by decide) rfl (by decide),
   by decide⟩

end Erdos1094
