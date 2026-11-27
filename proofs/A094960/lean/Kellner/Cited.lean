/-
Kellner's conjecture (A094960): the same theorems from the two cited inequalities in their
published form.

`AxlerLower` and `AxlerUpper` (the hypotheses used in `Kellner/Main.lean`) are weaker,
natural-number versions of two published statements of Christian Axler:

* lower bound: *New bounds for the prime counting function*, Integers 16 (2016), #A22
  (arXiv:1409.1780), Corollary 3.5 (p. 10; it is Corollary 3.6 in arXiv:1409.1780v7, where
  section 3 is numbered one higher);
* upper bound: *New estimates for some functions defined over primes*, Integers 18 (2018), #A52,
  Theorem 2 (p. 4, inequality (1.12)).

Here the two statements are written as in the papers, for real `x`, with
`π(x) = Nat.primeCounting ⌊x⌋₊`, and the weaker versions are deduced from them in Lean.
The two statements themselves are still hypotheses: they are NOT proved here.

History of the upper bound (all on 2026-11-26):

1. First it was the last statement of Corollary 3.4 of the 2016 paper (`x ≥ 5.43`). That statement
   is false as printed and was corrected by Axler in 2018 (to `x ≥ 2634800823`). A false
   hypothesis proves everything, so it was removed.
   See `../reviews/2026-11-26-gemini-4-neon-axler-match.md`.
2. Then it was Theorem 1.3 of the 2016 paper. That statement is true, but its published proof has
   a mistake, as Axler himself writes in the 2018 paper (#A52, Remark on p. 9): "there was a
   mistake in the first part of the proof … In the current paper, we filled the gap by proving
   Theorem 2." See `../reviews/2026-11-26-gemini-4-neon-rereview.md`.
3. Now it is that Theorem 2, the statement whose proof is the current one.
-/
import Kellner.Bernoulli

namespace Kellner

/-- Axler 2016 (#A22), Corollary 3.5, last column of the table (`a = b = c = d = 0`,
`x₀ = 468049`): "If `x ≥ x₀`, then `π(x) > x / (log x - 1 - 1 / log x)`". -/
def AxlerCor35 : Prop :=
  ∀ x : ℝ, 468049 ≤ x →
    x / (Real.log x - 1 - 1 / Real.log x) < (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- Axler 2018 (#A52), Theorem 2 (inequality (1.12), p. 4):
"For every `x ≥ 49`, we have `π(x) < x / (log x - 1 - 1/log x - 3.15/log^2 x - 12.85/log^3 x
- 71.3/log^4 x - 463.2275/log^5 x - 4585/log^6 x)`". -/
def Axler18Thm2 : Prop :=
  ∀ x : ℝ, 49 ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / (Real.log x - 1 - 1 / Real.log x - 3.15 / Real.log x ^ 2 - 12.85 / Real.log x ^ 3
        - 71.3 / Real.log x ^ 4 - 463.2275 / Real.log x ^ 5 - 4585 / Real.log x ^ 6)

theorem axlerLower_of_cor35 (h : AxlerCor35) : AxlerLower := by
  intro m hm
  have hx : (468049 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 := h m hx
  rw [Nat.floor_natCast] at h1
  have hL := log_ge_thirteen hx
  have hx0 : (0 : ℝ) < m := by linarith
  have hinv0 : 0 ≤ 1 / Real.log m := one_div_nonneg.2 (by linarith)
  have hinv1 : 1 / Real.log m ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hpos : 0 < Real.log m - 1 - 1 / Real.log m := by linarith
  have hle : (m : ℝ) / (Real.log m - 1) ≤ m / (Real.log m - 1 - 1 / Real.log m) := by
    rw [div_le_div_iff₀ (by linarith) hpos]
    exact mul_le_mul_of_nonneg_left (by linarith) hx0.le
  linarith

/-- For `a ≥ 0`, `L ≥ 13` and any `k`: `a / L^k ≤ a / 13^k`. -/
theorem term_le {a L : ℝ} (ha : 0 ≤ a) (hL : 13 ≤ L) (k : ℕ) : a / L ^ k ≤ a / 13 ^ k :=
  div_le_div_of_nonneg_left ha (by positivity) (pow_le_pow_left₀ (by norm_num) hL k)

/-- The six correction terms of Theorem 2 add up to at most `0.107` when `ln x ≥ 13`
(their value at `13` is `204859303/1930723600 = 0.1061049…`). -/
theorem tail_le {L : ℝ} (hL : 13 ≤ L) :
    1 / L + 3.15 / L ^ 2 + 12.85 / L ^ 3 + 71.3 / L ^ 4 + 463.2275 / L ^ 5
      + 4585 / L ^ 6 ≤ 0.107 := by
  have h1 := term_le (a := 1) (by norm_num) hL 1
  have h2 := term_le (a := 3.15) (by norm_num) hL 2
  have h3 := term_le (a := 12.85) (by norm_num) hL 3
  have h4 := term_le (a := 71.3) (by norm_num) hL 4
  have h5 := term_le (a := 463.2275) (by norm_num) hL 5
  have h6 := term_le (a := 4585) (by norm_num) hL 6
  simp only [pow_one] at h1
  have hnum : (1 : ℝ) / 13 + 3.15 / 13 ^ 2 + 12.85 / 13 ^ 3 + 71.3 / 13 ^ 4 + 463.2275 / 13 ^ 5
      + 4585 / 13 ^ 6 ≤ 0.107 := by norm_num
  linarith

theorem axlerUpper_of_thm2 (h : Axler18Thm2) : AxlerUpper := by
  intro m hm
  have hx : (468049 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL := log_ge_thirteen hx
  have hx0 : (0 : ℝ) < m := by linarith
  have h1 := h m (by linarith)
  rw [Nat.floor_natCast] at h1
  have ht := tail_le hL
  have hB0 : 0 < Real.log m - 1.107 := by linarith
  have hle : (m : ℝ) / (Real.log m - 1 - 1 / Real.log m - 3.15 / Real.log m ^ 2
        - 12.85 / Real.log m ^ 3 - 71.3 / Real.log m ^ 4 - 463.2275 / Real.log m ^ 5
        - 4585 / Real.log m ^ 6) ≤ m / (Real.log m - 1.107) := by
    rw [div_le_div_iff₀ (by linarith) hB0]
    exact mul_le_mul_of_nonneg_left (by linarith) hx0.le
  linarith

/-- **Theorem 1 (a), Kellner's conjecture**, from Axler's two statements as published. -/
theorem kellner_of_axler (h35 : AxlerCor35) (h2 : Axler18Thm2) :
    ∀ n : ℕ, 193 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum :=
  kellner (axlerLower_of_cor35 h35) (axlerUpper_of_thm2 h2)

/-- **Theorem 1 (d)**, from the same two statements: for every `n ≥ 193` there is a prime
`p > (n + 1) / √n` with `s_p(n) ≥ p`. This contains both inequalities of Kellner's Conjecture 1
(J. Number Theory 179 (2017), p. 2): the greatest such prime `P` satisfies `P > √n` and
`(n + 1) / P < √n`. -/
theorem kellner_partD_of_axler (h35 : AxlerCor35) (h2 : Axler18Thm2) :
    ∀ n : ℕ, 193 ≤ n →
      ∃ p : ℕ, p.Prime ∧ (n + 1) ^ 2 < p ^ 2 * n ∧ p ≤ (Nat.digits p n).sum :=
  kellner_partD (axlerLower_of_cor35 h35) (axlerUpper_of_thm2 h2)

/-- **Corollary A (A094960)**, from Axler's two statements as published. -/
theorem A094960_complete_of_axler (h35 : AxlerCor35) (h2 : Axler18Thm2) :
    ∀ k : ℕ, 1 ≤ k →
      ((∀ i : ℕ, ∃ z : ℤ,
          (Polynomial.derivative (Polynomial.bernoulli k)).coeff i = (z : ℚ)) ↔
        k ∈ [1, 2, 4, 6, 10, 12, 28, 30, 36, 60]) :=
  A094960_complete (axlerLower_of_cor35 h35) (axlerUpper_of_thm2 h2)

end Kellner
