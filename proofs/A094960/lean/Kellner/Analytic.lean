/-
Kellner's conjecture (A094960): the analytic part (Proposition 7 of `../proof.md`),
for `F ≥ 468049`.

The two explicit bounds for `π(x)` are NOT proved here and are not in Mathlib. They enter only
as the hypotheses `AxlerLower` and `AxlerUpper` of the theorems below; there is no `axiom`.

Differences from the draft (the draft works from `F ≥ 60184` and uses the lower bound from
`x ≥ 5393`): here the lower bound is used only for arguments `≥ 468049`, where it is exactly
Axler's Corollary 3.5, and the constants of the estimate are recomputed for `ln F ≥ 13`.
-/
import Kellner.Basic

namespace Kellner

/-- Lower bound for `π` on the natural numbers `m ≥ 468049`:
`m / (ln m - 1) ≤ π(m)`.

Source: C. Axler, *New bounds for the prime counting function*, Integers 16 (2016), #A22,
Corollary 3.5 (`π(x) > x / (ln x - 1 - 1 / ln x)` for every real `x ≥ 468049`), which is stronger;
the deduction is `axlerLower_of_cor35` in `Kellner/Cited.lean`. -/
def AxlerLower : Prop :=
  ∀ m : ℕ, 468049 ≤ m → (m : ℝ) / (Real.log m - 1) ≤ Nat.primeCounting m

/-- Upper bound for `π` on the natural numbers `m ≥ 468049`:
`π(m) ≤ m / (ln m - 1.107)`.

Source: C. Axler, *New estimates for some functions defined over primes*, Integers 18 (2018),
#A52, Theorem 2 (for every real `x ≥ 49`,
`π(x) < x / (ln x - 1 - 1/ln x - 3.15/ln^2 x - 12.85/ln^3 x - 71.3/ln^4 x - 463.2275/ln^5 x
- 4585/ln^6 x)`), together with the fact that the six correction terms add up to less than
`0.107` when `ln x ≥ 13`; the deduction is `axlerUpper_of_thm2` in `Kellner/Cited.lean`.

History (2026-11-26): this hypothesis was first stated from `m ≥ 60184` and attributed to the
last statement of Corollary 3.4 of Axler's 2016 paper, which is false as printed (corrigendum of
2018); then to Theorem 1.3 of the 2016 paper, whose proof has a gap that Axler closes in the 2018
paper by proving Theorem 2. Both were found by Gemini 4 Neon reviews (`../reviews/`). The
hypothesis is only used for `m ≥ 468049` (in `prop7`), so the threshold was raised to that value. -/
def AxlerUpper : Prop :=
  ∀ m : ℕ, 468049 ≤ m → (Nat.primeCounting m : ℝ) ≤ m / (Real.log m - 1.107)

/-! ## Numerical facts about the logarithm -/

theorem exp_thirteen_lt : Real.exp 13 < 468049 := by
  have h : Real.exp 13 = Real.exp 1 ^ 13 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  calc Real.exp 1 ^ 13 < (2.7182818286 : ℝ) ^ 13 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    _ < 468049 := by norm_num

/-- `ln x ≥ 13` for `x ≥ 468049`. -/
theorem log_ge_thirteen {x : ℝ} (hx : 468049 ≤ x) : 13 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [exp_thirteen_lt]

/-- `6 (ln x)^2 + ln x ≤ 0.0619 x` for `x ≥ 468049`. (From `ln x = 8 ln x^(1/8) ≤ 8 x^(1/8) - 8`.) -/
theorem log_sq_bound {x : ℝ} (hx : 468049 ≤ x) :
    6 * Real.log x ^ 2 + Real.log x ≤ 0.0619 * x := by
  have hx0 : 0 < x := by linarith
  have hL13 := log_ge_thirteen hx
  have hy0 : 0 < x ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hx0 _
  have hyx : (x ^ ((1 : ℝ) / 8)) ^ 8 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hLy : Real.log x ≤ 8 * x ^ ((1 : ℝ) / 8) - 8 := by
    have := Real.log_le_sub_one_of_pos hy0
    rw [Real.log_rpow hx0] at this
    linarith
  generalize x ^ ((1 : ℝ) / 8) = y at *
  generalize Real.log x = L at *
  have hy5 : 5.1 < y := by
    by_contra hcon
    have h : y ^ 8 ≤ (5.1 : ℝ) ^ 8 := pow_le_pow_left₀ hy0.le (not_lt.mp hcon) 8
    norm_num at h
    linarith
  have h1 : L ^ 2 ≤ 64 * y ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 8 * y - L by linarith) (show 0 ≤ 8 * y + L by linarith)]
  have h2 : (17596 : ℝ) ≤ y ^ 6 := by
    have h : (5.1 : ℝ) ^ 6 ≤ y ^ 6 := pow_le_pow_left₀ (by norm_num) hy5.le 6
    norm_num at h
    linarith
  have h3 : y ≤ y ^ 2 := by
    nlinarith [mul_nonneg hy0.le (show 0 ≤ y - 1 by linarith)]
  have h4 : 17596 * y ^ 2 ≤ y ^ 6 * y ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
  have h5 : y ^ 8 = y ^ 6 * y ^ 2 := by ring
  have h6 : 0 ≤ y ^ 2 := sq_nonneg y
  rw [← hyx, h5]
  linarith

/-! ## The real inequality behind Proposition 7 -/

/-- If `x ≥ 468049` and `s = ⌊x / (2 ln x)⌋`, then
`s^2 / x + 6 + x / (ln x - 1.107) ≤ (x + s) / (ln (x + s) - 1)`. -/
theorem real_core {x s : ℝ} (hx : 468049 ≤ x) (hs0 : 0 ≤ s)
    (hs1 : s ≤ x / (2 * Real.log x)) (hs2 : x / (2 * Real.log x) < s + 1) :
    s ^ 2 / x + 6 + x / (Real.log x - 1.107) ≤ (x + s) / (Real.log (x + s) - 1) := by
  have hx0 : 0 < x := by linarith
  have hL13 := log_ge_thirteen hx
  have hkey := log_sq_bound hx
  -- `t = s / x`
  obtain ⟨t, hts⟩ : ∃ t : ℝ, t * x = s := ⟨s / x, by field_simp⟩
  subst hts
  have ht0 : 0 ≤ t := nonneg_of_mul_nonneg_left hs0 hx0
  have hlog : Real.log (x + t * x) ≤ Real.log x + t := by
    have e : x + t * x = x * (1 + t) := by ring
    rw [e, Real.log_mul hx0.ne' (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + t by positivity)
    linarith
  have hlog' : Real.log x ≤ Real.log (x + t * x) := Real.log_le_log hx0 (by linarith)
  generalize Real.log (x + t * x) = M at *
  generalize Real.log x = L at *
  have hL0 : 0 < L := by linarith
  have h1 : 2 * L * (t * x) ≤ x := by
    rw [le_div_iff₀ (by positivity)] at hs1
    linarith
  have h2 : x < 2 * L * (t * x + 1) := by
    rw [div_lt_iff₀ (by positivity)] at hs2
    linarith
  have htL : 2 * L * t ≤ 1 := by
    have h : 2 * L * t * x ≤ 1 * x := by linarith
    exact le_of_mul_le_mul_right h hx0
  have ht26 : 26 * t ≤ 1 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 hL13)]
  have htLx : x / 2 - L < t * L * x := by linarith
  have hA0 : 0 < L + t - 1 := by linarith
  have hB0 : 0 < L - 1.107 := by linarith
  have hM0 : 0 < M - 1 := by linarith
  -- the main inequality, with `ln (x + s)` replaced by `L + t`
  have hcore : (t * x) ^ 2 / x + 6 + x / (L - 1.107) ≤ (x + t * x) / (L + t - 1) := by
    have e1 : (t * x) ^ 2 / x = t ^ 2 * x := by field_simp
    rw [e1, add_div' _ _ _ hB0.ne', div_le_div_iff₀ hB0 hA0]
    have hAB : (L + t - 1) * (L - 1.107) ≤ L * L :=
      mul_le_mul (by linarith) (by linarith) hB0.le hL0.le
    have htL2 : (t * L) ^ 2 ≤ 1 / 4 := by
      have h0 : 0 ≤ t * L := by positivity
      have h1 : t * L ≤ 1 / 2 := by linarith
      nlinarith
    have hq1 : t ^ 2 * x * ((L + t - 1) * (L - 1.107)) ≤ x / 4 := by
      have ha : t ^ 2 * x * ((L + t - 1) * (L - 1.107)) ≤ t ^ 2 * x * (L * L) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
      have hb : t ^ 2 * x * (L * L) = (t * L) ^ 2 * x := by ring
      have hc : (t * L) ^ 2 * x ≤ 1 / 4 * x := mul_le_mul_of_nonneg_right htL2 hx0.le
      linarith
    have hq3 : 26 * (t * x) ≤ x := by
      have h : 26 * t * x ≤ 1 * x := mul_le_mul_of_nonneg_right ht26 hx0.le
      linarith
    have hexp : ((t ^ 2 * x + 6) * (L - 1.107) + x) * (L + t - 1) =
        t ^ 2 * x * ((L + t - 1) * (L - 1.107)) + 6 * ((L + t - 1) * (L - 1.107)) +
          x * (L + t - 1) := by ring
    have hid : (x + t * x) * (L - 1.107) =
        x * (L + t - 1) + t * L * x - 2.107 * (t * x) - 0.107 * x := by ring
    rw [hexp, hid]
    linarith
  have hmono : (x + t * x) / (L + t - 1) ≤ (x + t * x) / (M - 1) := by
    rw [div_le_div_iff₀ hA0 hM0]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact le_trans hcore hmono

/-! ## Proposition 7 -/

/-- `K(F, S) ≤ S^2 / F + 2`. -/
theorem K_cast_le {F : ℕ} (hF : 0 < F) (S : ℕ) : (K F S : ℝ) ≤ (S : ℝ) ^ 2 / F + 2 := by
  have hx0 : (0 : ℝ) < F := by exact_mod_cast hF
  have hs0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have h : ((K F S : ℕ) : ℝ) ≤ ((S ^ 2 + 2 * F : ℕ) : ℝ) / ((F + S : ℕ) : ℝ) := by
    unfold K
    exact Nat.cast_div_le
  refine le_trans h ?_
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have e : ((S : ℝ) ^ 2 / F + 2) * (F + S) =
      (S : ℝ) ^ 2 + 2 * F + ((S : ℝ) ^ 3 / F + 2 * S) := by
    field_simp
  rw [e]
  have : 0 ≤ (S : ℝ) ^ 3 / F + 2 * S := by positivity
  linarith

/-- **Proposition 7**, for `F ≥ 468049`. With `S = ⌊F / (2 ln F)⌋`, the interval `(F, F + S]`
contains at least `K(F, S) + 4` primes: `π(F + S) - π(F) ≥ K(F, S) + 4`. -/
theorem prop7 (hLow : AxlerLower) (hUp : AxlerUpper) {F : ℕ} (hF : 468049 ≤ F) :
    ∃ S : ℕ, K F S + 4 + Nat.primeCounting F ≤ Nat.primeCounting (F + S) := by
  have hx : (468049 : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF
  have hx0 : (0 : ℝ) < F := by linarith
  have hL13 := log_ge_thirteen hx
  refine ⟨⌊(F : ℝ) / (2 * Real.log F)⌋₊, ?_⟩
  generalize hS : ⌊(F : ℝ) / (2 * Real.log F)⌋₊ = S
  have hnn : 0 ≤ (F : ℝ) / (2 * Real.log F) := div_nonneg hx0.le (by linarith)
  have hs1 : (S : ℝ) ≤ F / (2 * Real.log F) := by rw [← hS]; exact Nat.floor_le hnn
  have hs2 : (F : ℝ) / (2 * Real.log F) < S + 1 := by rw [← hS]; exact Nat.lt_floor_add_one _
  have hcore := real_core hx (Nat.cast_nonneg S) hs1 hs2
  have hlow := hLow (F + S) (by omega)
  have hup := hUp F (by omega)
  rw [Nat.cast_add] at hlow
  have hK := K_cast_le (F := F) (by omega) S
  have h : ((K F S + 4 + Nat.primeCounting F : ℕ) : ℝ) ≤ (Nat.primeCounting (F + S) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h

end Kellner
