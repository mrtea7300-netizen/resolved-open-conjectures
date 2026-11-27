/-
Kellner's conjecture (A094960): the finite check, a second time, with `native_decide`.

NOT USED by the final theorems (`Kellner/Main.lean` imports `Kellner/FiniteKernel.lean`, which
is checked by the kernel). This file is an independent cross-check with different, more direct
code: it uses Mathlib's `Nat.Prime` decision procedure and loops over every `F` and every `n`.

* for `1338 ≤ F < 468049` a Boolean function checks the window criterion (6.1) with `r = 2`
  for `F`, which by Proposition 6 settles all `n` with `⌊√n⌋ = F` at once;
* for `n < 1338 ^ 2` a Boolean function searches a witness prime for each `n`.

Both functions are proved sound here; they are evaluated with `native_decide`, so the
`finite_*` theorems of this file depend on one extra axiom each (trust in the Lean compiler).
-/
import Kellner.Basic

namespace Kellner.Native

open Finset

/-! ## The window check for one `F` -/

/-- One step of the prime count: from the count for `(F, F + s]` to the count for
`(F, F + s + 1]`. -/
def cntStep (F s cnt : ℕ) : ℕ := if (F + s + 1).Prime then cnt + 1 else cnt

/-- Scan `s = 1, 2, 3, ...` (at most `fuel` steps), keeping in `cnt` the number of primes in
`(F, F + s]`. Answer `true` as soon as `K(F, s) + 4 ≤ cnt`. -/
def scan (F : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, s, cnt =>
    if K F (s + 1) + 4 ≤ cntStep F s cnt then true
    else scan F fuel (s + 1) (cntStep F s cnt)

theorem cntStep_eq (F s cnt : ℕ) (hcnt : cnt = ((Ioc F (F + s)).filter Nat.Prime).card) :
    cntStep F s cnt = ((Ioc F (F + (s + 1))).filter Nat.Prime).card := by
  have e : Ioc F (F + (s + 1)) = insert (F + s + 1) (Ioc F (F + s)) := by
    ext x
    simp only [mem_Ioc, mem_insert]
    omega
  unfold cntStep
  rw [e, Finset.filter_insert]
  split_ifs with hp
  · rw [Finset.card_insert_of_notMem (by simp), hcnt]
  · exact hcnt

/-- Soundness of `scan`. -/
theorem scan_sound (F : ℕ) : ∀ fuel s cnt : ℕ,
    cnt = ((Ioc F (F + s)).filter Nat.Prime).card → scan F fuel s cnt = true → WindowOK F := by
  intro fuel
  induction fuel with
  | zero =>
    intro s cnt _ h
    simp [scan] at h
  | succ fuel ih =>
    intro s cnt hcnt h
    have hstep := cntStep_eq F s cnt hcnt
    rw [scan] at h
    split_ifs at h with hK
    · exact ⟨s + 1, by rw [← hstep]; exact hK⟩
    · exact ih (s + 1) _ hstep h

/-- The check for one `F`. -/
def checkF (F : ℕ) : Bool := scan F (4 * Nat.sqrt F + 200) 0 0

theorem checkF_sound {F : ℕ} (h : checkF F = true) : WindowOK F :=
  scan_sound F _ 0 0 (by simp) h

/-! ## Brute force for one `n` -/

/-- `p` is a witness for part (c) (hence for (a) and (b)) at `n`. -/
def witC (n p : ℕ) : Bool :=
  decide (p ≤ n / p + n % p) && decide (n < p ^ 2) && !decide (p ∣ (n + 1) * (n + 2)) &&
    decide p.Prime

/-- `p` is a witness for part (d) at `n`. -/
def witD (n p : ℕ) : Bool :=
  decide (p ≤ n / p + n % p) && decide ((n + 1) ^ 2 < p ^ 2 * n) && decide p.Prime

/-- Search a witness for part (c) among the 200 integers above `⌊√n⌋`. -/
def searchC (n : ℕ) : Bool := (List.range' (Nat.sqrt n + 1) 200).any (witC n)

/-- Search a witness for part (d) among the 200 integers above `⌊√n⌋`. -/
def searchD (n : ℕ) : Bool := (List.range' (Nat.sqrt n + 1) 200).any (witD n)

theorem searchC_sound {n : ℕ} (h : searchC n = true) :
    ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧ ¬ p ∣ (n + 1) * (n + 2) := by
  obtain ⟨p, -, hp⟩ := List.any_eq_true.1 h
  simp only [witC, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hp
  obtain ⟨⟨⟨hds, hsq⟩, hnd⟩, hpp⟩ := hp
  exact ⟨p, hpp, hsq, by rw [digits_sum_of_lt_sq hpp.two_le hsq]; exact hds, hnd⟩

theorem searchD_sound {n : ℕ} (h : searchD n = true) :
    ∃ p : ℕ, p.Prime ∧ (n + 1) ^ 2 < p ^ 2 * n ∧ p ≤ (Nat.digits p n).sum := by
  obtain ⟨p, -, hp⟩ := List.any_eq_true.1 h
  simp only [witD, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hds, hsq⟩, hpp⟩ := hp
  exact ⟨p, hpp, hsq,
    by rw [digits_sum_of_lt_sq hpp.two_le (lt_sq_of_succ_sq_lt hsq)]; exact hds⟩

/-! ## The exceptional set `E₀` (sanity check of the statement, and sharpness of 192) -/

/-- Is there a prime `p > √n` with `s_p(n) ≥ p`? (Such a prime is `≤ n`.) -/
def hasWitA (n : ℕ) : Bool :=
  (List.range (n + 1)).any
    (fun p => decide (p ≤ n / p + n % p) && decide (n < p ^ 2) && decide p.Prime)

theorem hasWitA_iff (n : ℕ) :
    hasWitA n = true ↔ ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum := by
  unfold hasWitA
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, -, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨hds, hsq⟩, hpp⟩ := hp
    exact ⟨p, hpp, hsq, by rw [digits_sum_of_lt_sq hpp.two_le hsq]; exact hds⟩
  · rintro ⟨p, hpp, hsq, hds⟩
    rw [digits_sum_of_lt_sq hpp.two_le hsq] at hds
    refine ⟨p, ?_, ?_⟩
    · rw [List.mem_range]
      have h1 := Nat.div_add_mod n p
      have h2 : n / p ≤ p * (n / p) := Nat.le_mul_of_pos_left _ hpp.pos
      generalize n / p = a at *
      generalize n % p = b at *
      omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hds, hsq⟩, hpp⟩

/-- The set `E₀` of the draft (26 numbers). -/
def E0 : List ℕ :=
  [1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80, 174,
    190, 191, 192]

/-! ## The three evaluations -/

/-- (computation) Among `1 ≤ n ≤ 192`, the `n` without a witness are exactly those in `E₀`. -/
theorem finite_E0 :
    (List.range' 1 192).all (fun n => hasWitA n == !(E0.contains n)) = true := by
  native_decide

/-- (computation) The window criterion holds for every `F` with `1338 ≤ F < 468049`. -/
theorem finite_window : (List.range' 1338 (468049 - 1338)).all checkF = true := by
  native_decide

/-- (computation) A witness for part (c) exists for every `n` with `1081 ≤ n < 1338 ^ 2`. -/
theorem finite_smallC : (List.range' 1081 (1338 ^ 2 - 1081)).all searchC = true := by
  native_decide

/-- (computation) A witness for part (d) exists for every `n` with `193 ≤ n < 1338 ^ 2`. -/
theorem finite_smallD : (List.range' 193 (1338 ^ 2 - 193)).all searchD = true := by
  native_decide

/-! ## What the evaluations say -/

theorem windowOK_of_lt {F : ℕ} (h1 : 1338 ≤ F) (h2 : F < 468049) : WindowOK F := by
  have h := List.all_eq_true.1 finite_window F (by rw [List.mem_range'_1]; omega)
  exact checkF_sound h

theorem partC_small {n : ℕ} (h1 : 1081 ≤ n) (h2 : n < 1338 ^ 2) :
    ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧ ¬ p ∣ (n + 1) * (n + 2) :=
  searchC_sound (List.all_eq_true.1 finite_smallC n (by rw [List.mem_range'_1]; omega))

theorem partD_small {n : ℕ} (h1 : 193 ≤ n) (h2 : n < 1338 ^ 2) :
    ∃ p : ℕ, p.Prime ∧ (n + 1) ^ 2 < p ^ 2 * n ∧ p ≤ (Nat.digits p n).sum :=
  searchD_sound (List.all_eq_true.1 finite_smallD n (by rw [List.mem_range'_1]; omega))

/-- For `1 ≤ n ≤ 192`: there is a prime `p > √n` with `s_p(n) ≥ p` if and only if `n ∉ E₀`. -/
theorem exceptions_iff {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 192) :
    (∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum) ↔ n ∉ E0 := by
  have h := List.all_eq_true.1 finite_E0 n (by rw [List.mem_range'_1]; omega)
  rw [← hasWitA_iff]
  cases hw : hasWitA n <;> simp_all

end Kellner.Native
