/-
Kellner's conjecture (A094960): the final statements (Theorem 1 of `../proof.md`).

`s_p(n)` is `(Nat.digits p n).sum`; "`p > √n`" is `n < p ^ 2`; "`p > (n + 1) / √n`" is
`(n + 1) ^ 2 < p ^ 2 * n`.

Every theorem that needs the explicit bounds for `π(x)` takes them as the two hypotheses
`AxlerLower` and `AxlerUpper` (defined in `Kellner/Analytic.lean`). They are not proved here.
The finite part (`n < 468049 ^ 2`) is `Kellner/FiniteKernel.lean`, checked by the kernel.
-/
import Kellner.FiniteKernel
import Kellner.Analytic

namespace Kellner

/-- `⌊√n⌋ ^ 2 ≤ n ≤ ⌊√n⌋ ^ 2 + 2 ⌊√n⌋`. -/
theorem sqrt_bounds (n : ℕ) : n.sqrt ^ 2 ≤ n ∧ n ≤ n.sqrt ^ 2 + 2 * n.sqrt := by
  have h1 := Nat.sqrt_le' n
  have h2 := Nat.lt_succ_sqrt' n
  generalize n.sqrt = s at *
  refine ⟨h1, ?_⟩
  have : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
  rw [Nat.succ_eq_add_one, this] at h2
  omega

/-- The window criterion (6.1) with `r = 2` holds for every `F ≥ 1361`:
by a kernel computation below `468049`, by Proposition 7 from there on. -/
theorem windowOK_of_ge (hLow : AxlerLower) (hUp : AxlerUpper) {F : ℕ} (hF : 1361 ≤ F) :
    WindowOK F := by
  by_cases h : F < 468049
  · exact windowOK_of_lt hF h
  · obtain ⟨S, hS⟩ := prop7 hLow hUp (not_lt.mp h)
    exact windowOK_of_primeCounting hS

/-- **Theorem 1 (c).** For every `n ≥ 1081` there is a prime `p > √n` with `s_p(n) ≥ p` that does
not divide `(n + 1)(n + 2)`. -/
theorem kellner_partC (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ n : ℕ, 1081 ≤ n →
      ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧ ¬ p ∣ (n + 1) * (n + 2) := by
  intro n hn
  by_cases h : n < 1361 ^ 2
  · exact partC_small hn h
  · obtain ⟨h1, h2⟩ := sqrt_bounds n
    have hF : 1361 ≤ n.sqrt := Nat.le_sqrt'.2 (not_lt.mp h)
    exact window_partC (by omega) h1 h2 (windowOK_of_ge hLow hUp hF)

/-- **Theorem 1 (d).** For every `n ≥ 193` there is a prime `p > (n + 1) / √n` with
`s_p(n) ≥ p`. -/
theorem kellner_partD (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ n : ℕ, 193 ≤ n →
      ∃ p : ℕ, p.Prime ∧ (n + 1) ^ 2 < p ^ 2 * n ∧ p ≤ (Nat.digits p n).sum := by
  intro n hn
  by_cases h : n < 1361 ^ 2
  · exact partD_small hn h
  · obtain ⟨h1, h2⟩ := sqrt_bounds n
    have hF : 1361 ≤ n.sqrt := Nat.le_sqrt'.2 (not_lt.mp h)
    exact window_partD (by omega) h1 h2 (windowOK_of_ge hLow hUp hF)

/-- **Theorem 1 (a): Kellner's conjecture.** For every `n > 192` there is a prime `p > √n` with
`s_p(n) ≥ p`. -/
theorem kellner (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ n : ℕ, 193 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum := by
  intro n hn
  obtain ⟨p, hpp, hsq, hds⟩ := kellner_partD hLow hUp n hn
  exact ⟨p, hpp, lt_sq_of_succ_sq_lt hsq, hds⟩

/-- **Theorem 1 (b).** For every `n ≥ 1081` there is a prime `p > √n` with `s_p(n) ≥ p` that does
not divide `n + 1`. -/
theorem kellner_partB (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ n : ℕ, 1081 ≤ n →
      ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧ ¬ p ∣ n + 1 := by
  intro n hn
  obtain ⟨p, hpp, hsq, hds, hnd⟩ := kellner_partC hLow hUp n hn
  exact ⟨p, hpp, hsq, hds, fun h => hnd (Dvd.dvd.mul_right h _)⟩

/-- **Sharpness.** There is no such prime for `n = 192`. -/
theorem kellner_sharp :
    ¬ ∃ p : ℕ, p.Prime ∧ 192 < p ^ 2 ∧ p ≤ (Nat.digits p 192).sum := by
  intro h
  exact (exceptions_iff (n := 192) (by norm_num) le_rfl).1 h (by decide)

/-- **The exceptional set.** For `1 ≤ n ≤ 192`, a prime `p > √n` with `s_p(n) ≥ p` exists if and
only if `n` is not one of the 26 numbers of `E₀`. -/
theorem kellner_exceptions :
    ∀ n : ℕ, 1 ≤ n → n ≤ 192 →
      ((∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum) ↔
        n ∉ [1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80,
          174, 190, 191, 192]) :=
  fun _ h1 h2 => exceptions_iff h1 h2

end Kellner
