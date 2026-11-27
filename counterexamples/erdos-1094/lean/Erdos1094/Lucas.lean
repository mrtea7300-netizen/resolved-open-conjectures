/-
Lucas-theorem digit-dominance criterion for the least prime factor of a binomial coefficient.

For a prime `p`, `p ∤ Nat.choose n k` if and only if every base-`p` digit of `k` is at most the
corresponding base-`p` digit of `n`. Structurally recursive fueled checkers (`digitsLeFuel` and
`hasCarryFuel`) reduce directly in the Lean kernel in `O(log_p k)` integer divisions without ever
evaluating `Nat.choose n k`, allowing kernel-checked verification of `(n.choose k).minFac` even
when `n.choose k` has millions of digits.
-/
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial

namespace Erdos1094

/-- Structurally recursive check that every base-`p` digit of `k` is `≤` the corresponding
base-`p` digit of `n` (within `fuel` base-`p` digits, requiring `k` to reach `0`). -/
def digitsLeFuel : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, k => k == 0
  | fuel + 1, p, n, k =>
    if k == 0 then true
    else if n == 0 then false
    else decide (k % p ≤ n % p) && digitsLeFuel fuel p (n / p) (k / p)

/-- Structurally recursive check that some base-`p` digit of `k` strictly exceeds the
corresponding base-`p` digit of `n` (within `fuel` base-`p` digits). -/
def hasCarryFuel : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, p, n, k =>
    if k == 0 then false
    else decide (n % p < k % p) || hasCarryFuel fuel p (n / p) (k / p)

/-- For a prime `p` and `m ≤ n < p`, `p` does not divide `C(n, m)`. -/
theorem not_dvd_choose_of_lt {p n m : ℕ} (hp : p.Prime) (hn : n < p) (hm : m ≤ n) :
    ¬ p ∣ n.choose m := by
  intro h
  have h1 : n.choose m ∣ n.factorial :=
    ⟨m.factorial * (n - m).factorial, by
      rw [← Nat.choose_mul_factorial_mul_factorial hm, mul_assoc]⟩
  have hle : p ≤ n := hp.dvd_factorial.1 (dvd_trans h h1)
  omega

/-- One step of Lucas's theorem expressed as divisibility by `p`. -/
theorem dvd_choose_iff_lucas_step {p n k : ℕ} (hp : p.Prime) :
    p ∣ n.choose k ↔ p ∣ (n % p).choose (k % p) * (n / p).choose (k / p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun h => hlucas.symm.trans h, fun h => hlucas.trans h⟩

/-- Lucas's theorem in base-`p` digit-dominance form: for prime `p`, `p ∤ C(n, k)` if and only if
every base-`p` digit of `k` is `≤` the corresponding base-`p` digit of `n`. -/
theorem not_dvd_choose_iff_forall_digit_le {p : ℕ} (hp : p.Prime) :
    ∀ n k : ℕ, ¬ p ∣ n.choose k ↔ ∀ i : ℕ, k / p ^ i % p ≤ n / p ^ i % p := by
  intro n k
  induction k using Nat.strong_induction_on generalizing n with
  | ind k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.choose_zero_right, Nat.zero_div, Nat.zero_mod, Nat.zero_le, implies_true,
        iff_true]
      exact hp.not_dvd_one
    · have hlt : k / p < k := Nat.div_lt_self (Nat.pos_of_ne_zero hk0) hp.one_lt
      have hih := ih (k / p) hlt (n / p)
      rw [dvd_choose_iff_lucas_step hp, hp.dvd_mul, not_or, hih]
      constructor
      · rintro ⟨hmod, hdiv⟩ i
        cases i with
        | zero =>
          simp only [pow_zero, Nat.div_one]
          by_contra hgt
          have hzero : (n % p).choose (k % p) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          exact hmod (hzero ▸ dvd_zero p)
        | succ i =>
          have h := hdiv i
          simpa [pow_succ', Nat.div_div_eq_div_mul] using h
      · intro hall
        refine ⟨not_dvd_choose_of_lt hp (Nat.mod_lt n hp.pos) ?_, ?_⟩
        · simpa using hall 0
        · intro i
          have h := hall (i + 1)
          simpa [pow_succ', Nat.div_div_eq_div_mul] using h

/-- Soundness of `digitsLeFuel`: if `digitsLeFuel fuel p n k = true` for prime `p`,
then `p ∤ C(n, k)`. -/
theorem not_dvd_choose_of_digitsLeFuel {fuel p n k : ℕ} (hp : p.Prime)
    (h : digitsLeFuel fuel p n k = true) : ¬ p ∣ n.choose k := by
  induction fuel generalizing n k with
  | zero =>
    simp only [digitsLeFuel, beq_iff_eq] at h
    subst h
    simpa using hp.not_dvd_one
  | succ fuel ih =>
    simp only [digitsLeFuel, beq_iff_eq] at h
    by_cases hk0 : k = 0
    · subst hk0
      simpa using hp.not_dvd_one
    · simp only [hk0, ↓reduceIte] at h
      by_cases hn0 : n = 0
      · simp [hn0] at h
      · simp only [hn0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
        rw [dvd_choose_iff_lucas_step hp, hp.dvd_mul, not_or]
        exact ⟨not_dvd_choose_of_lt hp (Nat.mod_lt n hp.pos) h.1, ih h.2⟩

/-- Soundness of `hasCarryFuel`: if `hasCarryFuel fuel p n k = true` for prime `p`,
then `p ∣ C(n, k)`. -/
theorem dvd_choose_of_hasCarryFuel {fuel p n k : ℕ} (hp : p.Prime)
    (h : hasCarryFuel fuel p n k = true) : p ∣ n.choose k := by
  induction fuel generalizing n k with
  | zero =>
    simp [hasCarryFuel] at h
  | succ fuel ih =>
    simp only [hasCarryFuel, beq_iff_eq] at h
    by_cases hk0 : k = 0
    · simp [hk0] at h
    · simp only [hk0, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at h
      rw [dvd_choose_iff_lucas_step hp, hp.dvd_mul]
      rcases h with hlt | hrec
      · left
        rw [Nat.choose_eq_zero_of_lt hlt]
        exact dvd_zero p
      · right
        exact ih hrec

/-- Boolean check that every prime `r < q` satisfies `digitsLeFuel fuel r N k = true`
(so `r ∤ C(N, k)`). -/
def allSmallPrimesCarryFree (fuel q N k : ℕ) : Bool :=
  (List.range q).all fun r => if r.Prime then digitsLeFuel fuel r N k else true

/-- Criterion for `m.minFac = q`: `q` is prime, `q ∣ m`, and no prime `r < q` divides `m`. -/
theorem minFac_eq_of_dvd_of_not_dvd {m q : ℕ} (hq : q.Prime) (hdvd : q ∣ m)
    (hsmall : ∀ r : ℕ, r.Prime → r < q → ¬ r ∣ m) : m.minFac = q := by
  have hm1 : m ≠ 1 := by
    intro h1
    rw [h1] at hdvd
    exact hq.not_dvd_one hdvd
  have hle : m.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hdvd
  have hge : q ≤ m.minFac := by
    by_contra hlt
    exact hsmall m.minFac (Nat.minFac_prime hm1) (by omega) (Nat.minFac_dvd m)
  exact le_antisymm hle hge

/-- Kernel-friendly verification of `(N.choose k).minFac = q` via Lucas's theorem. -/
theorem minFac_choose_eq {fuel N k q : ℕ} (hq : q.Prime)
    (hdvd : hasCarryFuel fuel q N k = true)
    (hsmall : allSmallPrimesCarryFree fuel q N k = true) :
    (N.choose k).minFac = q := by
  refine minFac_eq_of_dvd_of_not_dvd hq (dvd_choose_of_hasCarryFuel hq hdvd) ?_
  intro r hr hrq
  have hall := List.all_eq_true.1 hsmall r (List.mem_range.2 hrq)
  simp only [hr, ↓reduceIte] at hall
  exact not_dvd_choose_of_digitsLeFuel hr hall

/-- If `m.minFac = q`, then every prime divisor `p` of `m` satisfies `q ≤ p`. -/
theorem le_of_prime_dvd_of_minFac_eq {m q p : ℕ} (hmin : m.minFac = q)
    (hp : p.Prime) (hdvd : p ∣ m) : q ≤ p := by
  rw [← hmin]
  exact Nat.minFac_le_of_dvd hp.two_le hdvd

end Erdos1094
