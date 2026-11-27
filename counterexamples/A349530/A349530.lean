/-
  OEIS A349530, Conjecture 3 (Zhi-Wei Sun, Nov 2021) — Disproof via an infinite
  family of counterexamples, formally verified in Lean 4 (zero external
  dependencies, zero sorry, standard axioms only).

  For every k : Nat, let a = 5 * k + 4, n = 5 ^ a + 5, and m = 11 * 5 ^ (a - 1).
  Then 5^a < n <= 3 * 5^a and m < 3 * 5^a, yet the n numbers j * (j^4 + 1)
  for 1 <= j <= n are pairwise distinct modulo m.

  In particular, for every k >= 1 (starting at k = 1, a = 9: n = 1,953,126..1,953,130,
  m = 4,296,875 < 5,859,375 = 3 * 5^9), D(n) <= 11 * 5^(a - 1) < 3 * 5^a,
  contradicting Conjecture 3.
-/

namespace A349530

def f (x : Nat) : Nat := x * (x ^ 4 + 1)

private theorem pow5_sub_factor (x y : Nat) (hxy : y ≤ x) :
    (x - y) * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) + y ^ 5 = x ^ 5 := by
  -- Multiply out (x - y) * S = x * S - y * S via telescoping
  have h1 : x * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) =
      x ^ 5 + (x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + x * y ^ 4) := by
    simp only [Nat.mul_add, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
  have h2 : y * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) =
      (x ^ 4 * y + x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 + x * y ^ 4) + y ^ 5 := by
    simp only [Nat.mul_add, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
  have hsub : (x - y) * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) +
      y * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) =
      x * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hxy]
  omega

private theorem f_sub_factor (x y : Nat) (hxy : y ≤ x) :
    f x - f y = (x - y) * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 + 1) := by
  have hpow := pow5_sub_factor x y hxy
  have hfx : f x = x ^ 5 + x := by
    simp only [f, Nat.mul_add, Nat.mul_one, Nat.pow_succ, Nat.mul_comm]
  have hfy : f y = y ^ 5 + y := by
    simp only [f, Nat.mul_add, Nat.mul_one, Nat.pow_succ, Nat.mul_comm]
  rw [hfx, hfy, Nat.mul_add, Nat.mul_one]
  omega

private theorem f_mod_congr (m a b : Nat) (h : a % m = b % m) : f a % m = f b % m := by
  simp only [f]
  rw [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, h, ← Nat.pow_mod, ← Nat.add_mod, ← Nat.mul_mod]

private theorem mod5_inj (x y : Nat) (h : f x % 5 = f y % 5) : x % 5 = y % 5 := by
  have hfx : f x % 5 = f (x % 5) % 5 := f_mod_congr 5 x (x % 5) (Nat.mod_mod x 5).symm
  have hfy : f y % 5 = f (y % 5) % 5 := f_mod_congr 5 y (y % 5) (Nat.mod_mod y 5).symm
  rw [hfx, hfy] at h
  have hx : x % 5 < 5 := Nat.mod_lt x (by decide)
  have hy : y % 5 < 5 := Nat.mod_lt y (by decide)
  generalize hx' : x % 5 = a at hx h
  generalize hy' : y % 5 = b at hy h
  have hdec : ∀ a < 5, ∀ b < 5, f a % 5 = f b % 5 → a = b := by decide
  exact hdec a hx b hy h

private theorem factor_mod5_eq_one (x y : Nat) (hxy : x % 5 = y % 5) :
    (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 + 1) % 5 = 1 := by
  have hred :
      (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 + 1) % 5 =
      ((x % 5) ^ 4 + (x % 5) ^ 3 * (y % 5) + (x % 5) ^ 2 * (y % 5) ^ 2 +
        (x % 5) * (y % 5) ^ 3 + (y % 5) ^ 4 + 1) % 5 := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
  rw [hred, hxy]
  have hy : y % 5 < 5 := Nat.mod_lt y (by decide)
  generalize y % 5 = b at hy
  have hdec : ∀ b < 5, (b ^ 4 + b ^ 3 * b + b ^ 2 * b ^ 2 + b * b ^ 3 + b ^ 4 + 1) % 5 = 1 := by
    decide
  exact hdec b hy

private theorem prime5_dvd_mul {a b : Nat} (h : 5 ∣ a * b) (hb : b % 5 = 1) : 5 ∣ a := by
  have hmod : (a * b) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.mul_mod, hb, Nat.mul_one, Nat.mod_mod] at hmod
  exact Nat.dvd_of_mod_eq_zero hmod

private theorem pow5_dvd_of_mul {e a b : Nat} (h : 5 ^ e ∣ a * b) (hb : b % 5 = 1) : 5 ^ e ∣ a := by
  induction e generalizing a with
  | zero => exact Nat.one_dvd a
  | succ e ih =>
    have h5 : 5 ∣ a * b := Nat.dvd_trans (by rw [Nat.pow_succ]; exact Nat.dvd_mul_left 5 (5 ^ e)) h
    have h5a : 5 ∣ a := prime5_dvd_mul h5 hb
    rcases h5a with ⟨a', rfl⟩
    rw [Nat.pow_succ] at h ⊢
    rw [Nat.mul_assoc] at h
    have h' : 5 ^ e * 5 ∣ (a' * b) * 5 := by
      rw [Nat.mul_comm (a' * b) 5]; exact h
    have he : 5 ^ e ∣ a' * b := (Nat.mul_dvd_mul_iff_right (by decide : 0 < 5)).mp h'
    have hea' : 5 ^ e ∣ a' := ih he
    rcases hea' with ⟨c, rfl⟩
    exact ⟨c, by rw [Nat.mul_comm 5 (5 ^ e * c), Nat.mul_assoc, Nat.mul_comm c 5, ← Nat.mul_assoc]⟩

private theorem dvd_sub_of_mod_eq {m u v : Nat} (hvu : v ≤ u) (h : u % m = v % m) : m ∣ u - v := by
  have hu := Nat.div_add_mod u m
  have hv := Nat.div_add_mod v m
  refine ⟨u / m - v / m, ?_⟩
  rw [Nat.mul_sub_left_distrib]
  omega

private theorem mod_eq_of_dvd_sub {m u v : Nat} (hvu : v ≤ u) (h : m ∣ u - v) : u % m = v % m := by
  rcases h with ⟨k, hk⟩
  have hu : u = v + m * k := by omega
  rw [hu, Nat.add_mul_mod_self_left]

/-- Hensel's lemma for `f(x) = x(x^4 + 1)`: `f` is injective modulo `5^e` for every `e`. -/
theorem f_inj_mod_pow5 (e : Nat) :
    ∀ x y : Nat, f x % 5 ^ e = f y % 5 ^ e → x % 5 ^ e = y % 5 ^ e := by
  induction e with
  | zero => intro x y _; simp [Nat.mod_one]
  | succ e ih =>
    intro x y h
    -- Show x % 5 = y % 5
    have h_5 : f x % 5 = f y % 5 := by
      have hdvd : 5 ∣ 5 ^ (e + 1) := by rw [Nat.pow_succ]; exact Nat.dvd_mul_left 5 (5 ^ e)
      have := congrArg (· % 5) h
      simpa [Nat.mod_mod_of_dvd _ hdvd] using this
    have hxy_5 : x % 5 = y % 5 := mod5_inj x y h_5
    -- Assume WLOG y ≤ x
    suffices ∀ u v : Nat, v ≤ u → f u % 5 ^ (e + 1) = f v % 5 ^ (e + 1) →
        u % 5 = v % 5 → u % 5 ^ (e + 1) = v % 5 ^ (e + 1) by
      by_cases hle : y ≤ x
      · exact this x y hle h hxy_5
      · exact (this y x (by omega) h.symm hxy_5.symm).symm
    intro u v hvu hfuv huv5
    have hfle : f v ≤ f u := by
      simp only [f]
      exact Nat.mul_le_mul hvu (Nat.add_le_add_right (Nat.pow_le_pow_left hvu 4) 1)
    have hdvdf : 5 ^ (e + 1) ∣ f u - f v := dvd_sub_of_mod_eq hfle hfuv
    rw [f_sub_factor u v hvu] at hdvdf
    have hfac1 : (u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + u * v ^ 3 + v ^ 4 + 1) % 5 = 1 :=
      factor_mod5_eq_one u v huv5
    have hdvduv : 5 ^ (e + 1) ∣ u - v := pow5_dvd_of_mul hdvdf hfac1
    exact mod_eq_of_dvd_sub hvu hdvduv

/-- Periodicity of `5^(5k + 3) mod 11 = 4`. -/
theorem pow5_mod11 (k : Nat) : 5 ^ (5 * k + 3) % 11 = 4 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hexp : 5 * (k + 1) + 3 = (5 * k + 3) + 5 := by omega
    rw [hexp, Nat.pow_add, Nat.mul_mod, ih]

/-- Finite check modulo 11: for shift `4`, all 5 values `f(r + 4t) mod 11` (`t = 0..4`)
    are distinct for every `r < 11`, and all 6 values (`t = 0..5`) are distinct for `1 <= r <= 5`. -/
private theorem mod11_distinct_5 :
    ∀ r < 11, ∀ t1 < 5, ∀ t2 < 5, t1 < t2 →
      f (r + 4 * t1) % 11 ≠ f (r + 4 * t2) % 11 := by
  decide

private theorem mod11_distinct_6 :
    ∀ r < 5, ∀ t1 < 6, ∀ t2 < 6, t1 < t2 →
      f ((r + 1) + 4 * t1) % 11 ≠ f ((r + 1) + 4 * t2) % 11 := by
  decide

/-- Main theorem: For every `k : Nat`, with `a = 5*k + 4`, `n = 5^a + 5`, and
    `m = 11 * 5^(a - 1)`, we have `5^a < n <= 3 * 5^a` and `m < 3 * 5^a`, yet all `n`
    values `f(1), ..., f(n)` are pairwise distinct modulo `m`.
    For every `k >= 1` (`n >= 5^9 + 1 = 1,953,126`), this disproves Conjecture 3 of OEIS A349530. -/
theorem a349530_conj3_infinite_counterexamples (k : Nat) :
    let a := 5 * k + 4
    let n := 5 ^ a + 5
    let m := 11 * 5 ^ (a - 1)
    5 ^ a < n ∧ n ≤ 3 * 5 ^ a ∧ m < 3 * 5 ^ a ∧
    ∀ i j : Nat, 1 ≤ i → i < j → j ≤ n → f i % m ≠ f j % m := by
  intro a n m
  have ha1 : a - 1 = 5 * k + 3 := by omega
  have h5a : 5 ^ a = 5 * 5 ^ (a - 1) := by
    have h1 : 5 ^ a = 5 ^ ((a - 1) + 1) := congrArg (5 ^ ·) (by omega)
    rw [h1, Nat.pow_succ, Nat.mul_comm]
  have h5am1_pos : 125 ≤ 5 ^ (a - 1) := by
    rw [ha1]
    have h125 : 5 ^ 3 = 125 := by decide
    rw [← h125]
    exact Nat.pow_le_pow_right (by decide : 0 < 5) (by omega)
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro i j hi hij hj hfeq
  -- Deduce f i % 5^(a-1) = f j % 5^(a-1) and f i % 11 = f j % 11
  have hf5 : f i % 5 ^ (a - 1) = f j % 5 ^ (a - 1) := by
    have hd : 5 ^ (a - 1) ∣ m := Nat.dvd_mul_left _ _
    have := congrArg (· % 5 ^ (a - 1)) hfeq
    simpa [Nat.mod_mod_of_dvd _ hd] using this
  have hf11 : f i % 11 = f j % 11 := by
    have hd : 11 ∣ m := Nat.dvd_mul_right _ _
    have := congrArg (· % 11) hfeq
    simpa [Nat.mod_mod_of_dvd _ hd] using this
  -- By Hensel's lemma, i ≡ j (mod 5^(a-1)), so j - i = d * P with d ≥ 1
  have hij5 : i % 5 ^ (a - 1) = j % 5 ^ (a - 1) := f_inj_mod_pow5 (a - 1) i j hf5
  let P := 5 ^ (a - 1)
  have hP_pos : 0 < P := by omega
  have hP_mod11 : P % 11 = 4 := by
    change 5 ^ (a - 1) % 11 = 4
    rw [ha1]; exact pow5_mod11 k
  have hdvd_ji : P ∣ j - i := dvd_sub_of_mod_eq (by omega) hij5.symm
  rcases hdvd_ji with ⟨d, hd_eq⟩
  have hd_pos : 1 ≤ d := by
    cases d with
    | zero => simp at hd_eq; omega
    | succ _ => omega
  -- Write i = r + t1 * P and j = r + t2 * P with 1 ≤ r ≤ P and t1 < t2
  let r0 := (i - 1) % P
  let r := r0 + 1
  let t1 := (i - 1) / P
  let t2 := t1 + d
  have hr_range : 1 ≤ r ∧ r ≤ P := by
    have := Nat.mod_lt (i - 1) hP_pos
    omega
  have hi_eq : i = r + t1 * P := by
    have hdm := Nat.div_add_mod (i - 1) P
    rw [Nat.mul_comm P t1] at hdm
    omega
  have hj_eq : j = r + t2 * P := by
    have hmul : t2 * P = t1 * P + d * P := Nat.add_mul t1 d P
    rw [Nat.mul_comm P d] at hd_eq
    omega
  have ht12 : t1 < t2 := by omega
  -- Reduce i and j modulo 11
  have hi11 : i % 11 = (r % 11 + 4 * t1) % 11 := by
    rw [hi_eq, Nat.add_mod, Nat.mul_mod, hP_mod11, Nat.mul_comm (t1 % 11) 4]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  have hj11 : j % 11 = (r % 11 + 4 * t2) % 11 := by
    rw [hj_eq, Nat.add_mod, Nat.mul_mod, hP_mod11, Nat.mul_comm (t2 % 11) 4]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  have hfeq11 : f (r % 11 + 4 * t1) % 11 = f (r % 11 + 4 * t2) % 11 := by
    rw [← f_mod_congr 11 i (r % 11 + 4 * t1) hi11, ← f_mod_congr 11 j (r % 11 + 4 * t2) hj11]
    exact hf11
  -- Case split on r ≤ 5 vs r > 5
  by_cases hr5 : r ≤ 5
  · have ht2_lt6 : t2 < 6 := by
      by_cases hge : 6 ≤ t2
      · exfalso
        have : 6 * P ≤ t2 * P := Nat.mul_le_mul_right P hge
        omega
      · omega
    have hr_mod : r % 11 = r := Nat.mod_eq_of_lt (by omega)
    rw [hr_mod] at hfeq11
    have hr_succ : r = (r - 1) + 1 := by omega
    rw [hr_succ] at hfeq11
    exact mod11_distinct_6 (r - 1) (by omega) t1 (by omega) t2 ht2_lt6 ht12 hfeq11
  · have ht2_lt5 : t2 < 5 := by
      by_cases hge : 5 ≤ t2
      · exfalso
        have : 5 * P ≤ t2 * P := Nat.mul_le_mul_right P hge
        omega
      · omega
    exact mod11_distinct_5 (r % 11) (Nat.mod_lt r (by decide)) t1 (by omega) t2 ht2_lt5 ht12 hfeq11

end A349530

#print axioms A349530.a349530_conj3_infinite_counterexamples
