/-
Kellner's conjecture (A094960): Corollary A of `../proof.md`, the OEIS statement itself.

  The derivative of the Bernoulli polynomial `B_k(x)` has only integer coefficients
  if and only if `k ∈ {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}`.

Ingredients:
* `Polynomial.bernoulli` and `Polynomial.derivative_bernoulli` from Mathlib
  (`B_k' = k B_{k-1}`, so the coefficients are `k * C(k-1, j) * B_j`);
* the von Staudt-Clausen theorem from Mathlib (`Bernoulli.vonStaudt_clausen`,
  `Bernoulli.dvd_den_bernoulli`); it is NOT a hypothesis here;
* Lucas' theorem from Mathlib (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`);
* for `k ≥ 193`: `Kellner.kellner` (Theorem 1 (a)), hence the two hypotheses `AxlerLower`,
  `AxlerUpper`; this is Lemma 1 (ii) of the draft with `i = 1`, for a prime `p > √k`;
* for `k ≤ 192`: a table of witnesses `(k, j, p)` for the 182 non-members and a divisibility
  check for the ten members, both evaluated by the kernel (`decide +kernel`).
-/
import Kellner.Main

namespace Kellner

open Polynomial

/-- The derivative of the `k`-th Bernoulli polynomial has only integer coefficients. -/
def DerivIntegral (k : ℕ) : Prop :=
  ∀ i : ℕ, ∃ z : ℤ, (derivative (Polynomial.bernoulli k)).coeff i = (z : ℚ)

/-- The coefficients of `B_k'(x) = k B_{k-1}(x)`. -/
theorem coeff_derivative_bernoulli (k i : ℕ) :
    (derivative (Polynomial.bernoulli k)).coeff i =
      (k : ℚ) * (if i ≤ k - 1 then _root_.bernoulli (k - 1 - i) * ((k - 1).choose i : ℚ)
        else 0) := by
  rw [Polynomial.derivative_bernoulli, ← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul,
    Polynomial.coeff_bernoulli]

/-- If `x * N` is an integer then the denominator of `x` divides `N`. -/
theorem den_dvd_of_mul_eq_int {x : ℚ} {N : ℕ} (hN : N ≠ 0) {z : ℤ}
    (h : x * (N : ℚ) = (z : ℚ)) : x.den ∣ N := by
  have hN' : ((N : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hN
  have hx : x = Rat.divInt z (N : ℤ) := by
    rw [Rat.divInt_eq_div, eq_div_iff hN']
    exact_mod_cast h
  have h2 := Rat.den_dvd z (N : ℤ)
  rw [← hx] at h2
  exact Int.natCast_dvd_natCast.1 h2

/-- The criterion for a non-integral coefficient: a prime `p` and an even index `2j ≥ 2` with
`(p - 1) ∣ 2j` (so that `p` divides the denominator of `B_{2j}`, by von Staudt-Clausen) and
`p ∤ k * C(k-1, 2j)`. -/
theorem not_derivIntegral_of_witness {k p j : ℕ} (hp : p.Prime) (hj : 0 < j)
    (hpj : p - 1 ∣ 2 * j) (hjk : 2 * j + 1 ≤ k) (hnd : ¬ p ∣ k * (k - 1).choose (2 * j)) :
    ¬ DerivIntegral k := by
  intro hint
  obtain ⟨z, hz⟩ := hint (k - 1 - 2 * j)
  have hcond : k - 1 - 2 * j ≤ k - 1 := by omega
  rw [coeff_derivative_bernoulli] at hz
  simp only [hcond, ↓reduceIte] at hz
  have e : k - 1 - (k - 1 - 2 * j) = 2 * j := by omega
  rw [e, Nat.choose_symm (by omega)] at hz
  have := Fact.mk hp
  have hden : p ∣ (_root_.bernoulli (2 * j)).den := Bernoulli.dvd_den_bernoulli hj hpj
  have hN : k * (k - 1).choose (2 * j) ≠ 0 := fun h0 => hnd (h0 ▸ dvd_zero p)
  have hz' : _root_.bernoulli (2 * j) * ((k * (k - 1).choose (2 * j) : ℕ) : ℚ) = (z : ℚ) := by
    rw [← hz]
    push_cast
    ring
  exact hnd (dvd_trans hden (den_dvd_of_mul_eq_int hN hz'))

/-! ## `k ≥ 193`: Lemma 1 (ii) with `i = 1` -/

theorem not_dvd_choose_of_lt {p n m : ℕ} (hp : p.Prime) (hn : n < p) (hm : m ≤ n) :
    ¬ p ∣ n.choose m := by
  intro h
  have h1 : n.choose m ∣ n.factorial :=
    ⟨m.factorial * (n - m).factorial, by
      rw [← Nat.choose_mul_factorial_mul_factorial hm, mul_assoc]⟩
  have := (hp.dvd_factorial).1 (dvd_trans h h1)
  omega

/-- **Lemma 1 (ii)** of the draft with `i = 1`, for a prime `p > √k`: if `p ≥ 3` is prime,
`k < p ^ 2` and the two base-`p` digits of `k` have sum `≥ p`, then `B_k'(x)` has a coefficient
that is not an integer. -/
theorem lemma1 {k p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hsq : k < p ^ 2)
    (hds : p ≤ k / p + k % p) : ¬ DerivIntegral k := by
  have hdm := Nat.div_add_mod k p
  have ha : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.pos]
    nlinarith
  have hb : k % p < p := Nat.mod_lt _ hp.pos
  generalize k / p = a at *
  generalize k % p = b at *
  subst hdm
  obtain ⟨t, rfl⟩ : ∃ t, p = 2 * t + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact ⟨p / 2, by omega⟩
  have := Fact.mk hp
  refine not_derivIntegral_of_witness hp (j := (a + 1) * t)
    (Nat.mul_pos (by omega) (by omega)) ?_ ?_ ?_
  · have e0 : 2 * t + 1 - 1 = 2 * t := by omega
    rw [e0]
    exact ⟨a + 1, by ring⟩
  · nlinarith
  · intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · have h' : (2 * t + 1) ∣ b := (Nat.dvd_add_right (Nat.dvd_mul_right _ a)).1 h
      have := Nat.le_of_dvd (by omega) h'
      omega
    · have e1 : (2 * t + 1) * a + b - 1 = (2 * t + 1) * a + (b - 1) := by omega
      have e2 : 2 * ((a + 1) * t) = (2 * t + 1) * a + (2 * t - a) := by
        obtain ⟨c, hc⟩ : ∃ c, 2 * t = a + c := ⟨2 * t - a, by omega⟩
        have hc' : 2 * t - a = c := by omega
        rw [hc']
        nlinarith
      rw [e1, e2] at h
      have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2 * t + 1)
        (n := (2 * t + 1) * a + (b - 1)) (k := (2 * t + 1) * a + (2 * t - a))
      obtain ⟨d1, m1⟩ := div_mod_of_lt (p := 2 * t + 1) (a := a) (c := b - 1) (by omega)
      obtain ⟨d2, m2⟩ := div_mod_of_lt (p := 2 * t + 1) (a := a) (c := 2 * t - a) (by omega)
      rw [d1, m1, d2, m2, Nat.choose_self, mul_one] at hl
      have h0 : (b - 1).choose (2 * t - a) ≡ 0 [MOD 2 * t + 1] :=
        hl.symm.trans (Nat.modEq_zero_iff_dvd.2 h)
      exact not_dvd_choose_of_lt hp (by omega) (by omega) (Nat.modEq_zero_iff_dvd.1 h0)

/-- For every `k ≥ 193`, `B_k'(x)` has a coefficient that is not an integer. -/
theorem not_derivIntegral_of_ge (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ k : ℕ, 193 ≤ k → ¬ DerivIntegral k := by
  intro k hk
  obtain ⟨p, hpp, hsq, hds⟩ := kellner hLow hUp k hk
  rw [digits_sum_of_lt_sq hpp.two_le hsq] at hds
  have hp3 : 3 ≤ p := by
    by_contra hcon
    have h2 : p ≤ 2 := by omega
    have h4 : p ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  exact lemma1 hpp hp3 hsq hds

/-! ## Integrality: von Staudt-Clausen bounds the denominators -/

theorem sum_inv_mul_prod (T : Finset ℕ) (h0 : ∀ p ∈ T, p ≠ 0) :
    (∑ p ∈ T, (1 : ℚ) / p) * ((∏ p ∈ T, p : ℕ) : ℚ) =
      ((∑ p ∈ T, ∏ q ∈ T.erase p, q : ℕ) : ℚ) := by
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast h0 p hp
  rw [← Finset.mul_prod_erase T (fun q => (q : ℚ)) hp, one_div, inv_mul_cancel_left₀ hp0]

/-- von Staudt-Clausen in the form used here: `B_{2j}` times the product of the primes `p` with
`(p - 1) ∣ 2j` is an integer. -/
theorem bernoulli_mul_prod_int (j : ℕ) :
    ∃ z : ℤ, _root_.bernoulli (2 * j) *
      ((∏ p ∈ (Finset.range (2 * j + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * j), p : ℕ) : ℚ)
        = (z : ℚ) := by
  obtain ⟨w, hw⟩ := Bernoulli.vonStaudt_clausen j
  have h0 : ∀ p ∈ (Finset.range (2 * j + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * j),
      p ≠ 0 := fun p hp => ((Finset.mem_filter.1 hp).2.1).ne_zero
  have hsum := sum_inv_mul_prod _ h0
  generalize (Finset.range (2 * j + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * j) = T at *
  refine ⟨w * ((∏ p ∈ T, p : ℕ) : ℤ) - ((∑ p ∈ T, ∏ q ∈ T.erase p, q : ℕ) : ℤ), ?_⟩
  have hB : _root_.bernoulli (2 * j) = (w : ℚ) - ∑ p ∈ T, (1 : ℚ) / p := by
    rw [hw]
    ring
  rw [hB, sub_mul, hsum]
  push_cast
  ring

/-- If for every even index `2j ≥ 2` below `k`, every prime `p` with `(p - 1) ∣ 2j` divides
`k * C(k-1, 2j)`, then `B_k'(x)` has only integer coefficients. -/
theorem derivIntegral_of_dvd {k : ℕ}
    (h : ∀ j : ℕ, 0 < j → 2 * j + 1 ≤ k → ∀ p : ℕ, p.Prime → p - 1 ∣ 2 * j →
      p ∣ k * (k - 1).choose (2 * j)) : DerivIntegral k := by
  intro i
  rw [coeff_derivative_bernoulli]
  by_cases hi : i ≤ k - 1
  · simp only [hi, ↓reduceIte]
    obtain ⟨m, hm⟩ : ∃ m, k - 1 - i = m := ⟨_, rfl⟩
    have hch : (k - 1).choose i = (k - 1).choose m := by
      rw [← hm, Nat.choose_symm hi]
    have hmk : m ≤ k - 1 := by omega
    rw [hm, hch]
    clear hch hm hi
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact ⟨((k * (k - 1).choose (2 * 0) : ℕ) : ℤ), by
          rw [Nat.mul_zero, _root_.bernoulli_zero]
          push_cast
          ring⟩
      · obtain ⟨z, hz⟩ := bernoulli_mul_prod_int j
        have hD : (∏ p ∈ (Finset.range (2 * j + 2)).filter
            (fun p => p.Prime ∧ (p - 1) ∣ 2 * j), p) ∣ k * (k - 1).choose (2 * j) := by
          apply Finset.prod_primes_dvd
          · intro p hp
            exact ((Finset.mem_filter.1 hp).2.1).prime
          · intro p hp
            obtain ⟨-, hpp, hdiv⟩ := Finset.mem_filter.1 hp
            exact h j hj (by omega) p hpp hdiv
        obtain ⟨c, hc⟩ := hD
        refine ⟨z * (c : ℤ), ?_⟩
        have e : (k : ℚ) * (_root_.bernoulli (2 * j) * ((k - 1).choose (2 * j) : ℚ)) =
            _root_.bernoulli (2 * j) * ((k * (k - 1).choose (2 * j) : ℕ) : ℚ) := by
          push_cast
          ring
        rw [e, hc, Nat.cast_mul, ← mul_assoc, hz]
        push_cast
        ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · -- the index is 1: `B_1 = -1/2` and `k (k - 1)` is even
        obtain ⟨c, hc⟩ := Nat.even_mul_pred_self k
        refine ⟨-(c : ℤ), ?_⟩
        have hc' : ((k * (k - 1) : ℕ) : ℚ) = (c : ℚ) + c := by exact_mod_cast hc
        rw [Nat.mul_zero, Nat.zero_add, _root_.bernoulli_one, Nat.choose_one_right]
        push_cast at hc' ⊢
        linarith
      · have hz : _root_.bernoulli (2 * j + 1) = 0 :=
          _root_.bernoulli_eq_zero_of_odd ⟨j, rfl⟩ (by omega)
        exact ⟨0, by rw [hz]; simp⟩
  · simp only [hi, ↓reduceIte]
    exact ⟨0, by simp⟩

/-! ## `k ≤ 192`: kernel computations -/

/-- `C(n, m)` by factorials (fast to evaluate). -/
def chooseF (n m : ℕ) : ℕ := n.factorial / (m.factorial * (n - m).factorial)

theorem chooseF_eq {n m : ℕ} (h : m ≤ n) : chooseF n m = n.choose m :=
  (Nat.choose_eq_factorial_div_factorial h).symm

/-- The ten terms of A094960. -/
def members : List ℕ := [1, 2, 4, 6, 10, 12, 28, 30, 36, 60]

/-- For each `k ≤ 192` that is not a member: `(k, j, p)` with `p` prime, `(p - 1) ∣ 2j`,
`2j + 1 ≤ k` and `p ∤ k * C(k-1, 2j)` (found by `gen_table.py`, checked below). -/
def nonMemberTable : List (ℕ × ℕ × ℕ) :=
  [(3, 1, 2), (5, 2, 2), (7, 1, 2), (8, 2, 3), (9, 4, 2), (11, 1, 2), (13, 2, 2), (14, 2, 3),
   (15, 1, 2), (16, 3, 3), (17, 2, 3), (18, 6, 5), (19, 1, 2), (20, 5, 3), (21, 2, 2), (22, 6, 3),
   (23, 1, 2), (24, 4, 5), (25, 3, 3), (26, 2, 3), (27, 1, 2), (29, 2, 2), (31, 1, 2), (32, 2, 3),
   (33, 9, 7), (34, 3, 3), (35, 1, 2), (37, 2, 2), (38, 5, 3), (39, 1, 2), (40, 6, 3), (41, 2, 3),
   (42, 8, 5), (43, 1, 2), (44, 2, 3), (45, 2, 2), (46, 9, 3), (47, 1, 2), (48, 6, 5), (49, 4, 5),
   (50, 2, 3), (51, 1, 2), (52, 3, 3), (53, 2, 2), (54, 10, 11), (55, 1, 2), (56, 14, 3),
   (57, 4, 2), (58, 15, 3), (59, 1, 2), (61, 2, 2), (62, 2, 3), (63, 1, 2), (64, 4, 5), (65, 5, 3),
   (66, 20, 5), (67, 1, 2), (68, 2, 3), (69, 2, 2), (70, 3, 3), (71, 1, 2), (72, 8, 5), (73, 4, 2),
   (74, 4, 5), (75, 1, 2), (76, 6, 3), (77, 2, 2), (78, 26, 5), (79, 1, 2), (80, 2, 3), (81, 8, 2),
   (82, 9, 7), (83, 1, 2), (84, 4, 5), (85, 2, 2), (86, 2, 3), (87, 1, 2), (88, 3, 3), (89, 2, 3),
   (90, 6, 7), (91, 1, 2), (92, 5, 3), (93, 2, 2), (94, 4, 5), (95, 1, 2), (96, 9, 7), (97, 3, 3),
   (98, 2, 3), (99, 1, 2), (100, 9, 3), (101, 2, 2), (102, 18, 13), (103, 1, 2), (104, 2, 3),
   (105, 4, 2), (106, 3, 3), (107, 1, 2), (108, 15, 11), (109, 2, 2), (110, 14, 3), (111, 1, 2),
   (112, 15, 3), (113, 2, 3), (114, 4, 5), (115, 1, 2), (116, 2, 3), (117, 2, 2), (118, 6, 5),
   (119, 1, 2), (120, 10, 11), (121, 4, 2), (122, 2, 3), (123, 1, 2), (124, 3, 3), (125, 2, 2),
   (126, 30, 13), (127, 1, 2), (128, 5, 3), (129, 12, 13), (130, 6, 3), (131, 1, 2), (132, 6, 7),
   (133, 2, 2), (134, 2, 3), (135, 1, 2), (136, 15, 7), (137, 4, 2), (138, 6, 5), (139, 1, 2),
   (140, 2, 3), (141, 2, 2), (142, 3, 3), (143, 1, 2), (144, 4, 5), (145, 8, 2), (146, 5, 3),
   (147, 1, 2), (148, 6, 3), (149, 2, 2), (150, 27, 19), (151, 1, 2), (152, 2, 3), (153, 4, 2),
   (154, 9, 3), (155, 1, 2), (156, 66, 23), (157, 2, 2), (158, 2, 3), (159, 1, 2), (160, 3, 3),
   (161, 2, 3), (162, 18, 5), (163, 1, 2), (164, 4, 5), (165, 2, 2), (166, 9, 7), (167, 1, 2),
   (168, 6, 5), (169, 3, 3), (170, 2, 3), (171, 1, 2), (172, 8, 5), (173, 2, 2), (174, 4, 5),
   (175, 1, 2), (176, 2, 3), (177, 8, 2), (178, 3, 3), (179, 1, 2), (180, 9, 7), (181, 2, 2),
   (182, 5, 3), (183, 1, 2), (184, 4, 5), (185, 2, 3), (186, 10, 11), (187, 1, 2), (188, 2, 3),
   (189, 2, 2), (190, 21, 7), (191, 1, 2), (192, 8, 5)]

/-- (kernel computation) Every entry of the table is a valid witness. -/
theorem table_ok : ∀ t ∈ nonMemberTable,
    t.2.2 ∈ primes193 ∧ 0 < t.2.1 ∧ (t.2.2 - 1) ∣ 2 * t.2.1 ∧ 2 * t.2.1 + 1 ≤ t.1 ∧
      ¬ t.2.2 ∣ t.1 * chooseF (t.1 - 1) (2 * t.2.1) := by
  decide +kernel

/-- (kernel computation) Every `1 ≤ k ≤ 192` is a member or occurs in the table. -/
theorem cover_ok : ∀ k ∈ List.range' 1 192,
    k ∈ members ∨ k ∈ nonMemberTable.map Prod.fst := by
  decide +kernel

/-- (kernel computation) The divisibility condition of `derivIntegral_of_dvd` for the ten
members. -/
theorem members_ok : ∀ k ∈ members, ∀ j ∈ List.range' 1 (k / 2), 2 * j + 1 ≤ k →
    ∀ p ∈ primes193, (p - 1) ∣ 2 * j → p ∣ k * chooseF (k - 1) (2 * j) := by
  decide +kernel

theorem primes193_lt : ∀ q ∈ primes193, q < 193 := by decide

theorem derivIntegral_of_mem_members {k : ℕ} (hk : k ∈ members) : DerivIntegral k := by
  have hk60 : k ≤ 60 := by
    have : ∀ x ∈ members, x ≤ 60 := by decide
    exact this k hk
  apply derivIntegral_of_dvd
  intro j hj hjk p hpp hdiv
  have hpj : p - 1 ≤ 2 * j := Nat.le_of_dvd (by omega) hdiv
  have hmem : p ∈ primes193 := (primes193_spec p (by omega)).1 hpp
  have := members_ok k hk j (by rw [List.mem_range'_1]; omega) hjk p hmem hdiv
  rwa [chooseF_eq (by omega)] at this

theorem not_derivIntegral_of_table {k j p : ℕ} (h : (k, j, p) ∈ nonMemberTable) :
    ¬ DerivIntegral k := by
  have h5 := table_ok (k, j, p) h
  dsimp only at h5
  obtain ⟨hmem, hj, hdiv, hjk, hnd⟩ := h5
  have hpp : p.Prime := (primes193_spec p (primes193_lt p hmem)).2 hmem
  refine not_derivIntegral_of_witness hpp hj hdiv hjk ?_
  have e : chooseF (k - 1) (2 * j) = (k - 1).choose (2 * j) := chooseF_eq (by omega)
  simpa only [e] using hnd

/-! ## Corollary A -/

/-- **Corollary A (A094960; Kellner 2023, Conjecture 1 (ii)).** For `k ≥ 1`, the derivative of
the Bernoulli polynomial `B_k(x)` has only integer coefficients if and only if
`k ∈ {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}`. -/
theorem A094960_complete (hLow : AxlerLower) (hUp : AxlerUpper) :
    ∀ k : ℕ, 1 ≤ k →
      ((∀ i : ℕ, ∃ z : ℤ, (derivative (Polynomial.bernoulli k)).coeff i = (z : ℚ)) ↔
        k ∈ [1, 2, 4, 6, 10, 12, 28, 30, 36, 60]) := by
  intro k hk
  change DerivIntegral k ↔ k ∈ members
  constructor
  · intro hint
    by_contra hnot
    by_cases hbig : 193 ≤ k
    · exact not_derivIntegral_of_ge hLow hUp k hbig hint
    · rcases cover_ok k (by rw [List.mem_range'_1]; omega) with hm | ht
      · exact hnot hm
      · obtain ⟨⟨k', j, p⟩, hmem, rfl⟩ := List.mem_map.1 ht
        exact not_derivIntegral_of_table hmem hint
  · exact derivIntegral_of_mem_members

/-- The half of Corollary A that needs no hypothesis: the ten numbers are terms of A094960,
and no other `k ≤ 192` is. -/
theorem A094960_upto_192 :
    ∀ k : ℕ, 1 ≤ k → k ≤ 192 →
      ((∀ i : ℕ, ∃ z : ℤ, (derivative (Polynomial.bernoulli k)).coeff i = (z : ℚ)) ↔
        k ∈ [1, 2, 4, 6, 10, 12, 28, 30, 36, 60]) := by
  intro k hk hk192
  change DerivIntegral k ↔ k ∈ members
  constructor
  · intro hint
    by_contra hnot
    rcases cover_ok k (by rw [List.mem_range'_1]; omega) with hm | ht
    · exact hnot hm
    · obtain ⟨⟨k', j, p⟩, hmem, rfl⟩ := List.mem_map.1 ht
      exact not_derivIntegral_of_table hmem hint
  · exact derivIntegral_of_mem_members

end Kellner
