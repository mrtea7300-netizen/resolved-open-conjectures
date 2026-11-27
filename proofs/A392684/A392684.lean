/-
  OEIS A392684 — Complete formal proof of Zhi-Wei Sun's conjecture (Jan 19, 2026)
  for k = 3 (Conjecture (i) for k = 3 and N(3) = 6 in Conjecture (ii)):

    Every integer n >= 6 can be written as n = x + y + z with x >= y >= z >= 1
    such that lcm(x, y, z) = m * (m + 1) * (m + 2) for some integer m >= 1,
    and no integer 1 <= n <= 5 has such a representation.

  Self-contained Lean 4 proof (zero external dependencies, zero sorry, standard axioms only).
-/

namespace A392684

/-- Three-argument least common multiple. -/
def lcm3 (x y z : Nat) : Nat := Nat.lcm (Nat.lcm x y) z

/-- Existence of an ordered representation `n = x + y + z` (`x >= y >= z >= 1`)
    whose lcm is a product of three consecutive positive integers. -/
def HasRep (n : Nat) : Prop :=
  ∃ x y z m : Nat,
    1 ≤ z ∧ z ≤ y ∧ y ≤ x ∧ x + y + z = n ∧ 1 ≤ m ∧
    lcm3 x y z = m * (m + 1) * (m + 2)

/-! ### Elementary gcd / coprimality / lcm helpers -/

private theorem lcm3_comm12 (x y z : Nat) : lcm3 x y z = lcm3 y x z := by
  simp only [lcm3, Nat.lcm_comm x y]

private theorem lcm3_comm23 (x y z : Nat) : lcm3 x y z = lcm3 x z y := by
  simp only [lcm3, Nat.lcm_assoc, Nat.lcm_comm y z]

/-- Any unordered valid triple `(u, v, w)` can be sorted into `z ≤ y ≤ x`. -/
private theorem hasRep_of_unordered {n u v w m : Nat}
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsum : u + v + w = n)
    (hm : 1 ≤ m) (hlcm : lcm3 u v w = m * (m + 1) * (m + 2)) : HasRep n := by
  by_cases huv : v ≤ u
  · by_cases hvw : w ≤ v
    · exact ⟨u, v, w, m, hw, hvw, huv, hsum, hm, hlcm⟩
    · by_cases huw : w ≤ u
      · exact ⟨u, w, v, m, hv, by omega, huw, by omega, hm, by rw [lcm3_comm23]; exact hlcm⟩
      · exact ⟨w, u, v, m, hv, huv, by omega, by omega, hm, by
          rw [lcm3_comm12, lcm3_comm23]; exact hlcm⟩
  · by_cases huw : w ≤ u
    · exact ⟨v, u, w, m, hw, huw, by omega, by omega, hm, by rw [lcm3_comm12]; exact hlcm⟩
    · by_cases hvw : w ≤ v
      · exact ⟨v, w, u, m, hu, by omega, hvw, by omega, hm, by
          rw [lcm3_comm23, lcm3_comm12]; exact hlcm⟩
      · exact ⟨w, v, u, m, hu, by omega, by omega, by omega, hm, by
          rw [lcm3_comm12, lcm3_comm23, lcm3_comm12]; exact hlcm⟩

private theorem coprime_of_dvd_one {a b : Nat} (h : ∀ d, d ∣ a → d ∣ b → d ∣ 1) :
    Nat.Coprime a b :=
  Nat.eq_one_of_dvd_one (h _ (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b))

private theorem coprime_succ (k : Nat) : Nat.Coprime k (k + 1) :=
  coprime_of_dvd_one fun _ h1 h2 => (Nat.dvd_add_right h1).mp h2

private theorem coprime_odd_add2 {m : Nat} (hodd : m % 2 = 1) : Nat.Coprime m (m + 2) := by
  apply coprime_of_dvd_one
  intro d h1 h2
  have hd2 : d ∣ 2 := (Nat.dvd_add_right h1).mp h2
  have hd_le : d ≤ 2 := Nat.le_of_dvd (by decide) hd2
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd2 (by decide)
  by_cases h2d : d = 2
  · subst h2d
    have := Nat.mod_eq_zero_of_dvd h1
    omega
  · have : d = 1 := by omega
    subst this; exact Nat.dvd_refl 1

private theorem coprime_two_mul_succ (k : Nat) : Nat.Coprime (2 * k + 1) (k + 1) := by
  apply coprime_of_dvd_one
  intro d h1 h2
  have h22 : d ∣ 2 * (k + 1) := Nat.dvd_trans h2 (Nat.dvd_mul_left (k + 1) 2)
  have heq : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  rw [heq] at h22
  exact (Nat.dvd_add_right h1).mp h22

private theorem coprime_two_mul_self (k : Nat) : Nat.Coprime (2 * k + 1) k := by
  apply coprime_of_dvd_one
  intro d h1 h2
  have h22 : d ∣ 2 * k := Nat.dvd_trans h2 (Nat.dvd_mul_left k 2)
  exact (Nat.dvd_add_right h22).mp h1

private theorem coprime_odd_two {x : Nat} (hodd : x % 2 = 1) : Nat.Coprime x 2 := by
  apply coprime_of_dvd_one
  intro d h1 h2
  have hd_le : d ≤ 2 := Nat.le_of_dvd (by decide) h2
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos h2 (by decide)
  by_cases h2d : d = 2
  · subst h2d
    have := Nat.mod_eq_zero_of_dvd h1
    omega
  · have : d = 1 := by omega
    subst this; exact Nat.dvd_refl 1

private theorem lcm3_dvd {x y z M : Nat} (hx : x ∣ M) (hy : y ∣ M) (hz : z ∣ M) :
    lcm3 x y z ∣ M :=
  Nat.lcm_dvd (Nat.lcm_dvd hx hy) hz

private theorem dvd_lcm3_1 (x y z : Nat) : x ∣ lcm3 x y z :=
  Nat.dvd_trans (Nat.dvd_lcm_left x y) (Nat.dvd_lcm_left (Nat.lcm x y) z)

private theorem dvd_lcm3_2 (x y z : Nat) : y ∣ lcm3 x y z :=
  Nat.dvd_trans (Nat.dvd_lcm_right x y) (Nat.dvd_lcm_left (Nat.lcm x y) z)

private theorem dvd_lcm3_3 (x y z : Nat) : z ∣ lcm3 x y z :=
  Nat.dvd_lcm_right (Nat.lcm x y) z

/-! ### Four Master LCM Lemmas (covering all 24 templates) -/

private theorem lcm3_mul_dvd {m a b c : Nat}
    (ha : a ∣ (m + 1) * (m + 2)) (hb : b ∣ m * (m + 2)) (hc : c ∣ m * (m + 1)) :
    lcm3 (a * m) (b * (m + 1)) (c * (m + 2)) ∣ m * (m + 1) * (m + 2) := by
  apply lcm3_dvd
  · rcases ha with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [Nat.mul_assoc m (m + 1) (m + 2), hk]
    simp [Nat.mul_comm, Nat.mul_left_comm]
  · rcases hb with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 : m * (m + 1) * (m + 2) = (m * (m + 2)) * (m + 1) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [h1, hk]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · rcases hc with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Master Lemma A (odd `m`). -/
private theorem master_odd {m a b c : Nat} (hodd : m % 2 = 1)
    (ha : a ∣ (m + 1) * (m + 2)) (hb : b ∣ m * (m + 2)) (hc : c ∣ m * (m + 1)) :
    lcm3 (a * m) (b * (m + 1)) (c * (m + 2)) = m * (m + 1) * (m + 2) := by
  apply Nat.dvd_antisymm (lcm3_mul_dvd ha hb hc)
  have hm : m ∣ lcm3 (a * m) (b * (m + 1)) (c * (m + 2)) :=
    Nat.dvd_trans (Nat.dvd_mul_left m a) (dvd_lcm3_1 _ _ _)
  have hm1 : m + 1 ∣ lcm3 (a * m) (b * (m + 1)) (c * (m + 2)) :=
    Nat.dvd_trans (Nat.dvd_mul_left (m + 1) b) (dvd_lcm3_2 _ _ _)
  have hm2 : m + 2 ∣ lcm3 (a * m) (b * (m + 1)) (c * (m + 2)) :=
    Nat.dvd_trans (Nat.dvd_mul_left (m + 2) c) (dvd_lcm3_3 _ _ _)
  have h01 : m * (m + 1) ∣ lcm3 (a * m) (b * (m + 1)) (c * (m + 2)) :=
    (coprime_succ m).mul_dvd_of_dvd_of_dvd hm hm1
  have hc02 : Nat.Coprime (m * (m + 1)) (m + 2) :=
    (coprime_odd_add2 hodd).mul_left (coprime_succ (m + 1))
  exact hc02.mul_dvd_of_dvd_of_dvd h01 hm2

/-- Common final step for even `m`: once `m * (m + 2) ∣ L`, multiply by `m + 1`. -/
private theorem even_finish {m a b c : Nat}
    (h02 : m * (m + 2) ∣ lcm3 (a * m) (b * (m + 1)) (c * (m + 2))) :
    m * (m + 1) * (m + 2) ∣ lcm3 (a * m) (b * (m + 1)) (c * (m + 2)) := by
  have hm1 : m + 1 ∣ lcm3 (a * m) (b * (m + 1)) (c * (m + 2)) :=
    Nat.dvd_trans (Nat.dvd_mul_left (m + 1) b) (dvd_lcm3_2 _ _ _)
  have hcop : Nat.Coprime (m * (m + 2)) (m + 1) :=
    (coprime_succ m).mul_left (coprime_succ (m + 1)).symm
  have hprod := hcop.mul_dvd_of_dvd_of_dvd h02 hm1
  have heq : m * (m + 2) * (m + 1) = m * (m + 1) * (m + 2) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [heq] at hprod
  exact hprod

/-- Master Lemma B1 (`m = 2*k`, both `a` and `c` even). -/
private theorem master_even_both {k a b c : Nat}
    (ha2 : 2 ∣ a) (hc2 : 2 ∣ c)
    (ha : a ∣ (2 * k + 1) * (2 * k + 2))
    (hb : b ∣ (2 * k) * (2 * k + 2))
    (hc : c ∣ (2 * k) * (2 * k + 1)) :
    lcm3 (a * (2 * k)) (b * (2 * k + 1)) (c * (2 * k + 2)) =
      (2 * k) * (2 * k + 1) * (2 * k + 2) := by
  apply Nat.dvd_antisymm (lcm3_mul_dvd ha hb hc)
  apply even_finish
  rcases ha2 with ⟨a', rfl⟩
  rcases hc2 with ⟨c', rfl⟩
  have h4k : 4 * k ∣ lcm3 (2 * a' * (2 * k)) (b * (2 * k + 1)) (2 * c' * (2 * k + 2)) :=
    Nat.dvd_trans ⟨a', by
      have : 2 * a' * (2 * k) = (2 * 2) * k * a' := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      exact this⟩ (dvd_lcm3_1 _ _ _)
  have h4k1 : 4 * (k + 1) ∣ lcm3 (2 * a' * (2 * k)) (b * (2 * k + 1)) (2 * c' * (2 * k + 2)) :=
    Nat.dvd_trans ⟨c', by
      have h2k2 : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [h2k2]
      have : 2 * c' * (2 * (k + 1)) = (2 * 2) * (k + 1) * c' := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      exact this⟩ (dvd_lcm3_3 _ _ _)
  have h4 : 4 ∣ lcm3 (2 * a' * (2 * k)) (b * (2 * k + 1)) (2 * c' * (2 * k + 2)) :=
    Nat.dvd_trans (Nat.dvd_mul_right 4 k) h4k
  rcases h4 with ⟨L', hL'⟩
  rw [hL'] at h4k h4k1 ⊢
  have hk : k ∣ L' := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp h4k
  have hk1 : k + 1 ∣ L' := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp h4k1
  have hkk1 : k * (k + 1) ∣ L' := (coprime_succ k).mul_dvd_of_dvd_of_dvd hk hk1
  have heq : (2 * k) * (2 * k + 2) = 4 * (k * (k + 1)) := by
    have h2k2 : 2 * k + 2 = 2 * (k + 1) := by omega
    rw [h2k2]
    have : (2 * k) * (2 * (k + 1)) = (2 * 2) * (k * (k + 1)) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    exact this
  rw [heq]
  exact Nat.mul_dvd_mul_left 4 hkk1

/-- Master Lemma B2 (`m = 4*k`, `2 ∣ a`). -/
private theorem master_even_mod4_0 {k a b c : Nat}
    (ha2 : 2 ∣ a)
    (ha : a ∣ (4 * k + 1) * (4 * k + 2))
    (hb : b ∣ (4 * k) * (4 * k + 2))
    (hc : c ∣ (4 * k) * (4 * k + 1)) :
    lcm3 (a * (4 * k)) (b * (4 * k + 1)) (c * (4 * k + 2)) =
      (4 * k) * (4 * k + 1) * (4 * k + 2) := by
  apply Nat.dvd_antisymm (lcm3_mul_dvd ha hb hc)
  apply even_finish
  rcases ha2 with ⟨a', rfl⟩
  have h8k : 8 * k ∣ lcm3 (2 * a' * (4 * k)) (b * (4 * k + 1)) (c * (4 * k + 2)) :=
    Nat.dvd_trans ⟨a', by
      have : 2 * a' * (4 * k) = (2 * 4) * k * a' := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      exact this⟩ (dvd_lcm3_1 _ _ _)
  have h2k1 : 2 * k + 1 ∣ lcm3 (2 * a' * (4 * k)) (b * (4 * k + 1)) (c * (4 * k + 2)) :=
    Nat.dvd_trans ⟨2 * c, by
      have h4k2 : 4 * k + 2 = 2 * (2 * k + 1) := by omega
      rw [h4k2]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]⟩ (dvd_lcm3_3 _ _ _)
  have hcop2 : Nat.Coprime (2 * k + 1) 2 := coprime_odd_two (by omega)
  have hcop8 : Nat.Coprime (2 * k + 1) 8 := by
    have h4 : Nat.Coprime (2 * k + 1) 4 := hcop2.mul_right hcop2
    exact h4.mul_right hcop2
  have hcop8k : Nat.Coprime (8 * k) (2 * k + 1) :=
    (hcop8.mul_right (coprime_two_mul_self k)).symm
  have hprod := hcop8k.mul_dvd_of_dvd_of_dvd h8k h2k1
  have heq : 8 * k * (2 * k + 1) = (4 * k) * (4 * k + 2) := by
    have h4k2 : 4 * k + 2 = 2 * (2 * k + 1) := by omega
    have h8 : (8 : Nat) = 4 * 2 := by decide
    rw [h4k2, h8]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [heq] at hprod
  exact hprod

/-- Master Lemma B3 (`m = 4*k + 2`, `2 ∣ c`). -/
private theorem master_even_mod4_2 {k a b c : Nat}
    (hc2 : 2 ∣ c)
    (ha : a ∣ (4 * k + 2 + 1) * (4 * k + 2 + 2))
    (hb : b ∣ (4 * k + 2) * (4 * k + 2 + 2))
    (hc : c ∣ (4 * k + 2) * (4 * k + 2 + 1)) :
    lcm3 (a * (4 * k + 2)) (b * (4 * k + 2 + 1)) (c * (4 * k + 2 + 2)) =
      (4 * k + 2) * (4 * k + 2 + 1) * (4 * k + 2 + 2) := by
  apply Nat.dvd_antisymm (lcm3_mul_dvd ha hb hc)
  apply even_finish
  rcases hc2 with ⟨c', rfl⟩
  have h2k1 : 2 * k + 1 ∣ lcm3 (a * (4 * k + 2)) (b * (4 * k + 2 + 1)) (2 * c' * (4 * k + 2 + 2)) :=
    Nat.dvd_trans ⟨2 * a, by
      have h4k2 : 4 * k + 2 = 2 * (2 * k + 1) := by omega
      rw [h4k2]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]⟩ (dvd_lcm3_1 _ _ _)
  have h8k1 : 8 * (k + 1) ∣ lcm3 (a * (4 * k + 2)) (b * (4 * k + 2 + 1)) (2 * c' * (4 * k + 2 + 2)) :=
    Nat.dvd_trans ⟨c', by
      have h4k4 : 4 * k + 2 + 2 = 4 * (k + 1) := by omega
      rw [h4k4]
      have : 2 * c' * (4 * (k + 1)) = (2 * 4) * (k + 1) * c' := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      exact this⟩ (dvd_lcm3_3 _ _ _)
  have hcop2 : Nat.Coprime (2 * k + 1) 2 := coprime_odd_two (by omega)
  have hcop8 : Nat.Coprime (2 * k + 1) 8 := (hcop2.mul_right hcop2).mul_right hcop2
  have hcop : Nat.Coprime (2 * k + 1) (8 * (k + 1)) :=
    hcop8.mul_right (coprime_two_mul_succ k)
  have hprod := hcop.mul_dvd_of_dvd_of_dvd h2k1 h8k1
  have heq : (2 * k + 1) * (8 * (k + 1)) = (4 * k + 2) * (4 * k + 2 + 2) := by
    have h4k4 : 4 * k + 2 + 2 = 4 * (k + 1) := by omega
    have h4k2 : 4 * k + 2 = 2 * (2 * k + 1) := by omega
    have h8 : (8 : Nat) = 2 * 4 := by decide
    rw [h4k4, h4k2, h8]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [heq] at hprod
  exact hprod

/-! ### Helper tactic-friendly wrappers for each of the 24 templates -/

private theorem rep_odd {n m a b c : Nat}
    (ha_pos : 1 ≤ a) (hb_pos : 1 ≤ b) (hc_pos : 1 ≤ c) (hm : 1 ≤ m) (hodd : m % 2 = 1)
    (hsum : a * m + b * (m + 1) + c * (m + 2) = n)
    (ha : a ∣ (m + 1) * (m + 2)) (hb : b ∣ m * (m + 2)) (hc : c ∣ m * (m + 1)) : HasRep n :=
  hasRep_of_unordered (Nat.mul_pos ha_pos hm) (Nat.mul_pos hb_pos (by omega))
    (Nat.mul_pos hc_pos (by omega)) hsum hm (master_odd hodd ha hb hc)

private theorem rep_even_both {n k a b c : Nat}
    (ha_pos : 1 ≤ a) (hb_pos : 1 ≤ b) (hc_pos : 1 ≤ c) (hk : 1 ≤ k)
    (ha2 : 2 ∣ a) (hc2 : 2 ∣ c)
    (hsum : a * (2 * k) + b * (2 * k + 1) + c * (2 * k + 2) = n)
    (ha : a ∣ (2 * k + 1) * (2 * k + 2)) (hb : b ∣ (2 * k) * (2 * k + 2))
    (hc : c ∣ (2 * k) * (2 * k + 1)) : HasRep n :=
  hasRep_of_unordered (Nat.mul_pos ha_pos (by omega)) (Nat.mul_pos hb_pos (by omega))
    (Nat.mul_pos hc_pos (by omega)) hsum (by omega) (master_even_both ha2 hc2 ha hb hc)

private theorem rep_mod4_0 {n k a b c : Nat}
    (ha_pos : 1 ≤ a) (hb_pos : 1 ≤ b) (hc_pos : 1 ≤ c) (hk : 1 ≤ k) (ha2 : 2 ∣ a)
    (hsum : a * (4 * k) + b * (4 * k + 1) + c * (4 * k + 2) = n)
    (ha : a ∣ (4 * k + 1) * (4 * k + 2)) (hb : b ∣ (4 * k) * (4 * k + 2))
    (hc : c ∣ (4 * k) * (4 * k + 1)) : HasRep n :=
  hasRep_of_unordered (Nat.mul_pos ha_pos (by omega)) (Nat.mul_pos hb_pos (by omega))
    (Nat.mul_pos hc_pos (by omega)) hsum (by omega) (master_even_mod4_0 ha2 ha hb hc)

private theorem rep_mod4_2 {n k a b c : Nat}
    (ha_pos : 1 ≤ a) (hb_pos : 1 ≤ b) (hc_pos : 1 ≤ c) (hc2 : 2 ∣ c)
    (hsum : a * (4 * k + 2) + b * (4 * k + 2 + 1) + c * (4 * k + 2 + 2) = n)
    (ha : a ∣ (4 * k + 2 + 1) * (4 * k + 2 + 2)) (hb : b ∣ (4 * k + 2) * (4 * k + 2 + 2))
    (hc : c ∣ (4 * k + 2) * (4 * k + 2 + 1)) : HasRep n :=
  hasRep_of_unordered (Nat.mul_pos ha_pos (by omega)) (Nat.mul_pos hb_pos (by omega))
    (Nat.mul_pos hc_pos (by omega)) hsum (by omega) (master_even_mod4_2 hc2 ha hb hc)

/-! ### Divisibility helpers for the 24 templates -/

private theorem dvd_of_mod_zero {d x : Nat} (h : x % d = 0) : d ∣ x :=
  Nat.dvd_of_mod_eq_zero h

private theorem dvd_mul_of_left {d a b : Nat} (h : d ∣ a) : d ∣ a * b :=
  Nat.dvd_trans h (Nat.dvd_mul_right a b)

private theorem dvd_mul_of_right {d a b : Nat} (h : d ∣ b) : d ∣ a * b :=
  Nat.dvd_trans h (Nat.dvd_mul_left b a)

private theorem mul_dvd_mul_of_dvd {a b c d : Nat} (h1 : a ∣ c) (h2 : b ∣ d) : a * b ∣ c * d :=
  Nat.mul_dvd_mul h1 h2

/-! ### The 24 Templates -/

private theorem tpl_1 {n : Nat} (hge : 6 ≤ n) (hmod : n % 6 = 0) : HasRep n := by
  let t := (n - 6) / 6
  exact rep_odd (m := 2 * t + 1) (a := 1) (b := 1) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (Nat.one_dvd _) (Nat.one_dvd _) (Nat.one_dvd _)

private theorem tpl_2 {n : Nat} (hge : 9 ≤ n) (hmod : n % 8 = 1) : HasRep n := by
  let t := (n - 9) / 8
  exact rep_odd (m := 2 * t + 1) (a := 1) (b := 1) (c := 2)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (Nat.one_dvd _) (Nat.one_dvd _) (dvd_mul_of_right (dvd_of_mod_zero (by omega)))

private theorem tpl_3 {n : Nat} (hge : 7 ≤ n) (hmod : n % 8 = 7) : HasRep n := by
  let t := (n - 7) / 8
  exact rep_odd (m := 2 * t + 1) (a := 2) (b := 1) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (dvd_mul_of_left (dvd_of_mod_zero (by omega))) (Nat.one_dvd _) (Nat.one_dvd _)

private theorem tpl_4 {n : Nat} (hge : 10 ≤ n) (hmod : n % 10 = 0) : HasRep n := by
  let t := (n - 10) / 10
  exact rep_odd (m := 2 * t + 1) (a := 2) (b := 1) (c := 2)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (dvd_mul_of_left (dvd_of_mod_zero (by omega))) (Nat.one_dvd _)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega)))

private theorem tpl_5 {n : Nat} (hge : 15 ≤ n) (hmod : n % 10 = 5) : HasRep n := by
  let k := (n - 5) / 10
  exact rep_even_both (k := k) (a := 2) (b := 1) (c := 2)
    (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega))) (Nat.one_dvd _)
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))

private theorem tpl_6 {n : Nat} (hge : 19 ≤ n) (hmod : n % 16 = 3) : HasRep n := by
  let k := (n - 3) / 16
  exact rep_mod4_0 (k := k) (a := 2) (b := 1) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by decide) (by omega)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega))) (Nat.one_dvd _) (Nat.one_dvd _)

private theorem tpl_7 {n : Nat} (hge : 24 ≤ n) (hmod : n % 16 = 8) : HasRep n := by
  let k := (n - 8) / 16
  exact rep_even_both (k := k) (a := 2) (b := 4) (c := 2)
    (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega)))
    (mul_dvd_mul_of_dvd (dvd_of_mod_zero (d := 2) (by omega)) (dvd_of_mod_zero (d := 2) (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))

private theorem tpl_8 {n : Nat} (hge : 13 ≤ n) (hmod : n % 16 = 13) : HasRep n := by
  let k := (n - 13) / 16
  exact rep_mod4_2 (k := k) (a := 1) (b := 1) (c := 2)
    (by decide) (by decide) (by decide) (by decide) (by omega)
    (Nat.one_dvd _) (Nat.one_dvd _) (dvd_mul_of_left (dvd_of_mod_zero (by omega)))

private theorem tpl_9 {n : Nat} (hge : 24 ≤ n) (hmod : n % 20 = 4) : HasRep n := by
  let k := (n - 4) / 20
  exact rep_mod4_0 (k := k) (a := 2) (b := 2) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by decide) (by omega)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega))) (Nat.one_dvd _)

private theorem tpl_10 {n : Nat} (hge : 16 ≤ n) (hmod : n % 20 = 16) : HasRep n := by
  let k := (n - 16) / 20
  exact rep_mod4_2 (k := k) (a := 1) (b := 2) (c := 2)
    (by decide) (by decide) (by decide) (by decide) (by omega)
    (Nat.one_dvd _) (dvd_mul_of_left (dvd_of_mod_zero (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))

private theorem tpl_11 {n : Nat} (hge : 27 ≤ n) (hmod : n % 24 = 3) : HasRep n := by
  let t := (n - 27) / 24
  exact rep_odd (m := 4 * t + 3) (a := 1) (b := 1) (c := 4)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (Nat.one_dvd _) (Nat.one_dvd _) (dvd_mul_of_right (dvd_of_mod_zero (by omega)))

private theorem tpl_12 {n : Nat} (hge : 21 ≤ n) (hmod : n % 24 = 21) : HasRep n := by
  let t := (n - 21) / 24
  exact rep_odd (m := 4 * t + 3) (a := 4) (b := 1) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (dvd_mul_of_left (dvd_of_mod_zero (by omega))) (Nat.one_dvd _) (Nat.one_dvd _)

private theorem tpl_13 {n : Nat} (hge : 32 ≤ n) (hmod : n % 30 = 2) : HasRep n := by
  let t := (n - 32) / 30
  exact rep_odd (m := 6 * t + 5) (a := 1) (b := 1) (c := 3)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (Nat.one_dvd _) (Nat.one_dvd _) (dvd_mul_of_right (dvd_of_mod_zero (by omega)))

private theorem tpl_14 {n : Nat} (hge : 8 ≤ n) (hmod : n % 30 = 8) : HasRep n := by
  let t := (n - 8) / 30
  exact rep_odd (m := 6 * t + 1) (a := 3) (b := 1) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega))) (Nat.one_dvd _) (Nat.one_dvd _)

private theorem tpl_15 {n : Nat} (hge : 22 ≤ n) (hmod : n % 30 = 22) : HasRep n := by
  let t := (n - 22) / 30
  exact rep_odd (m := 6 * t + 3) (a := 1) (b := 1) (c := 3)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (Nat.one_dvd _) (Nat.one_dvd _) (dvd_mul_of_left (dvd_of_mod_zero (by omega)))

private theorem tpl_16 {n : Nat} (hge : 28 ≤ n) (hmod : n % 30 = 28) : HasRep n := by
  let t := (n - 28) / 30
  exact rep_odd (m := 6 * t + 5) (a := 3) (b := 1) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (dvd_mul_of_left (dvd_of_mod_zero (by omega))) (Nat.one_dvd _) (Nat.one_dvd _)

private theorem tpl_17 {n : Nat} (hge : 53 ≤ n) (hmod : n % 48 = 5) : HasRep n := by
  let t := (n - 53) / 48
  exact rep_odd (m := 6 * t + 5) (a := 1) (b := 1) (c := 6)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (Nat.one_dvd _) (Nat.one_dvd _) (dvd_mul_of_right (dvd_of_mod_zero (by omega)))

private theorem tpl_18 {n : Nat} (hge : 11 ≤ n) (hmod : n % 48 = 11) : HasRep n := by
  let t := (n - 11) / 48
  exact rep_odd (m := 6 * t + 1) (a := 6) (b := 1) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (mul_dvd_mul_of_dvd (dvd_of_mod_zero (d := 2) (by omega)) (dvd_of_mod_zero (d := 3) (by omega)))
    (Nat.one_dvd _) (Nat.one_dvd _)

private theorem tpl_19 {n : Nat} (hge : 37 ≤ n) (hmod : n % 48 = 37) : HasRep n := by
  let t := (n - 37) / 48
  exact rep_odd (m := 6 * t + 3) (a := 1) (b := 1) (c := 6)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (Nat.one_dvd _) (Nat.one_dvd _)
    (mul_dvd_mul_of_dvd (dvd_of_mod_zero (d := 3) (by omega)) (dvd_of_mod_zero (d := 2) (by omega)))

private theorem tpl_20 {n : Nat} (hge : 43 ≤ n) (hmod : n % 48 = 43) : HasRep n := by
  let t := (n - 43) / 48
  exact rep_odd (m := 6 * t + 5) (a := 6) (b := 1) (c := 1)
    (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (dvd_mul_of_left (dvd_of_mod_zero (by omega))) (Nat.one_dvd _) (Nat.one_dvd _)

private theorem tpl_21 {n : Nat} (hge : 74 ≤ n) (hmod : n % 60 = 14) : HasRep n := by
  let t := (n - 74) / 60
  exact rep_even_both (k := 3 * t + 3) (a := 2) (b := 2) (c := 6)
    (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))

private theorem tpl_22 {n : Nat} (hge : 26 ≤ n) (hmod : n % 60 = 26) : HasRep n := by
  let t := (n - 26) / 60
  exact rep_even_both (k := 3 * t + 1) (a := 6) (b := 2) (c := 2)
    (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (mul_dvd_mul_of_dvd (dvd_of_mod_zero (d := 3) (by omega)) (dvd_of_mod_zero (d := 2) (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))

private theorem tpl_23 {n : Nat} (hge : 34 ≤ n) (hmod : n % 60 = 34) : HasRep n := by
  let t := (n - 34) / 60
  exact rep_even_both (k := 3 * t + 1) (a := 2) (b := 2) (c := 6)
    (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))
    (mul_dvd_mul_of_dvd (dvd_of_mod_zero (d := 2) (by omega)) (dvd_of_mod_zero (d := 3) (by omega)))

private theorem tpl_24 {n : Nat} (hge : 46 ≤ n) (hmod : n % 60 = 46) : HasRep n := by
  let t := (n - 46) / 60
  exact rep_even_both (k := 3 * t + 2) (a := 6) (b := 2) (c := 2)
    (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by omega)
    (dvd_mul_of_right (dvd_of_mod_zero (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))
    (dvd_mul_of_left (dvd_of_mod_zero (by omega)))

/-! ### Verification that the 24 congruences cover all residues mod 240 -/

private def isCovered240 (r : Nat) : Bool :=
  r % 6 == 0 || r % 8 == 1 || r % 8 == 7 || r % 10 == 0 || r % 10 == 5 ||
  r % 16 == 3 || r % 16 == 8 || r % 16 == 13 || r % 20 == 4 || r % 20 == 16 ||
  r % 24 == 3 || r % 24 == 21 || r % 30 == 2 || r % 30 == 8 || r % 30 == 22 ||
  r % 30 == 28 || r % 48 == 5 || r % 48 == 11 || r % 48 == 37 || r % 48 == 43 ||
  r % 60 == 14 || r % 60 == 26 || r % 60 == 34 || r % 60 == 46

private theorem cover_mod_240 : ∀ r < 240, isCovered240 r = true := by
  decide +kernel

/-! ### Main Theorems -/

/-- The lone finite case `n = 14 = 6 + 6 + 2`, `lcm(6, 6, 2) = 6 = 1 * 2 * 3`. -/
private theorem rep_14 : HasRep 14 :=
  ⟨6, 6, 2, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Main Theorem 1: For every `n >= 6`, `A392684(n) > 0`. -/
theorem a392684_pos (n : Nat) (hn : 6 ≤ n) : HasRep n := by
  by_cases h14 : n = 14
  · subst h14; exact rep_14
  · have hcov := cover_mod_240 (n % 240) (Nat.mod_lt n (by decide))
    simp only [isCovered240, Bool.or_eq_true, beq_iff_eq] at hcov
    rcases hcov with ((((((((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
    · have hm : n % 6 = 0 := by rw [← Nat.mod_mod_of_dvd n (by decide : 6 ∣ 240)]; exact h
      exact tpl_1 (by omega) hm
    · have hm : n % 8 = 1 := by rw [← Nat.mod_mod_of_dvd n (by decide : 8 ∣ 240)]; exact h
      exact tpl_2 (by omega) hm
    · have hm : n % 8 = 7 := by rw [← Nat.mod_mod_of_dvd n (by decide : 8 ∣ 240)]; exact h
      exact tpl_3 (by omega) hm
    · have hm : n % 10 = 0 := by rw [← Nat.mod_mod_of_dvd n (by decide : 10 ∣ 240)]; exact h
      exact tpl_4 (by omega) hm
    · have hm : n % 10 = 5 := by rw [← Nat.mod_mod_of_dvd n (by decide : 10 ∣ 240)]; exact h
      exact tpl_5 (by omega) hm
    · have hm : n % 16 = 3 := by rw [← Nat.mod_mod_of_dvd n (by decide : 16 ∣ 240)]; exact h
      exact tpl_6 (by omega) hm
    · have hm : n % 16 = 8 := by rw [← Nat.mod_mod_of_dvd n (by decide : 16 ∣ 240)]; exact h
      by_cases h8 : n = 8
      · subst h8; exact tpl_14 (by decide) (by decide)
      · exact tpl_7 (by omega) hm
    · have hm : n % 16 = 13 := by rw [← Nat.mod_mod_of_dvd n (by decide : 16 ∣ 240)]; exact h
      exact tpl_8 (by omega) hm
    · have hm : n % 20 = 4 := by rw [← Nat.mod_mod_of_dvd n (by decide : 20 ∣ 240)]; exact h
      exact tpl_9 (by omega) hm
    · have hm : n % 20 = 16 := by rw [← Nat.mod_mod_of_dvd n (by decide : 20 ∣ 240)]; exact h
      exact tpl_10 (by omega) hm
    · have hm : n % 24 = 3 := by rw [← Nat.mod_mod_of_dvd n (by decide : 24 ∣ 240)]; exact h
      exact tpl_11 (by omega) hm
    · have hm : n % 24 = 21 := by rw [← Nat.mod_mod_of_dvd n (by decide : 24 ∣ 240)]; exact h
      exact tpl_12 (by omega) hm
    · have hm : n % 30 = 2 := by rw [← Nat.mod_mod_of_dvd n (by decide : 30 ∣ 240)]; exact h
      exact tpl_13 (by omega) hm
    · have hm : n % 30 = 8 := by rw [← Nat.mod_mod_of_dvd n (by decide : 30 ∣ 240)]; exact h
      exact tpl_14 (by omega) hm
    · have hm : n % 30 = 22 := by rw [← Nat.mod_mod_of_dvd n (by decide : 30 ∣ 240)]; exact h
      exact tpl_15 (by omega) hm
    · have hm : n % 30 = 28 := by rw [← Nat.mod_mod_of_dvd n (by decide : 30 ∣ 240)]; exact h
      exact tpl_16 (by omega) hm
    · have hm : n % 48 = 5 := by rw [← Nat.mod_mod_of_dvd n (by decide : 48 ∣ 240)]; exact h
      exact tpl_17 (by omega) hm
    · have hm : n % 48 = 11 := by rw [← Nat.mod_mod_of_dvd n (by decide : 48 ∣ 240)]; exact h
      exact tpl_18 (by omega) hm
    · have hm : n % 48 = 37 := by rw [← Nat.mod_mod_of_dvd n (by decide : 48 ∣ 240)]; exact h
      exact tpl_19 (by omega) hm
    · have hm : n % 48 = 43 := by rw [← Nat.mod_mod_of_dvd n (by decide : 48 ∣ 240)]; exact h
      exact tpl_20 (by omega) hm
    · have hm : n % 60 = 14 := by rw [← Nat.mod_mod_of_dvd n (by decide : 60 ∣ 240)]; exact h
      exact tpl_21 (by omega) hm
    · have hm : n % 60 = 26 := by rw [← Nat.mod_mod_of_dvd n (by decide : 60 ∣ 240)]; exact h
      exact tpl_22 (by omega) hm
    · have hm : n % 60 = 34 := by rw [← Nat.mod_mod_of_dvd n (by decide : 60 ∣ 240)]; exact h
      exact tpl_23 (by omega) hm
    · have hm : n % 60 = 46 := by rw [← Nat.mod_mod_of_dvd n (by decide : 60 ∣ 240)]; exact h
      exact tpl_24 (by omega) hm

/-- Main Theorem 2: No integer `1 <= n <= 5` has a representation (`N(3) = 6`). -/
theorem a392684_zero_lt_six (n : Nat) (hn : n < 6) : ¬ HasRep n := by
  rintro ⟨x, y, z, m, hz, hzy, hyx, hsum, hm, hlcm⟩
  have h6 : 6 ≤ m * (m + 1) * (m + 2) := by
    have h1 : 1 * 2 * 3 ≤ m * (m + 1) * (m + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul hm (by omega)) (by omega)
    omega
  have hle : lcm3 x y z < 6 := by
    have hdec : ∀ x < 6, ∀ y < 6, ∀ z < 6,
        (1 ≤ z ∧ z ≤ y ∧ y ≤ x ∧ x + y + z < 6) → lcm3 x y z < 6 := by
      decide
    exact hdec x (by omega) y (by omega) z (by omega) ⟨hz, hzy, hyx, by omega⟩
  omega

end A392684

#print axioms A392684.a392684_pos
#print axioms A392684.a392684_zero_lt_six
