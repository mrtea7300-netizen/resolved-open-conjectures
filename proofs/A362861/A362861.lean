/-
  Complete formal proof of OEIS A362861 Conjecture 1(i) (both parts) and
  Conjecture 1(ii) (first part):
    1. `exact_characterization_5_5`: For every n >= 1, 2*n is a sum of distinct
       elements of {5^a + 5^b : a, b >= 0} iff n is not in
       {2, 7, 10, 11, 12, 27, 35, 50, 51, 52, 55, 60, 135, 255}.
    2. `all_even_rep_3_3`: For every n >= 1, 2*n is a sum of distinct elements
       of {3^a + 3^b : a, b >= 0}.
    3. `all_even_rep_3_7`: For every n >= 1, 2*n is a sum of distinct elements
       of {3^a + 7^b : a, b >= 0}.

  Zero external dependencies (pure Lean 4 core). Zero `sorry`.
-/

namespace A362861

def IsForm (k m x : Nat) : Prop :=
  ∃ a b : Nat, x = k ^ a + m ^ b

def IsRep (k m n : Nat) : Prop :=
  ∃ L : List Nat, L.Nodup ∧ (∀ x ∈ L, IsForm k m x) ∧ L.sum = n

def IsHalfForm (k m h : Nat) : Prop :=
  IsForm k m (2 * h)

/-! ### Fast bitset subset-sum verifier and Brown's one-step extension -/

def subsetBits : List Nat → Nat
  | [] => 1
  | x :: xs =>
    let b := subsetBits xs
    b ||| (b <<< x)

theorem testBit_one_iff (n : Nat) : Nat.testBit 1 n = true ↔ n = 0 := by
  cases n with
  | zero => decide
  | succ k =>
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have h2 : 1 < 2 ^ (k + 1) := by
      have : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      have hpos : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)
      omega
    rw [Nat.div_eq_of_lt h2]
    simp

theorem subsetBits_sound : ∀ (L : List Nat) (n : Nat),
    Nat.testBit (subsetBits L) n = true → ∃ sub : List Nat, sub.Sublist L ∧ sub.sum = n
  | [], n, h => by
    have hn : n = 0 := (testBit_one_iff n).mp h
    exact ⟨[], List.Sublist.slnil, hn.symm⟩
  | x :: xs, n, h => by
    simp only [subsetBits, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h1 | h2
    · rcases subsetBits_sound xs n h1 with ⟨sub, hsub, hsum⟩
      exact ⟨sub, List.Sublist.cons x hsub, hsum⟩
    · rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      rcases h2 with ⟨hle, hbit⟩
      rcases subsetBits_sound xs (n - x) hbit with ⟨sub, hsub, hsum⟩
      refine ⟨x :: sub, List.Sublist.cons_cons x hsub, ?_⟩
      simp only [List.sum_cons]
      omega

theorem sublist_nodup {L sub : List Nat} (hsub : sub.Sublist L) (hnd : L.Nodup) : sub.Nodup := by
  induction hsub with
  | slnil => exact List.nodup_nil
  | cons a _ ih => exact ih (List.nodup_cons.mp hnd).2
  | cons_cons a hsub' ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    exact List.nodup_cons.mpr ⟨fun ha => hna (hsub'.subset ha), ih hnd'⟩

theorem map_double_nodup {L : List Nat} (hnd : L.Nodup) : (L.map (2 * ·)).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have ⟨hnx, hnd'⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, ih hnd'⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, heq⟩
    simp only at heq
    have hxy : x = y := by omega
    subst hxy
    exact hnx hy

theorem map_double_sum (L : List Nat) : (L.map (2 * ·)).sum = 2 * L.sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem half_rep_to_even_rep {k m n : Nat} {L sub : List Nat}
    (hsub : sub.Sublist L) (hnd : L.Nodup) (hform : ∀ h ∈ L, IsHalfForm k m h)
    (hsum : sub.sum = n) : IsRep k m (2 * n) := by
  refine ⟨sub.map (2 * ·), map_double_nodup (sublist_nodup hsub hnd), ?_, ?_⟩
  · intro x hx
    rcases List.mem_map.mp hx with ⟨h, hh, rfl⟩
    exact hform h (hsub.subset hh)
  · rw [map_double_sum, hsum]

theorem add_one_interval {L : List Nat} {lo hi x : Nat}
    (hlohi : lo ≤ hi)
    (hcov : ∀ n, lo ≤ n → n ≤ hi → ∃ sub : List Nat, sub.Sublist L ∧ sub.sum = n)
    (hx : x ≤ hi - lo + 1) :
    ∀ n, lo ≤ n → n ≤ hi + x → ∃ sub : List Nat, sub.Sublist (x :: L) ∧ sub.sum = n := by
  intro n hlo hhi
  by_cases hle : n ≤ hi
  · rcases hcov n hlo hle with ⟨sub, hsub, hsum⟩
    exact ⟨sub, List.Sublist.cons x hsub, hsum⟩
  · have h1 : lo ≤ n - x := by omega
    have h2 : n - x ≤ hi := by omega
    rcases hcov (n - x) h1 h2 with ⟨sub, hsub, hsum⟩
    refine ⟨x :: sub, List.Sublist.cons_cons x hsub, ?_⟩
    simp only [List.sum_cons]
    omega

theorem odd_pow_odd (p : Nat) (hp : p % 2 = 1) (a : Nat) : p ^ a % 2 = 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, hp]

theorem two_mul_half_pow_sum (k m a b : Nat) (hk : k % 2 = 1) (hm : m % 2 = 1) :
    2 * ((k ^ a + m ^ b) / 2) = k ^ a + m ^ b := by
  have h1 := odd_pow_odd k hk a
  have h2 := odd_pow_odd m hm b
  omega

theorem isHalfForm_pow_sum (k m a b : Nat) (hk : k % 2 = 1) (hm : m % 2 = 1) :
    IsHalfForm k m ((k ^ a + m ^ b) / 2) :=
  ⟨a, b, two_mul_half_pow_sum k m a b hk hm⟩

/-! ### Subset-sum completeness for exclusion proofs -/

theorem mem_le_sum {L : List Nat} {x : Nat} (hx : x ∈ L) : x ≤ L.sum := by
  induction L with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.sum_cons]
    cases List.mem_cons.mp hx with
    | inl h => subst h; omega
    | inr h => have := ih h; omega

theorem erase_sum_add {L : List Nat} {u : Nat} (hu : u ∈ L) :
    u + (L.erase u).sum = L.sum := by
  induction L with
  | nil => cases hu
  | cons y ys ih =>
    by_cases hy : y == u
    · have hyeq : y = u := beq_iff_eq.mp hy
      subst hyeq
      simp [List.erase_cons_head]
    · have hyne : y ≠ u := fun h => hy (beq_iff_eq.mpr h)
      have hu' : u ∈ ys := by
        cases List.mem_cons.mp hu with
        | inl h => exact absurd h.symm hyne
        | inr h => exact h
      rw [List.erase_cons_tail (by simp [hyne])]
      simp only [List.sum_cons]
      have := ih hu'
      omega

theorem erase_not_mem_of_nodup {L : List Nat} {u : Nat} (hnd : L.Nodup) : u ∉ L.erase u := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    have ⟨hny, hnd'⟩ := List.nodup_cons.mp hnd
    by_cases hy : y = u
    · subst hy
      simp [List.erase_cons_head, hny]
    · rw [List.erase_cons_tail (by simp [hy])]
      simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm hy, ih hnd'⟩

theorem subsetBits_complete : ∀ (U L : List Nat),
    L.Nodup → (∀ x ∈ L, x ∈ U) → Nat.testBit (subsetBits U) L.sum = true
  | [], L, _, hsub => by
    cases L with
    | nil => decide
    | cons x xs => cases hsub x (List.mem_cons_self ..)
  | u :: us, L, hnd, hsub => by
    simp only [subsetBits, Nat.testBit_or, Bool.or_eq_true]
    by_cases hu : u ∈ L
    · right
      rw [Nat.testBit_shiftLeft]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have hsum := erase_sum_add hu
      have hle : u ≤ L.sum := by omega
      refine ⟨hle, ?_⟩
      have heq : L.sum - u = (L.erase u).sum := by omega
      rw [heq]
      apply subsetBits_complete us (L.erase u) (hnd.erase u)
      intro x hx
      have hxL : x ∈ L := List.mem_of_mem_erase hx
      have hne : x ≠ u := fun h => by
        subst h
        exact erase_not_mem_of_nodup hnd hx
      cases List.mem_cons.mp (hsub x hxL) with
      | inl h => exact absurd h hne
      | inr h => exact h
    · left
      apply subsetBits_complete us L hnd
      intro x hx
      cases List.mem_cons.mp (hsub x hx) with
      | inl h => subst h; exact absurd hx hu
      | inr h => exact h

/-! =======================================================================
    PART 1: A362861 Conjecture 1(i), Part A — {5^a + 5^b}
    ======================================================================= -/

def exc55 : List Nat := [2, 7, 10, 11, 12, 27, 35, 50, 51, 52, 55, 60, 135, 255]

def base5 : List Nat := [1, 3, 5, 13, 15, 25, 63, 65, 75, 125, 313, 315, 325, 375, 625]

theorem base5_nodup : base5.Nodup := by decide

theorem base5_form : ∀ h ∈ base5, IsHalfForm 5 5 h := by
  intro h hh
  simp only [base5, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, rfl⟩
  · exact ⟨1, 0, rfl⟩
  · exact ⟨1, 1, rfl⟩
  · exact ⟨2, 0, rfl⟩
  · exact ⟨2, 1, rfl⟩
  · exact ⟨2, 2, rfl⟩
  · exact ⟨3, 0, rfl⟩
  · exact ⟨3, 1, rfl⟩
  · exact ⟨3, 2, rfl⟩
  · exact ⟨3, 3, rfl⟩
  · exact ⟨4, 0, rfl⟩
  · exact ⟨4, 1, rfl⟩
  · exact ⟨4, 2, rfl⟩
  · exact ⟨4, 3, rfl⟩
  · exact ⟨4, 4, rfl⟩

theorem base5_covers_bool :
    let b := subsetBits base5
    (List.range 1832).all (fun i => Nat.testBit b (256 + i)) = true := by
  decide +kernel

theorem base5_covers_256_2087 :
    ∀ n, 256 ≤ n → n ≤ 2087 → ∃ sub : List Nat, sub.Sublist base5 ∧ sub.sum = n := by
  intro n hlo hhi
  have hmem : n - 256 ∈ List.range 1832 := List.mem_range.mpr (by omega)
  have hbit : Nat.testBit (subsetBits base5) (256 + (n - 256)) = true :=
    List.all_eq_true.mp base5_covers_bool (n - 256) hmem
  have heq : 256 + (n - 256) = n := by omega
  rw [heq] at hbit
  exact subsetBits_sound base5 n hbit

def base5Ext : List Nat := 1875 :: 1625 :: 1575 :: 1565 :: 1563 :: base5

theorem base5Ext_nodup : base5Ext.Nodup := by decide

theorem base5Ext_form : ∀ h ∈ base5Ext, IsHalfForm 5 5 h := by
  intro h hh
  simp only [base5Ext, List.mem_cons] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | hh
  · exact ⟨5, 4, rfl⟩
  · exact ⟨5, 3, rfl⟩
  · exact ⟨5, 2, rfl⟩
  · exact ⟨5, 1, rfl⟩
  · exact ⟨5, 0, rfl⟩
  · exact base5_form h hh

theorem base5Ext_lt : ∀ h ∈ base5Ext, 2 * h < 5 ^ 6 := by decide

theorem base5Ext_covers :
    ∀ n, 256 ≤ n → n ≤ 10290 → ∃ sub : List Nat, sub.Sublist base5Ext ∧ sub.sum = n := by
  have h1 := add_one_interval (by omega) base5_covers_256_2087 (x := 1563) (by omega)
  have h2 := add_one_interval (by omega) h1 (x := 1565) (by omega)
  have h3 := add_one_interval (by omega) h2 (x := 1575) (by omega)
  have h4 := add_one_interval (by omega) h3 (x := 1625) (by omega)
  exact add_one_interval (by omega) h4 (x := 1875) (by omega)

def chain5 : Nat → List Nat
  | 0 => base5Ext
  | k + 1 =>
    ((5 ^ (k + 6) + 625) / 2) :: ((5 ^ (k + 6) + 125) / 2) :: ((5 ^ (k + 6) + 25) / 2) ::
    ((5 ^ (k + 6) + 5) / 2) :: ((5 ^ (k + 6) + 1) / 2) :: chain5 k

def upper5 : Nat → Nat
  | 0 => 10290
  | k + 1 => upper5 k + (5 ^ (k + 7) + 781) / 2

theorem pow5_ge (k : Nat) : 5 ^ (k + 6) ≥ 15625 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have : 5 ^ (k + 1 + 6) = 5 ^ (k + 6) * 5 := by
      rw [show k + 1 + 6 = (k + 6) + 1 by omega, Nat.pow_succ]
    omega

theorem pow5_step (k : Nat) : 5 ^ (k + 7) = 5 * 5 ^ (k + 6) := by
  rw [show k + 7 = (k + 6) + 1 by omega, Nat.pow_succ]
  omega

theorem chain5_lt (k : Nat) : ∀ h ∈ chain5 k, 2 * h < 5 ^ (k + 6) := by
  induction k with
  | zero => exact base5Ext_lt
  | succ k ih =>
    intro h hh
    have hstep := pow5_step k
    have hge := pow5_ge k
    have hidx : k + 1 + 6 = k + 7 := by omega
    rw [hidx, hstep]
    simp only [chain5, List.mem_cons] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | hh
    · omega
    · omega
    · omega
    · omega
    · omega
    · have := ih h hh; omega

theorem chain5_nodup (k : Nat) : (chain5 k).Nodup := by
  induction k with
  | zero => exact base5Ext_nodup
  | succ k ih =>
    have hlt := chain5_lt k
    have hodd := odd_pow_odd 5 (by decide) (k + 6)
    have hnot : ∀ c ≥ 1, c % 2 = 1 → (5 ^ (k + 6) + c) / 2 ∉ chain5 k := by
      intro c hc hco hmem
      have := hlt _ hmem
      omega
    simp only [chain5, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨by omega, by omega, by omega, by omega, hnot 625 (by omega) (by decide)⟩,
            ⟨by omega, by omega, by omega, hnot 125 (by omega) (by decide)⟩,
            ⟨by omega, by omega, hnot 25 (by omega) (by decide)⟩,
            ⟨by omega, hnot 5 (by omega) (by decide)⟩,
            hnot 1 (by omega) (by decide), ih⟩

theorem chain5_form (k : Nat) : ∀ h ∈ chain5 k, IsHalfForm 5 5 h := by
  induction k with
  | zero => exact base5Ext_form
  | succ k ih =>
    intro h hh
    simp only [chain5, List.mem_cons] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | hh
    · exact isHalfForm_pow_sum 5 5 (k + 6) 4 (by decide) (by decide)
    · exact isHalfForm_pow_sum 5 5 (k + 6) 3 (by decide) (by decide)
    · exact isHalfForm_pow_sum 5 5 (k + 6) 2 (by decide) (by decide)
    · exact isHalfForm_pow_sum 5 5 (k + 6) 1 (by decide) (by decide)
    · exact isHalfForm_pow_sum 5 5 (k + 6) 0 (by decide) (by decide)
    · exact ih h hh

theorem upper5_ge (k : Nat) : upper5 k - 255 ≥ (5 ^ (k + 6) + 625) / 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [upper5]
    have hidx : 5 ^ (k + 1 + 6) = 5 ^ (k + 7) := by rw [show k + 1 + 6 = k + 7 by omega]
    rw [hidx]
    have hu : upper5 k ≥ 255 := by
      have hge := pow5_ge k
      generalize 5 ^ (k + 6) = q at ih hge
      omega
    clear ih
    generalize 5 ^ (k + 7) = p
    omega

theorem chain5_covers (k : Nat) :
    ∀ n, 256 ≤ n → n ≤ upper5 k → ∃ sub : List Nat, sub.Sublist (chain5 k) ∧ sub.sum = n := by
  induction k with
  | zero => exact base5Ext_covers
  | succ k ih =>
    have hge := upper5_ge k
    have hpow := pow5_ge k
    have hodd := odd_pow_odd 5 (by decide) (k + 6)
    have h1 := add_one_interval (by omega) ih (x := (5 ^ (k + 6) + 1) / 2) (by omega)
    have h2 := add_one_interval (by omega) h1 (x := (5 ^ (k + 6) + 5) / 2) (by omega)
    have h3 := add_one_interval (by omega) h2 (x := (5 ^ (k + 6) + 25) / 2) (by omega)
    have h4 := add_one_interval (by omega) h3 (x := (5 ^ (k + 6) + 125) / 2) (by omega)
    have h5 := add_one_interval (by omega) h4 (x := (5 ^ (k + 6) + 625) / 2) (by omega)
    have heq : upper5 (k + 1) =
        ((((upper5 k + (5 ^ (k + 6) + 1) / 2) + (5 ^ (k + 6) + 5) / 2) +
          (5 ^ (k + 6) + 25) / 2) + (5 ^ (k + 6) + 125) / 2) + (5 ^ (k + 6) + 625) / 2 := by
      simp only [upper5]
      have hstep := pow5_step k
      omega
    intro n hlo hhi
    rw [heq] at hhi
    exact h5 n hlo hhi

theorem nat_le_pow5_half (n : Nat) : n ≤ (5 ^ (n + 6) + 625) / 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hge := pow5_ge n
    have : 5 ^ (n + 1 + 6) = 5 ^ (n + 6) * 5 := by
      rw [show n + 1 + 6 = (n + 6) + 1 by omega, Nat.pow_succ]
    omega

theorem all_ge_256_rep_5_5 (n : Nat) (hn : n ≥ 256) : IsRep 5 5 (2 * n) := by
  have hle : n ≤ upper5 n := by
    have h1 := upper5_ge n
    have h2 := nat_le_pow5_half n
    omega
  rcases chain5_covers n n hn hle with ⟨sub, hsub, hsum⟩
  exact half_rep_to_even_rep hsub (chain5_nodup n) (chain5_form n) hsum

theorem small55_good_bool :
    let b := subsetBits base5
    (List.range 255).all (fun i =>
      let n := i + 1
      (n ∈ exc55) || Nat.testBit b n) = true := by
  decide +kernel

def small55Elems : List Nat := [2, 6, 10, 26, 30, 50, 126, 130, 150, 250]

theorem form55_le_510 (x : Nat) (hf : IsForm 5 5 x) (hle : x ≤ 510) :
    x ∈ small55Elems := by
  rcases hf with ⟨a, b, rfl⟩
  match a, b with
  | 0, 0 | 0, 1 | 0, 2 | 0, 3
  | 1, 0 | 1, 1 | 1, 2 | 1, 3
  | 2, 0 | 2, 1 | 2, 2 | 2, 3
  | 3, 0 | 3, 1 | 3, 2 | 3, 3 => decide
  | a + 4, _ =>
    have hpow : 5 ^ (a + 4) ≥ 5 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have hle1 : 5 ^ (a + 4) ≤ 510 := Nat.le_trans (Nat.le_add_right _ _) hle
    have : 5 ^ 4 = 625 := rfl
    omega
  | _, b + 4 =>
    have hpow : 5 ^ (b + 4) ≥ 5 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have hle2 : 5 ^ (b + 4) ≤ 510 := Nat.le_trans (Nat.le_add_left _ _) hle
    have : 5 ^ 4 = 625 := rfl
    omega

theorem exc55_impossible_bool :
    let b := subsetBits small55Elems
    exc55.all (fun n => !(Nat.testBit b (2 * n))) = true := by
  decide +kernel

theorem exc55_not_rep (n : Nat) (hn : n ∈ exc55) : ¬ IsRep 5 5 (2 * n) := by
  intro ⟨L, hnd, hform, hsum⟩
  have hn255 : n ≤ 255 := by
    simp only [exc55, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hsub : ∀ x ∈ L, x ∈ small55Elems := by
    intro x hx
    have hxle : x ≤ 510 := by
      have := mem_le_sum hx
      omega
    exact form55_le_510 x (hform x hx) hxle
  have hbit := subsetBits_complete small55Elems L hnd hsub
  rw [hsum] at hbit
  have hnot := List.all_eq_true.mp exc55_impossible_bool n hn
  simp [hbit] at hnot

/-- Theorem 1 (A362861 Conjecture 1(i), Part A): Exact characterization of A362861. -/
theorem exact_characterization_5_5 (n : Nat) (hn : n ≥ 1) :
    IsRep 5 5 (2 * n) ↔ n ∉ exc55 := by
  constructor
  · intro hrep hmem
    exact exc55_not_rep n hmem hrep
  · intro hnotmem
    by_cases h256 : n ≥ 256
    · exact all_ge_256_rep_5_5 n h256
    · have hmem : n - 1 ∈ List.range 255 := List.mem_range.mpr (by omega)
      have hbool := List.all_eq_true.mp small55_good_bool (n - 1) hmem
      have heq : (n - 1) + 1 = n := by omega
      simp only [heq, Bool.or_eq_true, decide_eq_true_eq] at hbool
      rcases hbool with hin | hbit
      · exact absurd hin hnotmem
      · rcases subsetBits_sound base5 n hbit with ⟨sub, hsub, hsum⟩
        exact half_rep_to_even_rep hsub base5_nodup base5_form hsum

/-! =======================================================================
    PART 2: A362861 Conjecture 1(i), Part B — {3^a + 3^b}
    ======================================================================= -/

def base3 : List Nat := [1, 2, 3, 5, 6, 9]

theorem base3_nodup : base3.Nodup := by decide

theorem base3_form : ∀ h ∈ base3, IsHalfForm 3 3 h := by
  intro h hh
  simp only [base3, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, rfl⟩
  · exact ⟨1, 0, rfl⟩
  · exact ⟨1, 1, rfl⟩
  · exact ⟨2, 0, rfl⟩
  · exact ⟨2, 1, rfl⟩
  · exact ⟨2, 2, rfl⟩

theorem base3_lt : ∀ h ∈ base3, 2 * h < 3 ^ 3 := by decide

theorem base3_covers_bool :
    let b := subsetBits base3
    (List.range 25).all (fun i => Nat.testBit b (1 + i)) = true := by
  decide

theorem base3_covers :
    ∀ n, 1 ≤ n → n ≤ 25 → ∃ sub : List Nat, sub.Sublist base3 ∧ sub.sum = n := by
  intro n hlo hhi
  have hmem : n - 1 ∈ List.range 25 := List.mem_range.mpr (by omega)
  have hbit : Nat.testBit (subsetBits base3) (1 + (n - 1)) = true :=
    List.all_eq_true.mp base3_covers_bool (n - 1) hmem
  have heq : 1 + (n - 1) = n := by omega
  rw [heq] at hbit
  exact subsetBits_sound base3 n hbit

def chain3 : Nat → List Nat
  | 0 => base3
  | k + 1 =>
    ((3 ^ (k + 3) + 9) / 2) :: ((3 ^ (k + 3) + 3) / 2) :: ((3 ^ (k + 3) + 1) / 2) :: chain3 k

def upper3 : Nat → Nat
  | 0 => 25
  | k + 1 => upper3 k + (3 ^ (k + 4) + 13) / 2

theorem pow3_ge3 (k : Nat) : 3 ^ (k + 3) ≥ 27 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have : 3 ^ (k + 1 + 3) = 3 ^ (k + 3) * 3 := by
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, Nat.pow_succ]
    omega

theorem pow3_step3 (k : Nat) : 3 ^ (k + 4) = 3 * 3 ^ (k + 3) := by
  rw [show k + 4 = (k + 3) + 1 by omega, Nat.pow_succ]
  omega

theorem chain3_lt (k : Nat) : ∀ h ∈ chain3 k, 2 * h < 3 ^ (k + 3) := by
  induction k with
  | zero => exact base3_lt
  | succ k ih =>
    intro h hh
    have hstep := pow3_step3 k
    have hge := pow3_ge3 k
    have hidx : k + 1 + 3 = k + 4 := by omega
    rw [hidx, hstep]
    simp only [chain3, List.mem_cons] at hh
    rcases hh with rfl | rfl | rfl | hh
    · omega
    · omega
    · omega
    · have := ih h hh; omega

theorem chain3_nodup (k : Nat) : (chain3 k).Nodup := by
  induction k with
  | zero => exact base3_nodup
  | succ k ih =>
    have hlt := chain3_lt k
    have hodd := odd_pow_odd 3 (by decide) (k + 3)
    have hnot : ∀ c ≥ 1, c % 2 = 1 → (3 ^ (k + 3) + c) / 2 ∉ chain3 k := by
      intro c hc hco hmem
      have := hlt _ hmem
      omega
    simp only [chain3, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨by omega, by omega, hnot 9 (by omega) (by decide)⟩,
            ⟨by omega, hnot 3 (by omega) (by decide)⟩,
            hnot 1 (by omega) (by decide), ih⟩

theorem chain3_form (k : Nat) : ∀ h ∈ chain3 k, IsHalfForm 3 3 h := by
  induction k with
  | zero => exact base3_form
  | succ k ih =>
    intro h hh
    simp only [chain3, List.mem_cons] at hh
    rcases hh with rfl | rfl | rfl | hh
    · exact isHalfForm_pow_sum 3 3 (k + 3) 2 (by decide) (by decide)
    · exact isHalfForm_pow_sum 3 3 (k + 3) 1 (by decide) (by decide)
    · exact isHalfForm_pow_sum 3 3 (k + 3) 0 (by decide) (by decide)
    · exact ih h hh

theorem upper3_ge (k : Nat) : upper3 k ≥ (3 ^ (k + 3) + 9) / 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [upper3]
    have hidx : 3 ^ (k + 1 + 3) = 3 ^ (k + 4) := by rw [show k + 1 + 3 = k + 4 by omega]
    rw [hidx]
    omega

theorem chain3_covers (k : Nat) :
    ∀ n, 1 ≤ n → n ≤ upper3 k → ∃ sub : List Nat, sub.Sublist (chain3 k) ∧ sub.sum = n := by
  induction k with
  | zero => exact base3_covers
  | succ k ih =>
    have hge := upper3_ge k
    have hpow := pow3_ge3 k
    have hodd := odd_pow_odd 3 (by decide) (k + 3)
    have h1 := add_one_interval (by omega) ih (x := (3 ^ (k + 3) + 1) / 2) (by omega)
    have h2 := add_one_interval (by omega) h1 (x := (3 ^ (k + 3) + 3) / 2) (by omega)
    have h3 := add_one_interval (by omega) h2 (x := (3 ^ (k + 3) + 9) / 2) (by omega)
    have heq : upper3 (k + 1) =
        ((upper3 k + (3 ^ (k + 3) + 1) / 2) + (3 ^ (k + 3) + 3) / 2) + (3 ^ (k + 3) + 9) / 2 := by
      simp only [upper3]
      have hstep := pow3_step3 k
      omega
    intro n hlo hhi
    rw [heq] at hhi
    exact h3 n hlo hhi

theorem nat_le_pow3_half (n : Nat) : n ≤ (3 ^ (n + 3) + 9) / 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hge := pow3_ge3 n
    have : 3 ^ (n + 1 + 3) = 3 ^ (n + 3) * 3 := by
      rw [show n + 1 + 3 = (n + 3) + 1 by omega, Nat.pow_succ]
    omega

/-- Theorem 2 (A362861 Conjecture 1(i), Part B): Every positive even number is a sum of distinct 3^a + 3^b. -/
theorem all_even_rep_3_3 (n : Nat) (hn : n ≥ 1) : IsRep 3 3 (2 * n) := by
  have hle : n ≤ upper3 n := Nat.le_trans (nat_le_pow3_half n) (upper3_ge n)
  rcases chain3_covers n n hn hle with ⟨sub, hsub, hsum⟩
  exact half_rep_to_even_rep hsub (chain3_nodup n) (chain3_form n) hsum

/-! =======================================================================
    PART 3: A362861 Conjecture 1(ii), Part A — {3^a + 7^b}
    ======================================================================= -/

def base37 : List Nat := [1, 2, 4, 5, 8, 14, 17, 25, 26, 29, 38]

theorem base37_nodup : base37.Nodup := by decide

theorem base37_form : ∀ h ∈ base37, IsHalfForm 3 7 h := by
  intro h hh
  simp only [base37, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, rfl⟩
  · exact ⟨1, 0, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨1, 1, rfl⟩
  · exact ⟨2, 1, rfl⟩
  · exact ⟨3, 0, rfl⟩
  · exact ⟨3, 1, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨1, 2, rfl⟩
  · exact ⟨2, 2, rfl⟩
  · exact ⟨3, 2, rfl⟩

theorem base37_lt : ∀ h ∈ base37, 2 * h < 3 ^ 4 := by decide

theorem base37_covers_bool :
    let b := subsetBits base37
    (List.range 168).all (fun i => Nat.testBit b (1 + i)) = true := by
  decide

theorem base37_covers :
    ∀ n, 1 ≤ n → n ≤ 168 → ∃ sub : List Nat, sub.Sublist base37 ∧ sub.sum = n := by
  intro n hlo hhi
  have hmem : n - 1 ∈ List.range 168 := List.mem_range.mpr (by omega)
  have hbit : Nat.testBit (subsetBits base37) (1 + (n - 1)) = true :=
    List.all_eq_true.mp base37_covers_bool (n - 1) hmem
  have heq : 1 + (n - 1) = n := by omega
  rw [heq] at hbit
  exact subsetBits_sound base37 n hbit

def chain37 : Nat → List Nat
  | 0 => base37
  | k + 1 =>
    ((3 ^ (k + 4) + 49) / 2) :: ((3 ^ (k + 4) + 7) / 2) :: ((3 ^ (k + 4) + 1) / 2) :: chain37 k

def upper37 : Nat → Nat
  | 0 => 168
  | k + 1 => upper37 k + (3 ^ (k + 5) + 57) / 2

theorem pow3_ge4 (k : Nat) : 3 ^ (k + 4) ≥ 81 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have : 3 ^ (k + 1 + 4) = 3 ^ (k + 4) * 3 := by
      rw [show k + 1 + 4 = (k + 4) + 1 by omega, Nat.pow_succ]
    omega

theorem pow3_step4 (k : Nat) : 3 ^ (k + 5) = 3 * 3 ^ (k + 4) := by
  rw [show k + 5 = (k + 4) + 1 by omega, Nat.pow_succ]
  omega

theorem chain37_lt (k : Nat) : ∀ h ∈ chain37 k, 2 * h < 3 ^ (k + 4) := by
  induction k with
  | zero => exact base37_lt
  | succ k ih =>
    intro h hh
    have hstep := pow3_step4 k
    have hge := pow3_ge4 k
    have hidx : k + 1 + 4 = k + 5 := by omega
    rw [hidx, hstep]
    simp only [chain37, List.mem_cons] at hh
    rcases hh with rfl | rfl | rfl | hh
    · omega
    · omega
    · omega
    · have := ih h hh; omega

theorem chain37_nodup (k : Nat) : (chain37 k).Nodup := by
  induction k with
  | zero => exact base37_nodup
  | succ k ih =>
    have hlt := chain37_lt k
    have hodd := odd_pow_odd 3 (by decide) (k + 4)
    have hnot : ∀ c ≥ 1, c % 2 = 1 → (3 ^ (k + 4) + c) / 2 ∉ chain37 k := by
      intro c hc hco hmem
      have := hlt _ hmem
      omega
    simp only [chain37, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨by omega, by omega, hnot 49 (by omega) (by decide)⟩,
            ⟨by omega, hnot 7 (by omega) (by decide)⟩,
            hnot 1 (by omega) (by decide), ih⟩

theorem chain37_form (k : Nat) : ∀ h ∈ chain37 k, IsHalfForm 3 7 h := by
  induction k with
  | zero => exact base37_form
  | succ k ih =>
    intro h hh
    simp only [chain37, List.mem_cons] at hh
    rcases hh with rfl | rfl | rfl | hh
    · exact isHalfForm_pow_sum 3 7 (k + 4) 2 (by decide) (by decide)
    · exact isHalfForm_pow_sum 3 7 (k + 4) 1 (by decide) (by decide)
    · exact isHalfForm_pow_sum 3 7 (k + 4) 0 (by decide) (by decide)
    · exact ih h hh

theorem upper37_ge (k : Nat) : upper37 k ≥ (3 ^ (k + 4) + 49) / 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [upper37]
    have hidx : 3 ^ (k + 1 + 4) = 3 ^ (k + 5) := by rw [show k + 1 + 4 = k + 5 by omega]
    rw [hidx]
    omega

theorem chain37_covers (k : Nat) :
    ∀ n, 1 ≤ n → n ≤ upper37 k → ∃ sub : List Nat, sub.Sublist (chain37 k) ∧ sub.sum = n := by
  induction k with
  | zero => exact base37_covers
  | succ k ih =>
    have hge := upper37_ge k
    have hpow := pow3_ge4 k
    have hodd := odd_pow_odd 3 (by decide) (k + 4)
    have h1 := add_one_interval (by omega) ih (x := (3 ^ (k + 4) + 1) / 2) (by omega)
    have h2 := add_one_interval (by omega) h1 (x := (3 ^ (k + 4) + 7) / 2) (by omega)
    have h3 := add_one_interval (by omega) h2 (x := (3 ^ (k + 4) + 49) / 2) (by omega)
    have heq : upper37 (k + 1) =
        ((upper37 k + (3 ^ (k + 4) + 1) / 2) + (3 ^ (k + 4) + 7) / 2) + (3 ^ (k + 4) + 49) / 2 := by
      simp only [upper37]
      have hstep := pow3_step4 k
      omega
    intro n hlo hhi
    rw [heq] at hhi
    exact h3 n hlo hhi

theorem nat_le_pow37_half (n : Nat) : n ≤ (3 ^ (n + 4) + 49) / 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hge := pow3_ge4 n
    have : 3 ^ (n + 1 + 4) = 3 ^ (n + 4) * 3 := by
      rw [show n + 1 + 4 = (n + 4) + 1 by omega, Nat.pow_succ]
    omega

/-- Theorem 3 (A362861 Conjecture 1(ii), Part A): Every positive even number is a sum of distinct 3^a + 7^b. -/
theorem all_even_rep_3_7 (n : Nat) (hn : n ≥ 1) : IsRep 3 7 (2 * n) := by
  have hle : n ≤ upper37 n := Nat.le_trans (nat_le_pow37_half n) (upper37_ge n)
  rcases chain37_covers n n hn hle with ⟨sub, hsub, hsum⟩
  exact half_rep_to_even_rep hsub (chain37_nodup n) (chain37_form n) hsum

#print axioms exact_characterization_5_5
#print axioms all_even_rep_3_3
#print axioms all_even_rep_3_7

end A362861
