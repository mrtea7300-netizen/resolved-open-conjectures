/-
  Complete formal proof of OEIS A362743 Conjecture 1 (first part):
    For every integer n >= 1, n can be written as a sum of distinct numbers of the
    form 4^a + 5^b (a, b >= 0) if and only if n is not in {1, 3, 4, 10, 12, 18}.

  Zero external dependencies (pure Lean 4 core). Zero `sorry`.
-/

namespace A362743

def IsForm (x : Nat) : Prop :=
  ∃ a b : Nat, x = 4 ^ a + 5 ^ b

def IsRep (n : Nat) : Prop :=
  ∃ L : List Nat, L.Nodup ∧ (∀ x ∈ L, IsForm x) ∧ L.sum = n

/-! ### Subset-sum helper and Brown's one-step interval extension -/

def canSum : List Nat → Nat → Bool
  | [], n => n == 0
  | x :: xs, n => canSum xs n || (decide (x ≤ n) && canSum xs (n - x))

theorem canSum_sound : ∀ (L : List Nat) (n : Nat),
    canSum L n = true → ∃ sub : List Nat, sub.Sublist L ∧ sub.sum = n
  | [], n, h => by
    simp only [canSum, beq_iff_eq] at h
    exact ⟨[], List.Sublist.slnil, h.symm⟩
  | x :: xs, n, h => by
    simp only [canSum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h1 | ⟨hle, h2⟩
    · rcases canSum_sound xs n h1 with ⟨sub, hsub, hsum⟩
      exact ⟨sub, List.Sublist.cons x hsub, hsum⟩
    · rcases canSum_sound xs (n - x) h2 with ⟨sub, hsub, hsum⟩
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

/-! ### Base 9 elements and block t = 3 -/

def base9 : List Nat := [2, 5, 6, 9, 17, 21, 26, 29, 41]

theorem base9_nodup : base9.Nodup := by decide

theorem base9_form : ∀ x ∈ base9, IsForm x := by
  intro x hx
  simp only [base9, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, rfl⟩
  · exact ⟨1, 0, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨1, 1, rfl⟩
  · exact ⟨2, 0, rfl⟩
  · exact ⟨2, 1, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨1, 2, rfl⟩
  · exact ⟨2, 2, rfl⟩

theorem base9_lt_64 : ∀ x ∈ base9, x < 64 := by decide

theorem base9_covers_19_137_bool :
    (List.range 119).all (fun i => canSum base9 (19 + i)) = true := by
  decide

theorem base9_covers_19_137 :
    ∀ n, 19 ≤ n → n ≤ 137 → ∃ sub : List Nat, sub.Sublist base9 ∧ sub.sum = n := by
  intro n hlo hhi
  have hmem : n - 19 ∈ List.range 119 := List.mem_range.mpr (by omega)
  have hbool : canSum base9 (19 + (n - 19)) = true :=
    List.all_eq_true.mp base9_covers_19_137_bool (n - 19) hmem
  have heq : 19 + (n - 19) = n := by omega
  rw [heq] at hbool
  exact canSum_sound base9 n hbool

def baseList : List Nat := 189 :: 89 :: 69 :: 65 :: base9

theorem baseList_nodup : baseList.Nodup := by decide

theorem baseList_form : ∀ x ∈ baseList, IsForm x := by
  intro x hx
  simp only [baseList, List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | rfl | hx
  · exact ⟨3, 3, rfl⟩
  · exact ⟨3, 2, rfl⟩
  · exact ⟨3, 1, rfl⟩
  · exact ⟨3, 0, rfl⟩
  · exact base9_form x hx

theorem baseList_lt_256 : ∀ x ∈ baseList, x < 256 := by decide

theorem baseList_covers_19_549 :
    ∀ n, 19 ≤ n → n ≤ 549 → ∃ sub : List Nat, sub.Sublist baseList ∧ sub.sum = n := by
  have h1 := add_one_interval (by omega) base9_covers_19_137 (x := 65) (by omega)
  have h2 := add_one_interval (by omega) h1 (x := 69) (by omega)
  have h3 := add_one_interval (by omega) h2 (x := 89) (by omega)
  exact add_one_interval (by omega) h3 (x := 189) (by omega)

/-! ### Infinite block ladder for t >= 4 -/

def chain : Nat → List Nat
  | 0 => baseList
  | k + 1 =>
    (4 ^ (k + 4) + 125) :: (4 ^ (k + 4) + 25) :: (4 ^ (k + 4) + 5) :: (4 ^ (k + 4) + 1) :: chain k

def upperB : Nat → Nat
  | 0 => 549
  | k + 1 => upperB k + 4 ^ (k + 5) + 156

theorem pow4_ge (k : Nat) : 4 ^ (k + 4) ≥ 256 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have : 4 ^ (k + 1 + 4) = 4 ^ (k + 4) * 4 := by rw [show k + 1 + 4 = (k + 4) + 1 by omega, Nat.pow_succ]
    omega

theorem pow4_step (k : Nat) : 4 ^ (k + 5) = 4 * 4 ^ (k + 4) := by
  rw [show k + 5 = (k + 4) + 1 by omega, Nat.pow_succ]
  omega

theorem chain_lt (k : Nat) : ∀ x ∈ chain k, x < 4 ^ (k + 4) := by
  induction k with
  | zero =>
    intro x hx
    exact baseList_lt_256 x hx
  | succ k ih =>
    intro x hx
    have hstep := pow4_step k
    have hge := pow4_ge k
    have hprev_lt : 4 ^ (k + 4) < 4 ^ (k + 1 + 4) := by
      have : k + 1 + 4 = k + 5 := by omega
      rw [this, hstep]; omega
    simp only [chain, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    · have : k + 1 + 4 = k + 5 := by omega
      rw [this, hstep]; omega
    · have : k + 1 + 4 = k + 5 := by omega
      rw [this, hstep]; omega
    · have : k + 1 + 4 = k + 5 := by omega
      rw [this, hstep]; omega
    · have : k + 1 + 4 = k + 5 := by omega
      rw [this, hstep]; omega
    · exact Nat.lt_trans (ih x hx) hprev_lt

theorem chain_nodup (k : Nat) : (chain k).Nodup := by
  induction k with
  | zero => exact baseList_nodup
  | succ k ih =>
    have hlt := chain_lt k
    have hnot : ∀ c ≥ 1, 4 ^ (k + 4) + c ∉ chain k := by
      intro c hc hmem
      have := hlt _ hmem
      omega
    simp only [chain, List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨by omega, by omega, by omega, hnot 125 (by omega)⟩,
            ⟨by omega, by omega, hnot 25 (by omega)⟩,
            ⟨by omega, hnot 5 (by omega)⟩,
            hnot 1 (by omega), ih⟩

theorem chain_form (k : Nat) : ∀ x ∈ chain k, IsForm x := by
  induction k with
  | zero => exact baseList_form
  | succ k ih =>
    intro x hx
    simp only [chain, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | hx
    · exact ⟨k + 4, 3, rfl⟩
    · exact ⟨k + 4, 2, rfl⟩
    · exact ⟨k + 4, 1, rfl⟩
    · exact ⟨k + 4, 0, rfl⟩
    · exact ih x hx

theorem upperB_ge (k : Nat) : upperB k - 18 ≥ 4 ^ (k + 4) + 125 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [upperB]
    have hstep : 4 ^ (k + 1 + 4) = 4 ^ (k + 5) := by rw [show k + 1 + 4 = k + 5 by omega]
    rw [hstep]
    omega

theorem chain_covers (k : Nat) :
    ∀ n, 19 ≤ n → n ≤ upperB k → ∃ sub : List Nat, sub.Sublist (chain k) ∧ sub.sum = n := by
  induction k with
  | zero => exact baseList_covers_19_549
  | succ k ih =>
    have hge := upperB_ge k
    have hpow := pow4_ge k
    have h1 := add_one_interval (by omega) ih (x := 4 ^ (k + 4) + 1) (by omega)
    have h2 := add_one_interval (by omega) h1 (x := 4 ^ (k + 4) + 5) (by omega)
    have h3 := add_one_interval (by omega) h2 (x := 4 ^ (k + 4) + 25) (by omega)
    have h4 := add_one_interval (by omega) h3 (x := 4 ^ (k + 4) + 125) (by omega)
    have heq : upperB (k + 1) =
        (((upperB k + (4 ^ (k + 4) + 1)) + (4 ^ (k + 4) + 5)) + (4 ^ (k + 4) + 25)) +
          (4 ^ (k + 4) + 125) := by
      simp only [upperB]
      have hstep := pow4_step k
      omega
    intro n hlo hhi
    rw [heq] at hhi
    exact h4 n hlo hhi

theorem nat_le_pow4 (n : Nat) : n ≤ 4 ^ (n + 4) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hge := pow4_ge n
    have : 4 ^ (n + 1 + 4) = 4 ^ (n + 4) * 4 := by
      rw [show n + 1 + 4 = (n + 4) + 1 by omega, Nat.pow_succ]
    omega

theorem all_ge_19_representable (n : Nat) (hn : n ≥ 19) : IsRep n := by
  have hle : n ≤ upperB n := by
    have h1 := upperB_ge n
    have h2 := nat_le_pow4 n
    omega
  rcases chain_covers n n hn hle with ⟨sub, hsub, hsum⟩
  exact ⟨sub, sublist_nodup hsub (chain_nodup n),
         fun x hx => chain_form n x (hsub.subset hx), hsum⟩

/-! ### Exact characterization for all n >= 1 -/

def exceptions : List Nat := [1, 3, 4, 10, 12, 18]

theorem small_good_bool :
    (List.range 18).all (fun i =>
      let n := i + 1
      (n ∈ exceptions) || canSum base9 n) = true := by
  decide

theorem form_le_18 (x : Nat) (hf : IsForm x) (hle : x ≤ 18) :
    x ∈ ([2, 5, 6, 9, 17] : List Nat) := by
  rcases hf with ⟨a, b, rfl⟩
  match a, b with
  | 0, 0 => decide
  | 1, 0 => decide
  | 2, 0 => decide
  | 0, 1 => decide
  | 1, 1 => decide
  | 2, 1 => omega
  | a + 3, _ =>
    have hpow : 4 ^ (a + 3) ≥ 4 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have hle1 : 4 ^ (a + 3) ≤ 18 := Nat.le_trans (Nat.le_add_right _ _) hle
    have : 4 ^ 3 = 64 := rfl
    omega
  | _, b + 2 =>
    have hpow : 5 ^ (b + 2) ≥ 5 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
    have hle2 : 5 ^ (b + 2) ≤ 18 := Nat.le_trans (Nat.le_add_left _ _) hle
    have : 5 ^ 2 = 25 := rfl
    omega

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

theorem canSum_of_nodup_subset : ∀ (U L : List Nat),
    L.Nodup → (∀ x ∈ L, x ∈ U) → canSum U L.sum = true
  | [], L, _, hsub => by
    cases L with
    | nil => rfl
    | cons x xs => cases hsub x (List.mem_cons_self ..)
  | u :: us, L, hnd, hsub => by
    simp only [canSum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hu : u ∈ L
    · right
      have hsum := erase_sum_add hu
      have hle : u ≤ L.sum := by omega
      refine ⟨hle, ?_⟩
      have heq : L.sum - u = (L.erase u).sum := by omega
      rw [heq]
      apply canSum_of_nodup_subset us (L.erase u) (hnd.erase u)
      intro x hx
      have hxL : x ∈ L := List.mem_of_mem_erase hx
      have hne : x ≠ u := fun h => by
        subst h
        exact erase_not_mem_of_nodup hnd hx
      cases List.mem_cons.mp (hsub x hxL) with
      | inl h => exact absurd h hne
      | inr h => exact h
    · left
      apply canSum_of_nodup_subset us L hnd
      intro x hx
      cases List.mem_cons.mp (hsub x hx) with
      | inl h => subst h; exact absurd hx hu
      | inr h => exact h

theorem exceptions_impossible_bool :
    exceptions.all (fun n => !(canSum [2, 5, 6, 9, 17] n)) = true := by
  decide

theorem exception_not_rep (n : Nat) (hn : n ∈ exceptions) : ¬ IsRep n := by
  intro ⟨L, hnd, hform, hsum⟩
  have hn18 : n ≤ 18 := by
    simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hsub : ∀ x ∈ L, x ∈ ([2, 5, 6, 9, 17] : List Nat) := by
    intro x hx
    have hxle : x ≤ 18 := by
      have := mem_le_sum hx
      omega
    exact form_le_18 x (hform x hx) hxle
  have hcan := canSum_of_nodup_subset [2, 5, 6, 9, 17] L hnd hsub
  rw [hsum] at hcan
  have hnot := List.all_eq_true.mp exceptions_impossible_bool n hn
  simp [hcan] at hnot

/-- Main Theorem: Complete characterization of OEIS A362743 (Conjecture 1, first part). -/
theorem exact_characterization (n : Nat) (hn : n ≥ 1) :
    IsRep n ↔ n ∉ exceptions := by
  constructor
  · intro hrep hmem
    exact exception_not_rep n hmem hrep
  · intro hnotmem
    by_cases h19 : n ≥ 19
    · exact all_ge_19_representable n h19
    · have hmem : n - 1 ∈ List.range 18 := List.mem_range.mpr (by omega)
      have hbool := List.all_eq_true.mp small_good_bool (n - 1) hmem
      have heq : (n - 1) + 1 = n := by omega
      simp only [heq, Bool.or_eq_true, decide_eq_true_eq] at hbool
      rcases hbool with hin | hcan
      · exact absurd hin hnotmem
      · rcases canSum_sound base9 n hcan with ⟨sub, hsub, hsum⟩
        exact ⟨sub, sublist_nodup hsub base9_nodup,
               fun x hx => base9_form x (hsub.subset hx), hsum⟩

#print axioms all_ge_19_representable
#print axioms exact_characterization

end A362743
