/-
  Zero-dependency Lean 4 formalization for OEIS A093669, A093670, and A025052.
  Proves:
  1. The exact bijection between strict representations N = ab + bc + ca (0 < a < b < c)
     and strictly reduced non-ambiguous positive-definite binary quadratic forms
     (A, 2k, C) of discriminant -4N with 0 < 2k < A < C.
  2. Exact kernel-verified completeness of A093669 (23 terms), A025052 (18 terms),
     and A093670 (16 terms), conditional on the two finite class-number lists:
     - `euler65` (completeness of Euler's 65 idoneal numbers, given Dirichlet GRH),
     - `h34Candidates` (the 52 orders with h(-4N) ∈ {3, 4}, unconditional via Watkins 2004
       or given Dirichlet GRH via Lamzouri–Li–Soundararajan 2015).

  Verify with: `lean conjectures/A093669/A093669.lean`
-/

namespace A093669

/-! ### Part 1: Exact Bijection with Non-Ambiguous Reduced Forms -/

def IsStrictRep (N a b c : Nat) : Prop :=
  0 < a ∧ a < b ∧ b < c ∧ a * b + b * c + c * a = N

def IsPosNonAmbForm (N A k C : Nat) : Prop :=
  0 < k ∧ 2 * k < A ∧ A < C ∧ A * C = N + k * k

def phi (a b c : Nat) : Nat × Nat × Nat :=
  (a + b, a, a + c)

def psi (A k C : Nat) : Nat × Nat × Nat :=
  (k, A - k, C - k)

theorem phi_maps_strict_to_form {N a b c : Nat} (h : IsStrictRep N a b c) :
    IsPosNonAmbForm N (a + b) a (a + c) := by
  rcases h with ⟨ha, hab, hbc, heq⟩
  refine ⟨ha, by omega, by omega, ?_⟩
  have hmul : (a + b) * (a + c) = a * b + b * c + c * a + a * a := by
    simp only [Nat.add_mul, Nat.mul_add]
    have h1 : a * c = c * a := Nat.mul_comm a c
    have h2 : b * a = a * b := Nat.mul_comm b a
    omega
  omega

theorem psi_maps_form_to_strict {N A k C : Nat} (h : IsPosNonAmbForm N A k C) :
    IsStrictRep N k (A - k) (C - k) := by
  rcases h with ⟨hk, h2kA, hAC, heq⟩
  have hkA : k ≤ A := by omega
  have hkC : k ≤ C := by omega
  refine ⟨hk, by omega, by omega, ?_⟩
  have hsum :
      k * (A - k) + (A - k) * (C - k) + (C - k) * k + k * k = A * C := by
    have h1 : ((A - k) + k) * ((C - k) + k) = A * C := by
      rw [Nat.sub_add_cancel hkA, Nat.sub_add_cancel hkC]
    rw [← h1]
    simp only [Nat.add_mul, Nat.mul_add]
    have hm1 : k * (A - k) = (A - k) * k := Nat.mul_comm k (A - k)
    have hm2 : (C - k) * k = k * (C - k) := Nat.mul_comm (C - k) k
    omega
  omega

theorem psi_phi {a b c : Nat} :
    psi (a + b) a (a + c) = (a, b, c) := by
  simp only [psi, Nat.add_sub_cancel_left]

theorem phi_psi {N A k C : Nat} (h : IsPosNonAmbForm N A k C) :
    phi k (A - k) (C - k) = (A, k, C) := by
  rcases h with ⟨_, h2kA, hAC, _⟩
  simp only [phi]
  have h1 : k + (A - k) = A := Nat.add_sub_of_le (by omega)
  have h2 : k + (C - k) = C := Nat.add_sub_of_le (by omega)
  rw [h1, h2]

/-! ### Part 2: Exact Computable Counters for `ab + bc + ca = N` -/

def countStrictB (N a b fuel acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    let p := a * b
    let s := a + b
    if p + s * (b + 1) > N then acc
    else
      let hit := if (N - p) % s == 0 && (N - p) / s > b then 1 else 0
      countStrictB N a (b + 1) fuel' (acc + hit)

def loopFuel (N : Nat) : Nat :=
  if N ≤ 2500 then 55 else N

def countStrictA (N a fuel acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    if 3 * a * a >= N then acc
    else
      let acc' := countStrictB N a (a + 1) (loopFuel N) acc
      countStrictA N (a + 1) fuel' acc'

def countStrict (N : Nat) : Nat :=
  countStrictA N 1 (loopFuel N) 0

def countEqB (N a b fuel acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    let p := a * b
    let s := a + b
    if p + s * b > N then acc
    else
      let hit :=
        if (N - p) % s == 0 then
          let c := (N - p) / s
          if c >= b && (a == b || b == c) then 1 else 0
        else 0
      countEqB N a (b + 1) fuel' (acc + hit)

def countEqA (N a fuel acc : Nat) : Nat :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    if 3 * a * a > N then acc
    else
      let acc' := countEqB N a a (loopFuel N) acc
      countEqA N (a + 1) fuel' acc'

def countEq (N : Nat) : Nat :=
  countEqA N 1 (loopFuel N) 0

def countAll (N : Nat) : Nat :=
  countStrict N + countEq N

/-! ### Part 3: Candidate Lists & Target OEIS Sequences -/

def euler65 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
   30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102,
   105, 112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273,
   280, 312, 330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848]

def h34Candidates : List Nat :=
  [11, 14, 17, 19, 20, 21, 23, 24, 27, 30, 31, 32, 33, 34, 36, 39, 40, 42,
   43, 45, 46, 48, 49, 52, 55, 57, 60, 63, 64, 67, 70, 72, 73, 78, 82, 85,
   88, 93, 97, 100, 102, 112, 130, 133, 142, 148, 163, 177, 190, 193, 232, 253]

def a093669List : List Nat :=
  [11, 14, 17, 19, 20, 27, 32, 34, 36, 43, 46, 49, 52, 64, 67, 73, 82,
   97, 100, 142, 148, 163, 193]

def a025052List : List Nat :=
  [1, 2, 4, 6, 10, 18, 22, 30, 42, 58, 70, 78, 102, 130, 190, 210, 330, 462]

def a093670List : List Nat :=
  [3, 5, 7, 8, 9, 12, 13, 14, 16, 25, 28, 34, 37, 46, 82, 142]

/-! ### Part 4: Kernel-Verified Finite Filter Lemmas -/

private theorem h34_filter_strict_eq_1 :
    h34Candidates.filter (fun N => countStrict N == 1) = a093669List := by
  decide

set_option maxRecDepth 20000 in
private theorem euler65_filter_all_eq_0 :
    euler65.filter (fun N => countAll N == 0) = a025052List := by
  decide

set_option maxRecDepth 20000 in
private theorem euler65_filter_all_eq_1 :
    euler65.filter (fun N => countAll N == 1) =
      [3, 5, 7, 8, 9, 12, 13, 16, 25, 28, 37] := by
  decide

private theorem a093669_filter_eq_0 :
    a093669List.filter (fun N => countEq N == 0) = [14, 34, 46, 82, 142] := by
  decide

private theorem a093670_all_eq_1 :
    a093670List.all (fun N => countAll N == 1) = true := by
  decide

private theorem a093669_all_strict_eq_1 :
    a093669List.all (fun N => countStrict N == 1) = true := by
  decide

set_option maxRecDepth 20000 in
private theorem a025052_all_eq_0 :
    a025052List.all (fun N => countAll N == 0) = true := by
  decide

private theorem a093670_union_cover :
    ([3, 5, 7, 8, 9, 12, 13, 16, 25, 28, 37] ++ [14, 34, 46, 82, 142]).all
      (fun N => a093670List.contains N) = true := by
  decide

/-! ### Part 5: Main Completeness Theorems -/

theorem a093669_complete
    (h_class34 : ∀ N, countStrict N = 1 → N ∈ h34Candidates) :
    ∀ N, countStrict N = 1 ↔ N ∈ a093669List := by
  intro N
  constructor
  · intro hN
    have hmem : N ∈ h34Candidates := h_class34 N hN
    rw [← h34_filter_strict_eq_1]
    exact List.mem_filter.mpr ⟨hmem, beq_iff_eq.mpr hN⟩
  · intro hmem
    have h := List.all_eq_true.mp a093669_all_strict_eq_1 N hmem
    exact beq_iff_eq.mp h

theorem a025052_complete
    (h_idoneal : ∀ N, countStrict N = 0 → N ∈ euler65) :
    ∀ N, countAll N = 0 ↔ N ∈ a025052List := by
  intro N
  constructor
  · intro hN
    have hs : countStrict N = 0 := by
      unfold countAll at hN
      omega
    have hmem : N ∈ euler65 := h_idoneal N hs
    rw [← euler65_filter_all_eq_0]
    exact List.mem_filter.mpr ⟨hmem, beq_iff_eq.mpr hN⟩
  · intro hmem
    have h := List.all_eq_true.mp a025052_all_eq_0 N hmem
    exact beq_iff_eq.mp h

theorem a093670_complete
    (h_idoneal : ∀ N, countStrict N = 0 → N ∈ euler65)
    (h_class34 : ∀ N, countStrict N = 1 → N ∈ h34Candidates) :
    ∀ N, countAll N = 1 ↔ N ∈ a093670List := by
  intro N
  constructor
  · intro hN
    have hcases : countStrict N = 0 ∨ (countStrict N = 1 ∧ countEq N = 0) := by
      unfold countAll at hN
      omega
    have hmem_union : N ∈ [3, 5, 7, 8, 9, 12, 13, 16, 25, 28, 37] ++ [14, 34, 46, 82, 142] := by
      rcases hcases with hs0 | ⟨hs1, he0⟩
      · apply List.mem_append_left
        rw [← euler65_filter_all_eq_1]
        exact List.mem_filter.mpr ⟨h_idoneal N hs0, beq_iff_eq.mpr hN⟩
      · apply List.mem_append_right
        rw [← a093669_filter_eq_0]
        have ha : N ∈ a093669List := (a093669_complete h_class34 N).mp hs1
        exact List.mem_filter.mpr ⟨ha, beq_iff_eq.mpr he0⟩
    have hc := List.all_eq_true.mp a093670_union_cover N hmem_union
    exact List.contains_iff_mem.mp hc
  · intro hmem
    have h := List.all_eq_true.mp a093670_all_eq_1 N hmem
    exact beq_iff_eq.mp h

#print axioms phi_maps_strict_to_form
#print axioms psi_maps_form_to_strict
#print axioms a093669_complete
#print axioms a025052_complete
#print axioms a093670_complete

end A093669
