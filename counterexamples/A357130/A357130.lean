/-
  Formal disproof of OEIS A357130 Conjecture 2(ii) — equivalently, Conjecture 1,
  equation (1) of Han Wang and Zhi-Wei Sun, "On Two New Kinds of Restricted Sumsets",
  Electronic Journal of Combinatorics 33(2) (2026), #P2.64 (arXiv:2210.12044).

  Zero external dependencies (pure Lean 4 core). Zero `sorry`.

  We formally prove:
  1. `counterexample_Z_n3`: In Z, for A1 = [0, 1, 2], A2 = [0, 2], A3 = [0, 1, 2]
     (all distinct lists of length >= 2), every valid triple (a1, a2, a3) with
     a1 != a2 and a2 != a3 has a1 + a2 + a3 in [2, 3, 4] (size 3 < 4 = 3 + 2 + 3 - 4).
  2. `counterexample_Z_all_odd`: For EVERY m >= 1 (every odd n = 2*m + 1 >= 3),
     an explicit family A_0, ..., A_{2m} of finite sets in Z with |A_i| >= 2
     has sum of sizes 4*m + 4 (so the conjectured bound is 4), yet every valid
     sum lies in a 3-element set [tailSum m + 2, tailSum m + 3, tailSum m + 4].
  3. `counterexample_mod5_n3`: In Z/5Z (Fin 5, p(G) = 5), for A1 = [0, 1],
     A2 = [0, 1, 2, 3, 4], A3 = [2, 4] (so |A2| > |A1|, |A3|), every valid triple
     satisfies a1 + a2 + a3 != 4 (size <= 4 < 5 = min(5, 2 + 5 + 2 - 4)).
-/

namespace A357130

/-! ### Part 1: Universal counterexample in Z for n = 3 -/

def A1_Z : List Int := [0, 1, 2]
def A2_Z : List Int := [0, 2]
def A3_Z : List Int := [0, 1, 2]

theorem A_Z_sizes :
    A1_Z.Nodup ∧ A2_Z.Nodup ∧ A3_Z.Nodup ∧
    A1_Z.length = 3 ∧ A2_Z.length = 2 ∧ A3_Z.length = 3 := by
  decide

theorem counterexample_Z_n3 (a1 a2 a3 : Int)
    (h1 : a1 ∈ A1_Z) (h2 : a2 ∈ A2_Z) (h3 : a3 ∈ A3_Z)
    (h12 : a1 ≠ a2) (h23 : a2 ≠ a3) :
    a1 + a2 + a3 ∈ ([2, 3, 4] : List Int) := by
  simp only [A1_Z, A2_Z, A3_Z, List.mem_cons, List.not_mem_nil, or_false] at h1 h2 h3 ⊢
  rcases h2 with rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;> rcases h3 with rfl | rfl | rfl <;> omega

theorem counterexample_Z_n3_bound :
    ([2, 3, 4] : List Int).length < A1_Z.length + A2_Z.length + A3_Z.length - 2 * 3 + 1 + 3 % 2 := by
  decide

/-! ### Part 2: Infinite family in Z for every odd n = 2*m + 1 >= 3 -/

def familySet (i : Nat) : List Int :=
  if i = 0 then [0, 1, 2]
  else if i = 1 then [0, 2]
  else if i = 2 then [0, 1, 2]
  else
    let j : Int := Int.ofNat ((i + 1) / 2)
    [3 * j, 3 * j + 1]

theorem familySet_nodup (i : Nat) : (familySet i).Nodup := by
  unfold familySet
  split
  · decide
  · split
    · decide
    · split
      · decide
      · dsimp only
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          and_true]
        constructor
        · omega
        · decide

theorem familySet_length_ge_two (i : Nat) : (familySet i).length ≥ 2 := by
  unfold familySet
  split
  · decide
  · split
    · decide
    · split
      · decide
      · simp

def sumLengths : Nat → Nat
  | 0 => 0
  | k + 1 => sumLengths k + (familySet k).length

theorem sumLengths_odd (m : Nat) (hm : m ≥ 1) : sumLengths (2 * m + 1) = 4 * m + 4 := by
  induction m with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => decide
    | succ r =>
      have hih := ih (by omega)
      have h2r : 2 * (r + 1 + 1) + 1 = (2 * (r + 1) + 1) + 2 := by omega
      have hlen1 : (familySet (2 * (r + 1) + 1)).length = 2 := by
        unfold familySet
        have h3 : 2 * (r + 1) + 1 ≠ 2 := by omega
        simp [h3]
      have hlen2 : (familySet (2 * (r + 1) + 1 + 1)).length = 2 := by
        unfold familySet
        have h3 : 2 * (r + 1) + 1 + 1 ≠ 2 := by omega
        simp [h3]
      rw [h2r]
      change sumLengths (2 * (r + 1) + 1) + (familySet (2 * (r + 1) + 1)).length +
             (familySet (2 * (r + 1) + 1 + 1)).length = 4 * (r + 1 + 1) + 4
      rw [hih, hlen1, hlen2]
      omega

def tailSum : Nat → Int
  | 0 => 0
  | 1 => 0
  | m + 1 => tailSum m + (6 * Int.ofNat (m + 1) + 1)

def seqSum (a : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => seqSum a k + a k

theorem counterexample_Z_all_odd (m : Nat) (hm : m ≥ 1) (a : Nat → Int)
    (hmem : ∀ i < 2 * m + 1, a i ∈ familySet i)
    (hne : ∀ i < 2 * m, a i ≠ a (i + 1)) :
    seqSum a (2 * m + 1) ∈ ([tailSum m + 2, tailSum m + 3, tailSum m + 4] : List Int) := by
  induction m with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      have h0 : a 0 ∈ A1_Z := hmem 0 (by omega)
      have h1 : a 1 ∈ A2_Z := hmem 1 (by omega)
      have h2 : a 2 ∈ A3_Z := hmem 2 (by omega)
      have h01 : a 0 ≠ a 1 := hne 0 (by omega)
      have h12 : a 1 ≠ a 2 := hne 1 (by omega)
      have hbase := counterexample_Z_n3 (a 0) (a 1) (a 2) h0 h1 h2 h01 h12
      change (((0 + a 0) + a 1) + a 2) ∈ ([0 + 2, 0 + 3, 0 + 4] : List Int)
      simp only [Int.zero_add]
      exact hbase
    | succ r =>
      have hprev := ih (by omega)
        (fun i hi => hmem i (by omega))
        (fun i hi => hne i (by omega))
      have hidx1 : 2 * (r + 1) + 1 < 2 * (r + 1 + 1) + 1 := by omega
      have hidx2 : 2 * (r + 1) + 2 < 2 * (r + 1 + 1) + 1 := by omega
      have ha1 : a (2 * (r + 1) + 1) ∈ familySet (2 * (r + 1) + 1) := hmem _ hidx1
      have ha2 : a (2 * (r + 1) + 2) ∈ familySet (2 * (r + 1) + 2) := hmem _ hidx2
      have hadiff : a (2 * (r + 1) + 1) ≠ a (2 * (r + 1) + 2) := hne (2 * (r + 1) + 1) (by omega)
      have hset1 : familySet (2 * (r + 1) + 1) = [3 * Int.ofNat (r + 2), 3 * Int.ofNat (r + 2) + 1] := by
        unfold familySet
        have h3 : 2 * (r + 1) + 1 ≠ 2 := by omega
        have hdiv : (2 * (r + 1) + 1 + 1) / 2 = r + 2 := by omega
        simp [h3, hdiv]
      have hset2 : familySet (2 * (r + 1) + 2) = [3 * Int.ofNat (r + 2), 3 * Int.ofNat (r + 2) + 1] := by
        unfold familySet
        have h2 : 2 * (r + 1) + 2 ≠ 1 := by omega
        have hdiv : (2 * (r + 1) + 2 + 1) / 2 = r + 2 := by omega
        simp [h2, hdiv]
      rw [hset1] at ha1
      rw [hset2] at ha2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha1 ha2
      have hpair : a (2 * (r + 1) + 1) + a (2 * (r + 1) + 2) = 6 * Int.ofNat (r + 2) + 1 := by
        rcases ha1 with h1 | h1 <;> rcases ha2 with h2 | h2 <;> omega
      have hsum_step :
          seqSum a (2 * (r + 1 + 1) + 1) =
          seqSum a (2 * (r + 1) + 1) + (a (2 * (r + 1) + 1) + a (2 * (r + 1) + 2)) := by
        have h2eq : 2 * (r + 1 + 1) + 1 = (2 * (r + 1) + 1) + 2 := by omega
        rw [h2eq]
        simp only [seqSum]
        omega
      rw [hsum_step, hpair]
      have htail : tailSum (r + 1 + 1) = tailSum (r + 1) + (6 * Int.ofNat (r + 2) + 1) := rfl
      rw [htail]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hprev ⊢
      rcases hprev with h | h | h <;> omega

theorem counterexample_Z_all_odd_bound (m : Nat) (hm : m ≥ 1) :
    3 < sumLengths (2 * m + 1) - 2 * (2 * m + 1) + 1 + (2 * m + 1) % 2 := by
  rw [sumLengths_odd m hm]
  omega

/-! ### Part 3: Modular counterexample in Z/5Z with |A2| > |A1|, |A3| -/

def A1_5 : List (Fin 5) := [0, 1]
def A2_5 : List (Fin 5) := [0, 1, 2, 3, 4]
def A3_5 : List (Fin 5) := [2, 4]

theorem A_5_sizes :
    A1_5.Nodup ∧ A2_5.Nodup ∧ A3_5.Nodup ∧
    A1_5.length = 2 ∧ A2_5.length = 5 ∧ A3_5.length = 2 := by
  decide

theorem counterexample_mod5_n3 :
    ∀ a1 ∈ A1_5, ∀ a2 ∈ A2_5, ∀ a3 ∈ A3_5,
      a1 ≠ a2 → a2 ≠ a3 → a1 + a2 + a3 ≠ (4 : Fin 5) := by
  decide

theorem counterexample_mod5_n3_bound :
    4 < min 5 (A1_5.length + A2_5.length + A3_5.length - 2 * 3 + 1 + 3 % 2) := by
  decide

#print axioms counterexample_Z_n3
#print axioms counterexample_Z_all_odd
#print axioms counterexample_Z_all_odd_bound
#print axioms counterexample_mod5_n3
#print axioms counterexample_mod5_n3_bound

end A357130
