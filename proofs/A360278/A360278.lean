/-
  Complete formal proof of OEIS A360278 Conjectures 1, 2, and 3
  (also resolving the open odd-n and B = 1 determinant conjectures in
  Zhi-Wei Sun, arXiv:2302.08315):

    1. `conjecture1`: For v(0)=2, v(1)=A, v(n+1)=A*v(n)+v(n-1),
         A^2 * det[v(j+k) + delta(j,k)]_{1<=j,k<=n} = v(n+1)^2 - (A^2 + 4)*(n % 2).
       Corollary `conjecture1_lucas`: det[L(j+k) + delta(j,k)] = L(n+1)^2 - 5*(n % 2).
    2. `conjecture2`: For v(0)=2, v(1)=A, v(n+1)=A*v(n)-v(n-1) and u(0)=0, u(1)=1,
         det[v(j+k) + delta(j,k)]_{1<=j,k<=n} = u(n+1)^2 - n^2.
    3. `conjecture3`: For Fibonacci numbers F(n),
         det[F(j+k) + delta(j,k)]_{1<=j,k<=n} = F(n+1)^2 + (n % 2).

  Zero external dependencies (pure Lean 4 core). Zero `sorry`.
-/

namespace A360278

/-! ### Part 0: Core `Fin.succAbove` and `predOfNe` helpers -/

def succAbove {n : Nat} (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if h : i.val < p.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

theorem succAbove_val {n : Nat} (p : Fin (n + 1)) (i : Fin n) :
    (succAbove p i).val = if i.val < p.val then i.val else i.val + 1 := by
  unfold succAbove; split <;> rfl

theorem succAbove_zero {n : Nat} (i : Fin n) : succAbove (0 : Fin (n + 1)) i = i.succ := by
  ext; rw [succAbove_val]; simp

theorem succAbove_ne {n : Nat} (p : Fin (n + 1)) (i : Fin n) : succAbove p i ≠ p := by
  intro h
  have hv := congrArg Fin.val h
  rw [succAbove_val] at hv
  split at hv <;> omega

theorem succAbove_inj {n : Nat} {p : Fin (n + 1)} {i j : Fin n}
    (h : succAbove p i = succAbove p j) : i = j := by
  ext
  have hv := congrArg Fin.val h
  rw [succAbove_val, succAbove_val] at hv
  split at hv <;> split at hv <;> omega

def predOfNe {m : Nat} (i j : Fin (m + 1)) (h : j ≠ i) : Fin m :=
  if hlt : j.val < i.val then ⟨j.val, by omega⟩
  else ⟨j.val - 1, by
    have := j.isLt
    have : j.val ≠ i.val := fun heq => h (Fin.ext heq)
    omega⟩

theorem predOfNe_val {m : Nat} (i j : Fin (m + 1)) (h : j ≠ i) :
    (predOfNe i j h).val = if j.val < i.val then j.val else j.val - 1 := by
  unfold predOfNe; split <;> rfl

theorem succAbove_predOfNe {m : Nat} (i j : Fin (m + 1)) (h : j ≠ i) :
    succAbove i (predOfNe i j h) = j := by
  ext
  rw [succAbove_val, predOfNe_val]
  have hne : j.val ≠ i.val := fun heq => h (Fin.ext heq)
  by_cases hlt : j.val < i.val
  · simp [hlt]
  · have hge : ¬ (j.val - 1 < i.val) := by omega
    simp [hlt, hge]; omega

/-! ### Part 1: Finite sums and recursive Laplace determinant over Int -/

def sumFin : ∀ {n : Nat}, (Fin n → Int) → Int
  | 0, _ => 0
  | _ + 1, f => f 0 + sumFin (fun i => f i.succ)

theorem sumFin_zero {n : Nat} : sumFin (n := n) (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumFin, ih]

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumFin, ih]; omega

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin (fun i => c * f i) = c * sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp only [sumFin, ih, Int.mul_add]

theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin f = sumFin g := by
  have : f = g := funext h
  rw [this]

theorem sumFin_single {n : Nat} (k : Fin n) (f : Fin n → Int)
    (h : ∀ i, i ≠ k → f i = 0) : sumFin f = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    simp only [sumFin]
    cases k using Fin.cases with
    | zero =>
      have hrest : sumFin (fun i : Fin n => f i.succ) = 0 := by
        rw [sumFin_congr (fun i => h i.succ (Fin.succ_ne_zero i)), sumFin_zero]
      omega
    | succ k' =>
      have h0 : f 0 = 0 := h 0 (Ne.symm (Fin.succ_ne_zero k'))
      have hrest := ih k' (fun i => f i.succ) (fun i hi => h i.succ (fun heq => hi (Fin.succ_inj.mp heq)))
      omega

theorem sumFin_comm {m n : Nat} (f : Fin m → Fin n → Int) :
    sumFin (fun i => sumFin (fun j => f i j)) = sumFin (fun j => sumFin (fun i => f i j)) := by
  induction m with
  | zero => simp [sumFin, sumFin_zero]
  | succ m ih => simp only [sumFin, sumFin_add, ih]

def signFin {n : Nat} (i : Fin n) : Int :=
  if i.val % 2 = 0 then 1 else -1

theorem signFin_succ {n : Nat} (i : Fin n) : signFin i.succ = -signFin i := by
  unfold signFin
  simp only [Fin.val_succ]
  split <;> split <;> omega

def minor {n : Nat} (M : Fin (n + 1) → Fin (n + 1) → Int) (i : Fin (n + 1)) :
    Fin n → Fin n → Int :=
  fun r c => M (succAbove i r) c.succ

def det : ∀ {n : Nat}, (Fin n → Fin n → Int) → Int
  | 0, _ => 1
  | _ + 1, M => sumFin (fun i => signFin i * M i 0 * det (minor M i))

def idMat (n : Nat) : Fin n → Fin n → Int :=
  fun i j => if i = j then 1 else 0

theorem det_id (n : Nat) : det (idMat n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [det]
    rw [sumFin_single (0 : Fin (n + 1))]
    · have h0 : signFin (0 : Fin (n + 1)) = 1 := rfl
      have hm : idMat (n + 1) 0 0 = 1 := rfl
      have hmin : minor (idMat (n + 1)) 0 = idMat n := by
        funext r c
        simp only [minor, idMat, succAbove_zero, Fin.succ_inj]
      rw [h0, hm, hmin, ih]; rfl
    · intro i hi
      simp [idMat, hi]

def replaceCol {n : Nat} (M : Fin n → Fin n → Int) (c : Fin n) (v : Fin n → Int) :
    Fin n → Fin n → Int :=
  fun i j => if j = c then v i else M i j

theorem minor_replaceCol_zero {n : Nat} (M : Fin (n + 1) → Fin (n + 1) → Int) (v : Fin (n + 1) → Int)
    (i : Fin (n + 1)) : minor (replaceCol M 0 v) i = minor M i := by
  funext r c
  simp [minor, replaceCol, Fin.succ_ne_zero c]

theorem minor_replaceCol_succ {n : Nat} (M : Fin (n + 1) → Fin (n + 1) → Int) (c : Fin n)
    (v : Fin (n + 1) → Int) (i : Fin (n + 1)) :
    minor (replaceCol M c.succ v) i = replaceCol (minor M i) c (fun r => v (succAbove i r)) := by
  funext r k
  simp [minor, replaceCol, Fin.succ_inj]

theorem det_col_add {n : Nat} (M : Fin n → Fin n → Int) (c : Fin n) (u v : Fin n → Int) :
    det (replaceCol M c (fun i => u i + v i)) = det (replaceCol M c u) + det (replaceCol M c v) := by
  induction n with
  | zero => exact Fin.elim0 c
  | succ n ih =>
    simp only [det]
    cases c using Fin.cases with
    | zero =>
      rw [← sumFin_add]
      apply sumFin_congr; intro i
      simp only [minor_replaceCol_zero, replaceCol, ite_true]
      grind
    | succ c' =>
      rw [← sumFin_add]
      apply sumFin_congr; intro i
      have hne : (0 : Fin (n + 1)) ≠ c'.succ := Ne.symm (Fin.succ_ne_zero c')
      simp only [minor_replaceCol_succ, replaceCol, hne, ite_false]
      rw [ih]; grind

theorem det_col_smul {n : Nat} (M : Fin n → Fin n → Int) (c : Fin n) (a : Int) (u : Fin n → Int) :
    det (replaceCol M c (fun i => a * u i)) = a * det (replaceCol M c u) := by
  induction n with
  | zero => exact Fin.elim0 c
  | succ n ih =>
    simp only [det]
    cases c using Fin.cases with
    | zero =>
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro i
      simp only [minor_replaceCol_zero, replaceCol, ite_true]
      grind
    | succ c' =>
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro i
      have hne : (0 : Fin (n + 1)) ≠ c'.succ := Ne.symm (Fin.succ_ne_zero c')
      simp only [minor_replaceCol_succ, replaceCol, hne, ite_false]
      rw [ih]; grind

theorem det_eq_zero_of_col_zero {n : Nat} (M : Fin n → Fin n → Int) (c : Fin n)
    (hz : ∀ i, M i c = 0) : det M = 0 := by
  have h1 : M = replaceCol M c (fun i => 0 * M i c) := by
    funext i j; simp only [replaceCol]
    split
    · subst_vars; rw [hz]; rfl
    · rfl
  rw [h1, det_col_smul, Int.zero_mul]

/-! ### Alternating property: equal columns imply det = 0 -/

theorem succAbove_comm_pair {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    let i' : Fin (n + 2) := succAbove i j
    let j' : Fin (n + 1) := predOfNe i' i (Ne.symm (succAbove_ne i j))
    (∀ r : Fin n, succAbove i (succAbove j r) = succAbove i' (succAbove j' r)) ∧
    signFin i * signFin j = -(signFin i' * signFin j') := by
  intro i' j'
  have hi'_val : i'.val = if j.val < i.val then j.val else j.val + 1 := succAbove_val i j
  have hj'_val : j'.val = if i.val < i'.val then i.val else i.val - 1 := predOfNe_val i' i _
  constructor
  · intro r
    ext
    rw [succAbove_val, succAbove_val, succAbove_val, succAbove_val]
    split at hi'_val <;> split at hj'_val <;> split <;> split <;> split <;> split <;> omega
  · unfold signFin
    by_cases hlt : j.val < i.val
    · have hi' : i'.val = j.val := by simp [hlt] at hi'_val; exact hi'_val
      have hj' : j'.val = i.val - 1 := by
        have hnot : ¬ i.val < i'.val := by omega
        simp [hnot] at hj'_val; exact hj'_val
      rw [hi', hj']
      split <;> split <;> omega
    · have hi' : i'.val = j.val + 1 := by simp [hlt] at hi'_val; exact hi'_val
      have hj' : j'.val = i.val := by
        have hlt' : i.val < i'.val := by omega
        simp [hlt'] at hj'_val; exact hj'_val
      rw [hi', hj']
      split <;> split <;> omega

theorem sumFin_drop {m : Nat} (a : Fin (m + 1)) (h : Fin (m + 1) → Int) (ha : h a = 0) :
    sumFin h = sumFin (fun j : Fin m => h (succAbove a j)) := by
  induction m with
  | zero =>
    have ha0 : a = 0 := Fin.ext (by omega)
    subst ha0; simp [sumFin, ha]
  | succ m ih =>
    cases a using Fin.cases with
    | zero =>
      rw [sumFin, ha, Int.zero_add]
      apply sumFin_congr; intro j; rw [succAbove_zero]
    | succ a' =>
      change h 0 + sumFin (fun k => h k.succ) =
             h (succAbove a'.succ 0) + sumFin (fun j : Fin m => h (succAbove a'.succ j.succ))
      have h0 : succAbove a'.succ (0 : Fin (m + 1)) = 0 := by ext; rw [succAbove_val]; simp
      have hsucc : ∀ j : Fin m, succAbove a'.succ j.succ = (succAbove a' j).succ := by
        intro j; ext; rw [succAbove_val]; simp only [Fin.val_succ]; rw [succAbove_val]
        split <;> split <;> omega
      rw [h0, sumFin_congr (fun j => congrArg h (hsucc j)), ← ih a' (fun k => h k.succ) ha]

theorem sumFin_antisymm_pair {n : Nat} (F : Fin (n + 2) → Fin (n + 1) → Int)
    (hanti : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)),
      let i' := succAbove i j
      let j' := predOfNe i' i (Ne.symm (succAbove_ne i j))
      F i j = -F i' j') :
    sumFin (fun i => sumFin (fun j => F i j)) = 0 := by
  let G : Fin (n + 2) → Fin (n + 2) → Int :=
    fun a b => if h : b ≠ a then F a (predOfNe a b h) else 0
  have hrow : ∀ a : Fin (n + 2), sumFin (fun j : Fin (n + 1) => F a j) = sumFin (fun b => G a b) := by
    intro a
    rw [sumFin_drop a (G a) (by simp [G])]
    apply sumFin_congr; intro j
    have hne : succAbove a j ≠ a := succAbove_ne a j
    simp only [G, dif_pos hne]
    congr 1
    exact (succAbove_inj (succAbove_predOfNe a (succAbove a j) hne)).symm
  have hGanti : ∀ a b : Fin (n + 2), G a b = -G b a := by
    intro a b
    by_cases hab : b = a
    · subst hab; simp [G]
    · have hba : a ≠ b := Ne.symm hab
      simp only [G, dif_pos hab, dif_pos hba]
      have hspec := hanti a (predOfNe a b hab)
      have heq1 : succAbove a (predOfNe a b hab) = b := succAbove_predOfNe a b hab
      have hne1 : a ≠ succAbove a (predOfNe a b hab) := Ne.symm (succAbove_ne a (predOfNe a b hab))
      have heq2 : predOfNe (succAbove a (predOfNe a b hab)) a hne1 = predOfNe b a hba := by
        ext; rw [predOfNe_val, predOfNe_val, heq1]
      dsimp only at hspec
      rw [heq2, heq1] at hspec
      exact hspec
  rw [sumFin_congr hrow]
  have hneg : sumFin (fun a => sumFin (fun b => G a b)) =
              -sumFin (fun a => sumFin (fun b => G a b)) := by
    calc sumFin (fun a => sumFin (fun b => G a b))
        = sumFin (fun a => sumFin (fun b => (-1) * G b a)) := by
          apply sumFin_congr; intro a; apply sumFin_congr; intro b; rw [hGanti a b]; omega
      _ = sumFin (fun a => (-1) * sumFin (fun b => G b a)) := by
          apply sumFin_congr; intro a; rw [sumFin_mul_left]
      _ = (-1) * sumFin (fun a => sumFin (fun b => G b a)) := by rw [sumFin_mul_left]
      _ = (-1) * sumFin (fun b => sumFin (fun a => G b a)) := by rw [sumFin_comm]
      _ = -sumFin (fun a => sumFin (fun b => G a b)) := by omega
  omega

theorem det_eq_zero_of_col0_eq_col1 {n : Nat} (M : Fin (n + 2) → Fin (n + 2) → Int)
    (heq : ∀ i, M i 0 = M i 1) : det M = 0 := by
  rw [det]
  have hexp : ∀ i : Fin (n + 2),
      signFin i * M i 0 * det (minor M i) =
      sumFin (fun j : Fin (n + 1) =>
        signFin i * signFin j * M i 0 * M (succAbove i j) 0 *
        det (minor (minor M i) j)) := by
    intro i
    rw [det, ← sumFin_mul_left]
    apply sumFin_congr; intro j
    have h01 : minor M i j 0 = M (succAbove i j) 0 := by
      simp only [minor]; exact (heq (succAbove i j)).symm
    rw [h01]; grind
  rw [sumFin_congr hexp]
  apply sumFin_antisymm_pair
  intro i j
  have ⟨hmap, hsign⟩ := succAbove_comm_pair i j
  dsimp only at hmap hsign ⊢
  let i' := succAbove i j
  let j' := predOfNe i' i (Ne.symm (succAbove_ne i j))
  have hmin : minor (minor M i) j = minor (minor M i') j' := by
    funext r c; simp only [minor]; rw [hmap r]
  have hi_eq : succAbove i' j' = i := succAbove_predOfNe i' i (Ne.symm (succAbove_ne i j))
  rw [hmin, hi_eq, hsign]; grind

theorem det_swap_col0_col1 {n : Nat} (M : Fin (n + 2) → Fin (n + 2) → Int) :
    det (replaceCol (replaceCol M 0 (fun i => M i 1)) 1 (fun i => M i 0)) = -det M := by
  let u : Fin (n + 2) → Int := fun i => M i 0
  let v : Fin (n + 2) → Int := fun i => M i 1
  let uv : Fin (n + 2) → Int := fun i => u i + v i
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by intro h; have := congrArg Fin.val h; simp at this
  have h0 : det (replaceCol (replaceCol M 0 uv) 1 uv) = 0 :=
    det_eq_zero_of_col0_eq_col1 _ (fun i => by simp [replaceCol, h01])
  rw [det_col_add] at h0
  have h1 : replaceCol (replaceCol M 0 uv) 1 u = replaceCol (replaceCol M 1 u) 0 uv := by
    funext i j; simp only [replaceCol]; split <;> split <;> grind
  have h2 : replaceCol (replaceCol M 0 uv) 1 v = replaceCol (replaceCol M 1 v) 0 uv := by
    funext i j; simp only [replaceCol]; split <;> split <;> grind
  rw [h1, h2, det_col_add, det_col_add] at h0
  have huu : det (replaceCol (replaceCol M 1 u) 0 u) = 0 :=
    det_eq_zero_of_col0_eq_col1 _ (fun i => by simp [replaceCol, h01])
  have hvv : det (replaceCol (replaceCol M 1 v) 0 v) = 0 :=
    det_eq_zero_of_col0_eq_col1 _ (fun i => by simp [replaceCol, h01])
  have huv : replaceCol (replaceCol M 1 v) 0 u = M := by
    funext i j; simp only [replaceCol, u, v]
    split
    · subst_vars; rfl
    · split
      · subst_vars; rfl
      · rfl
  have hvu : replaceCol (replaceCol M 1 u) 0 v = replaceCol (replaceCol M 0 v) 1 u := by
    funext i j; simp only [replaceCol]; split <;> split <;> grind
  rw [huu, hvv, huv, hvu] at h0
  change det (replaceCol (replaceCol M 0 v) 1 u) = -det M
  omega

theorem det_swap_adj : ∀ {n : Nat} (M : Fin n → Fin n → Int) (c : Nat) (hc : c + 1 < n),
    det (replaceCol (replaceCol M ⟨c, by omega⟩ (fun i => M i ⟨c + 1, hc⟩))
          ⟨c + 1, hc⟩ (fun i => M i ⟨c, by omega⟩)) = -det M
  | 0, _, _, hc => by omega
  | 1, _, _, hc => by omega
  | n + 2, M, 0, _ => det_swap_col0_col1 M
  | n + 2, M, c + 1, hc => by
    let c1 : Fin (n + 2) := ⟨c + 1, by omega⟩
    let c2 : Fin (n + 2) := ⟨c + 2, hc⟩
    have hc1 : c1 = (⟨c, by omega⟩ : Fin (n + 1)).succ := rfl
    have hc2 : c2 = (⟨c + 1, by omega⟩ : Fin (n + 1)).succ := rfl
    rw [det, det]
    have hterm : ∀ i : Fin (n + 2),
        signFin i * (replaceCol (replaceCol M c1 (fun i => M i c2)) c2 (fun i => M i c1)) i 0 *
          det (minor (replaceCol (replaceCol M c1 (fun i => M i c2)) c2 (fun i => M i c1)) i) =
        (-1) * (signFin i * M i 0 * det (minor M i)) := by
      intro i
      have h0c1 : (0 : Fin (n + 2)) ≠ c1 := by intro h; have := congrArg Fin.val h; simp [c1] at this
      have h0c2 : (0 : Fin (n + 2)) ≠ c2 := by intro h; have := congrArg Fin.val h; simp [c2] at this
      have hm0 : (replaceCol (replaceCol M c1 (fun i => M i c2)) c2 (fun i => M i c1)) i 0 = M i 0 := by
        simp [replaceCol, h0c1, h0c2]
      rw [hm0, hc1, hc2, minor_replaceCol_succ, minor_replaceCol_succ]
      have hih := det_swap_adj (minor M i) c (by omega)
      have hdet_eq :
          det (replaceCol (replaceCol (minor M i) ⟨c, by omega⟩ (fun r => M (succAbove i r) (⟨c + 1, by omega⟩ : Fin (n + 1)).succ))
                ⟨c + 1, by omega⟩ (fun r => M (succAbove i r) (⟨c, by omega⟩ : Fin (n + 1)).succ)) =
          -det (minor M i) := hih
      rw [hdet_eq]; grind
    rw [sumFin_congr hterm, sumFin_mul_left]
    grind

theorem det_eq_zero_of_adj_eq : ∀ {n : Nat} (M : Fin n → Fin n → Int) (c : Nat) (hc : c + 1 < n),
    (∀ i, M i ⟨c, by omega⟩ = M i ⟨c + 1, hc⟩) → det M = 0
  | 0, _, _, hc, _ => by omega
  | 1, _, _, hc, _ => by omega
  | n + 2, M, 0, _, heq => det_eq_zero_of_col0_eq_col1 M heq
  | n + 2, M, c + 1, hc, heq => by
    rw [det]
    have hterm : ∀ i : Fin (n + 2), signFin i * M i 0 * det (minor M i) = 0 := by
      intro i
      have hih := det_eq_zero_of_adj_eq (minor M i) c (by omega) (fun r => heq (succAbove i r))
      rw [hih, Int.mul_zero]
    rw [sumFin_congr hterm, sumFin_zero]

theorem det_eq_zero_of_lt_col_eq {n : Nat} :
    ∀ (d : Nat) (M : Fin n → Fin n → Int) (c1 : Nat) (hc2 : c1 + 1 + d < n),
      (∀ i, M i ⟨c1, by omega⟩ = M i ⟨c1 + 1 + d, hc2⟩) → det M = 0
  | 0, M, c1, hc2, heq => det_eq_zero_of_adj_eq M c1 hc2 heq
  | d + 1, M, c1, hc2, heq => by
    have hswap := det_swap_adj M (c1 + 1 + d) (by omega)
    let M' := replaceCol (replaceCol M ⟨c1 + 1 + d, by omega⟩ (fun i => M i ⟨c1 + 1 + d + 1, by omega⟩))
                ⟨c1 + 1 + d + 1, by omega⟩ (fun i => M i ⟨c1 + 1 + d, by omega⟩)
    have hzero : det M' = 0 := by
      apply det_eq_zero_of_lt_col_eq d M' c1 (by omega)
      intro i
      have hne1 : (⟨c1, by omega⟩ : Fin n) ≠ ⟨c1 + 1 + d, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have hne2 : (⟨c1, by omega⟩ : Fin n) ≠ ⟨c1 + 1 + d + 1, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have hne3 : (⟨c1 + 1 + d, by omega⟩ : Fin n) ≠ ⟨c1 + 1 + d + 1, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      simp only [M', replaceCol, hne1, hne2, hne3, ite_false, ite_true]
      exact heq i
    have : det M' = -det M := hswap
    omega

theorem det_eq_zero_of_col_eq {n : Nat} (M : Fin n → Fin n → Int) (c1 c2 : Fin n)
    (h12 : c1 ≠ c2) (heq : ∀ i, M i c1 = M i c2) : det M = 0 := by
  have hne : c1.val ≠ c2.val := fun h => h12 (Fin.ext h)
  by_cases hlt : c1.val < c2.val
  · exact det_eq_zero_of_lt_col_eq (c2.val - c1.val - 1) M c1.val (by omega)
      (fun i => by
        have h1 : (⟨c1.val, by omega⟩ : Fin n) = c1 := Fin.ext rfl
        have h2 : (⟨c1.val + 1 + (c2.val - c1.val - 1), by omega⟩ : Fin n) = c2 := Fin.ext (by simp; omega)
        rw [h1, h2]; exact heq i)
  · exact det_eq_zero_of_lt_col_eq (c1.val - c2.val - 1) M c2.val (by omega)
      (fun i => by
        have h1 : (⟨c2.val, by omega⟩ : Fin n) = c2 := Fin.ext rfl
        have h2 : (⟨c2.val + 1 + (c1.val - c2.val - 1), by omega⟩ : Fin n) = c1 := Fin.ext (by simp; omega)
        rw [h1, h2]; exact (heq i).symm)

/-! ### Part 2: Rank-1 and Rank-2 Matrix Determinant Lemma -/

theorem det_replace1 : ∀ {n : Nat} (c : Fin n) (u : Fin n → Int),
    det (replaceCol (idMat n) c u) = u c
  | 0, c, _ => Fin.elim0 c
  | n + 1, c, u => by
    cases c using Fin.cases with
    | zero =>
      simp only [det]
      rw [sumFin_single (0 : Fin (n + 1))]
      · have h0 : signFin (0 : Fin (n + 1)) = 1 := rfl
        have hm0 : replaceCol (idMat (n + 1)) 0 u 0 0 = u 0 := rfl
        have hmin : minor (replaceCol (idMat (n + 1)) 0 u) 0 = idMat n := by
          funext r k; simp [minor, replaceCol, idMat, Fin.succ_ne_zero k, succAbove_zero, Fin.succ_inj]
        rw [h0, hm0, hmin, det_id]; omega
      · intro i hi
        have hi_pos : i.val ≥ 1 := by have : i.val ≠ 0 := fun h => hi (Fin.ext h); omega
        have hmin_zero : det (minor (replaceCol (idMat (n + 1)) 0 u) i) = 0 := by
          apply det_eq_zero_of_col_zero _ ⟨i.val - 1, by omega⟩
          intro r
          have hne : succAbove i r ≠ (⟨i.val - 1, by omega⟩ : Fin n).succ := by
            have : (⟨i.val - 1, by omega⟩ : Fin n).succ = i := Fin.ext (by simp; omega)
            rw [this]; exact succAbove_ne i r
          simp only [minor, replaceCol, idMat, Fin.succ_ne_zero, ite_false, hne]
        rw [hmin_zero, Int.mul_zero]
    | succ c' =>
      simp only [det]
      rw [sumFin_single (0 : Fin (n + 1))]
      · have h0 : signFin (0 : Fin (n + 1)) = 1 := rfl
        have hm0 : replaceCol (idMat (n + 1)) c'.succ u 0 0 = 1 := by
          simp [replaceCol, idMat, Ne.symm (Fin.succ_ne_zero c')]
        have hmin : minor (replaceCol (idMat (n + 1)) c'.succ u) 0 =
                    replaceCol (idMat n) c' (fun r => u r.succ) := by
          funext r k; simp [minor, replaceCol, idMat, succAbove_zero, Fin.succ_inj]
        rw [h0, hm0, hmin, det_replace1 c']; omega
      · intro i hi
        have hm0 : replaceCol (idMat (n + 1)) c'.succ u i 0 = 0 := by
          simp [replaceCol, idMat, Ne.symm (Fin.succ_ne_zero c'), hi]
        rw [hm0, Int.mul_zero, Int.zero_mul]

theorem det_shifted_id : ∀ {m : Nat} (c : Fin m) (w : Fin m → Int),
    det (fun r k : Fin m =>
      if k = c then w r else if succAbove c.succ r = k.succ then 1 else 0) =
    signFin c * w ⟨0, by have := c.isLt; omega⟩
  | 0, c, _ => Fin.elim0 c
  | m + 1, c, w => by
    cases c using Fin.cases with
    | zero =>
      simp only [det]
      rw [sumFin_single (0 : Fin (m + 1))]
      · have hs0 : signFin (0 : Fin (m + 1)) = 1 := rfl
        have hmin : minor (fun r k : Fin (m + 1) =>
            if k = 0 then w r else if succAbove (0 : Fin (m + 1)).succ r = k.succ then 1 else 0) 0 =
            idMat m := by
          funext r k
          have h1 : succAbove (0 : Fin (m + 1)).succ r.succ = r.succ.succ := by
            ext; rw [succAbove_val]; simp
          simp only [minor, idMat, Fin.succ_ne_zero k, ite_false, succAbove_zero, h1, Fin.succ_inj]
        rw [hs0, hmin, det_id]; simp
      · intro i hi
        have hi_pos : i.val ≥ 1 := by have : i.val ≠ 0 := fun h => hi (Fin.ext h); omega
        have hmin0 : det (minor (fun r k : Fin (m + 1) =>
            if k = 0 then w r else if succAbove (0 : Fin (m + 1)).succ r = k.succ then 1 else 0) i) = 0 := by
          apply det_eq_zero_of_col_zero _ ⟨i.val - 1, by omega⟩
          intro r
          have hne : succAbove (0 : Fin (m + 1)).succ (succAbove i r) ≠ (⟨i.val - 1, by omega⟩ : Fin m).succ.succ := by
            intro heq
            have hv := congrArg Fin.val heq
            rw [succAbove_val, succAbove_val] at hv
            simp only [Fin.val_succ, Fin.val_zero] at hv
            split at hv <;> split at hv <;> omega
          simp only [minor, Fin.succ_ne_zero, ite_false, hne]
        rw [hmin0, Int.mul_zero]
    | succ c0 =>
      simp only [det]
      let oneFin : Fin (m + 1) := ⟨1, by have := c0.isLt; omega⟩
      rw [sumFin_single oneFin]
      · have hs1 : signFin oneFin = -1 := by unfold signFin; simp [oneFin]
        have h0ne : (0 : Fin (m + 1)) ≠ c0.succ := Ne.symm (Fin.succ_ne_zero c0)
        have h1eq : succAbove c0.succ.succ oneFin = (0 : Fin (m + 1)).succ := by
          ext; rw [succAbove_val]; simp [oneFin]
        have hm1 : (if (0 : Fin (m + 1)) = c0.succ then w oneFin
                    else if succAbove c0.succ.succ oneFin = (0 : Fin (m + 1)).succ then 1 else 0) = 1 := by
          simp [h0ne, h1eq]
        have hmin : minor (fun r k : Fin (m + 1) =>
            if k = c0.succ then w r else if succAbove c0.succ.succ r = k.succ then 1 else 0) oneFin =
            (fun r k : Fin m =>
              if k = c0 then w (succAbove oneFin r)
              else if succAbove c0.succ r = k.succ then 1 else 0) := by
          funext r k
          simp only [minor, Fin.succ_inj]
          split
          · rfl
          · have hiff : (succAbove c0.succ.succ (succAbove oneFin r) = k.succ.succ) ↔
                        (succAbove c0.succ r = k.succ) := by
              constructor <;> intro h <;> ext <;> have hv := congrArg Fin.val h
              · rw [succAbove_val, succAbove_val] at hv; rw [succAbove_val]
                simp only [Fin.val_succ, oneFin] at hv ⊢
                split at hv <;> split at hv <;> split <;> omega
              · rw [succAbove_val] at hv; rw [succAbove_val, succAbove_val]
                simp only [Fin.val_succ, oneFin] at hv ⊢
                split at hv <;> split <;> split <;> omega
            by_cases hc : succAbove c0.succ r = k.succ
            · simp [hc, hiff.mpr hc]
            · have hnc : ¬ succAbove c0.succ.succ (succAbove oneFin r) = k.succ.succ := fun h => hc (hiff.mp h)
              simp [hc, hnc]
        rw [hs1, hm1, hmin, det_shifted_id c0]
        have hw0 : succAbove oneFin ⟨0, by have := c0.isLt; omega⟩ = ⟨0, by omega⟩ := by
          ext; rw [succAbove_val]; simp [oneFin]
        rw [hw0, signFin_succ]; grind
      · intro i hi
        have h0ne : (0 : Fin (m + 1)) ≠ c0.succ := Ne.symm (Fin.succ_ne_zero c0)
        have hne : succAbove c0.succ.succ i ≠ (0 : Fin (m + 1)).succ := by
          intro heq
          have hv := congrArg Fin.val heq
          rw [succAbove_val] at hv
          simp only [Fin.val_succ, Fin.val_zero] at hv
          have : i.val ≠ 1 := fun h => hi (Fin.ext h)
          split at hv <;> omega
        simp only [h0ne, hne, ite_false, Int.mul_zero, Int.zero_mul]

theorem det_replace2 : ∀ {n : Nat} (c1 c2 : Fin n) (h12 : c1 ≠ c2) (u1 u2 : Fin n → Int),
    det (replaceCol (replaceCol (idMat n) c1 u1) c2 u2) = u1 c1 * u2 c2 - u1 c2 * u2 c1
  | 0, c1, _, _, _, _ => Fin.elim0 c1
  | n + 1, c1, c2, h12, u1, u2 => by
    cases c1 using Fin.cases with
    | zero =>
      cases c2 using Fin.cases with
      | zero => exact absurd rfl h12
      | succ c2' =>
        simp only [det, sumFin]
        have h0_term :
            signFin (0 : Fin (n + 1)) * (replaceCol (replaceCol (idMat (n + 1)) 0 u1) c2'.succ u2) 0 0 *
              det (minor (replaceCol (replaceCol (idMat (n + 1)) 0 u1) c2'.succ u2) 0) =
            u1 0 * u2 c2'.succ := by
          have hs : signFin (0 : Fin (n + 1)) = 1 := rfl
          have hm : (replaceCol (replaceCol (idMat (n + 1)) 0 u1) c2'.succ u2) 0 0 = u1 0 := by
            simp [replaceCol, Ne.symm (Fin.succ_ne_zero c2')]
          have hmin : minor (replaceCol (replaceCol (idMat (n + 1)) 0 u1) c2'.succ u2) 0 =
                      replaceCol (idMat n) c2' (fun r => u2 r.succ) := by
            funext r k; simp [minor, replaceCol, idMat, Fin.succ_ne_zero k, succAbove_zero, Fin.succ_inj]
          rw [hs, hm, hmin, det_replace1 c2']; grind
        rw [h0_term, sumFin_single c2']
        · have hm : (replaceCol (replaceCol (idMat (n + 1)) 0 u1) c2'.succ u2) c2'.succ 0 = u1 c2'.succ := by
            simp [replaceCol, Ne.symm (Fin.succ_ne_zero c2')]
          have hmin_eq : minor (replaceCol (replaceCol (idMat (n + 1)) 0 u1) c2'.succ u2) c2'.succ =
              (fun r k : Fin n =>
                if k = c2' then u2 (succAbove c2'.succ r)
                else if succAbove c2'.succ r = k.succ then 1 else 0) := by
            funext r k; simp [minor, replaceCol, idMat, Fin.succ_inj, Fin.succ_ne_zero k]
          rw [hm, hmin_eq, det_shifted_id c2']
          have h0eq : succAbove c2'.succ ⟨0, by have := c2'.isLt; omega⟩ = 0 := by
            ext; rw [succAbove_val]; simp
          rw [h0eq, signFin_succ]
          have hs2 : signFin c2' * signFin c2' = 1 := by unfold signFin; split <;> decide
          grind
        · intro j hj
          have hne : j.succ ≠ c2'.succ := fun h => hj (Fin.succ_inj.mp h)
          have hmin0 : det (minor (replaceCol (replaceCol (idMat (n + 1)) 0 u1) c2'.succ u2) j.succ) = 0 := by
            apply det_eq_zero_of_col_zero _ j
            intro r
            have hne' : succAbove j.succ r ≠ j.succ := succAbove_ne j.succ r
            simp only [minor, replaceCol, idMat, hne, Fin.succ_ne_zero, ite_false, hne']
          rw [hmin0, Int.mul_zero]
    | succ c1' =>
      cases c2 using Fin.cases with
      | zero =>
        have hcomm : replaceCol (replaceCol (idMat (n + 1)) c1'.succ u1) 0 u2 =
                     replaceCol (replaceCol (idMat (n + 1)) 0 u2) c1'.succ u1 := by
          funext i j; simp only [replaceCol]; split <;> split <;> grind
        rw [hcomm, det_replace2 0 c1'.succ (Ne.symm (Fin.succ_ne_zero c1')) u2 u1]; grind
      | succ c2' =>
        simp only [det]
        rw [sumFin_single (0 : Fin (n + 1))]
        · have hs0 : signFin (0 : Fin (n + 1)) = 1 := rfl
          have hm0 : (replaceCol (replaceCol (idMat (n + 1)) c1'.succ u1) c2'.succ u2) 0 0 = 1 := by
            simp [replaceCol, idMat, Ne.symm (Fin.succ_ne_zero c1'), Ne.symm (Fin.succ_ne_zero c2')]
          have hmin : minor (replaceCol (replaceCol (idMat (n + 1)) c1'.succ u1) c2'.succ u2) 0 =
                      replaceCol (replaceCol (idMat n) c1' (fun r => u1 r.succ)) c2' (fun r => u2 r.succ) := by
            funext r k; simp [minor, replaceCol, idMat, succAbove_zero, Fin.succ_inj]
          rw [hs0, hm0, hmin, det_replace2 c1' c2' (fun h => h12 (congrArg Fin.succ h))]; omega
        · intro i hi
          have hm0 : (replaceCol (replaceCol (idMat (n + 1)) c1'.succ u1) c2'.succ u2) i 0 = 0 := by
            simp [replaceCol, idMat, Ne.symm (Fin.succ_ne_zero c1'), Ne.symm (Fin.succ_ne_zero c2'), hi]
          rw [hm0, Int.mul_zero, Int.zero_mul]

/-! ### Prefix dot product and Rank-2 Matrix Determinant Lemma -/

def prefixDot {n : Nat} (a b : Fin n → Int) : Nat → Int
  | 0 => 0
  | m + 1 => if h : m < n then prefixDot a b m + a ⟨m, h⟩ * b ⟨m, h⟩ else prefixDot a b m

def dot {n : Nat} (a b : Fin n → Int) : Int := prefixDot a b n

def matPrefix {n : Nat} (u1 u2 v1 v2 : Fin n → Int) (m : Nat) : Fin n → Fin n → Int :=
  fun i j =>
    if j.val < m then (if i = j then 1 else 0) + u1 i * v1 j + u2 i * v2 j
    else if i = j then 1 else 0

def matRank1WithCol {n : Nat} (u1 u2 v2 : Fin n → Int) (c : Fin n) (m : Nat) : Fin n → Fin n → Int :=
  fun i j =>
    if j = c then u1 i
    else if j.val < m then (if i = j then 1 else 0) + u2 i * v2 j
    else if i = j then 1 else 0

theorem det_matRank1WithCol_u2_cancel {n : Nat} (u1 u2 v2 : Fin n → Int) (c j0 : Fin n)
    (hjlt : j0.val < c.val) : ∀ k ≤ j0.val,
      det (replaceCol (matRank1WithCol u1 u2 v2 c k) j0 u2) =
      det (replaceCol (replaceCol (idMat n) c u1) j0 u2)
  | 0, _ => by apply congrArg det; funext i j; simp [replaceCol, matRank1WithCol, idMat]
  | k + 1, hk => by
    have hkn : k < n := by have := j0.isLt; omega
    let jk : Fin n := ⟨k, hkn⟩
    have hjkj0 : jk ≠ j0 := by intro h; have := congrArg Fin.val h; simp [jk] at this; omega
    have hjkc : jk ≠ c := by intro h; have := congrArg Fin.val h; simp [jk] at this; omega
    have hs : replaceCol (matRank1WithCol u1 u2 v2 c (k + 1)) j0 u2 =
        replaceCol (replaceCol (matRank1WithCol u1 u2 v2 c k) j0 u2) jk
          (fun i => (if i = jk then 1 else 0) + v2 jk * u2 i) := by
      funext i j; simp only [replaceCol, matRank1WithCol]
      by_cases h1 : j = jk
      · subst h1; simp only [ite_true, hjkj0, hjkc, ite_false, jk]
        have : k < k + 1 := by omega
        simp [this, Int.mul_comm]
      · simp only [h1, ite_false]
        by_cases h2 : j = j0
        · simp [h2]
        · simp only [h2, ite_false]
          by_cases h3 : j = c
          · simp [h3]
          · simp only [h3, ite_false]
            have hne : j.val ≠ k := fun h => h1 (Fin.ext h)
            have hiff : (j.val < k + 1) ↔ (j.val < k) := by omega
            by_cases hlt : j.val < k
            · simp [hlt, show j.val < k + 1 by omega]
            · simp [hlt, show ¬ j.val < k + 1 by omega]
    rw [hs, det_col_add, det_col_smul]
    have hzero : det (replaceCol (replaceCol (matRank1WithCol u1 u2 v2 c k) j0 u2) jk u2) = 0 :=
      det_eq_zero_of_col_eq _ jk j0 hjkj0 (fun i => by simp [replaceCol, hjkj0])
    have hsame : replaceCol (replaceCol (matRank1WithCol u1 u2 v2 c k) j0 u2) jk (fun i => if i = jk then 1 else 0) =
                 replaceCol (matRank1WithCol u1 u2 v2 c k) j0 u2 := by
      funext i j; simp only [replaceCol, matRank1WithCol]
      split
      · rename_i h; subst h; simp [hjkj0, hjkc, jk]
      · rfl
    rw [hzero, Int.mul_zero, Int.add_zero, hsame, det_matRank1WithCol_u2_cancel u1 u2 v2 c j0 hjlt k (by omega)]

theorem det_matRank1WithCol {n : Nat} (u1 u2 v2 : Fin n → Int) (c : Fin n) :
    ∀ m ≤ c.val,
      det (matRank1WithCol u1 u2 v2 c m) =
        u1 c + u1 c * prefixDot v2 u2 m - u2 c * prefixDot v2 u1 m
  | 0, _ => by
    have heq : matRank1WithCol u1 u2 v2 c 0 = replaceCol (idMat n) c u1 := by
      funext i j; simp [matRank1WithCol, replaceCol, idMat]
    rw [heq, det_replace1 c u1]; simp [prefixDot]
  | m + 1, hmc => by
    have hm : m < n := by have := c.isLt; omega
    let j0 : Fin n := ⟨m, hm⟩
    have hjlt : j0.val < c.val := by simp [j0]; omega
    have hjc : j0 ≠ c := by intro h; have := congrArg Fin.val h; omega
    have hsplit : matRank1WithCol u1 u2 v2 c (m + 1) =
        replaceCol (matRank1WithCol u1 u2 v2 c m) j0
          (fun i => (if i = j0 then 1 else 0) + v2 j0 * u2 i) := by
      funext i j; simp only [matRank1WithCol, replaceCol]
      by_cases h1 : j = j0
      · subst h1; simp only [ite_true, hjc, ite_false, j0]
        have : m < m + 1 := by omega
        simp [this, Int.mul_comm]
      · simp only [h1, ite_false]
        by_cases h2 : j = c
        · simp [h2]
        · simp only [h2, ite_false]
          have hne : j.val ≠ m := fun h => h1 (Fin.ext h)
          have hiff : (j.val < m + 1) ↔ (j.val < m) := by omega
          by_cases hlt : j.val < m
          · simp [hlt, show j.val < m + 1 by omega]
          · simp [hlt, show ¬ j.val < m + 1 by omega]
    rw [hsplit, det_col_add, det_col_smul]
    have ht1 : replaceCol (matRank1WithCol u1 u2 v2 c m) j0 (fun i => if i = j0 then 1 else 0) =
               matRank1WithCol u1 u2 v2 c m := by
      funext i j; simp only [replaceCol, matRank1WithCol]
      split
      · rename_i h; subst h; simp [hjc, j0]
      · rfl
    rw [ht1, det_matRank1WithCol u1 u2 v2 c m (by omega),
        det_matRank1WithCol_u2_cancel u1 u2 v2 c j0 hjlt m (Nat.le_refl m),
        det_replace2 c j0 (Ne.symm hjc) u1 u2]
    simp only [prefixDot, dif_pos hm, j0]; grind

theorem det_matPrefix_two_cols_cancel {n : Nat} (u1 u2 v1 v2 : Fin n → Int) (c jk : Fin n)
    (hjklt : jk.val < c.val) : ∀ t ≤ jk.val,
      det (replaceCol (replaceCol (matPrefix u1 u2 v1 v2 t) c u1) jk u2) =
      det (replaceCol (replaceCol (idMat n) c u1) jk u2)
  | 0, _ => by apply congrArg det; funext i j; simp [replaceCol, matPrefix, idMat]
  | t + 1, ht => by
    have htn : t < n := by have := jk.isLt; omega
    let jt : Fin n := ⟨t, htn⟩
    have hjtc : jt ≠ c := by intro h; have := congrArg Fin.val h; simp [jt] at this; omega
    have hjtjk : jt ≠ jk := by intro h; have := congrArg Fin.val h; simp [jt] at this; omega
    have hsp : replaceCol (replaceCol (matPrefix u1 u2 v1 v2 (t + 1)) c u1) jk u2 =
        replaceCol (replaceCol (replaceCol (matPrefix u1 u2 v1 v2 t) c u1) jk u2) jt
          (fun i => ((if i = jt then 1 else 0) + v1 jt * u1 i) + v2 jt * u2 i) := by
      funext i j; simp only [replaceCol, matPrefix]
      by_cases h1 : j = jt
      · subst h1; simp only [ite_true, hjtjk, hjtc, ite_false, jt]
        have : t < t + 1 := by omega
        simp [this, Int.mul_comm]
      · simp only [h1, ite_false]
        by_cases h2 : j = jk
        · simp [h2]
        · simp only [h2, ite_false]
          by_cases h3 : j = c
          · simp [h3]
          · simp only [h3, ite_false]
            have hne : j.val ≠ t := fun h => h1 (Fin.ext h)
            have hiff : (j.val < t + 1) ↔ (j.val < t) := by omega
            by_cases hlt : j.val < t
            · simp [hlt, show j.val < t + 1 by omega]
            · simp [hlt, show ¬ j.val < t + 1 by omega]
    rw [hsp, det_col_add, det_col_smul]
    have hz2 : det (replaceCol (replaceCol (replaceCol (matPrefix u1 u2 v1 v2 t) c u1) jk u2) jt u2) = 0 :=
      det_eq_zero_of_col_eq _ jt jk hjtjk (fun i => by simp [replaceCol, hjtjk])
    rw [hz2, Int.mul_zero, Int.add_zero, det_col_add, det_col_smul]
    have hjkc' : c ≠ jk := by intro h; have := congrArg Fin.val h; omega
    have hz1 : det (replaceCol (replaceCol (replaceCol (matPrefix u1 u2 v1 v2 t) c u1) jk u2) jt u1) = 0 :=
      det_eq_zero_of_col_eq _ jt c hjtc (fun i => by simp [replaceCol, hjtjk, hjtc, hjkc'])
    have hsm : replaceCol (replaceCol (replaceCol (matPrefix u1 u2 v1 v2 t) c u1) jk u2) jt
                (fun i => if i = jt then 1 else 0) =
               replaceCol (replaceCol (matPrefix u1 u2 v1 v2 t) c u1) jk u2 := by
      funext i j; simp only [replaceCol, matPrefix]
      split
      · rename_i h; subst h; simp [hjtjk, hjtc, jt]
      · rfl
    rw [hz1, Int.mul_zero, Int.add_zero, hsm, det_matPrefix_two_cols_cancel u1 u2 v1 v2 c jk hjklt t (by omega)]

theorem det_matPrefix_with_col {n : Nat} (u1 u2 v1 v2 : Fin n → Int) (c : Fin n) :
    ∀ m ≤ c.val,
      det (replaceCol (matPrefix u1 u2 v1 v2 m) c u1) =
        u1 c + u1 c * prefixDot v2 u2 m - u2 c * prefixDot v2 u1 m := by
  intro m hm
  have hred : ∀ k ≤ m,
      det (replaceCol (matPrefix u1 u2 v1 v2 k) c u1) = det (matRank1WithCol u1 u2 v2 c k) := by
    intro k
    induction k with
    | zero => intro _; apply congrArg det; funext i j; simp [replaceCol, matPrefix, matRank1WithCol]
    | succ k ihk =>
      intro hk
      have hkn : k < n := by have := c.isLt; omega
      let jk : Fin n := ⟨k, hkn⟩
      have hjklt : jk.val < c.val := by simp [jk]; omega
      have hjkc : jk ≠ c := by intro h; have := congrArg Fin.val h; omega
      have hs : replaceCol (matPrefix u1 u2 v1 v2 (k + 1)) c u1 =
          replaceCol (replaceCol (matPrefix u1 u2 v1 v2 k) c u1) jk
            (fun i => ((if i = jk then 1 else 0) + v2 jk * u2 i) + v1 jk * u1 i) := by
        funext i j; simp only [replaceCol, matPrefix]
        by_cases h1 : j = jk
        · subst h1; simp only [ite_true, hjkc, ite_false, jk]
          have : k < k + 1 := by omega
          simp [this]; grind
        · simp only [h1, ite_false]
          by_cases h2 : j = c
          · simp [h2]
          · simp only [h2, ite_false]
            have hne : j.val ≠ k := fun h => h1 (Fin.ext h)
            have hiff : (j.val < k + 1) ↔ (j.val < k) := by omega
            by_cases hlt : j.val < k
            · simp [hlt, show j.val < k + 1 by omega]
            · simp [hlt, show ¬ j.val < k + 1 by omega]
      rw [hs, det_col_add, det_col_smul]
      have hz1 : det (replaceCol (replaceCol (matPrefix u1 u2 v1 v2 k) c u1) jk u1) = 0 :=
        det_eq_zero_of_col_eq _ jk c hjkc (fun i => by simp [replaceCol, hjkc])
      rw [hz1, Int.mul_zero, Int.add_zero, det_col_add, det_col_smul]
      have hs_rhs : matRank1WithCol u1 u2 v2 c (k + 1) =
          replaceCol (matRank1WithCol u1 u2 v2 c k) jk
            (fun i => (if i = jk then 1 else 0) + v2 jk * u2 i) := by
        funext i j; simp only [replaceCol, matRank1WithCol]
        by_cases h1 : j = jk
        · subst h1; simp only [ite_true, hjkc, ite_false, jk]
          have : k < k + 1 := by omega
          simp [this, Int.mul_comm]
        · simp only [h1, ite_false]
          by_cases h2 : j = c
          · simp [h2]
          · simp only [h2, ite_false]
            have hne : j.val ≠ k := fun h => h1 (Fin.ext h)
            have hiff : (j.val < k + 1) ↔ (j.val < k) := by omega
            by_cases hlt : j.val < k
            · simp [hlt, show j.val < k + 1 by omega]
            · simp [hlt, show ¬ j.val < k + 1 by omega]
      rw [hs_rhs, det_col_add, det_col_smul]
      have hl1 : replaceCol (replaceCol (matPrefix u1 u2 v1 v2 k) c u1) jk (fun i => if i = jk then 1 else 0) =
                 replaceCol (matPrefix u1 u2 v1 v2 k) c u1 := by
        funext i j; simp only [replaceCol, matPrefix]
        split
        · rename_i h; subst h; simp [hjkc, jk]
        · rfl
      have hr1 : replaceCol (matRank1WithCol u1 u2 v2 c k) jk (fun i => if i = jk then 1 else 0) =
                 matRank1WithCol u1 u2 v2 c k := by
        funext i j; simp only [replaceCol, matRank1WithCol]
        split
        · rename_i h; subst h; simp [hjkc, jk]
        · rfl
      rw [hl1, hr1, ihk (by omega),
          det_matPrefix_two_cols_cancel u1 u2 v1 v2 c jk hjklt k (Nat.le_refl k),
          det_matRank1WithCol_u2_cancel u1 u2 v2 c jk hjklt k (Nat.le_refl k)]
  rw [hred m (Nat.le_refl m), det_matRank1WithCol u1 u2 v2 c m hm]

theorem det_matPrefix {n : Nat} (u1 u2 v1 v2 : Fin n → Int) :
    ∀ m ≤ n,
      det (matPrefix u1 u2 v1 v2 m) =
        (1 + prefixDot v1 u1 m) * (1 + prefixDot v2 u2 m) -
        prefixDot v1 u2 m * prefixDot v2 u1 m
  | 0, _ => by
    have heq : matPrefix u1 u2 v1 v2 0 = idMat n := by funext i j; simp [matPrefix, idMat]
    rw [heq, det_id]; simp [prefixDot]
  | m + 1, hmn => by
    have hm : m < n := by omega
    let c : Fin n := ⟨m, hm⟩
    have hsp : matPrefix u1 u2 v1 v2 (m + 1) =
        replaceCol (matPrefix u1 u2 v1 v2 m) c
          (fun i => ((if i = c then 1 else 0) + v1 c * u1 i) + v2 c * u2 i) := by
      funext i j; simp only [matPrefix, replaceCol]
      by_cases hjc : j = c
      · subst hjc; simp only [ite_true, c]
        have : m < m + 1 := by omega
        simp [this, Int.mul_comm]
      · simp only [hjc, ite_false]
        have hne : j.val ≠ m := fun h => hjc (Fin.ext h)
        have hiff : (j.val < m + 1) ↔ (j.val < m) := by omega
        by_cases hlt : j.val < m
        · simp [hlt, show j.val < m + 1 by omega]
        · simp [hlt, show ¬ j.val < m + 1 by omega]
    rw [hsp, det_col_add, det_col_smul, det_col_add, det_col_smul]
    have ht0 : replaceCol (matPrefix u1 u2 v1 v2 m) c (fun i => if i = c then 1 else 0) =
               matPrefix u1 u2 v1 v2 m := by
      funext i j; simp only [replaceCol, matPrefix]
      split
      · rename_i h; subst h; simp [c]
      · rfl
    have ht2_symm : matPrefix u1 u2 v1 v2 m = matPrefix u2 u1 v2 v1 m := by
      funext i j; simp only [matPrefix]; split
      · omega
      · rfl
    have hmc : m ≤ c.val := by simp [c]
    rw [ht0, det_matPrefix u1 u2 v1 v2 m (by omega),
        det_matPrefix_with_col u1 u2 v1 v2 c m hmc,
        ht2_symm, det_matPrefix_with_col u2 u1 v2 v1 c m hmc]
    simp only [prefixDot, dif_pos hm, c]; grind

/-- Rank-2 Matrix Determinant Lemma: det(I_n + u1 v1^T + u2 v2^T) = det(I_2 + V^T U). -/
theorem det_id_add_rank2 {n : Nat} (u1 u2 v1 v2 : Fin n → Int) :
    det (fun i j : Fin n => (if i = j then 1 else 0) + u1 i * v1 j + u2 i * v2 j) =
      (1 + dot v1 u1) * (1 + dot v2 u2) - dot v1 u2 * dot v2 u1 := by
  have heq : (fun i j : Fin n => (if i = j then 1 else 0) + u1 i * v1 j + u2 i * v2 j) =
             matPrefix u1 u2 v1 v2 n := by
    funext i j; simp [matPrefix, j.isLt]
  rw [heq]
  exact det_matPrefix u1 u2 v1 v2 n (Nat.le_refl n)

/-! ### Part 3: Helper relating `dot` to natural-number sums -/

def sumNat (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumNat f n + f (n + 1)

theorem prefixDot_eq_sumNat {n : Nat} (a b : Nat → Int) :
    ∀ m ≤ n, prefixDot (fun i : Fin n => a (i.val + 1)) (fun i : Fin n => b (i.val + 1)) m =
             sumNat (fun k => a k * b k) m
  | 0, _ => rfl
  | m + 1, hm => by
    have hmn : m < n := by omega
    rw [prefixDot, dif_pos hmn, sumNat, prefixDot_eq_sumNat a b m (by omega)]

theorem dot_eq_sumNat (n : Nat) (a b : Nat → Int) :
    dot (fun i : Fin n => a (i.val + 1)) (fun i : Fin n => b (i.val + 1)) =
      sumNat (fun k => a k * b k) n :=
  prefixDot_eq_sumNat a b n (Nat.le_refl n)

/-! ### Part 4: Lucas sequences and Conjectures 1, 2, 3 of OEIS A360278 -/

def uSeq (A B : Int) : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => A * uSeq A B (n + 1) - B * uSeq A B n

def vSeq (A B : Int) : Nat → Int
  | 0 => 2
  | 1 => A
  | n + 2 => A * vSeq A B (n + 1) - B * vSeq A B n

theorem w_add_decomp (A B : Int) (w : Nat → Int)
    (hw : ∀ m, w (m + 2) = A * w (m + 1) - B * w m) :
    ∀ j k, w (j + (k + 1)) = w (j + 1) * uSeq A B (k + 1) - B * w j * uSeq A B k
  | j, 0 => by simp [uSeq]
  | j, 1 => by
    simp only [uSeq]
    rw [show j + (1 + 1) = j + 2 by omega, hw j]; grind
  | j, k + 2 => by
    have ih1 := w_add_decomp A B w hw j (k + 1)
    have ih0 := w_add_decomp A B w hw j k
    have hidx : j + (k + 2 + 1) = (j + (k + 1)) + 2 := by omega
    have hidx1 : (j + (k + 1)) + 1 = j + (k + 1 + 1) := by omega
    rw [hidx, hw, hidx1, ih1, ih0]
    simp only [uSeq]; grind

def epsInt (n : Nat) : Int := if n % 2 = 0 then 0 else 1

/-! #### Conjecture 1 (B = -1) -/

theorem v1_of_u1 (A : Int) :
    ∀ n, vSeq A (-1) (n + 1) = A * uSeq A (-1) (n + 1) + 2 * uSeq A (-1) n
  | 0 => by simp [vSeq, uSeq]
  | 1 => by simp [vSeq, uSeq]
  | n + 2 => by
    have ih1 := v1_of_u1 A (n + 1)
    have ih0 := v1_of_u1 A n
    have hv : vSeq A (-1) (n + 3) = A * vSeq A (-1) (n + 2) + vSeq A (-1) (n + 1) := by simp [vSeq]
    have hu : uSeq A (-1) (n + 3) = A * uSeq A (-1) (n + 2) + uSeq A (-1) (n + 1) := by simp [uSeq]
    have hu2 : uSeq A (-1) (n + 2) = A * uSeq A (-1) (n + 1) + uSeq A (-1) n := by simp [uSeq]
    rw [hv, hu, ih1, ih0, hu2]; grind

theorem cassini_u1 (A : Int) :
    ∀ n, uSeq A (-1) (n + 1) * uSeq A (-1) (n + 1) -
         A * uSeq A (-1) (n + 1) * uSeq A (-1) n -
         uSeq A (-1) n * uSeq A (-1) n = if n % 2 = 0 then 1 else -1
  | 0 => by simp [uSeq]
  | n + 1 => by
    have ih := cassini_u1 A n
    have hrec : uSeq A (-1) (n + 2) = A * uSeq A (-1) (n + 1) + uSeq A (-1) n := by simp [uSeq]
    rw [hrec]
    split at ih <;> split <;> grind

theorem u1_v1_cross (A : Int) :
    ∀ k, uSeq A (-1) (k + 1) * vSeq A (-1) k - uSeq A (-1) k * vSeq A (-1) (k + 1) =
         if k % 2 = 0 then 2 else -2
  | 0 => by simp [uSeq, vSeq]
  | k + 1 => by
    have ih := u1_v1_cross A k
    have hu : uSeq A (-1) (k + 2) = A * uSeq A (-1) (k + 1) + uSeq A (-1) k := by simp [uSeq]
    have hv : vSeq A (-1) (k + 2) = A * vSeq A (-1) (k + 1) + vSeq A (-1) k := by simp [vSeq]
    rw [hu, hv]; split at ih <;> split <;> grind

theorem conj1_s11 (A : Int) :
    ∀ n, A * sumNat (fun j => uSeq A (-1) j * vSeq A (-1) (j + 1)) n =
         uSeq A (-1) (n + 1) * vSeq A (-1) (n + 1) - A * (1 - epsInt n)
  | 0 => by simp [sumNat, uSeq, vSeq, epsInt]
  | n + 1 => by
    have ih := conj1_s11 A n
    have hu : uSeq A (-1) (n + 2) = A * uSeq A (-1) (n + 1) + uSeq A (-1) n := by simp [uSeq]
    have hv1 := v1_of_u1 A n
    have hv2 := v1_of_u1 A (n + 1)
    have hcas := cassini_u1 A n
    simp only [sumNat, epsInt] at ih ⊢
    split at hcas <;> split <;> grind

theorem conj1_s12 (A : Int) :
    ∀ n, A * sumNat (fun j => uSeq A (-1) j * vSeq A (-1) j) n =
         uSeq A (-1) (n + 1) * vSeq A (-1) n - 2 * (1 - epsInt n)
  | 0 => by simp [sumNat, uSeq, vSeq, epsInt]
  | n + 1 => by
    have ih := conj1_s12 A n
    have hu : uSeq A (-1) (n + 2) = A * uSeq A (-1) (n + 1) + uSeq A (-1) n := by simp [uSeq]
    have hd := u1_v1_cross A n
    simp only [sumNat, epsInt] at ih ⊢
    split at hd <;> split <;> grind

theorem conj1_s21 (A : Int) :
    ∀ n, A * sumNat (fun j => uSeq A (-1) (j - 1) * vSeq A (-1) (j + 1)) n =
         uSeq A (-1) n * vSeq A (-1) (n + 1) - (A * A + 2) * epsInt n
  | 0 => by simp [sumNat, uSeq, vSeq, epsInt]
  | n + 1 => by
    have ih := conj1_s21 A n
    have hrel : ∀ k, A * uSeq A (-1) k * vSeq A (-1) (k + 2) =
                     uSeq A (-1) (k + 1) * vSeq A (-1) (k + 2) - uSeq A (-1) k * vSeq A (-1) (k + 1) +
                     (if k % 2 = 0 then -(A * A + 2) else A * A + 2) := by
      intro k
      induction k with
      | zero => simp [uSeq, vSeq]; grind
      | succ k ihk =>
        have hu2 : uSeq A (-1) (k + 2) = A * uSeq A (-1) (k + 1) + uSeq A (-1) k := by simp [uSeq]
        have hv3 : vSeq A (-1) (k + 3) = A * vSeq A (-1) (k + 2) + vSeq A (-1) (k + 1) := by simp [vSeq]
        rw [hu2, hv3]; split at ihk <;> split <;> grind
    have hr := hrel n
    simp only [sumNat, Nat.add_sub_cancel, epsInt] at ih ⊢
    split at hr <;> split <;> grind

theorem conj1_s22 (A : Int) :
    ∀ n, A * sumNat (fun j => uSeq A (-1) (j - 1) * vSeq A (-1) j) n =
         uSeq A (-1) n * vSeq A (-1) n - A * epsInt n
  | 0 => by simp [sumNat, uSeq, vSeq, epsInt]
  | n + 1 => by
    have hshift : sumNat (fun j => uSeq A (-1) (j - 1) * vSeq A (-1) j) (n + 1) =
                  sumNat (fun j => uSeq A (-1) j * vSeq A (-1) (j + 1)) n := by
      induction n with
      | zero => simp [sumNat, uSeq]
      | succ k ihk =>
        change sumNat (fun j => uSeq A (-1) (j - 1) * vSeq A (-1) j) (k + 1) +
               uSeq A (-1) (k + 1 + 1 - 1) * vSeq A (-1) (k + 1 + 1) =
               sumNat (fun j => uSeq A (-1) j * vSeq A (-1) (j + 1)) k +
               uSeq A (-1) (k + 1) * vSeq A (-1) (k + 1 + 1)
        rw [ihk, Nat.add_sub_cancel]
    rw [hshift, conj1_s11 A n]
    simp only [epsInt]; split <;> split <;> grind

/-- Conjecture 1 of OEIS A360278 (and arXiv:2302.08315). -/
theorem conjecture1 (A : Int) (n : Nat) :
    A * A * det (fun i j : Fin n => (if i = j then 1 else 0) + vSeq A (-1) (i.val + j.val + 2)) =
      vSeq A (-1) (n + 1) * vSeq A (-1) (n + 1) - (A * A + 4) * epsInt n := by
  have hmat : (fun i j : Fin n => (if i = j then 1 else 0) + vSeq A (-1) (i.val + j.val + 2)) =
      (fun i j : Fin n =>
        (if i = j then 1 else 0) +
        vSeq A (-1) (i.val + 2) * uSeq A (-1) (j.val + 1) +
        vSeq A (-1) (i.val + 1) * uSeq A (-1) j.val) := by
    funext i j
    have hd := w_add_decomp A (-1) (vSeq A (-1)) (fun m => by simp [vSeq]) (i.val + 1) j.val
    rw [show i.val + 1 + (j.val + 1) = i.val + j.val + 2 by omega] at hd
    rw [hd]; grind
  rw [hmat, det_id_add_rank2]
  have hs11 := dot_eq_sumNat n (fun k => uSeq A (-1) k) (fun k => vSeq A (-1) (k + 1))
  have hs12 := dot_eq_sumNat n (fun k => uSeq A (-1) k) (fun k => vSeq A (-1) k)
  have hs21 := dot_eq_sumNat n (fun k => uSeq A (-1) (k - 1)) (fun k => vSeq A (-1) (k + 1))
  have hs22 := dot_eq_sumNat n (fun k => uSeq A (-1) (k - 1)) (fun k => vSeq A (-1) k)
  simp only [Nat.add_sub_cancel] at hs21 hs22
  rw [hs11, hs12, hs21, hs22]
  have h11 := conj1_s11 A n
  have h12 := conj1_s12 A n
  have h21 := conj1_s21 A n
  have h22 := conj1_s22 A n
  have hv1 := v1_of_u1 A n
  have hcas := cassini_u1 A n
  have hvn : vSeq A (-1) n = 2 * uSeq A (-1) (n + 1) - A * uSeq A (-1) n := by
    cases n with
    | zero => simp [vSeq, uSeq]
    | succ k =>
      have hk := v1_of_u1 A k
      have hu : uSeq A (-1) (k + 2) = A * uSeq A (-1) (k + 1) + uSeq A (-1) k := by simp [uSeq]
      rw [hk, hu]; grind
  let s11 := sumNat (fun k => uSeq A (-1) k * vSeq A (-1) (k + 1)) n
  let s12 := sumNat (fun k => uSeq A (-1) k * vSeq A (-1) k) n
  let s21 := sumNat (fun k => uSeq A (-1) (k - 1) * vSeq A (-1) (k + 1)) n
  let s22 := sumNat (fun k => uSeq A (-1) (k - 1) * vSeq A (-1) k) n
  have hmul : A * A * ((1 + s11) * (1 + s22) - s12 * s21) =
              (A + A * s11) * (A + A * s22) - (A * s12) * (A * s21) := by grind
  rw [hmul, h11, h12, h21, h22, hv1, hvn]
  clear hmat hs11 hs12 hs21 hs22 h11 h12 h21 h22 hv1 hvn hmul s11 s12 s21 s22
  simp only [epsInt] at *
  split at hcas <;> split <;> grind

/-- Corollary (OEIS A360278 main sequence, Lucas numbers A = 1). -/
theorem conjecture1_lucas (n : Nat) :
    det (fun i j : Fin n => (if i = j then 1 else 0) + vSeq 1 (-1) (i.val + j.val + 2)) =
      vSeq 1 (-1) (n + 1) * vSeq 1 (-1) (n + 1) - 5 * epsInt n := by
  have h := conjecture1 1 n
  simp only [Int.one_mul] at h
  exact h

/-! #### Conjecture 2 (B = +1) -/

theorem v2_of_u2 (A : Int) :
    ∀ n, vSeq A 1 (n + 1) = A * uSeq A 1 (n + 1) - 2 * uSeq A 1 n
  | 0 => by simp [vSeq, uSeq]
  | 1 => by simp [vSeq, uSeq]
  | n + 2 => by
    have ih1 := v2_of_u2 A (n + 1)
    have ih0 := v2_of_u2 A n
    have hv : vSeq A 1 (n + 3) = A * vSeq A 1 (n + 2) - vSeq A 1 (n + 1) := by simp [vSeq]
    have hu : uSeq A 1 (n + 3) = A * uSeq A 1 (n + 2) - uSeq A 1 (n + 1) := by simp [uSeq]
    have hu2 : uSeq A 1 (n + 2) = A * uSeq A 1 (n + 1) - uSeq A 1 n := by simp [uSeq]
    rw [hv, hu, ih1, ih0, hu2]; grind

theorem cassini_u2 (A : Int) :
    ∀ n, uSeq A 1 (n + 1) * uSeq A 1 (n + 1) -
         A * uSeq A 1 (n + 1) * uSeq A 1 n +
         uSeq A 1 n * uSeq A 1 n = 1
  | 0 => by simp [uSeq]
  | n + 1 => by
    have ih := cassini_u2 A n
    have hrec : uSeq A 1 (n + 2) = A * uSeq A 1 (n + 1) - uSeq A 1 n := by simp [uSeq]
    grind

theorem conj2_s11 (A : Int) :
    ∀ n, sumNat (fun j => uSeq A 1 j * vSeq A 1 (j + 1)) n =
         uSeq A 1 (n + 1) * uSeq A 1 (n + 1) - (n : Int) - 1
  | 0 => by simp [sumNat, uSeq]
  | n + 1 => by
    have ih := conj2_s11 A n
    have hv := v2_of_u2 A (n + 1)
    have hu : uSeq A 1 (n + 2) = A * uSeq A 1 (n + 1) - uSeq A 1 n := by simp [uSeq]
    have hcas := cassini_u2 A n
    simp only [sumNat]; grind

theorem conj2_s12 (A : Int) :
    ∀ n, sumNat (fun j => uSeq A 1 j * vSeq A 1 j) n = uSeq A 1 n * uSeq A 1 (n + 1)
  | 0 => by simp [sumNat, uSeq]
  | n + 1 => by
    have ih := conj2_s12 A n
    have hv := v2_of_u2 A n
    have hu : uSeq A 1 (n + 2) = A * uSeq A 1 (n + 1) - uSeq A 1 n := by simp [uSeq]
    simp only [sumNat]; grind

theorem conj2_s21 (A : Int) :
    ∀ n, sumNat (fun j => uSeq A 1 (j - 1) * vSeq A 1 (j + 1)) n =
         uSeq A 1 n * uSeq A 1 (n + 1) - A * (n : Int)
  | 0 => by simp [sumNat, uSeq]
  | n + 1 => by
    have ih := conj2_s21 A n
    have hv := v2_of_u2 A (n + 1)
    have hu : uSeq A 1 (n + 2) = A * uSeq A 1 (n + 1) - uSeq A 1 n := by simp [uSeq]
    have hcas := cassini_u2 A n
    simp only [sumNat, Nat.add_sub_cancel]; grind

theorem conj2_s22 (A : Int) :
    ∀ n, sumNat (fun j => uSeq A 1 (j - 1) * vSeq A 1 j) n =
         uSeq A 1 n * uSeq A 1 n - (n : Int)
  | 0 => by simp [sumNat, uSeq]
  | n + 1 => by
    have hshift : sumNat (fun j => uSeq A 1 (j - 1) * vSeq A 1 j) (n + 1) =
                  sumNat (fun j => uSeq A 1 j * vSeq A 1 (j + 1)) n := by
      induction n with
      | zero => simp [sumNat, uSeq]
      | succ k ihk =>
        change sumNat (fun j => uSeq A 1 (j - 1) * vSeq A 1 j) (k + 1) +
               uSeq A 1 (k + 1 + 1 - 1) * vSeq A 1 (k + 1 + 1) =
               sumNat (fun j => uSeq A 1 j * vSeq A 1 (j + 1)) k +
               uSeq A 1 (k + 1) * vSeq A 1 (k + 1 + 1)
        rw [ihk, Nat.add_sub_cancel]
    rw [hshift, conj2_s11 A n]; omega

/-- Conjecture 2 of OEIS A360278 (and arXiv:2302.08315). -/
theorem conjecture2 (A : Int) (n : Nat) :
    det (fun i j : Fin n => (if i = j then 1 else 0) + vSeq A 1 (i.val + j.val + 2)) =
      uSeq A 1 (n + 1) * uSeq A 1 (n + 1) - (n : Int) * (n : Int) := by
  have hmat : (fun i j : Fin n => (if i = j then 1 else 0) + vSeq A 1 (i.val + j.val + 2)) =
      (fun i j : Fin n =>
        (if i = j then 1 else 0) +
        vSeq A 1 (i.val + 2) * uSeq A 1 (j.val + 1) +
        (-vSeq A 1 (i.val + 1)) * uSeq A 1 j.val) := by
    funext i j
    have hd := w_add_decomp A 1 (vSeq A 1) (fun m => by simp [vSeq]) (i.val + 1) j.val
    rw [show i.val + 1 + (j.val + 1) = i.val + j.val + 2 by omega] at hd
    rw [hd]; grind
  rw [hmat, det_id_add_rank2]
  have hsum_neg : ∀ (f g : Nat → Int) (m : Nat), sumNat (fun k => f k * -g k) m = -sumNat (fun k => f k * g k) m := by
    intro f g m
    induction m with
    | zero => rfl
    | succ k ihk =>
      change sumNat (fun k => f k * -g k) k + f (k + 1) * -g (k + 1) =
             -(sumNat (fun k => f k * g k) k + f (k + 1) * g (k + 1))
      rw [ihk]; grind
  have hs11 := dot_eq_sumNat n (fun k => uSeq A 1 k) (fun k => vSeq A 1 (k + 1))
  have hs12 : dot (fun j : Fin n => uSeq A 1 (j.val + 1)) (fun i : Fin n => -vSeq A 1 (i.val + 1)) =
              -sumNat (fun k => uSeq A 1 k * vSeq A 1 k) n := by
    rw [dot_eq_sumNat n (fun k => uSeq A 1 k) (fun k => -vSeq A 1 k), hsum_neg]
  have hs21 := dot_eq_sumNat n (fun k => uSeq A 1 (k - 1)) (fun k => vSeq A 1 (k + 1))
  have hs22 : dot (fun j : Fin n => uSeq A 1 j.val) (fun i : Fin n => -vSeq A 1 (i.val + 1)) =
              -sumNat (fun k => uSeq A 1 (k - 1) * vSeq A 1 k) n := by
    have h1 := dot_eq_sumNat n (fun k => uSeq A 1 (k - 1)) (fun k => -vSeq A 1 k)
    simp only [Nat.add_sub_cancel] at h1
    rw [h1, hsum_neg]
  simp only [Nat.add_sub_cancel] at hs21
  rw [hs11, hs12, hs21, hs22, conj2_s11, conj2_s12, conj2_s21, conj2_s22]
  have hcas := cassini_u2 A n
  grind

/-! #### Conjecture 3 (Fibonacci) -/

abbrev fib (n : Nat) : Int := uSeq 1 (-1) n

theorem fib_s11 : ∀ n, sumNat (fun j => fib j * fib (j + 1)) n =
                       fib (n + 1) * fib (n + 1) - (1 - epsInt n)
  | 0 => by simp [sumNat, fib, uSeq, epsInt]
  | n + 1 => by
    have ih := fib_s11 n
    have hrec : fib (n + 2) = fib (n + 1) + fib n := by simp [fib, uSeq]
    have hcas := cassini_u1 1 n
    simp only [sumNat, epsInt] at ih ⊢
    split at hcas <;> split <;> grind

theorem fib_s12 : ∀ n, sumNat (fun j => fib j * fib j) n = fib n * fib (n + 1)
  | 0 => by simp [sumNat, fib, uSeq]
  | n + 1 => by
    have ih := fib_s12 n
    have hrec : fib (n + 2) = fib (n + 1) + fib n := by simp [fib, uSeq]
    simp only [sumNat]; grind

theorem fib_s21 : ∀ n, sumNat (fun j => fib (j - 1) * fib (j + 1)) n =
                       fib n * fib (n + 1) - epsInt n
  | 0 => by simp [sumNat, fib, uSeq, epsInt]
  | n + 1 => by
    have ih := fib_s21 n
    have hrec : fib (n + 2) = fib (n + 1) + fib n := by simp [fib, uSeq]
    have hcas := cassini_u1 1 n
    simp only [sumNat, Nat.add_sub_cancel, epsInt] at ih ⊢
    split at hcas <;> split <;> grind

theorem fib_s22 : ∀ n, sumNat (fun j => fib (j - 1) * fib j) n =
                       fib n * fib n - epsInt n
  | 0 => by simp [sumNat, fib, uSeq, epsInt]
  | n + 1 => by
    have hshift : sumNat (fun j => fib (j - 1) * fib j) (n + 1) =
                  sumNat (fun j => fib j * fib (j + 1)) n := by
      induction n with
      | zero => simp [sumNat, fib, uSeq]
      | succ k ihk =>
        change sumNat (fun j => fib (j - 1) * fib j) (k + 1) + fib (k + 1 + 1 - 1) * fib (k + 1 + 1) =
               sumNat (fun j => fib j * fib (j + 1)) k + fib (k + 1) * fib (k + 1 + 1)
        rw [ihk, Nat.add_sub_cancel]
    rw [hshift, fib_s11 n]
    simp only [epsInt]; split <;> split <;> grind

/-- Conjecture 3 of OEIS A360278 (and arXiv:2302.08315). -/
theorem conjecture3 (n : Nat) :
    det (fun i j : Fin n => (if i = j then 1 else 0) + fib (i.val + j.val + 2)) =
      fib (n + 1) * fib (n + 1) + epsInt n := by
  have hmat : (fun i j : Fin n => (if i = j then 1 else 0) + fib (i.val + j.val + 2)) =
      (fun i j : Fin n =>
        (if i = j then 1 else 0) +
        fib (i.val + 2) * fib (j.val + 1) +
        fib (i.val + 1) * fib j.val) := by
    funext i j
    have hd := w_add_decomp 1 (-1) fib (fun m => by simp [fib, uSeq]) (i.val + 1) j.val
    rw [show i.val + 1 + (j.val + 1) = i.val + j.val + 2 by omega] at hd
    rw [hd]; grind
  rw [hmat, det_id_add_rank2]
  have hs11 := dot_eq_sumNat n (fun k => fib k) (fun k => fib (k + 1))
  have hs12 := dot_eq_sumNat n (fun k => fib k) (fun k => fib k)
  have hs21 := dot_eq_sumNat n (fun k => fib (k - 1)) (fun k => fib (k + 1))
  have hs22 := dot_eq_sumNat n (fun k => fib (k - 1)) (fun k => fib k)
  simp only [Nat.add_sub_cancel] at hs21 hs22
  rw [hs11, hs12, hs21, hs22, fib_s11, fib_s12, fib_s21, fib_s22]
  have hcas := cassini_u1 1 n
  simp only [epsInt] at *
  split at hcas <;> split <;> grind

#print axioms det_id_add_rank2
#print axioms conjecture1
#print axioms conjecture1_lucas
#print axioms conjecture2
#print axioms conjecture3

end A360278
