/-
  OEIS A210445 — Complete formal proof of Zhi-Wei Sun's conjecture (Jan 20, 2013):
    a(n) = least positive integer k such that k * n is practical.
    Conjecture: a(n) < n for all n > 1, and a(n) < n / 2 for all n > 47.

  Self-contained Lean 4 proof (zero external dependencies, zero sorry, zero extra axioms)
  directly from the textbook subset-sum definition of a practical number.
-/

namespace A210445

/-- Textbook definition: a positive integer `m` is practical if every integer `r`
    with `r ≤ m` can be written as a sum of distinct positive divisors of `m`. -/
def IsPractical (m : Nat) : Prop :=
  0 < m ∧ ∀ r : Nat, r ≤ m →
    ∃ S : List Nat, S.Nodup ∧ (∀ d ∈ S, d ∣ m) ∧ S.sum = r

/-- Stronger form used in the induction: every `r ≤ B` is a sum of distinct divisors of `m`. -/
def IsBPractical (m B : Nat) : Prop :=
  0 < m ∧ ∀ r : Nat, r ≤ B →
    ∃ S : List Nat, S.Nodup ∧ (∀ d ∈ S, d ∣ m) ∧ S.sum = r

/-- Elementary primality predicate. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Geometric sum `1 + p + p^2 + ... + p^e`. -/
def geo (p : Nat) : Nat → Nat
  | 0 => 1
  | e + 1 => geo p e + p ^ (e + 1)

theorem geo_pos (p e : Nat) : 0 < geo p e := by
  induction e with
  | zero => simp [geo]
  | succ e ih => simp [geo]; omega

theorem geo_mono (p e : Nat) : geo p e ≤ geo p (e + 1) := by
  simp [geo]

theorem pow_le_geo (p e : Nat) : p ^ e ≤ geo p e := by
  cases e with
  | zero => simp [geo]
  | succ e => simp [geo]

theorem geo_mul_pred_add_one (p : Nat) (hp : 1 ≤ p) (e : Nat) :
    (p - 1) * geo p e + 1 = p ^ (e + 1) := by
  induction e with
  | zero => simp [geo]; omega
  | succ e ih =>
    simp only [geo, Nat.mul_add]
    have h1 : (p - 1) * geo p e + 1 = p ^ (e + 1) := ih
    have h2 : (p - 1) * p ^ (e + 1) + p ^ (e + 1) = p ^ (e + 1 + 1) := by
      have hsucc : (p - 1 + 1) * p ^ (e + 1) = (p - 1) * p ^ (e + 1) + p ^ (e + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      have hp1 : p - 1 + 1 = p := by omega
      rw [← hsucc, hp1, Nat.mul_comm, ← Nat.pow_succ]
    omega

/-! ### Elementary divisibility & Euclid's lemma -/

theorem exists_least_prime_dvd {n : Nat} (hn : 2 ≤ n) :
    ∃ p : Nat, IsPrime p ∧ p ∣ n ∧ p ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hprim : ∀ d, d ∣ n → d = 1 ∨ d = n
    · exact ⟨n, ⟨hn, hprim⟩, Nat.dvd_refl n, Nat.le_refl n⟩
    · have hex : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
        cases Classical.em (∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n) with
        | inl h => exact h
        | inr h =>
          exfalso; apply hprim; intro d hd
          cases Classical.em (d = 1) with
          | inl h1 => exact Or.inl h1
          | inr h1 =>
            cases Classical.em (d = n) with
            | inl h2 => exact Or.inr h2
            | inr h2 => exact absurd ⟨d, hd, h1, h2⟩ h
      rcases hex with ⟨d, hd, hd1, hdn⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      have hd_le : d ≤ n := Nat.le_of_dvd (by omega) hd
      have hd_lt : d < n := by omega
      have hd_ge2 : 2 ≤ d := by omega
      rcases ih d hd_lt hd_ge2 with ⟨p, hp, hpd, hple⟩
      exact ⟨p, hp, Nat.dvd_trans hpd hd, Nat.le_trans hple hd_le⟩

theorem prime_coprime_of_not_dvd {p a : Nat} (hp : IsPrime p) (hnd : ¬ p ∣ a) :
    Nat.gcd p a = 1 := by
  have hd : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  cases hp.2 _ hd with
  | inl h => exact h
  | inr h =>
    exfalso
    apply hnd
    rw [← h]
    exact Nat.gcd_dvd_right p a

theorem prime_dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  cases Classical.em (p ∣ a) with
  | inl ha => exact Or.inl ha
  | inr hna =>
    right
    have hcop : Nat.gcd p a = 1 := prime_coprime_of_not_dvd hp hna
    have h1 : p ∣ p * b := Nat.dvd_mul_right p b
    have h2 : p ∣ Nat.gcd (p * b) (a * b) := Nat.dvd_gcd h1 h
    rw [Nat.gcd_mul_right, hcop, Nat.one_mul] at h2
    exact h2

theorem not_pow_succ_dvd_pow_mul {p u : Nat} (hp : IsPrime p) (hnd : ¬ p ∣ u) :
    ∀ e : Nat, ¬ (p ^ (e + 1) ∣ p ^ e * u) := by
  intro e h
  have hp_pos : 0 < p := by have := hp.1; omega
  have hpe_pos : 0 < p ^ e := Nat.pow_pos hp_pos
  rw [Nat.pow_succ, Nat.mul_comm (p ^ e) p] at h
  have h' : p * p ^ e ∣ u * p ^ e := by
    rw [Nat.mul_comm u (p ^ e)]; exact h
  have : p ∣ u := (Nat.mul_dvd_mul_iff_right hpe_pos).mp h'
  exact hnd this

/-! ### List helpers for subset-sum construction -/

theorem sum_map_mul (c : Nat) (L : List Nat) :
    (L.map (c * ·)).sum = c * L.sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih, Nat.mul_add]

theorem nodup_map_mul {c : Nat} (hc : 0 < c) {L : List Nat} (hL : L.Nodup) :
    (L.map (c * ·)).Nodup := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hL ⊢
    constructor
    · intro hmem
      rcases List.mem_map.mp hmem with ⟨b, hb, heq⟩
      have : b = a := Nat.eq_of_mul_eq_mul_left hc heq
      subst this
      exact hL.1 hb
    · exact ih hL.2

theorem nodup_append_of_disjoint {A B : List Nat} (hA : A.Nodup) (hB : B.Nodup)
    (hdisj : ∀ x ∈ A, x ∉ B) : (A ++ B).Nodup := by
  induction A with
  | nil => simpa using hB
  | cons a t ih =>
    simp only [List.nodup_cons] at hA
    simp only [List.cons_append, List.nodup_cons]
    constructor
    · intro hx
      cases List.mem_append.mp hx with
      | inl ht => exact hA.1 ht
      | inr hb => exact hdisj a (by simp) hb
    · exact ih hA.2 (fun x hx => hdisj x (by simp [hx]))

/-! ### Core induction: multiplying a B-practical number by a coprime prime power -/

theorem isBPractical_mul_prime_pow {u B p : Nat}
    (hu : IsBPractical u B) (hp : IsPrime p) (hnd : ¬ p ∣ u) (hpB : p ≤ B + 1) :
    ∀ e : Nat, IsBPractical (p ^ e * u) (geo p e * B) := by
  intro e
  induction e with
  | zero =>
    simpa [geo] using hu
  | succ e ih =>
    have hp_pos : 0 < p := by have := hp.1; omega
    have hpe1_pos : 0 < p ^ (e + 1) := Nat.pow_pos hp_pos
    refine ⟨Nat.mul_pos hpe1_pos hu.1, ?_⟩
    intro r hr
    -- Bound p^(e+1) ≤ geo p e * B + 1
    have hstep : p ^ (e + 1) ≤ geo p e * B + 1 := by
      have hgeo := geo_mul_pred_add_one p (by have := hp.1; omega) e
      have hmul : (p - 1) * geo p e ≤ B * geo p e :=
        Nat.mul_le_mul_right (geo p e) (by omega)
      rw [Nat.mul_comm B (geo p e)] at hmul
      omega
    -- Write r = p^(e+1) * q + s with q ≤ B and s ≤ geo p e * B
    let q := min (r / p ^ (e + 1)) B
    let s := r - p ^ (e + 1) * q
    have hq_le_B : q ≤ B := Nat.min_le_right _ _
    have hq_le_div : q ≤ r / p ^ (e + 1) := Nat.min_le_left _ _
    have hpq_le_r : p ^ (e + 1) * q ≤ r := by
      have h1 : p ^ (e + 1) * q ≤ p ^ (e + 1) * (r / p ^ (e + 1)) :=
        Nat.mul_le_mul_left _ hq_le_div
      have h2 : p ^ (e + 1) * (r / p ^ (e + 1)) ≤ r := Nat.mul_div_le r (p ^ (e + 1))
      exact Nat.le_trans h1 h2
    have hs_le : s ≤ geo p e * B := by
      simp only [s, q]
      by_cases hle : r / p ^ (e + 1) ≤ B
      · rw [Nat.min_eq_left hle]
        have hdm := Nat.div_add_mod r (p ^ (e + 1))
        have hmod : r % p ^ (e + 1) < p ^ (e + 1) := Nat.mod_lt r hpe1_pos
        omega
      · have hgt : B ≤ r / p ^ (e + 1) := by omega
        rw [Nat.min_eq_right hgt]
        simp only [geo, Nat.add_mul] at hr
        omega
    -- Obtain subset-sum witnesses A (divisors of u) for q, and C (divisors of p^e * u) for s
    rcases hu.2 q hq_le_B with ⟨A, hAnodup, hAdvd, hAsum⟩
    rcases ih.2 s hs_le with ⟨C, hCnodup, hCdvd, hCsum⟩
    refine ⟨A.map (p ^ (e + 1) * ·) ++ C, ?_, ?_, ?_⟩
    · -- Nodup: every element of A.map is divisible by p^(e+1), while no element of C is
      apply nodup_append_of_disjoint (nodup_map_mul hpe1_pos hAnodup) hCnodup
      intro x hxA hxC
      rcases List.mem_map.mp hxA with ⟨a, _, rfl⟩
      have hdiv_x : p ^ (e + 1) ∣ p ^ (e + 1) * a := Nat.dvd_mul_right _ _
      have hdiv_C : p ^ (e + 1) * a ∣ p ^ e * u := hCdvd _ hxC
      exact not_pow_succ_dvd_pow_mul hp hnd e (Nat.dvd_trans hdiv_x hdiv_C)
    · -- All elements divide p^(e+1) * u
      intro d hd
      cases List.mem_append.mp hd with
      | inl hA =>
        rcases List.mem_map.mp hA with ⟨a, ha, rfl⟩
        exact Nat.mul_dvd_mul_left (p ^ (e + 1)) (hAdvd a ha)
      | inr hC =>
        have h1 : d ∣ p ^ e * u := hCdvd d hC
        have h2 : p ^ e * u ∣ p ^ (e + 1) * u := by
          refine ⟨p, ?_⟩
          rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm p u, ← Nat.mul_assoc]
        exact Nat.dvd_trans h1 h2
    · -- Sum equals r
      rw [List.sum_append, sum_map_mul, hAsum, hCsum]
      omega

/-! ### Stewart-valid prime-power lists and closure under bounded multiplication -/

def evalList : List (Nat × Nat) → Nat
  | [] => 1
  | (p, e) :: t => p ^ e * evalList t

theorem prime_dvd_pow {p q : Nat} (hp : IsPrime p) :
    ∀ e : Nat, p ∣ q ^ e → p ∣ q := by
  intro e h
  induction e with
  | zero =>
    simp only [Nat.pow_zero] at h
    have := Nat.le_of_dvd (by decide) h
    have := hp.1; omega
  | succ e ih =>
    rw [Nat.pow_succ] at h
    cases prime_dvd_mul hp h with
    | inl h1 => exact ih h1
    | inr h2 => exact h2

theorem prime_not_dvd_evalList {p : Nat} (hp : IsPrime p) :
    ∀ L : List (Nat × Nat), (∀ q e, (q, e) ∈ L → IsPrime q ∧ q < p) → ¬ (p ∣ evalList L) := by
  intro L hL
  induction L with
  | nil =>
    intro h
    simp only [evalList] at h
    have := Nat.le_of_dvd (by decide) h
    have := hp.1
    omega
  | cons hd tl ih =>
    rcases hd with ⟨q, e⟩
    have hq : IsPrime q ∧ q < p := hL q e (by simp)
    have htl : ¬ (p ∣ evalList tl) := ih (fun r er hr => hL r er (by simp [hr]))
    intro hdvd
    simp only [evalList] at hdvd
    cases prime_dvd_mul hp hdvd with
    | inr h => exact htl h
    | inl hpow =>
      have hpq : p ∣ q := prime_dvd_pow hp e hpow
      cases hq.1.2 p hpq with
      | inl h1 => have := hp.1; omega
      | inr h2 => have := hq.2; omega

inductive ValidStewart : List (Nat × Nat) → Nat → Prop
  | nil : ValidStewart [] 1
  | cons {L : List (Nat × Nat)} {B p e : Nat} :
      ValidStewart L B →
      IsPrime p →
      (∀ q eq, (q, eq) ∈ L → q < p) →
      1 ≤ e →
      p ≤ B + 1 →
      ValidStewart ((p, e) :: L) (geo p e * B)

theorem ValidStewart.all_primes {L : List (Nat × Nat)} {B : Nat} (h : ValidStewart L B) :
    ∀ q eq, (q, eq) ∈ L → IsPrime q := by
  induction h with
  | nil => intro q eq hmem; cases hmem
  | cons hL hp _ _ _ ih =>
    intro q eq hmem
    cases hmem with
    | head => exact hp
    | tail _ h => exact ih q eq h

theorem ValidStewart.toBPractical {L : List (Nat × Nat)} {B : Nat} (h : ValidStewart L B) :
    IsBPractical (evalList L) B := by
  induction h with
  | nil =>
    refine ⟨by decide, ?_⟩
    intro r hr
    cases r with
    | zero => exact ⟨[], by simp, by simp, by simp⟩
    | succ r =>
      have hr0 : r = 0 := by omega
      subst hr0
      exact ⟨[1], by simp, by simp, by simp⟩
  | @cons L B p e hL hp hlt _ hpB ih =>
    have hnd : ¬ (p ∣ evalList L) :=
      prime_not_dvd_evalList hp L (fun q eq hmem => ⟨hL.all_primes q eq hmem, hlt q eq hmem⟩)
    exact isBPractical_mul_prime_pow ih hp hnd hpB e

theorem ValidStewart.eval_le_B {L : List (Nat × Nat)} {B : Nat} (h : ValidStewart L B) :
    evalList L ≤ B := by
  induction h with
  | nil => simp [evalList]
  | @cons L B p e _ _ _ _ _ ih =>
    simp only [evalList]
    exact Nat.mul_le_mul (pow_le_geo p e) ih

theorem ValidStewart.insertPrime {L : List (Nat × Nat)} {B q : Nat}
    (h : ValidStewart L B) (hq : IsPrime q) (hqB : q ≤ B + 1) :
    ∃ L' B', ValidStewart L' B' ∧ evalList L' = q * evalList L ∧ B ≤ B' ∧
      (∀ r er, (r, er) ∈ L' → r = q ∨ ∃ er0, (r, er0) ∈ L) := by
  induction h with
  | nil =>
    have hq2 : q = 2 := by have := hq.1; omega
    subst hq2
    refine ⟨[(2, 1)], geo 2 1 * 1, ValidStewart.cons ValidStewart.nil hq (by simp) (by decide) (by decide),
      ?_, ?_, ?_⟩
    · simp [evalList]
    · simp [geo]
    · intro r er hmem; cases hmem with | head => exact Or.inl rfl | tail _ h => cases h
  | @cons L0 B0 p e hL0 hp hlt he hpB ih =>
    by_cases hgt : p < q
    · -- q > p: prepend (q, 1)
      have hlt' : ∀ r er, (r, er) ∈ (p, e) :: L0 → r < q := by
        intro r er hmem
        cases hmem with
        | head => exact hgt
        | tail _ h => exact Nat.lt_trans (hlt r er h) hgt
      refine ⟨(q, 1) :: (p, e) :: L0, geo q 1 * (geo p e * B0),
        ValidStewart.cons (ValidStewart.cons hL0 hp hlt he hpB) hq hlt' (by decide) hqB,
        ?_, ?_, ?_⟩
      · simp [evalList]
      · have hgq : 1 ≤ geo q 1 := geo_pos q 1
        calc geo p e * B0 = 1 * (geo p e * B0) := (Nat.one_mul _).symm
          _ ≤ geo q 1 * (geo p e * B0) := Nat.mul_le_mul_right _ hgq
      · intro r er hmem
        cases hmem with
        | head => exact Or.inl rfl
        | tail _ h => exact Or.inr ⟨er, h⟩
    · by_cases heq : q = p
      · -- q = p: increment exponent e → e + 1
        subst heq
        refine ⟨(q, e + 1) :: L0, geo q (e + 1) * B0,
          ValidStewart.cons hL0 hp hlt (by omega) hpB, ?_, ?_, ?_⟩
        · simp only [evalList, Nat.pow_succ]
          rw [Nat.mul_comm (q ^ e) q, Nat.mul_assoc]
        · exact Nat.mul_le_mul_right B0 (geo_mono q e)
        · intro r er hmem
          cases hmem with
          | head => exact Or.inl rfl
          | tail _ h => exact Or.inr ⟨er, List.mem_cons_of_mem _ h⟩
      · -- q < p ≤ B0 + 1: insert recursively into L0
        have hq_lt_p : q < p := by omega
        have hqB0 : q ≤ B0 + 1 := by omega
        rcases ih hqB0 with ⟨L0', B0', hL0', heval0, hB0_le, hmem0⟩
        have hlt' : ∀ r er, (r, er) ∈ L0' → r < p := by
          intro r er hr
          cases hmem0 r er hr with
          | inl hreq => rw [hreq]; exact hq_lt_p
          | inr hex => rcases hex with ⟨er0, hr0⟩; exact hlt r er0 hr0
        refine ⟨(p, e) :: L0', geo p e * B0',
          ValidStewart.cons hL0' hp hlt' he (Nat.le_trans hpB (Nat.add_le_add_right hB0_le 1)),
          ?_, ?_, ?_⟩
        · simp only [evalList, heval0]
          rw [← Nat.mul_assoc, Nat.mul_comm (p ^ e) q, Nat.mul_assoc]
        · exact Nat.mul_le_mul_left (geo p e) hB0_le
        · intro r er hmem
          cases hmem with
          | head => exact Or.inr ⟨e, by simp⟩
          | tail _ h =>
            cases hmem0 r er h with
            | inl hreq => exact Or.inl hreq
            | inr hex => rcases hex with ⟨er0, hr0⟩; exact Or.inr ⟨er0, List.mem_cons_of_mem _ hr0⟩

theorem ValidStewart.mul_bounded {L : List (Nat × Nat)} {B n : Nat}
    (h : ValidStewart L B) (hn1 : 1 ≤ n) (hnB : n ≤ B + 1) :
    IsPractical (evalList L * n) := by
  suffices ∀ m, ∀ {L : List (Nat × Nat)} {B : Nat},
      ValidStewart L B → 1 ≤ m → m ≤ B + 1 →
      ∃ L' B', ValidStewart L' B' ∧ evalList L' = m * evalList L by
    rcases this n h hn1 hnB with ⟨L', B', hL', heval⟩
    have hbp := hL'.toBPractical
    have hle := hL'.eval_le_B
    rw [heval, Nat.mul_comm] at hbp hle
    exact ⟨hbp.1, fun r hr => hbp.2 r (Nat.le_trans hr hle)⟩
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro L B hL hm1 hmB
    by_cases h1 : m = 1
    · subst h1
      exact ⟨L, B, hL, by simp⟩
    · have hm2 : 2 ≤ m := by omega
      rcases exists_least_prime_dvd hm2 with ⟨q, hq, hqm, hqle⟩
      rcases hqm with ⟨m', hm'eq⟩
      have hm'_pos : 1 ≤ m' := by
        cases m' with
        | zero => simp at hm'eq; omega
        | succ _ => omega
      have hm'_lt : m' < m := by
        have hq2 := hq.1
        have : 2 * m' ≤ q * m' := Nat.mul_le_mul_right m' hq2
        omega
      rcases hL.insertPrime hq (Nat.le_trans hqle hmB) with ⟨L1, B1, hL1, heval1, hBB1, _⟩
      have hm'_le : m' ≤ B1 + 1 := by omega
      rcases ih m' hm'_lt hL1 hm'_pos hm'_le with ⟨L2, B2, hL2, heval2⟩
      refine ⟨L2, B2, hL2, ?_⟩
      rw [heval2, heval1, ← Nat.mul_assoc, Nat.mul_comm m' q, ← hm'eq]

/-! ### Explicit small primes and the 5-template practical ladder -/

private theorem prime_2 : IsPrime 2 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hle := Nat.le_of_dvd (by decide) hd
  have hpos := Nat.pos_of_dvd_of_pos hd (by decide)
  omega

private theorem prime_3 : IsPrime 3 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hle := Nat.le_of_dvd (by decide) hd
  have hpos := Nat.pos_of_dvd_of_pos hd (by decide)
  have : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso; exact absurd hd (by decide)
  · exact Or.inr rfl

private theorem prime_5 : IsPrime 5 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hle := Nat.le_of_dvd (by decide) hd
  have hpos := Nat.pos_of_dvd_of_pos hd (by decide)
  have : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso; exact absurd hd (by decide)
  · exfalso; exact absurd hd (by decide)
  · exfalso; exact absurd hd (by decide)
  · exact Or.inr rfl

private theorem prime_7 : IsPrime 7 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hle := Nat.le_of_dvd (by decide) hd
  have hpos := Nat.pos_of_dvd_of_pos hd (by decide)
  have : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso; exact absurd hd (by decide)
  · exfalso; exact absurd hd (by decide)
  · exfalso; exact absurd hd (by decide)
  · exfalso; exact absurd hd (by decide)
  · exfalso; exact absurd hd (by decide)
  · exact Or.inr rfl

/-- Template 0: `2^a` has `ValidStewart` with `B = 2^(a+1) - 1`. -/
theorem valid_pow2 (a : Nat) :
    ∃ L B, ValidStewart L B ∧ evalList L = 2 ^ a ∧ B + 1 = 2 ^ (a + 1) := by
  cases a with
  | zero =>
    exact ⟨[], 1, ValidStewart.nil, by simp [evalList], by decide⟩
  | succ a =>
    refine ⟨[(2, a + 1)], geo 2 (a + 1) * 1,
      ValidStewart.cons ValidStewart.nil prime_2 (by simp) (by omega) (by decide),
      by simp [evalList], ?_⟩
    have h := geo_mul_pred_add_one 2 (by decide) (a + 1)
    simp at h ⊢
    exact h

/-- Helper: `geo 2 e + 1 = 2^(e+1)`. -/
theorem geo_two_add_one (e : Nat) : geo 2 e + 1 = 2 ^ (e + 1) := by
  have h := geo_mul_pred_add_one 2 (by decide) e
  simpa using h

/-- Template 1: `k = 24 * 2^a = 3 * 2^(a+3)`, `B + 1 = 64 * 2^a - 3`. -/
theorem valid_24 (a : Nat) :
    ∃ L B, ValidStewart L B ∧ evalList L = 24 * 2 ^ a ∧ B + 1 = 64 * 2 ^ a - 3 := by
  have h2 : ValidStewart [(2, a + 3)] (geo 2 (a + 3) * 1) :=
    ValidStewart.cons ValidStewart.nil prime_2 (by simp) (by omega) (by decide)
  have hgeo2 : geo 2 (a + 3) + 1 = 16 * 2 ^ a := by
    have h1 := geo_two_add_one (a + 3)
    have hpow : 2 ^ (a + 3 + 1) = 16 * 2 ^ a := by
      rw [Nat.add_assoc, Nat.pow_add]; simp [Nat.mul_comm]
    omega
  have hpow_pos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have h24 : ValidStewart [(3, 1), (2, a + 3)] (geo 3 1 * (geo 2 (a + 3) * 1)) :=
    ValidStewart.cons h2 prime_3 (by intro q eq hm; cases hm with | head => decide | tail _ h => cases h)
      (by decide) (by omega)
  refine ⟨[(3, 1), (2, a + 3)], geo 3 1 * (geo 2 (a + 3) * 1), h24, ?_, ?_⟩
  · simp only [evalList, Nat.pow_one, Nat.mul_one, Nat.pow_add]
    have h8 : (2 : Nat) ^ 3 = 8 := by decide
    rw [h8, Nat.mul_comm (2 ^ a) 8, ← Nat.mul_assoc]
  · have hg3 : geo 3 1 = 4 := by decide
    rw [hg3, Nat.mul_one]
    omega

/-- Template 2: `k = 30 * 2^a = 5 * 3 * 2^(a+1)`, `B + 1 = 96 * 2^a - 23`. -/
theorem valid_30 (a : Nat) :
    ∃ L B, ValidStewart L B ∧ evalList L = 30 * 2 ^ a ∧ B + 1 = 96 * 2 ^ a - 23 := by
  have h2 : ValidStewart [(2, a + 1)] (geo 2 (a + 1) * 1) :=
    ValidStewart.cons ValidStewart.nil prime_2 (by simp) (by omega) (by decide)
  have hgeo2 : geo 2 (a + 1) + 1 = 4 * 2 ^ a := by
    have h1 := geo_two_add_one (a + 1)
    have hpow : 2 ^ (a + 1 + 1) = 4 * 2 ^ a := by
      rw [Nat.add_assoc, Nat.pow_add]; simp [Nat.mul_comm]
    omega
  have hpow_pos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hg3 : geo 3 1 = 4 := by decide
  have hg5 : geo 5 1 = 6 := by decide
  have h3 : ValidStewart [(3, 1), (2, a + 1)] (geo 3 1 * (geo 2 (a + 1) * 1)) :=
    ValidStewart.cons h2 prime_3 (by intro q eq hm; cases hm with | head => decide | tail _ h => cases h)
      (by decide) (by omega)
  have h5 : ValidStewart [(5, 1), (3, 1), (2, a + 1)] (geo 5 1 * (geo 3 1 * (geo 2 (a + 1) * 1))) :=
    ValidStewart.cons h3 prime_5
      (by intro q eq hm; cases hm with | head => decide | tail _ h => cases h with | head => decide | tail _ h => cases h)
      (by decide) (by rw [hg3, Nat.mul_one]; omega)
  refine ⟨[(5, 1), (3, 1), (2, a + 1)], geo 5 1 * (geo 3 1 * (geo 2 (a + 1) * 1)), h5, ?_, ?_⟩
  · simp only [evalList, Nat.pow_one, Nat.mul_one, Nat.pow_add]
    omega
  · rw [hg5, hg3, Nat.mul_one]; omega

/-- Template 3: `k = 36 * 2^a = 3^2 * 2^(a+2)`, `B + 1 = 104 * 2^a - 12`. -/
theorem valid_36 (a : Nat) :
    ∃ L B, ValidStewart L B ∧ evalList L = 36 * 2 ^ a ∧ B + 1 = 104 * 2 ^ a - 12 := by
  have h2 : ValidStewart [(2, a + 2)] (geo 2 (a + 2) * 1) :=
    ValidStewart.cons ValidStewart.nil prime_2 (by simp) (by omega) (by decide)
  have hgeo2 : geo 2 (a + 2) + 1 = 8 * 2 ^ a := by
    have h1 := geo_two_add_one (a + 2)
    have hpow : 2 ^ (a + 2 + 1) = 8 * 2 ^ a := by
      rw [Nat.add_assoc, Nat.pow_add]; simp [Nat.mul_comm]
    omega
  have hpow_pos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hg32 : geo 3 2 = 13 := by decide
  have h3 : ValidStewart [(3, 2), (2, a + 2)] (geo 3 2 * (geo 2 (a + 2) * 1)) :=
    ValidStewart.cons h2 prime_3 (by intro q eq hm; cases hm with | head => decide | tail _ h => cases h)
      (by decide) (by omega)
  refine ⟨[(3, 2), (2, a + 2)], geo 3 2 * (geo 2 (a + 2) * 1), h3, ?_, ?_⟩
  · simp only [evalList, Nat.mul_one, Nat.pow_add]
    have h9 : (3 : Nat) ^ 2 = 9 := by decide
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    rw [h9, h4]; omega
  · rw [hg32, Nat.mul_one]; omega

/-- Template 4: `k = 42 * 2^a = 7 * 3 * 2^(a+1)`, `B + 1 = 128 * 2^a - 31`. -/
theorem valid_42 (a : Nat) :
    ∃ L B, ValidStewart L B ∧ evalList L = 42 * 2 ^ a ∧ B + 1 = 128 * 2 ^ a - 31 := by
  have h2 : ValidStewart [(2, a + 1)] (geo 2 (a + 1) * 1) :=
    ValidStewart.cons ValidStewart.nil prime_2 (by simp) (by omega) (by decide)
  have hgeo2 : geo 2 (a + 1) + 1 = 4 * 2 ^ a := by
    have h1 := geo_two_add_one (a + 1)
    have hpow : 2 ^ (a + 1 + 1) = 4 * 2 ^ a := by
      rw [Nat.add_assoc, Nat.pow_add]; simp [Nat.mul_comm]
    omega
  have hpow_pos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hg3 : geo 3 1 = 4 := by decide
  have hg7 : geo 7 1 = 8 := by decide
  have h3 : ValidStewart [(3, 1), (2, a + 1)] (geo 3 1 * (geo 2 (a + 1) * 1)) :=
    ValidStewart.cons h2 prime_3 (by intro q eq hm; cases hm with | head => decide | tail _ h => cases h)
      (by decide) (by omega)
  have h7 : ValidStewart [(7, 1), (3, 1), (2, a + 1)] (geo 7 1 * (geo 3 1 * (geo 2 (a + 1) * 1))) :=
    ValidStewart.cons h3 prime_7
      (by intro q eq hm; cases hm with | head => decide | tail _ h => cases h with | head => decide | tail _ h => cases h)
      (by decide) (by rw [hg3, Nat.mul_one]; omega)
  refine ⟨[(7, 1), (3, 1), (2, a + 1)], geo 7 1 * (geo 3 1 * (geo 2 (a + 1) * 1)), h7, ?_, ?_⟩
  · simp only [evalList, Nat.pow_one, Nat.mul_one, Nat.pow_add]
    omega
  · rw [hg7, hg3, Nat.mul_one]; omega

/-! ### Dyadic bracketing lemma -/

theorem exists_dyadic_bracket {c n : Nat} (hc : 0 < c) (hn : c < n) :
    ∃ a : Nat, c * 2 ^ a < n ∧ n ≤ c * 2 ^ (a + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hle : n ≤ 2 * c
    · exact ⟨0, by simpa using hn, by simpa [Nat.mul_comm] using hle⟩
    · have hhalf_gt : c < (n + 1) / 2 := by omega
      have hhalf_lt : (n + 1) / 2 < n := by omega
      rcases ih ((n + 1) / 2) hhalf_lt hhalf_gt with ⟨a, hlo, hhi⟩
      refine ⟨a + 1, ?_, ?_⟩
      · have : c * 2 ^ (a + 1) = 2 * (c * 2 ^ a) := by
          rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
        omega
      · have : c * 2 ^ (a + 1 + 1) = 2 * (c * 2 ^ (a + 1)) := by
          rw [Nat.pow_succ, Nat.mul_comm (2 ^ (a + 1)) 2, ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
        omega

/-! ### Main Theorems (Zhi-Wei Sun's Conjecture in OEIS A210445) -/

/-- Part 1 of A210445: For every `n > 1`, there exists `1 ≤ k < n` such that `k * n` is practical. -/
theorem a210445_part1 (n : Nat) (hn : 1 < n) :
    ∃ k : Nat, 0 < k ∧ k < n ∧ IsPractical (k * n) := by
  rcases exists_dyadic_bracket (c := 1) (by decide) hn with ⟨a, hlo, hhi⟩
  simp only [Nat.one_mul] at hlo hhi
  rcases valid_pow2 a with ⟨L, B, hL, heval, hB⟩
  refine ⟨2 ^ a, Nat.pow_pos (by decide), hlo, ?_⟩
  rw [← heval]
  exact hL.mul_bounded (by omega) (by omega)

/-- Part 2 of A210445: For every `n > 47`, there exists `1 ≤ k < n / 2` (i.e. `2 * k < n`)
    such that `k * n` is practical. -/
theorem a210445_part2 (n : Nat) (hn : 47 < n) :
    ∃ k : Nat, 0 < k ∧ 2 * k < n ∧ IsPractical (k * n) := by
  by_cases h48 : n = 48
  · -- n = 48 is itself practical (k = 1 < 48 / 2)
    subst h48
    rcases valid_24 1 with ⟨L, B, hL, heval, _⟩
    refine ⟨1, by decide, by decide, ?_⟩
    have hbp := hL.toBPractical
    have hle := hL.eval_le_B
    have h48eq : evalList L = 1 * 48 := by simpa using heval
    rw [h48eq] at hbp hle
    exact ⟨hbp.1, fun r hr => hbp.2 r (Nat.le_trans hr hle)⟩
  · have hn48 : 48 < n := by omega
    rcases exists_dyadic_bracket (c := 48) (by decide) hn48 with ⟨a, hlo, hhi⟩
    have hpow_pos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
    have hhi' : n ≤ 96 * 2 ^ a := by
      have : 48 * 2 ^ (a + 1) = 96 * 2 ^ a := by rw [Nat.pow_succ]; omega
      omega
    by_cases h1 : n ≤ 60 * 2 ^ a
    · rcases valid_24 a with ⟨L, B, hL, heval, hB⟩
      refine ⟨24 * 2 ^ a, by omega, by omega, ?_⟩
      rw [← heval]
      exact hL.mul_bounded (by omega) (by omega)
    · by_cases h2 : n ≤ 72 * 2 ^ a
      · rcases valid_30 a with ⟨L, B, hL, heval, hB⟩
        refine ⟨30 * 2 ^ a, by omega, by omega, ?_⟩
        rw [← heval]
        exact hL.mul_bounded (by omega) (by omega)
      · by_cases h3 : n ≤ 84 * 2 ^ a
        · rcases valid_36 a with ⟨L, B, hL, heval, hB⟩
          refine ⟨36 * 2 ^ a, by omega, by omega, ?_⟩
          rw [← heval]
          exact hL.mul_bounded (by omega) (by omega)
        · rcases valid_42 a with ⟨L, B, hL, heval, hB⟩
          refine ⟨42 * 2 ^ a, by omega, by omega, ?_⟩
          rw [← heval]
          exact hL.mul_bounded (by omega) (by omega)

end A210445

#print axioms A210445.a210445_part1
#print axioms A210445.a210445_part2
