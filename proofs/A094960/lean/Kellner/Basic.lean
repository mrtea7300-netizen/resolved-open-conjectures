/-
Kellner's conjecture (A094960): the elementary part.

This file formalizes sections 2-4 of `../proof.md`:
Lemma 2 (two digits), Lemma 3, Lemma 4, Lemma 5 and Proposition 6.
Everything here is proved from Mathlib, with no extra hypotheses.
-/
import Mathlib

namespace Kellner

open Finset

/-! ## Lemma 2: the two base-`p` digits of `n` when `n < p ^ 2` -/

/-- **Lemma 2** (the part that is used). If `n < p ^ 2` then the base-`p` digit sum of `n` is
`n / p + n % p`. -/
theorem digits_sum_of_lt_sq {p n : ℕ} (hp : 2 ≤ p) (h : n < p ^ 2) :
    (Nat.digits p n).sum = n / p + n % p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.digits_def' hp hn]
    have hlt : n / p < p := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      nlinarith
    rcases Nat.eq_zero_or_pos (n / p) with h0 | h0
    · rw [h0]; simp
    · rw [Nat.digits_of_lt p (n / p) (by omega) hlt]
      simp [add_comm]

/-! ## Lemma 3

In the draft, `p = F + s`, `c(s) = ⌊(s ^ 2 + e) / p⌋` and `a = ⌊n / p⌋ = F - s + c`. So
"`c(s₁) = c(s₂)`" is the same as "`n / p₁ + p₁ = n / p₂ + p₂`" (both sides are `2 F + c`), and
"`s` is failing" is "`n / p + n % p < p`". Stated this way the lemma does not mention `F`. -/

/-- **Lemma 3.** If `p < q` both fail (`n / p + n % p < p`, the same for `q`) and have the same
value of `c` (that is `n / p + p = n / q + q`), then `q = p + 1`. Neither `p` nor `q` is assumed
prime. -/
theorem lemma3 {n p q : ℕ} (hpq : p < q) (hfp : n / p + n % p < p) (hfq : n / q + n % q < q)
    (hc : n / p + p = n / q + q) : q = p + 1 := by
  by_contra hne
  obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
  have hd : 2 ≤ d := by omega
  have h1 := Nat.div_add_mod n p
  have h2 := Nat.div_add_mod n (p + d)
  generalize n / p = a at *
  generalize n % p = b at *
  generalize n / (p + d) = a' at *
  generalize n % (p + d) = b' at *
  have ha : a = a' + d := by omega
  subst ha
  obtain ⟨u, rfl⟩ : ∃ u, p = a' + d + b + 1 + u := ⟨p - (a' + d + b + 1), by omega⟩
  have h3 : (a' + d + b + 1 + u) * d + b = d * a' + b' := by nlinarith
  have h4 : d * d ≥ 2 * d := Nat.mul_le_mul_right d hd
  have h5 : u * d ≥ u * 2 := Nat.mul_le_mul_left u hd
  nlinarith

/-! ## Lemma 4 -/

/-- `K(F, S) = ⌊(S ^ 2 + 2 F) / (F + S)⌋` of the draft. -/
def K (F S : ℕ) : ℕ := (S ^ 2 + 2 * F) / (F + S)

/-- `c(s) ≥ 0`: if `F ^ 2 ≤ n` then `2 F ≤ n / p + p`. -/
theorem two_mul_le_div_add {n F p : ℕ} (hp : 0 < p) (h1 : F ^ 2 ≤ n) : 2 * F ≤ n / p + p := by
  by_cases h : 2 * F ≤ p
  · exact le_trans h (Nat.le_add_left _ _)
  · have h' : 2 * F - p ≤ n / p := by
      rw [Nat.le_div_iff_mul_le hp]
      obtain ⟨m, hm⟩ : ∃ m, 2 * F = p + m := ⟨2 * F - p, by omega⟩
      have : 2 * F - p = m := by omega
      rw [this]
      nlinarith [sq_nonneg ((p : ℤ) - m)]
    calc 2 * F = (2 * F - p) + p := by omega
      _ ≤ n / p + p := Nat.add_le_add_right h' p

/-- `c(s) ≤ K(F, S)` for `1 ≤ s ≤ S`: step (1) of the proof of Lemma 4. -/
theorem div_add_le {n F s S : ℕ} (hs : 1 ≤ s) (hsS : s ≤ S) (h2 : n ≤ F ^ 2 + 2 * F)
    (hlow : 2 * F ≤ n / (F + s) + (F + s)) :
    n / (F + s) + (F + s) ≤ 2 * F + K F S := by
  have hmul : n / (F + s) * (F + s) ≤ n := Nat.div_mul_le_self n (F + s)
  generalize n / (F + s) = a at *
  obtain ⟨c, hc⟩ : ∃ c, a + (F + s) = 2 * F + c := ⟨a + (F + s) - 2 * F, by omega⟩
  have ha : a + s = F + c := by omega
  -- `c * (F + s) ≤ s ^ 2 + 2 F`
  have hA : c * (F + s) ≤ s ^ 2 + 2 * F := by
    have : (F + c) * (F + s) = a * (F + s) + s * (F + s) := by rw [← ha]; ring
    nlinarith
  -- `h(s) ≤ h(S)`
  obtain ⟨j, rfl⟩ : ∃ j, S = s + j := ⟨S - s, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hB : ((s' + 1) ^ 2 + 2 * F) * (F + (s' + 1 + j)) ≤
      ((s' + 1 + j) ^ 2 + 2 * F) * (F + (s' + 1)) := by
    have e : ((s' + 1 + j) ^ 2 + 2 * F) * (F + (s' + 1)) =
        ((s' + 1) ^ 2 + 2 * F) * (F + (s' + 1 + j)) +
          j * (F * (2 * s' + j) + (s' + 1) * (s' + 1 + j)) := by ring
    rw [e]; exact Nat.le_add_right _ _
  have hC : c * (F + (s' + 1 + j)) * (F + (s' + 1)) ≤
      ((s' + 1 + j) ^ 2 + 2 * F) * (F + (s' + 1)) := by
    calc c * (F + (s' + 1 + j)) * (F + (s' + 1))
        = c * (F + (s' + 1)) * (F + (s' + 1 + j)) := by ring
      _ ≤ ((s' + 1) ^ 2 + 2 * F) * (F + (s' + 1 + j)) := Nat.mul_le_mul_right _ hA
      _ ≤ _ := hB
  have hD : c * (F + (s' + 1 + j)) ≤ (s' + 1 + j) ^ 2 + 2 * F :=
    Nat.le_of_mul_le_mul_right hC (by omega)
  have hK : c ≤ K F (s' + 1 + j) := by
    unfold K
    rw [Nat.le_div_iff_mul_le (by omega)]
    exact hD
  omega

/-- **Lemma 4.** For `F ≥ 2` and `F ^ 2 ≤ n ≤ F ^ 2 + 2 F` (that is `F = ⌊√n⌋`), the number of
primes `p` with `F < p ≤ F + S` that fail (`n / p + n % p < p`) is at most `K(F, S) + 1`. -/
theorem card_failing_le {n F S : ℕ} (hF : 2 ≤ F) (h1 : F ^ 2 ≤ n) (h2 : n ≤ F ^ 2 + 2 * F) :
    ((Ioc F (F + S)).filter (fun p => p.Prime ∧ n / p + n % p < p)).card ≤ K F S + 1 := by
  have key : ((Ioc F (F + S)).filter (fun p => p.Prime ∧ n / p + n % p < p)).card ≤
      (Icc (2 * F) (2 * F + K F S)).card := by
    apply Finset.card_le_card_of_injOn (fun p => n / p + p)
    · intro p hp
      have hp := Finset.mem_coe.1 hp
      simp only [mem_filter, mem_Ioc] at hp
      obtain ⟨⟨hFp, hpS⟩, -, -⟩ := hp
      obtain ⟨s, rfl⟩ : ∃ s, p = F + s := ⟨p - F, by omega⟩
      have hlow := two_mul_le_div_add (n := n) (F := F) (p := F + s) (by omega) h1
      have hup := div_add_le (n := n) (F := F) (s := s) (S := S) (by omega) (by omega) h2 hlow
      simp only [coe_Icc, Set.mem_Icc]
      exact ⟨hlow, hup⟩
    · intro p hp q hq hpq
      have hp := Finset.mem_coe.1 hp
      have hq := Finset.mem_coe.1 hq
      simp only [mem_filter, mem_Ioc] at hp hq
      obtain ⟨⟨hFp, -⟩, hpp, hpf⟩ := hp
      obtain ⟨⟨hFq, -⟩, hqp, hqf⟩ := hq
      simp only at hpq
      -- two consecutive integers `≥ 3` cannot both be prime
      have aux : ∀ p q : ℕ, F < p → p.Prime → q.Prime → q = p + 1 → False := by
        intro p q hFp hpp hqp hq
        rcases hpp.eq_two_or_odd with h | h
        · omega
        · have h2q : 2 ∣ q := by omega
          rcases (Nat.dvd_prime hqp).1 h2q with h | h <;> omega
      rcases lt_trichotomy p q with h | h | h
      · exact (aux p q hFp hpp hqp (lemma3 h hpf hqf hpq)).elim
      · exact h
      · exact (aux q p hFq hqp hpp (lemma3 h hqf hpf hpq.symm)).elim
  rw [Nat.card_Icc] at key
  omega

/-! ## Lemma 5 -/

/-- **Lemma 5 (i).** If `F ≥ 1`, `n ≤ F ^ 2 + 2 F` and `u ∈ {1, 2}`, at most one prime `p > F`
divides `n + u`. -/
theorem card_prime_dvd_le_one {n F u : ℕ} (S : ℕ) (hF : 1 ≤ F) (h2 : n ≤ F ^ 2 + 2 * F)
    (hu1 : 1 ≤ u) (hu : u ≤ 2) :
    ((Ioc F (F + S)).filter (fun p => p.Prime ∧ p ∣ n + u)).card ≤ 1 := by
  rw [Finset.card_le_one]
  have aux : ∀ p q : ℕ, F < p → p < q → p.Prime → q.Prime → p ∣ n + u → q ∣ n + u → False := by
    intro p q hFp hpq hpp hqp hpd hqd
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).2 (by omega)
    have hdvd : p * q ∣ n + u := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
    have hle : p * q ≤ n + u := Nat.le_of_dvd (by omega) hdvd
    have : (F + 1) * (F + 2) ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  intro p hp q hq
  simp only [mem_filter, mem_Ioc] at hp hq
  obtain ⟨⟨hFp, -⟩, hpp, hpd⟩ := hp
  obtain ⟨⟨hFq, -⟩, hqp, hqd⟩ := hq
  rcases lt_trichotomy p q with h | h | h
  · exact (aux p q hFp h hpp hqp hpd hqd).elim
  · exact h
  · exact (aux q p hFq h hqp hpp hqd hpd).elim

/-- **Lemma 5 (ii).** If `F ^ 2 ≤ n ≤ F ^ 2 + 2 F`, `F ≥ 1` and `p ≥ F + 2`, then
`(n + 1) ^ 2 < p ^ 2 * n`, that is `p > (n + 1) / √n`. -/
theorem lemma5_ii {n F p : ℕ} (hF : 1 ≤ F) (h1 : F ^ 2 ≤ n) (h2 : n ≤ F ^ 2 + 2 * F)
    (hp : F + 2 ≤ p) : (n + 1) ^ 2 < p ^ 2 * n := by
  have hn : 1 ≤ n := by nlinarith
  have hmono : (F + 2) ^ 2 * n ≤ p ^ 2 * n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp 2)
  have h3 : n * n ≤ n * (F ^ 2 + 2 * F) := Nat.mul_le_mul_left n h2
  have h4 : n * 1 ≤ n * F := Nat.mul_le_mul_left n hF
  nlinarith

/-- `(n + 1) ^ 2 < p ^ 2 * n` implies `n < p ^ 2` (so part (d) is stronger than part (a)). -/
theorem lt_sq_of_succ_sq_lt {n p : ℕ} (h : (n + 1) ^ 2 < p ^ 2 * n) : n < p ^ 2 := by
  by_contra hcon
  have : p ^ 2 * n ≤ n * n := by nlinarith [Nat.mul_le_mul_right n (not_lt.mp hcon)]
  nlinarith

/-! ## Proposition 6 and its consequences (section 4 of the draft) -/

/-- **Proposition 6.** Let `F ≥ 2`, `F ^ 2 ≤ n ≤ F ^ 2 + 2 F`. If the interval `(F, F + S]`
contains at least `K(F, S) + 2 + r` primes, then for every set `X` of at most `r` numbers there
is a prime `p` in `(F, F + S]`, not in `X`, with `s_p(n) ≥ p`. -/
theorem prop6 {n F S r : ℕ} (hF : 2 ≤ F) (h1 : F ^ 2 ≤ n) (h2 : n ≤ F ^ 2 + 2 * F)
    (hw : K F S + 2 + r ≤ ((Ioc F (F + S)).filter Nat.Prime).card)
    (X : Finset ℕ) (hX : X.card ≤ r) :
    ∃ p : ℕ, p.Prime ∧ F < p ∧ p ≤ F + S ∧ p ∉ X ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum := by
  have hB := card_failing_le (S := S) hF h1 h2
  have hlt : (((Ioc F (F + S)).filter (fun p => p.Prime ∧ n / p + n % p < p)) ∪ X).card <
      ((Ioc F (F + S)).filter Nat.Prime).card := by
    have := Finset.card_union_le
      ((Ioc F (F + S)).filter (fun p => p.Prime ∧ n / p + n % p < p)) X
    omega
  obtain ⟨p, hpA, hpn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [mem_filter, mem_Ioc, mem_union, not_or, not_and, not_lt] at hpA hpn
  obtain ⟨⟨hFp, hpS⟩, hpp⟩ := hpA
  obtain ⟨hgood, hpX⟩ := hpn
  have hsq : n < p ^ 2 := by nlinarith
  refine ⟨p, hpp, hFp, hpS, hpX, hsq, ?_⟩
  rw [digits_sum_of_lt_sq hpp.two_le hsq]
  exact hgood ⟨hFp, hpS⟩ hpp

/-- The window criterion (6.1) with `r = 2`: the interval `(F, F + S]` contains at least
`K(F, S) + 4` primes. -/
def WindowOK (F : ℕ) : Prop :=
  ∃ S : ℕ, K F S + 4 ≤ ((Ioc F (F + S)).filter Nat.Prime).card

/-- Parts (a), (b), (c) for one `n`, from the window criterion. -/
theorem window_partC {n F : ℕ} (hF : 2 ≤ F) (h1 : F ^ 2 ≤ n) (h2 : n ≤ F ^ 2 + 2 * F)
    (hw : WindowOK F) :
    ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧ ¬ p ∣ (n + 1) * (n + 2) := by
  obtain ⟨S, hS⟩ := hw
  have hX : (((Ioc F (F + S)).filter (fun p => p.Prime ∧ p ∣ n + 1)) ∪
      ((Ioc F (F + S)).filter (fun p => p.Prime ∧ p ∣ n + 2))).card ≤ 2 := by
    have := Finset.card_union_le ((Ioc F (F + S)).filter (fun p => p.Prime ∧ p ∣ n + 1))
      ((Ioc F (F + S)).filter (fun p => p.Prime ∧ p ∣ n + 2))
    have := card_prime_dvd_le_one (n := n) (F := F) (u := 1) S (by omega) h2 le_rfl (by norm_num)
    have := card_prime_dvd_le_one (n := n) (F := F) (u := 2) S (by omega) h2 (by norm_num) le_rfl
    omega
  obtain ⟨p, hpp, hFp, hpS, hpX, hsq, hds⟩ := prop6 hF h1 h2 hS _ hX
  refine ⟨p, hpp, hsq, hds, ?_⟩
  simp only [mem_union, mem_filter, mem_Ioc, not_or, not_and] at hpX
  intro hdvd
  rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
  · exact hpX.1 ⟨hFp, hpS⟩ hpp h
  · exact hpX.2 ⟨hFp, hpS⟩ hpp h

/-- Part (d) for one `n`, from the window criterion. -/
theorem window_partD {n F : ℕ} (hF : 2 ≤ F) (h1 : F ^ 2 ≤ n) (h2 : n ≤ F ^ 2 + 2 * F)
    (hw : WindowOK F) :
    ∃ p : ℕ, p.Prime ∧ (n + 1) ^ 2 < p ^ 2 * n ∧ p ≤ (Nat.digits p n).sum := by
  obtain ⟨S, hS⟩ := hw
  obtain ⟨p, hpp, hFp, hpS, hpX, hsq, hds⟩ :=
    prop6 (r := 2) hF h1 h2 hS {F + 1} (by simp)
  simp only [mem_singleton] at hpX
  exact ⟨p, hpp, lemma5_ii (by omega) h1 h2 (by omega), hds⟩

/-! ## Counting primes in a window with `Nat.primeCounting` -/

/-- The number of primes in `(a, b]` is `π(b) - π(a)`. -/
theorem card_primes_Ioc {a b : ℕ} (h : a ≤ b) :
    ((Ioc a b).filter Nat.Prime).card + Nat.primeCounting a = Nat.primeCounting b := by
  have e : (range (b + 1)).filter Nat.Prime =
      (range (a + 1)).filter Nat.Prime ∪ (Ioc a b).filter Nat.Prime := by
    ext x
    simp only [mem_filter, mem_union, mem_range, mem_Ioc]
    constructor
    · rintro ⟨hx, hp⟩
      by_cases hxa : x < a + 1
      · exact Or.inl ⟨hxa, hp⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
    · rintro (⟨hx, hp⟩ | ⟨⟨hx1, hx2⟩, hp⟩)
      · exact ⟨by omega, hp⟩
      · exact ⟨by omega, hp⟩
  have hdisj : Disjoint ((range (a + 1)).filter Nat.Prime) ((Ioc a b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_filter, mem_range, mem_Ioc] at hx hx'
    omega
  have hb : Nat.primeCounting b = ((range (b + 1)).filter Nat.Prime).card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have ha : Nat.primeCounting a = ((range (a + 1)).filter Nat.Prime).card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [hb, ha, e, Finset.card_union_of_disjoint hdisj]
  omega

/-- The window criterion in terms of `π`. -/
theorem windowOK_of_primeCounting {F S : ℕ}
    (h : K F S + 4 + Nat.primeCounting F ≤ Nat.primeCounting (F + S)) : WindowOK F := by
  refine ⟨S, ?_⟩
  have := card_primes_Ioc (a := F) (b := F + S) (by omega)
  omega

end Kellner
