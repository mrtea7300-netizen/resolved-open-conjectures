/-
Kellner's conjecture (A094960): the finite check, checked by the Lean kernel.

This replaces Proposition 9 of `../proof.md` (a C program over all `n < 60184 ^ 2`) for every
`n < 468049 ^ 2`, and it uses neither `native_decide` nor any axiom beyond the three standard
ones. The Boolean checkers below are evaluated by the kernel (`decide +kernel`).

* `1361 ≤ F < 468049`: the window criterion (6.1) with `r = 2` holds for `F`. It is read off
  from an increasing chain of 12217 primes (`Kellner/Data.lean`): if `q₀ < q₁ < ... < q_k` are
  primes and `K(q₀, q_k - q₀) + 4 ≤ k`, then every `F` with `q₀ ≤ F < q₁` satisfies the
  criterion with `S = q_k - F`.
* `193 ≤ n < 1361 ^ 2`: for each `F = ⌊√n⌋` a sweep over `[F ^ 2, (F + 1) ^ 2)`. If the prime
  `p > F` is a witness at `n`, with `n = a p + b`, it stays one up to `(a + 1) p - 1`
  (resp. `(a + 1) p - 3` when `p ∤ (n + 1)(n + 2)` is also required), so the sweep jumps there.
* primality of the numbers in `Kellner/Data.lean`: `n` is prime if `B < n < (B + 1) ^ 2` and
  `gcd(n, B!) = 1`.
-/
import Kellner.Basic
import Kellner.Data

namespace Kellner

open Finset

/-! ## Primality by one gcd -/

/-- `B < n < (B + 1) ^ 2` and `gcd(n, M) = 1`. -/
def gcdPrime (B M n : ℕ) : Bool :=
  Nat.blt B n && (Nat.blt n ((B + 1) * (B + 1)) && Nat.beq (Nat.gcd n M) 1)

/-- If every prime `≤ B` divides `M`, then `gcdPrime B M n = true` implies that `n` is prime. -/
theorem gcdPrime_sound {B M n : ℕ} (hM : ∀ p : ℕ, p.Prime → p ≤ B → p ∣ M)
    (h : gcdPrime B M n = true) : n.Prime := by
  simp only [gcdPrime, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h3 : Nat.gcd n M = 1 := Nat.eq_of_beq_eq_true h3
  by_contra hnp
  have hn0 : 0 < n := by omega
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hB : B = 0 := by omega
    subst hB
    omega
  have hmp := Nat.minFac_prime hn1
  have hsq := Nat.minFac_sq_le_self hn0 hnp
  have hmB : n.minFac ≤ B := by
    by_contra hcon
    have h4 : B + 1 ≤ n.minFac := by omega
    have h5 : (B + 1) * (B + 1) ≤ n.minFac * n.minFac := Nat.mul_le_mul h4 h4
    nlinarith
  have hd : n.minFac ∣ Nat.gcd n M := Nat.dvd_gcd (Nat.minFac_dvd n) (hM _ hmp hmB)
  rw [h3] at hd
  exact hmp.not_dvd_one hd

theorem dvd_factorial_of_prime_le (B : ℕ) : ∀ p : ℕ, p.Prime → p ≤ B → p ∣ B.factorial :=
  fun _ hp hpB => Nat.dvd_factorial hp.pos hpB

theorem M700_eq : Data.M700 = Nat.factorial 700 := by decide +kernel

/-- Primality test used for the chain (numbers between 700 and `701 ^ 2`). -/
def isPrimeBig (n : ℕ) : Bool := gcdPrime 700 Data.M700 n

theorem isPrimeBig_sound {n : ℕ} (h : isPrimeBig n = true) : n.Prime :=
  gcdPrime_sound (by rw [M700_eq]; exact dvd_factorial_of_prime_le 700) h

/-- Primality test used for `Data.smallPrimes` (numbers between 6 and `41 ^ 2`). -/
def isPrimeSmall (n : ℕ) : Bool :=
  gcdPrime 6 (Nat.factorial 6) n || gcdPrime 40 (Nat.factorial 40) n

theorem isPrimeSmall_sound {n : ℕ} (h : isPrimeSmall n = true) : n.Prime := by
  simp only [isPrimeSmall, Bool.or_eq_true] at h
  rcases h with h | h
  · exact gcdPrime_sound (dvd_factorial_of_prime_le 6) h
  · exact gcdPrime_sound (dvd_factorial_of_prime_le 40) h

/-! ## The window criterion along a chain of primes -/

/-- The list is strictly increasing. -/
def sortedB : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => Nat.blt a b && sortedB (b :: t)

theorem sortedB_sound : ∀ l : List ℕ, sortedB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [sortedB, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := sortedB_sound (b :: t) h.2
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 ((List.pairwise_cons.1 ih).1 x hx)

/-- `goodFrom q rest k`: some element `r` of `rest`, at position `j`, has
`K(q, r - q) + 4 ≤ k + j + 1`. -/
def goodFrom (q : ℕ) : List ℕ → ℕ → Bool
  | [], _ => false
  | r :: rs, k => Nat.ble (K q (r - q) + 4) (k + 1) || goodFrom q rs (k + 1)

theorem goodFrom_sound (q : ℕ) : ∀ (rest : List ℕ) (k : ℕ), goodFrom q rest k = true →
    ∃ (pre : List ℕ) (r : ℕ) (post : List ℕ),
      rest = pre ++ r :: post ∧ K q (r - q) + 4 ≤ k + pre.length + 1
  | [], _, h => by simp [goodFrom] at h
  | r :: rs, k, h => by
    simp only [goodFrom, Bool.or_eq_true, Nat.ble_eq] at h
    rcases h with h | h
    · exact ⟨[], r, rs, rfl, by simpa using h⟩
    · obtain ⟨pre, r', post, hrs, hK⟩ := goodFrom_sound q rs (k + 1) h
      refine ⟨r :: pre, r', post, by rw [hrs]; rfl, ?_⟩
      simp only [List.length_cons]
      omega

/-- For `q ≤ F < r`: `K(F, r - F) ≤ K(q, r - q)`. -/
theorem K_chain_le {q F r : ℕ} (h1 : q ≤ F) (h2 : F < r) : K F (r - F) ≤ K q (r - q) := by
  obtain ⟨j, rfl⟩ : ∃ j, F = q + j := ⟨F - q, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = q + j + s + 1 := ⟨r - (q + j) - 1, by omega⟩
  have e1 : q + j + s + 1 - (q + j) = s + 1 := by omega
  have e2 : q + j + s + 1 - q = j + s + 1 := by omega
  rw [e1, e2]
  unfold K
  have e3 : q + j + (s + 1) = q + (j + s + 1) := by ring
  rw [e3]
  apply Nat.div_le_div_right
  nlinarith [Nat.zero_le (j * s), Nat.zero_le (j * j)]

/-- If `q ≤ F`, all elements of the increasing list `rest` are primes `> F`, and
`goodFrom q rest 0`, then the window criterion holds for `F`. -/
theorem windowOK_of_goodFrom {q F : ℕ} {rest : List ℕ} (hprime : ∀ x ∈ rest, x.Prime)
    (hsorted : rest.Pairwise (· < ·)) (hq : q ≤ F) (hF : ∀ x ∈ rest, F < x)
    (h : goodFrom q rest 0 = true) : WindowOK F := by
  obtain ⟨pre, r, post, hrest, hK⟩ := goodFrom_sound q rest 0 h
  subst hrest
  have hFr : F < r := hF r (by simp)
  refine ⟨r - F, ?_⟩
  have hsub : (pre ++ [r]).toFinset ⊆ (Ioc F (F + (r - F))).filter Nat.Prime := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have hx' : x ∈ pre ++ r :: post := by
      rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (by simp at hx; simp [hx])
    have hxr : x ≤ r := by
      rcases List.mem_append.1 hx with hx | hx
      · exact le_of_lt ((List.pairwise_append.1 hsorted).2.2 x hx r (by simp))
      · simp at hx
        omega
    rw [mem_filter, mem_Ioc]
    exact ⟨⟨hF x hx', by omega⟩, hprime x hx'⟩
  have hnodup : (pre ++ [r]).Nodup := by
    have h1 : (pre ++ r :: post).Nodup := hsorted.imp (fun h => ne_of_lt h)
    have h2 : pre ++ r :: post = (pre ++ [r]) ++ post := by simp
    rw [h2] at h1
    exact h1.of_append_left
  have hcard : (pre ++ [r]).toFinset.card = pre.length + 1 := by
    rw [List.toFinset_card_of_nodup hnodup]
    simp
  have hle := Finset.card_le_card hsub
  have hKm := K_chain_le hq hFr
  omega

/-- Walk along the chain `q :: rest` until `stop`: every element below `stop` must satisfy
`goodFrom` with the elements after it. -/
def chainOK (stop : ℕ) : List ℕ → Bool
  | [] => false
  | q :: rest => Nat.ble stop q || (goodFrom q rest 0 && chainOK stop rest)

theorem chainOK_sound (stop : ℕ) : ∀ (rest : List ℕ) (q : ℕ),
    (∀ x ∈ q :: rest, x.Prime) → (q :: rest).Pairwise (· < ·) →
    chainOK stop (q :: rest) = true → ∀ F : ℕ, q ≤ F → F < stop → WindowOK F
  | [], q, _, _, h => by
    intro F hqF hF
    simp only [chainOK, goodFrom, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
    rcases h with h | ⟨hg, -⟩
    · omega
    · exact absurd hg (by simp)
  | r :: rs, q, hp, hs, h => by
    intro F hqF hF
    rw [chainOK] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
    rcases h with h | ⟨hg, hc⟩
    · omega
    · have hs' := List.pairwise_cons.1 hs
      have hp' : ∀ x ∈ r :: rs, x.Prime := fun x hx => hp x (List.mem_cons_of_mem _ hx)
      by_cases hFr : F < r
      · refine windowOK_of_goodFrom hp' hs'.2 hqF ?_ hg
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hFr
        · exact lt_trans hFr ((List.pairwise_cons.1 hs'.2).1 x hx)
      · exact chainOK_sound stop rs r hp' hs'.2 hc F (by omega) hF

/-- One piece of the chain: all elements prime, increasing, and `chainOK`. -/
def chunkOK (stop : ℕ) (l : List ℕ) : Bool :=
  l.all isPrimeBig && (sortedB l && chainOK stop l)

theorem chunkOK_sound {stop q : ℕ} {rest : List ℕ} (h : chunkOK stop (q :: rest) = true) :
    ∀ F : ℕ, q ≤ F → F < stop → WindowOK F := by
  simp only [chunkOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hp, hs, hc⟩ := h
  exact chainOK_sound stop rest q (fun x hx => isPrimeBig_sound (hp x hx)) (sortedB_sound _ hs) hc

/-- The pieces fit together: each piece starts where the previous one stopped. -/
def glueOK : ℕ → List (ℕ × List ℕ) → Bool
  | _, [] => true
  | lo, (stop, l) :: cs =>
    (match l with
      | [] => false
      | q :: _ => Nat.beq q lo) && (chunkOK stop l && glueOK stop cs)

/-- The last stopping point. -/
def lastStop : ℕ → List (ℕ × List ℕ) → ℕ
  | lo, [] => lo
  | _, (stop, _) :: cs => lastStop stop cs

theorem glueOK_sound : ∀ (cs : List (ℕ × List ℕ)) (lo : ℕ), glueOK lo cs = true →
    ∀ F : ℕ, lo ≤ F → F < lastStop lo cs → WindowOK F
  | [], lo, _ => by
    intro F h1 h2
    simp only [lastStop] at h2
    omega
  | (stop, l) :: cs, lo, h => by
    intro F h1 h2
    simp only [lastStop] at h2
    cases l with
    | nil => simp [glueOK] at h
    | cons q rest =>
      simp only [glueOK, Bool.and_eq_true] at h
      obtain ⟨hq, hchunk, hglue⟩ := h
      have hq : q = lo := Nat.eq_of_beq_eq_true hq
      subst hq
      by_cases hF : F < stop
      · exact chunkOK_sound hchunk F h1 hF
      · exact glueOK_sound cs stop hglue F (by omega) h2

/-- (kernel computation) The chain of `Kellner/Data.lean` passes all checks. -/
theorem chains_ok : glueOK 1361 Data.chains = true := by decide +kernel

theorem chains_lastStop : lastStop 1361 Data.chains = 468059 := by decide +kernel

/-- The window criterion (6.1) with `r = 2` holds for every `F` with `1361 ≤ F < 468049`. -/
theorem windowOK_of_lt {F : ℕ} (h1 : 1361 ≤ F) (h2 : F < 468049) : WindowOK F :=
  glueOK_sound Data.chains 1361 chains_ok F h1 (by rw [chains_lastStop]; omega)

/-! ## Small `n`: a sweep over `[F ^ 2, (F + 1) ^ 2)` -/

/-- A sweep: from position `n` jump to `jump n`, which must be larger, until `top` is reached. -/
def sweep (jump : ℕ → ℕ) (top : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, n => Nat.ble top n || (Nat.blt n (jump n) && sweep jump top fuel (jump n))

theorem sweep_sound {P : ℕ → Prop} {jump : ℕ → ℕ} {top : ℕ}
    (hj : ∀ n : ℕ, n < jump n → ∀ m : ℕ, n ≤ m → m < jump n → m < top → P m) :
    ∀ fuel n : ℕ, sweep jump top fuel n = true → ∀ m : ℕ, n ≤ m → m < top → P m := by
  intro fuel
  induction fuel with
  | zero =>
    intro n h
    simp [sweep] at h
  | succ fuel ih =>
    intro n h m hnm hm
    simp only [sweep, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    rcases h with h | ⟨hlt, hrec⟩
    · omega
    · by_cases hmj : m < jump n
      · exact hj n hlt m hnm hmj hm
      · exact ih (jump n) hrec m (by omega) hm

/-- First prime `p` of the list that is a witness for part (c) at `n`: the answer is the end
`(n / p + 1) * p - 2` of the interval on which `p` stays a witness (0 if there is none). -/
def jumpC (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps =>
    cond (Nat.ble p (n / p + n % p) && Nat.ble (n % p + 3) p) ((n / p + 1) * p - 2) (jumpC n ps)

theorem jumpC_spec (n : ℕ) : ∀ ps : List ℕ, n < jumpC n ps →
    ∃ p ∈ ps, p ≤ n / p + n % p ∧ n % p + 3 ≤ p ∧ jumpC n ps = (n / p + 1) * p - 2
  | [], h => by simp [jumpC] at h
  | p :: ps, h => by
    by_cases hc : (Nat.ble p (n / p + n % p) && Nat.ble (n % p + 3) p) = true
    · have e : jumpC n (p :: ps) = (n / p + 1) * p - 2 := by
        simp only [jumpC, hc, Bool.cond_true]
      rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at hc
      exact ⟨p, by simp, hc.1, hc.2, e⟩
    · have e : jumpC n (p :: ps) = jumpC n ps := by
        rw [Bool.not_eq_true] at hc
        simp only [jumpC, hc, Bool.cond_false]
      rw [e] at h ⊢
      obtain ⟨p', hp', h1, h2, h3⟩ := jumpC_spec n ps h
      exact ⟨p', List.mem_cons_of_mem _ hp', h1, h2, h3⟩

/-- The same for part (d): the interval ends at `min ((n / p + 1) * p) (p * p - 2)`. -/
def jumpD (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps =>
    cond (Nat.ble p (n / p + n % p) && Nat.ble (n + 3) (p * p))
      (min ((n / p + 1) * p) (p * p - 2)) (jumpD n ps)

theorem jumpD_spec (n : ℕ) : ∀ ps : List ℕ, n < jumpD n ps →
    ∃ p ∈ ps, p ≤ n / p + n % p ∧ n + 3 ≤ p * p ∧
      jumpD n ps = min ((n / p + 1) * p) (p * p - 2)
  | [], h => by simp [jumpD] at h
  | p :: ps, h => by
    by_cases hc : (Nat.ble p (n / p + n % p) && Nat.ble (n + 3) (p * p)) = true
    · have e : jumpD n (p :: ps) = min ((n / p + 1) * p) (p * p - 2) := by
        simp only [jumpD, hc, Bool.cond_true]
      rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at hc
      exact ⟨p, by simp, hc.1, hc.2, e⟩
    · have e : jumpD n (p :: ps) = jumpD n ps := by
        rw [Bool.not_eq_true] at hc
        simp only [jumpD, hc, Bool.cond_false]
      rw [e] at h ⊢
      obtain ⟨p', hp', h1, h2, h3⟩ := jumpD_spec n ps h
      exact ⟨p', List.mem_cons_of_mem _ hp', h1, h2, h3⟩

/-- Quotient and remainder of `p * a + c` when `c < p`. -/
theorem div_mod_of_lt {p a c : ℕ} (hc : c < p) :
    (p * a + c) / p = a ∧ (p * a + c) % p = c := by
  have hp : 0 < p := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- A witness `p` for part (c) at `n` stays a witness on `[n, (n / p + 1) * p - 2)`. -/
theorem partC_of_interval {n m p : ℕ} (hp : p.Prime) (h1 : p ≤ n / p + n % p)
    (hnm : n ≤ m) (hm : m < (n / p + 1) * p - 2) (hsq : m < p ^ 2) :
    ∃ p' : ℕ, p'.Prime ∧ m < p' ^ 2 ∧ p' ≤ (Nat.digits p' m).sum ∧ ¬ p' ∣ (m + 1) * (m + 2) := by
  have hdm := Nat.div_add_mod n p
  generalize n / p = a at *
  generalize n % p = b at *
  subst hdm
  obtain ⟨j, rfl⟩ : ∃ j, m = p * a + b + j := ⟨m - (p * a + b), by omega⟩
  have e : (a + 1) * p = p * a + p := by ring
  rw [e] at hm
  have hbj : b + j + 3 ≤ p := by omega
  have e2 : p * a + b + j = p * a + (b + j) := by ring
  obtain ⟨hdiv, hmod⟩ := div_mod_of_lt (p := p) (a := a) (c := b + j) (by omega)
  refine ⟨p, hp, hsq, ?_, ?_⟩
  · rw [digits_sum_of_lt_sq hp.two_le hsq, e2, hdiv, hmod]
    omega
  · intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · have e3 : p * a + b + j + 1 = p * a + (b + j + 1) := by ring
      rw [e3] at hd
      have h3 := Nat.le_of_dvd (by omega) ((Nat.dvd_add_right (Nat.dvd_mul_right p a)).1 hd)
      omega
    · have e3 : p * a + b + j + 2 = p * a + (b + j + 2) := by ring
      rw [e3] at hd
      have h3 := Nat.le_of_dvd (by omega) ((Nat.dvd_add_right (Nat.dvd_mul_right p a)).1 hd)
      omega

/-- A witness `p` for part (d) at `n` stays a witness on
`[n, min ((n / p + 1) * p) (p * p - 2))`. -/
theorem partD_of_interval {n m p : ℕ} (hp : p.Prime) (h1 : p ≤ n / p + n % p) (hnm : n ≤ m)
    (hm1 : m < (n / p + 1) * p) (hm2 : m + 3 ≤ p * p) (hm0 : 2 ≤ m) :
    ∃ p' : ℕ, p'.Prime ∧ (m + 1) ^ 2 < p' ^ 2 * m ∧ p' ≤ (Nat.digits p' m).sum := by
  have hsq : m < p ^ 2 := by
    rw [pow_two]
    omega
  have hdm := Nat.div_add_mod n p
  generalize n / p = a at *
  generalize n % p = b at *
  subst hdm
  obtain ⟨j, rfl⟩ : ∃ j, m = p * a + b + j := ⟨m - (p * a + b), by omega⟩
  have e : (a + 1) * p = p * a + p := by ring
  rw [e] at hm1
  have e2 : p * a + b + j = p * a + (b + j) := by ring
  obtain ⟨hdiv, hmod⟩ := div_mod_of_lt (p := p) (a := a) (c := b + j) (by omega)
  refine ⟨p, hp, ?_, ?_⟩
  · have h3 : (p * a + b + j + 3) * (p * a + b + j) ≤ p * p * (p * a + b + j) :=
      Nat.mul_le_mul_right _ hm2
    nlinarith
  · rw [digits_sum_of_lt_sq hp.two_le hsq, e2, hdiv, hmod]
    omega

/-- The primes of `Data.smallPrimes` above `F`. -/
def primesAbove (F : ℕ) : List ℕ := Data.smallPrimes.filter (fun p => Nat.blt F p)

/-- The check for one `F`: both sweeps over `[F ^ 2, (F + 1) ^ 2)`, part (c) from 1081 on and
part (d) from 193 on. -/
def checkSmallF (F : ℕ) : Bool :=
  sweep (fun n => jumpC n (primesAbove F)) ((F + 1) * (F + 1)) 3000 (max (F * F) 1081) &&
    sweep (fun n => jumpD n (primesAbove F)) ((F + 1) * (F + 1)) 3000 (max (F * F) 193)

/-- (kernel computation) The numbers in `Data.smallPrimes` are prime. -/
theorem smallPrimes_ok : Data.smallPrimes.all isPrimeSmall = true := by decide +kernel

theorem prime_of_mem_primesAbove {F p : ℕ} (h : p ∈ primesAbove F) : p.Prime ∧ F < p := by
  simp only [primesAbove, List.mem_filter, Nat.blt_eq] at h
  exact ⟨isPrimeSmall_sound (List.all_eq_true.1 smallPrimes_ok p h.1), h.2⟩

theorem checkSmallF_sound {F : ℕ} (h : checkSmallF F = true) :
    ∀ m : ℕ, F * F ≤ m → m < (F + 1) * (F + 1) →
      (1081 ≤ m → ∃ p : ℕ, p.Prime ∧ m < p ^ 2 ∧ p ≤ (Nat.digits p m).sum ∧
        ¬ p ∣ (m + 1) * (m + 2)) ∧
      (193 ≤ m → ∃ p : ℕ, p.Prime ∧ (m + 1) ^ 2 < p ^ 2 * m ∧ p ≤ (Nat.digits p m).sum) := by
  simp only [checkSmallF, Bool.and_eq_true] at h
  obtain ⟨hC, hD⟩ := h
  intro m hm1 hm2
  constructor
  · intro hm
    refine sweep_sound (P := fun m => ∃ p : ℕ, p.Prime ∧ m < p ^ 2 ∧ p ≤ (Nat.digits p m).sum ∧
      ¬ p ∣ (m + 1) * (m + 2)) ?_ 3000 _ hC m (by omega) hm2
    intro n hn m' hnm hmj hmtop
    obtain ⟨p, hp, h1, -, h3⟩ := jumpC_spec n _ hn
    obtain ⟨hpp, hFp⟩ := prime_of_mem_primesAbove hp
    rw [h3] at hmj
    have hsq : m' < p ^ 2 := by
      have : (F + 1) * (F + 1) ≤ p * p := Nat.mul_le_mul hFp hFp
      rw [pow_two]
      omega
    exact partC_of_interval hpp h1 hnm hmj hsq
  · intro hm
    refine sweep_sound (P := fun m => 2 ≤ m → ∃ p : ℕ, p.Prime ∧ (m + 1) ^ 2 < p ^ 2 * m ∧
      p ≤ (Nat.digits p m).sum) ?_ 3000 _ hD m (by omega) hm2 (by omega)
    intro n hn m' hnm hmj hmtop hm0
    obtain ⟨p, hp, h1, h2, h3⟩ := jumpD_spec n _ hn
    obtain ⟨hpp, -⟩ := prime_of_mem_primesAbove hp
    rw [h3] at hmj
    exact partD_of_interval hpp h1 hnm (by omega) (by omega) hm0

/-- (kernel computation) The sweeps succeed for every `F` with `13 ≤ F ≤ 1360`. -/
theorem small_ok : (List.range' 13 1348).all checkSmallF = true := by decide +kernel

theorem small_both {n : ℕ} (h1 : 193 ≤ n) (h2 : n < 1361 ^ 2) :
    (1081 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧
      ¬ p ∣ (n + 1) * (n + 2)) ∧
    (193 ≤ n → ∃ p : ℕ, p.Prime ∧ (n + 1) ^ 2 < p ^ 2 * n ∧ p ≤ (Nat.digits p n).sum) := by
  have hlo : 13 ≤ n.sqrt := Nat.le_sqrt'.2 (by omega)
  have hhi : n.sqrt < 1361 := Nat.sqrt_lt'.2 h2
  have hF := List.all_eq_true.1 small_ok n.sqrt (by rw [List.mem_range'_1]; omega)
  exact checkSmallF_sound hF n (Nat.sqrt_le n) (Nat.lt_succ_sqrt n)

/-- Part (c) for `1081 ≤ n < 1361 ^ 2`. -/
theorem partC_small {n : ℕ} (h1 : 1081 ≤ n) (h2 : n < 1361 ^ 2) :
    ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum ∧ ¬ p ∣ (n + 1) * (n + 2) :=
  (small_both (by omega) h2).1 h1

/-- Part (d) for `193 ≤ n < 1361 ^ 2`. -/
theorem partD_small {n : ℕ} (h1 : 193 ≤ n) (h2 : n < 1361 ^ 2) :
    ∃ p : ℕ, p.Prime ∧ (n + 1) ^ 2 < p ^ 2 * n ∧ p ≤ (Nat.digits p n).sum :=
  (small_both h1 h2).2 h1

/-! ## The exceptional set `E₀` (sanity check of the statement, and sharpness of 192) -/

/-- The primes below 193. -/
def primes193 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191]

/-- (kernel computation) `primes193` is exactly the set of primes below 193. -/
theorem primes193_spec : ∀ p : ℕ, p < 193 → (p.Prime ↔ p ∈ primes193) := by decide +kernel

/-- Is there a prime `p > √n` with `s_p(n) ≥ p`? (For `n ≤ 192`; such a prime is `≤ n`.) -/
def hasWitA (n : ℕ) : Bool :=
  primes193.any (fun p => Nat.ble p (n / p + n % p) && Nat.blt n (p * p))

theorem hasWitA_iff {n : ℕ} (hn : n ≤ 192) :
    hasWitA n = true ↔ ∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum := by
  unfold hasWitA
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, hmem, hp⟩
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hp
    obtain ⟨hds, hsq⟩ := hp
    have hpp : p.Prime := by
      by_cases hlt : p < 193
      · exact (primes193_spec p hlt).2 hmem
      · exfalso
        have hall : ∀ q ∈ primes193, q < 193 := by decide
        exact hlt (hall p hmem)
    have hsq' : n < p ^ 2 := by rw [pow_two]; exact hsq
    exact ⟨p, hpp, hsq', by rw [digits_sum_of_lt_sq hpp.two_le hsq']; exact hds⟩
  · rintro ⟨p, hpp, hsq, hds⟩
    rw [digits_sum_of_lt_sq hpp.two_le hsq] at hds
    have hpn : p ≤ n := by
      have h1 := Nat.div_add_mod n p
      have h2 : n / p ≤ p * (n / p) := Nat.le_mul_of_pos_left _ hpp.pos
      generalize n / p = a at *
      generalize n % p = b at *
      omega
    refine ⟨p, (primes193_spec p (by omega)).1 hpp, ?_⟩
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
    exact ⟨hds, by rw [← pow_two]; exact hsq⟩

/-- The set `E₀` of the draft (26 numbers). -/
def E0 : List ℕ :=
  [1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80, 174,
    190, 191, 192]

/-- (kernel computation) Among `1 ≤ n ≤ 192`, the `n` without a witness are exactly those in
`E₀`. -/
theorem finite_E0 :
    (List.range' 1 192).all (fun n => hasWitA n == !(E0.contains n)) = true := by
  decide +kernel

/-- For `1 ≤ n ≤ 192`: there is a prime `p > √n` with `s_p(n) ≥ p` if and only if `n ∉ E₀`. -/
theorem exceptions_iff {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 192) :
    (∃ p : ℕ, p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum) ↔ n ∉ E0 := by
  have h := List.all_eq_true.1 finite_E0 n (by rw [List.mem_range'_1]; omega)
  rw [← hasWitA_iff h2]
  cases hw : hasWitA n <;> simp_all

end Kellner
