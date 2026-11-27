# Imaginary quadratic fields whose class group has exponent 3

**Status:** proof (reviewed) (Gemini 4 Neon review, `reviews/`), assuming the Riemann Hypothesis for Dirichlet L-functions, which has a
Lean-checked proof (Alpöge 2026, not yet refereed). Not reviewed.

Every step is proved here, cited with its theorem number (source opened unless marked
`UNVERIFIED CITATION:`), or computed by the committed code. There is no `GAP:`.

## Theorem

Let D < 0 be a fundamental discriminant and Cl(D) the ideal class group of K = Q(√D).
Then the exponent of Cl(D) divides 3 if and only if D is one of

- D = −3, −4, −7, −8, −11, −19, −43, −67, −163 (class number 1), or
- D = −23, −31, −59, −83, −107, −139, −211, −283, −307, −331, −379, −499, −547, −643, −883, −907
  (Cl(D) ≅ C₃), or D = −4027 (Cl(D) ≅ C₃ × C₃).

So exactly **17 imaginary quadratic fields have class group of exponent 3**.

**Dependence.** Unconditionally it was known only that the list of exponent-3 fields is finite
(ineffectively; Boyd–Kisilevsky 1972 and Weinberger 1973, as reported in [EKN, §1]). The list above
was known to be complete under the Extended Riemann Hypothesis [EKN, Theorem 2]. The only analytic
input below is Bach–Sorenson's explicit Chebotarev bound for a quadratic field, whose hypothesis is
that ζ(s) and L(s, χ_D) have no zeros with Re s > 1/2 (Step 3). That is the Lean theorem
`LFunction_ne_zero_of_half_lt_re` (see [`docs/GRH-DIRICHLET.md`](../../docs/GRH-DIRICHLET.md)).

**How new this is.** The statement is one line from [EKN, Theorem 2] once GRH for Dirichlet
L-functions is granted. What this folder adds: (a) the check that EKN's hypothesis is only the
Dirichlet case; (b) an independent finite computation. EKN covered |D| ≤ 3.1·10²⁰, but the argument
needs only |D| < 9.7·10¹⁰. Here the range |D| < 2·10¹¹ is done with a prime sieve, plus an exact form-based class
group computation for the 66 fields the sieve cannot settle. It does not rely on any
GRH-conditional class group routine. As of 2026-11-27 I found no one stating the unconditional
exponent-3 result (searches listed in README.md).

## Notation and conventions

- D < 0 is a fundamental discriminant, K = Q(√D), O_K its ring of integers, h(D) = |Cl(D)|.
- χ_D(n) = (D/n) is the Kronecker symbol. It is a primitive real Dirichlet character of conductor
  |D|.
- A prime q **splits** in K if qO_K = 𝔮𝔮̄ with 𝔮 ≠ 𝔮̄. For odd q ∤ D this holds iff (D/q) = +1. For
  q = 2 it holds iff D ≡ 1 (mod 8).
- The exponent E(D) is the least e ≥ 1 with c^e = 1 for all c ∈ Cl(D).

## Step 1 — odd exponent forces D = −4, −8 or −p

**Lemma 0.** If E(D) is odd, then D ∈ {−4, −8} or D = −p with p ≡ 3 (mod 4) prime.

*Proof.*
- By Gauss's genus theory, the 2-rank of Cl(D) is ω(D) − 1, where ω(D) is the number of primes
  dividing D. This is the fact used in the proof of [EKN, Lemma 6] ("by genus theory we have that
  a₁ + … + a_r = ω(D) − 1").
  `UNVERIFIED CITATION:` a textbook statement is D. A. Cox, *Primes of the form x² + ny²*,
  Theorem 3.15 and §6 (theorem number not re-checked).
- If E(D) is odd, Cl(D) has no element of order 2, so ω(D) = 1.
- A fundamental discriminant is a product of prime discriminants p* (with 2* ∈ {−4, −8, 8} and
  p* = (−1)^{(p−1)/2} p for odd p); see the proof of [EKN, Lemma 7].
- With one factor and D < 0, D is −4, −8, or −p with p ≡ 3 (mod 4). ∎

## Step 2 — a small split prime has large order

**Lemma 1** ([EKN, Lemma 1]; proof included). Let c ≥ 1, let q split in K, and let 𝔮 | q. If
q^c < |D|/4, then the class of 𝔮 in Cl(D) has order > c.

*Proof.*
1. Suppose 𝔮^k = (α) for some 1 ≤ k ≤ c, with α ∈ O_K. Then N(α) = q^k < |D|/4.
2. Write α = (u + v√D)/2 with u, v ∈ ℤ. Then N(α) = (u² + |D|v²)/4.
3. If v ≠ 0, then N(α) ≥ |D|/4, a contradiction. So v = 0 and α = u/2 ∈ O_K ∩ ℚ = ℤ.
4. Then (α) is fixed by complex conjugation, so 𝔮^k = 𝔮̄^k.
5. Unique factorisation of ideals then gives 𝔮 = 𝔮̄, contradicting that q splits.
6. Hence no power 𝔮^k with k ≤ c is principal. ∎

**Corollary 1.** If E(D) divides 3, every prime q that splits in K satisfies 4q³ ≥ |D|.
(The order of [𝔮] is 1 or 3. Lemma 1 with c = 3 excludes both when 4q³ < |D|.)

## Step 3 — the analytic input (the only place GRH is used)

**Theorem (Bach–Sorenson).** E. Bach and J. Sorenson, *Explicit bounds for primes in residue
classes*, Math. Comp. 65 (1996), 1717–1735, Theorem 5.1 and Table 3 (pp. 1729–1731, opened).
- Let E/K be a Galois extension of number fields, E ≠ ℚ, with Δ = |disc E| and n = [E : ℚ], and
  let σ ∈ Gal(E/K).
- Assuming ERH, Table 3 ("valid only when K = ℚ") gives, for each range of log Δ and of n, a
  triple (A, B, C) such that there is a prime p with Artin symbol (p, E/ℚ) = σ and
  p ≤ (A log Δ + Bn + C)².
- For n = 2 and 25 ≤ log Δ ≤ 100 the triple is (1.881, 0.34, 5.5). The other rows with
  log Δ ≥ 25 are listed in `bound.py`.

**What "ERH" means there.** §2 of the paper states: "The remainder of the paper assumes that the
zeta functions of E and ℚ are zero-free in ℜ(s) > 1/2."

**Application.** Take E = ℚ(√D) over the base field ℚ, and σ = 1. (Bach–Sorenson's Lemmas 4.6 and 4.9 use Re(ρ) = 1/2 for the nontrivial zeros; this follows from the zero-free half-plane by the functional equation, and is also stated directly in grh-lean as `LFunction_eq_zero_re` and `riemannZeta_eq_zero_re`.)
- Then n = 2 and Δ = |D|.
- A prime with trivial Artin symbol is unramified with trivial Frobenius, i.e. split.
- The hypothesis is: ζ(s) and ζ_K(s) = ζ(s)·L(s, χ_D) have no zeros in Re s > 1/2.
  - The factorisation is (2.2) of the paper, Hecke's theorem for the abelian extension K/ℚ, and is
    classical for quadratic fields.
  - ζ is the Dirichlet L-function of the trivial character modulo 1.
  - χ_D is a Dirichlet character modulo |D|.
  - Both are covered by `LFunction_ne_zero_of_half_lt_re` (every modulus N ≥ 1 and every character
    mod N, except the pole s = 1 of the principal character).
- No Hecke L-function of a class-group character, no non-abelian Dedekind zeta function and no
  automorphic L-function is involved.

**Consequence.** Assuming GRH for Dirichlet L-functions: for |D| ≥ e²⁵ some prime q splits in K
with q ≤ (1.881 log|D| + 6.18)² (for log|D| ≤ 100), and with the corresponding Table 3 bound above.

## Step 4 — reduction to |D| < 2·10¹¹

Suppose E(D) divides 3 and |D| ≥ 2·10¹¹ (so log|D| ≥ 26.02).
1. By Step 3 there is a split prime q ≤ (A L + 2B + C)², with L = log|D| and (A, B, C) from the
   n = 2 column of Table 3.
2. By Corollary 1, |D| ≤ 4q³ ≤ 4(A L + 2B + C)⁶, i.e.
   F(L) := L − log 4 − 6 log(A L + 2B + C) ≤ 0.
3. On each row, F′(L) = 1 − 6A/(A L + 2B + C) > 0 as soon as A L + 2B + C > 6A.
4. `bound.py` checks F > 0 and A L + 2B + C > 6A at both ends of every row from L = log(2·10¹¹) on,
   in 50-digit arithmetic. Output: [`data/bound_out.txt`](data/bound_out.txt).
   - F(log(2·10¹¹)) = 0.5775.
   - F changes sign at |D| ≈ 9.652·10¹⁰. This agrees with EKN's Table 2 entry 9.7·10¹⁰ for
     exponent 3.
5. Hence F(L) > 0 for all L ≥ log(2·10¹¹), a contradiction.

So, assuming GRH for Dirichlet L-functions, **E(D) | 3 implies |D| < 2·10¹¹.** (The sharper
threshold 9.65·10¹⁰ would do; 2·10¹¹ leaves a margin, because the Table 3 constants are rounded
computer output.)

## Step 5 — the finite check (unconditional)

By Lemma 0 only D = −4, −8 and D = −p with p ≡ 3 (mod 4) prime, p < 2·10¹¹, remain.

**Sieve** (`split_sieve.c`). For every prime p ≡ 3 (mod 4) with 3 ≤ p < 2·10¹¹:
- Compute q(p), the least prime that splits in ℚ(√−p):
  - q = 2 splits iff p ≡ 7 (mod 8);
  - an odd q ≠ p splits iff −p mod q is a nonzero square mod q (table lookup).
- If 4q(p)³ < p (exact 128-bit integer test), Lemma 1 shows E(−p) ∤ 3.
- Every other p is printed as a survivor.

| Range | Primes in range | Primes ≡ 3 (mod 4) | Survivors | Max q(p) | Wall time |
|---|---|---|---|---|---|
| [3, 5·10¹⁰) | 2 119 654 577 | 1 059 832 412 | 66 | 107 | 47 s |
| [5·10¹⁰+1, 10¹¹) | 1 998 400 235 | 999 202 120 | 0 | 127 | 47 s |
| [10¹¹+1, 1.5·10¹¹) | 1 957 383 143 | 978 691 189 | 0 | 113 | 55 s |
| [1.5·10¹¹+1, 2·10¹¹) | 1 931 667 103 | 965 830 845 | 0 | 131 | 56 s |

- **Cross-check of the sieve.** The first two prime counts sum to 4 118 054 812 = π(10¹¹) − 1,
  the known value π(10¹¹) = 4 118 054 813 without the prime 2. All four sum to
  8 007 105 058 = π(2·10¹¹) − 1, with π(2·10¹¹) = 8 007 105 059. It also reproduces π(10⁶) − 1 = 78 497
  and π(10⁹) − 1 = 50 847 533.
- **Hardest case.** Among p > 10⁶, the largest 4q(p)³/p is 0.446, at p = 1 333 963 with q = 53.
  Above 5·10¹⁰ the largest is 1.5·10⁻⁴ (per-run records in `data/run_*.txt`). So the sieve condition is never close to failing in the
  upper range. Every survivor is below 2.6·10⁵.

**Survivors** (`exact_classgroups.py survivors`). The 66 survivors (largest 253 507) and D = −4, −8
were handled by explicit class groups:
- enumerate the reduced primitive positive definite forms of discriminant D (one per class, so h(D)
  is their number);
- compute the order of each class by Dirichlet composition and reduction (H. Cohen, *A Course in
  Computational Algebraic Number Theory*, Algorithms 5.4.2 and 5.4.7; `UNVERIFIED CITATION:`
  algorithm numbers not re-checked; the code is self-tested on h(−23) = 3, Cl(−4027) ≅ C₃×C₃,
  h(−163) = 1, Cl(−84) ≅ C₂×C₂, h(−47) = 5).

Output: [`data/survivors_classgroups.txt`](data/survivors_classgroups.txt). Exactly the 9 + 17
discriminants of the Theorem have exponent dividing 3, with the class groups stated.

**Independent cross-check for small |D|.** `exact_classgroups.py scan 30000` (all fundamental
D > −30000) and PARI/GP `quadclassunit` over the same range give the same 26 discriminants (log in
README.md).

## Step 6 — conclusion

- Assume E(D) | 3.
- By Lemma 0, D ∈ {−4, −8} or D = −p with p ≡ 3 (mod 4).
- By Steps 3–4, |D| < 2·10¹¹.
- By Step 5, D is in the list.
- Conversely, every listed D has the stated class group (Step 5 output).

The class-number-one part agrees with the unconditional Heegner–Baker–Stark theorem, which is a
sanity check. ∎

## Remarks and what this does not do

- **Other small exponents.** EKN computed all fields with |D| ≤ 3.1·10²⁰ and class group exponent
  ≤ 8 [EKN, Theorem 1, Table 1]. Their Theorem 2 says that under ERH this list is complete for
  exponents 1–5 and 8, and that for exponents 2, 4, 8 the absence of Siegel zeros suffices.
  - Their ERH input is the same Bach–Sorenson bound (their Theorem 3).
  - The Siegel-zero input concerns real zeros of L(s, χ_D) (their §3).
  - Both are covered by the Dirichlet theorem.
  - So, granting the Lean theorem, the exponent-4 (203 fields), exponent-5 (27) and exponent-8 (778)
    lists are unconditional too.
  - The ERH bounds are 3.4·10¹⁵ for exponent 4 and 2.3·10²⁰ for exponent 5 [EKN, Table 2]. For
    exponent 8 they use the Siegel–Tatuzawa route of their §4, which I have not checked.
  - **This repository has not re-checked those computations or the exponent-8 reduction.** Treat
    these as consequences of a cited computation, not as results here.
- **Exponent 2** (fundamental discriminants) is Weinberger's theorem. Through Kani's Corollary 23 it
  gives Euler's idoneal numbers, which others have already treated (see the scouting table).
- **Exponents 6 and 7** are not settled: the GRH bound (2.5·10²⁵, 3.9·10³⁰) exceeds EKN's search
  range.
- **Lean.** The analytic step, Bach–Sorenson Table 3, is the hard part to formalise. The finite
  check would be a large `native_decide` or a certified sieve. Not attempted.

## References

- [EKN] A.-S. Elsenhans, J. Klüners, F. Nicolae, *Imaginary quadratic number fields with class
  groups of small exponent*, arXiv:1803.02056v1 (2018), opened; published in Acta Arith. 193
  (2020) 217–233 (`UNVERIFIED CITATION:` published version and page numbers not opened). Used:
  Lemma 1, the proofs of Lemmas 6–7, Theorem 2, Theorem 3, Tables 1–2.
- [BS] E. Bach, J. Sorenson, *Explicit bounds for primes in residue classes*, Math. Comp. 65
  (1996), 1717–1735, opened. Used: §2 (statement of the hypothesis), Theorem 5.1, Table 3.
- [BK] D. W. Boyd, H. Kisilevsky, *On the exponent of the ideal class groups of complex quadratic
  fields*, Proc. Amer. Math. Soc. 31 (1972), 433–436 (opened by the Gemini reviewer: Lemmas 1–2, Theorems 2 and 4; the
  download returned HTML).
- [W] P. J. Weinberger, *Exponents of the class groups of complex quadratic fields*, Acta Arith. 22
  (1973), 117–124 (`UNVERIFIED CITATION:` not opened).
- [Al] L. Alpöge (with Claude), Lean 4 proof of GRH for Dirichlet L-functions, announced
  2026-11-20; statements quoted in `docs/GRH-DIRICHLET.md`.
