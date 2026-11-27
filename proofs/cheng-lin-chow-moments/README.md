# Cheng–Lin: Conjecture 3.30 (moment inequality from flag monotonicity) and Conjecture 3.14 (central moments of Chow polynomials)

- **Source:** R. Cheng, W. Lin, "Inequalities for Chow Polynomials and Chern Numbers of Matroids",
  arXiv:2603.21680v3 (29 Apr 2026), Conjecture 3.30 and Conjecture 3.14. (In v1 the first one is
  Conjecture 3.28.) Not an OEIS entry.
- **Status:** Conjecture 3.30: proof (reviewed). Conjecture 3.14: verified to rank 21 for even k ≤ 12
  (exact certificates; odd k is trivial); open in general.
  Each wrote its own exact check. No human has read the proof yet; that is still wanted.

## Statements (verbatim from the HTML of arXiv:2603.21680v3)

Notation of the paper. M is a matroid of rank d+1. For J = {j_1 < … < j_m} ⊆ [d], N_J(M) is the
number of flags of flats G_1 ⊊ … ⊊ G_m with rk(G_i) = j_i. The block sizes of J are

> n_{1}=j_{1}, n_{2}=j_{2}-j_{1}, …, n_{m}=j_{m}-j_{m-1}, n_{m+1}=d+2-j_{m},
> and for J=∅ we set m=0 and n_{1}=d+2.

and U_J := N_J(U_{d+1}) = n_{m+1}(d+1)!/∏ n_i!.

> Corollary 3.28. Let M be a matroid of rank d+1. Then
> Σ_{J⊂{1,…,d}} ∏_{i=1}^{m+1}(n_i−1) ( Σ_{i=1}^{m+1} n_i(n_i−3)/2 ) N_J ≤ 0, …

> Lemma 3.29. Let M be a matroid of rank d+1. For nested index sets J ⊆ J′, we have the
> monotonicity bound: N_J/U_J ≤ N_{J′}/U_{J′}.

> Conjecture 3.30. We conjecture that the inequality in Corollary 3.28
> Σ_{J⊂{1,…,d}} ∏_{i=1}^{m+1}(n_i−1) ( Σ_{i=1}^{m+1} n_i(n_i−3)/2 ) N_J ≤ 0
> is a nonnegative linear combination of the monotonicity inequalities established in Lemma 3.29.

> Remark 3.31. We verified Conjecture 3.30 by computer for all ranks d+1 with d ≤ 19.

> Conjecture 3.14. Let M be a matroid of rank d+1, and let k ≥ 0 be an integer. Then the central
> moments of X_M are bounded by the corresponding Boolean matroids:
> E[(X_M − d/2)^k] ≤ E[(X_d − d/2)^k].

Here X_M is the random variable whose probability generating function is the normalised Chow
polynomial of M, and X_d is the same for the Boolean matroid U_{d+1}. The paper says "Conjecture
3.14 remains unsolved"; it proves k = 2 (Corollary 3.6) and a version of k = 4 with a correction
term.

## Result 2: Conjecture 3.14 for rank ≤ 21 and k ≤ 12 (exact computation)

Claim: for every matroid M of rank d+1 with 2 ≤ d ≤ 20 and every even k ≤ 12,
E[(X_M − d/2)^k] ≤ E[(X_d − d/2)^k]. (For odd k both sides are 0 by the symmetry of Chow
polynomials; d ≤ 1 is trivial.)

Method. By Proposition 3.24 of the paper the Chow polynomial is Σ_J N_J P_J(x) with
P_J(x) = x^{-1} ∏ (x + ⋯ + x^{n_i−1}), so the claim is Σ_J a_J x_J ≤ 0 with
a_J = U_J P_J(1) ( m_k(J) − E_k ), where m_k(J) is the k-th central moment of a sum of independent
uniform variables on {1,…,n_i−1} and E_k the value for the Boolean matroid (so Σ_J a_J = 0).
`exactflow.py` computes the a_J exactly and finds, by an exact maximum flow in integers, a
nonnegative combination of the inequalities x_J ≤ x_{J′} (J ⊆ J′) equal to Σ a_J x_J. With Lemma
3.29 this proves the claim for that (d, k). Output: `moments_2_12.txt`, `moments_13_20.txt`
(all "ok" for k = 2, 4, 6, 8, 10, 12 and d = 2..20).

What this rests on: Proposition 3.24 and Lemma 3.29 of the paper (an arXiv preprint; GAP: we did not check their proofs), and our code.
The flow itself is not stored; rerunning recomputes it. A second, independent implementation
(`review_verify_c314.py`, by the reviewer) rebuilds the flow and checks the resulting identity exactly
for the same range d = 2..20, k ≤ 12 (`review_verify_c314_out.txt`; we reran it for d ≤ 14).

## What does not work, and what is open

- The same test with the convex functions (t − c)₊ in place of t^k **fails** from d = 4 on
  (`convex_2_12.txt`): monotonicity of N_J/U_J alone does not give convex-order domination of X_M
  by X_d. This says nothing about whether convex-order domination is true.
- No proof of Conjecture 3.14 for all d, even for k = 4 (see the partial work below).
- k = 4, partial (2026-11-27, `k4.py`, `k4thr.py`). For d ≥ 3 the k = 4 coefficient is
  (d+1)! μ_N(c) [ H(c) + G(c)(G(c)+N)/12 ] with H = Σ h(n_i), h(n) = (n+1−(n−1)⁴)/120 (checked
  against `exactflow.py` for d = 3..8; it is false for d = 2). Findings, all exact:
  the refinements "split off 2 or 3 on the left of any block, or on the right of the last block"
  suffice for d = 3..12, while the k = 2 moves (size 2 only) fail from d = 4 (`k4_out.txt`);
  the form without the term N·G/12 fails from d = 4, and the smallest multiple s of G that makes
  Σ μ (H + G²/12 + sG) x ≤ 0 is about N/24, not N/12 (`k4thr_out.txt`), so there is slack;
  there is a third identity w(a)(h(a) + g(a)²/12 + g(a)/10) = w(a−3)/30 + w(a−4)/80 for a ≥ 4
  (with w(1) = 0, w(0) = −1; checked for a ≤ 79 and by hand), which makes all "mass" terms of the
  first-block induction cancel exactly after left peels of sizes 2, 3, 4.
  GAP: the induction still does not close. The leftover is
  (1/30) Σ ν(p) w(m−4) [ x(p,m−4,4) − x(p,m) ] ≥ 0, the wrong sign; it comes from the fact that
  the form for N = 4 is positive on constants (+1/30). A stronger induction hypothesis that
  records the slack at the compositions (p, m−2, 2) is needed. Not found.
- k = 4, a lemma that does hold (proof sketch, machine-checked for n ≤ 16 in `k4nu_out.txt`): for the
  fully multiplicative weight ν(p) = ∏ w(p_i) (no special last block), every n ≥ 2, every monotone
  y ≥ 0 on C_n and every s ≥ n/12 − 1/15,  Σ_p ν(p) (H + G²/12 + sG)(p) y(p) ≤ 0, using only left
  peels of sizes 2, 3, 4. Sketch: first-block recursion; after peel 2 with weight w(2)(s − 1/10),
  peel 3 with weight 1/30 and peel 4 with weight 1/80 all mass terms cancel by identities (i) and
  (iii); the inner parameter s + g(a)/6 stays above the threshold because a(a−2)/12 ≥ 0. The bound
  −1/15 is sharp at n = 2 and n = 4. This is NOT Conjecture 3.14: the real weight μ has the factor
  n_k on the last block.
- Passing from ν to μ by splitting off the last block and keeping only the base terms of the
  lemma fails: the remaining form is ≤ 0 for N ≤ 8 and not for N = 9..16 (`k4rem.py`,
  `k4rem_out.txt`). The slack of the peels inside the prefix has to be used. Not solved.
- `restrict_out.txt`: which restricted families of refinements already suffice for k = 2
  (floating-point LP, d = 4..14). Splitting off a block of size 2 at either end of a block
  suffices for every d tested; so does splitting off 2 or 3 on the left only, or on the right only.
  Allowing splits only of the first block, or only of the last block, fails (first at d = 8 and
  d = 10). This narrowed the search for the proof.
- `c328.py` / `c328_2_20.txt`: floating-point LP formulation of Conjecture 3.30 as a
  maximum-closure problem, d ≤ 20, and `c328_21_27.txt` for d = 21..24 (the run for 25..27 was not
  finished). Evidence only; superseded by the proof.

## Novelty check (2026-11-27)

arXiv:2603.21680 is at v3 and still states both conjectures as open. arXiv search for the title
and for "Chow polynomial" with "moment", and a web search for the conjecture, found no proof. A
search is not a guarantee.
