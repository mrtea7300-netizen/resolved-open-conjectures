# Sun's Conjecture 2.1 of arXiv:1208.2683 (generalized Mandl inequality)

**Conjecture (Z.-W. Sun, 2012-09-12).** For any real α > 0,

    (1/n) Σ_{k=1}^{n} p_k^α  <  p_n^α/(α+1)    for all n ≥ 2⌈α⌉² + ⌈α⌉ + 6.

Source: Z.-W. Sun, *Conjectures involving arithmetical sequences*, arXiv:1208.2683 (v9), Conj. 2.1 and
Remark 2.1. Published in: Number Theory: Arithmetic in Shangri-La (S. Kanemitsu, H. Li, J. Liu, eds.),
World Sci., 2013, pp. 244–258. Remark 2.1 says the conjecture was verified for α = 2, 3, ..., 700 and
n ≤ 10^6. For α = 1 the statement is Mandl's inequality (Rosser–Schoenfeld 1975, Dusart 1998).

For 0 < α ≤ 1 the threshold is 2 + 1 + 6 = 9.

## Results

**Theorem A (counterexample).** For n = 9 the inequality fails for every α in (0, α₀], where
α₀ = 0.00233636… lies in (0.0023363, 0.0023364). For α in (α₀, 1] it holds at n = 9.
So Conjecture 2.1 is **false as stated**. Example: α = 1/1000 gives

    (1/9)(2^α + 3^α + ... + 23^α) − 23^α/(1+α) = +2.3213 × 10^-7 > 0.

**Theorem B.** For every real α in (0, 1] and every n ≥ 10,

    (1/n) Σ_{k≤n} p_k^α < p_n^α/(α+1).

Together, A and B describe exactly where the conjecture fails for 0 < α ≤ 1: only at n = 9 with
0 < α ≤ α₀. The conjecture holds for 0 < α ≤ 1 if the threshold 9 is replaced by 10.

Why it fails: as α → 0+, the inequality at n reduces to its first-order term in α,
θ(p_n) < n(log p_n − 1). At n = 9 this is false:
θ(23) − 9(log 23 − 1) = +0.0036508 > 0.

A numerical scan found no other violation: α on a grid in (0, 12], all n with threshold ≤ n ≤ 20000
(`scan_alpha_grid.py`, float). Theorem A is a single-point failure.

## Proof of Theorem A

Put Q_n(α) = n p_n^α − (1+α) Σ_{k≤n} p_k^α. The inequality at (n, α) holds if and only if Q_n(α) > 0.

Q_9(0) = 0 and Q_9'(0) = 9 log 23 − 9 − θ(23) = −0.0036508 < 0. `certify_small_n.py` proves
Q_9 < 0 on (0, 0.0023363] and Q_9 > 0 on [0.0023364, 1] by adaptive subdivision. On a cell [a, b]
with h = b − a, it uses Taylor's formula with Lagrange remainder,

    Q(α) ≥ Q(a) + min(Q'(a), 0)·h + min(Q''_low, 0)·h²/2   (and the mirror-image upper bound),

where Q''_low is a rigorous lower bound for Q'' on [a, b]. It comes from monotonicity: each
p^α (log p)^j is increasing in α. On the first cell Q(0) = 0 is used. Arithmetic is Decimal with
50 significant digits; exp and ln are correctly rounded, and every comparison has a margin of 1e-30.
Negative controls (`selftest.py`) confirm that the certifier refuses false claims, such as Q_9 > 0 on
(0, 1] or Q_9 < 0 up to 0.0023365. The point values at α = 10^-12, 10^-6, 10^-4, 10^-3 are in
`check.log`, Part 1, at 80 digits. ∎

## Proof of Theorem B

Notation: x = p_n, c = π(x)/x = n/x, S_n = Σ_{k≤n} p_k, and J(y) = ∫_0^y π(t) dt.
Then J(p_m) = m p_m − S_m.

**Step 0 (reformulation).** By Stieltjes integration,
Σ_{p≤x} p^α = x^α π(x) − α ∫_0^x t^{α−1} π(t) dt, and c ∫_0^x t^α dt = π(x) x^α/(α+1). So the claim
is equivalent to

    I(α) := ∫_0^x t^{α−1} (π(t) − c t) dt > 0.                              (0)

For α = 1, (0) reads J(x) > xπ(x)/2, i.e. 2S_n < n p_n (Mandl).

**Step 1 (Mandl with margin).** For every n ≥ 10,

    (n p_n − 2S_n)(2p_n − 23) > 23 n p_n,                                   (M)

and also 2S_m < m p_m for every m ≥ 9.

* For n ≤ 78498 (p_n < 10^6): exact integer check (`check.py`, Part 2). (M) holds for
  31 ≤ n ≤ 78498 and fails for 10 ≤ n ≤ 30. Those n are handled separately in Step 4.
  Mandl holds for all 9 ≤ m ≤ 78498.
* For p_n > 10^6 we prove g(y) := 2J(y) − (y+12)π(y) > 0 for all real y ≥ x₀ = 10^6 (Lemma 2 below).
  At y = p_n this gives n p_n − 2S_n = 2J(p_n) − p_n π(p_n) > 12n. Then
  (n p_n − 2S_n)(2p_n − 23) > 12n(2p_n − 23) ≥ 23 n p_n, because p_n ≥ 276.

*Lemma 2.* Use Dusart's bounds:

* (D1) π(t) ≥ (t/log t)(1 + 1/log t) for t ≥ 599 (Dusart 1999; also Dusart 2010, Thm 6.9).
* (D2) π(y) ≤ (y/log y)(1 + 1/log y + 2.51/log² y) for y ≥ 355991 (Dusart 2010, arXiv:1002.0442, Thm 6.9;
  also in Dusart 2018, Ramanujan J. 45).

Since t/L + t/L² = d/dt[t²/(2L)] + (3/2)t/L² (with L = log t), and 1/log² t ≥ 1/log² y on [x₀, y],
(D1) gives

    2J(y) ≥ 2J(x₀) − x₀²/L₀ + y²/L + 1.5(y² − x₀²)/L²,   L = log y, L₀ = log x₀.

Subtracting (D2) multiplied by (y + 12):

    g(y) ≥ K₁ + (y²/L²)·β,   K₁ = 2J(x₀) − x₀²/L₀ − 1.5 x₀²/L₀²,
    β = 0.5 − 2.51/L₀ − 12(L₀/x₀)(1 + 1/L₀ + 2.51/L₀²).

This step uses L ≥ L₀, the fact that L/y is decreasing, and the fact that y²/L² is increasing. The
exact values are π(10^6) = 78498 and Σ_{p≤10^6} p = 37550402023, so J(10^6) = 40947597977. They give
K₁ = 1.654 × 10^9 > 0 and β = 0.31814 > 0, hence g(y) ≥ K₁ + β x₀²/L₀² = 3.32 × 10^9 > 0
(`check.py`, Part 3). ∎

**Step 2 (J(t)/t² is strictly decreasing on [23, ∞)).** On [p_m, p_{m+1}) we have π = m and
J(t) = m t − S_m, so d/dt (J/t²) = (tπ − 2J)/t³ = (2S_m − m t)/t³. For m ≥ 9 and t ≥ p_m,
Step 1 gives 2S_m < m p_m ≤ m t, so the derivative is negative. J is continuous, which proves the claim.
Put H(t) = J(t) − c t²/2. For 23 ≤ t ≤ x this gives

    H(t) = t²(J(t)/t² − c/2) ≥ t²(J(x)/x² − c/2) = (t²/x²) H(x),   and   H(x) = n x/2 − S_n > 0.

**Step 3 (n ≥ 31).** Split (0) at T = 23 and integrate by parts on [T, x], using dH = (π − ct)dt:

    I = ∫_0^T (t^{α−1} − T^{α−1})(π − ct) dt + x^{α−1}H(x) + (1−α)∫_T^x H(t) t^{α−2} dt.

In the first integral t^{α−1} − T^{α−1} ≥ 0 and π ≥ 0, so it is
≥ −c ∫_0^T (t^{α−1} − T^{α−1}) t dt = −c(1−α)T^{α+1}/(2(α+1)). In the last integral, Step 2 gives
H(t) ≥ t²H(x)/x². Collecting terms, with h = H(x)/x² and r = T/x < 1:

    I·(α+1)/x^{α+1} ≥ 2h − (1−α) r^{α+1}(h + c/2) ≥ 2h − r(h + c/2).

The last expression is positive if and only if (n x − 2S_n)(2x − 23) > 23 n x, which is (M). So (0)
holds for all α in (0, 1] and all n ≥ 31.

**Step 4 (10 ≤ n ≤ 30).** For each of these 21 values, `certify_small_n.py` proves Q_n(α) > 0 on all
of (0, 1] by the same rigorous adaptive Taylor/interval method as in Theorem A. Here Q_n'(0) ranges
from 0.749 (n = 11) to 5.65 (n = 26). Log: `certify_small_n.log`. ∎

## What remains open in Conjecture 2.1

* α > 1 (thresholds 16, 27, …). Not attempted here. Note that the claim for all real α cannot be
  approached with present tools. For large α the sum is dominated by primes in [p_n(1 − O(1/α)), p_n],
  and with n ≈ 2α² this requires counting primes in intervals of length ≈ √(p_n log p_n) with relative
  error o(1/log p_n). That is beyond even RH. Each fixed α is presumably provable by the method of
  Step 3 combined with Dusart-type bounds and a finite check.
* Literature: I found no later paper on Conj. 2.1. I searched arXiv for Mandl/Sun and Axler's papers on
  sums of primes (arXiv:1409.1777, 1606.06874), and checked Hassani, math/0606765. The failure at n = 9
  appears to be new: Sun's verification used integer α ≥ 2.

## Files

* `check.py` / `check.log`: Part 1 (n = 9 values and bisection, 80 digits), Part 2 (exact check of (M)
  and Mandl for p_n < 10^6), Part 3 (constant of Lemma 2), Part 4 (float sanity scan, n ≤ 20000,
  α in [1e-5, 1]; its only violations are n = 9 with α ≤ 0.002).
* `certify_small_n.py` / `certify_small_n.log`: rigorous certification for n = 9 (both signs) and for
  n = 10..30.
* `selftest.py` / `selftest.log`: negative controls for the certifier.

Run: `nice -n 19 python3 check.py` (about 1 minute; needs numpy only for Part 4),
`python3 certify_small_n.py` (about 1 minute), `python3 selftest.py`.

---
Independent spot check (lead, 2026-11-27, 60-digit Decimal): at n = 9,
(1/9)Σ p_k^α − 23^α/(1+α) = +2.3213e-7 (α = 0.001), +1.169e-7 (α = 0.002), +1.454e-8 (α = 0.0023),
−2.654e-8 (α = 0.0024). This matches α₀ ≈ 0.0023364. The statement checked is Conjecture 2.1 exactly as written in the
arXiv source (v9), "For any α > 0 ... for all n ≥ 2⌈α⌉²+⌈α⌉+6". Dusart (2010, Thm 6.9) and Rosser–Schoenfeld constants were cited from memory by the drafting agent and should be double-checked
against the papers; the margin in Lemma 2 is large (2.6 in place of 2.51 still works).
