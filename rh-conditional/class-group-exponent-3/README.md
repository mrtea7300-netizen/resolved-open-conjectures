# Imaginary quadratic fields with class group of exponent 3

- **Source of the question:** D. Shanks (question); D. W. Boyd and H. Kisilevsky, Proc. AMS 31
  (1972) (finiteness); A.-S. Elsenhans, J. Klüners and F. Nicolae, arXiv:1803.02056 / Acta Arith.
  193 (2020) (complete list under ERH).
- **Status:** proof (reviewed), assuming the Riemann Hypothesis for Dirichlet L-functions, which has a
  Lean-checked proof (Alpöge 2026, not yet refereed).

## Statement

For a fundamental discriminant D < 0, the class group of ℚ(√D) has exponent 3 if and only if
D ∈ {−23, −31, −59, −83, −107, −139, −211, −283, −307, −331, −379, −499, −547, −643, −883, −907,
−4027}. For every D in this list Cl(D) ≅ C₃, except D = −4027, where Cl(D) ≅ C₃ × C₃. The
exponent is 1 exactly for the nine class-number-one discriminants.

Conventions: fundamental discriminants only, so this is the ideal class group of the maximal order.
"Exponent 3" means the class group is a nontrivial elementary abelian 3-group.

## Result

[`proof.md`](proof.md) gives the full argument. GRH is used once, through Bach–Sorenson's explicit
bound for the least split prime of a quadratic field. That bound needs only ζ and L(s, χ_D) to be
zero-free in Re s > 1/2, which the Lean theorem `LFunction_ne_zero_of_half_lt_re` provides. Under
it, the class group can have exponent dividing 3 only if |D| < 2·10¹¹. That range is then checked
here with no hypothesis at all.

## What is known

- Boyd–Kisilevsky (1972) and Weinberger (1973) showed finiteness, ineffectively (as reported in
  EKN §1).
- EKN (2018) computed every field with |D| ≤ 3.1·10²⁰ and exponent ≤ 8 and found the same 17. They
  state completeness under ERH (their Theorem 2).
- Novelty search, 2026-11-27, with nothing found stating the unconditional exponent-3 list:
  - web searches for the exponent-3 list together with Alpöge/GRH/unconditional;
  - google-deepmind/formal-conjectures at HEAD (cites Alpöge in 233, 985, idoneal, Mills, powerful
    numbers; no exponent-3 file);
  - senamakel/conjectures-lean and ChatAndBuild/conjectures, 42 and 17 listed consequences (they
    include idoneal numbers and class number one, but not exponent 3);
  - the Paderborn exponent tables (math.uni-paderborn.de/en/ag/ca/research/exponent), via a search
    snippet only, which still say "under ERH".
- The step from EKN is immediate. The work here is the hypothesis check and an independent finite
  computation.

## Handoff — read this first if you are picking the work up

- **Next step:** review; check the Bach–Sorenson Table 3 entries against the journal PDF.
  - The text was read from the AMS PDF; the numbers are rounded computer output.
  - The sieve was run to 2·10¹¹, past the threshold 9.65·10¹⁰, leaving margin F = 0.58.
- **How to resume:**
  - `sh build.sh` (Linux/WSL gcc), then `bin/split_sieve 3 50000000000` and
    `bin/split_sieve 50000000000 100000000000`, and likewise for [10¹¹, 1.5·10¹¹) and
    [1.5·10¹¹, 2·10¹¹);
  - `python exact_classgroups.py survivors data/run_*.txt`;
  - `python bound.py`.
- **Do not retry:** PARI's `quadclassunit` as the proof of the survivor class groups (it is
  GRH-conditional in general); it is used here only as a cross-check.
