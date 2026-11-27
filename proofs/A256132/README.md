# A256132 — Sum of three pentagonal numbers and a second pentagonal number

- **OEIS:** https://oeis.org/A256132
- **Status:** proof (reviewed) — the main statement; the "moreover" clause of Sun's Conjecture 5.2(i) (x, y, z not all even) is not addressed

## Statement (verbatim from OEIS)

From `oeis/oeisdata` (`seq/A256/A256132.seq`):

> Number of ways to write n as w*(3w+1)/2 + x*(3x-1)/2 + y*(3y-1)/2 + z*(3z-1)/2, where w,x,y,z are nonnegative integers with x <= y <= z.
>
> Conjecture: a(n) > 0 for all n. In other words, any nonnegative integer n can be expressed as the sum of three pentagonal numbers and a second pentagonal number.

Conventions: offset = `0, 3`; variables `w, x, y, z` are nonnegative integers (`0` allowed); `x <= y <= z` is an ordering convention for counting `a(n)` (the three pentagonal terms are symmetric). OEIS table covers `n = 0..6000` (Zhi-Wei Sun, Mar 15 2015).

## Sanity check

`python conjectures/A256132/verify.py --check` reproduces all 101 published terms (`n = 0..100`) of OEIS A256132 directly from the definition: **yes**.

## What is known

- **Prior work:** Linked OEIS preprint is Sun's `arXiv:1503.03743` (*A result similar to Lagrange's theorem*, JNT 2016), which proves the generalized octagonal four-term theorem and poses related conjectures. Ju & Kim (`arXiv:2010.16123`, *The pentagonal theorem of sixty-three*) covers sums of ordinary pentagonal numbers only (not mixed with second pentagonal numbers).
- **Novelty search done (2026-11-26):**
  - Checked `oeis/oeisdata` `seq/A256/A256132.seq` (last modified Nov 05 2025): still listed as open conjecture.
  - Checked `epoch-research/LeanOpenProblems-results` (`metadata/oeis/conjectures.json`) and `google-deepmind/alphaproof-nexus-results`: not present / not solved.
  - Queried arXiv API for `"A256132"`, `"three pentagonal"`, `"second pentagonal"`, `"pentagonal"` + `math.NT`, Ju/Kim/Oh/Sun/Meng papers, and web search for `"three pentagonal numbers and a second pentagonal number"`: no prior proof found.

## Handoff — read this first if you are picking the work up

- **How to resume:** Run `python conjectures/A256132/verify.py` to re-verify all computational claims in ~0.6 seconds.
- **Do not retry:** None.

## Result
