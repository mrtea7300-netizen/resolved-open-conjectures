# A271719 — Partitions n = x + y + z with x >= y > 0, z > 0, gcd(x,y,z) = 1 and x^2 + (2y+z)^2 a square

- **OEIS:** https://oeis.org/A271719
- **Status:** proof (reviewed)

## Statement (verbatim from OEIS)

From `oeis/oeisdata` (`seq/A271/A271719.seq`):

> Number of ordered ways to write n as x + y + z with x >= y > 0, z > 0 and gcd(x,y,z) = 1 such that x^2 + (2*y+z)^2 is a square.
>
> Conjecture: a(n) > 0 for all n > 10, and a(n) = 1 only for n = 11, 12, 14, 18, 24, 54.

Conventions: offset = `1, 6`; variables `x, y, z` are positive integers with `x >= y >= 1`, `z >= 1`, `gcd(x, y, z) = 1`, ordered triples `(x, y, z)`. OEIS b-file covers `n = 1..2000` (Zhi-Wei Sun, Apr 12 2016).

## Sanity check

`python conjectures/A271719/verify.py --check` reproduces all 70 published terms (`n = 1..70`) of OEIS A271719 directly from the definition: **yes**.

## What is known

- **Prior work:** Linked OEIS preprint is Sun's `arXiv:1604.06723` (*Refining Lagrange's four-square theorem*, JNT 2017), which poses related conjectures. Huang & Sun (`arXiv:2105.03416`) studied $n = x + y + z$ with $x^2 + y^2 + z^2$ or $x^2 + y^2 + 2z^2$ a square, not $x^2 + (2y+z)^2$.
- **Novelty search done (2026-11-26):**
  - Checked `oeis/oeisdata` `seq/A271/A271719.seq` (last modified Nov 05 2025): still listed as open conjecture.
  - Checked `epoch-research/LeanOpenProblems-results` (`metadata/oeis/conjectures.json`) and `google-deepmind/alphaproof-nexus-results`: not present / not solved.
  - Queried arXiv API for `"A271719"`, Huang/Sun papers, and web search for `"x^2 + (2y+z)^2"` and `"11, 12, 14, 18, 24, 54"`: no prior proof found.

## Handoff — read this first if you are picking the work up

- **How to resume:** Run `python conjectures/A271719/verify.py` (~37 seconds total, dominated by the independent direct `(x, y, z)` brute force on `1..1302`).
- **Do not retry:** None.

## Result
