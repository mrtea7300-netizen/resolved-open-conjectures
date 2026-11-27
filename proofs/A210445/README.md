# OEIS A210445

- **Status:** `proof (formalized)` (Lean 4.36.0, zero external dependencies, zero `sorry`, zero non-standard axioms)

## Verbatim statement

From OEIS `A210445.seq` (retrieved from `oeis/oeisdata`, updated May 30 2026):

> **Name:** Least positive integer k with k*n practical.
>
> **Conjecture:** a(n) < n for all n>1, and a(n) < n/2 for all n>47.
>
> **Offset:** `1,3`
> **Published terms (`n = 1..20`):** `1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 6, 1, 6, 2, 2, 1, 12, 1, 12, 1`

## Result

**Both parts of Zhi-Wei Sun's conjecture are proved and formally verified in Lean 4:**
- `A210445.a210445_part1`: for every $n > 1$, $\exists k,\; 0 < k < n \;\land\; \mathrm{IsPractical}(k \cdot n)$.
- `A210445.a210445_part2`: for every $n > 47$, $\exists k,\; 0 < k \;\land\; 2k < n \;\land\; \mathrm{IsPractical}(k \cdot n)$.

Here `IsPractical m` is defined directly from the textbook subset-sum definition: $m > 0$ and every $r \le m$ is a sum of distinct positive divisors of $m$.

See [`proof.md`](proof.md) for the human-readable proof and [`A210445.lean`](A210445.lean) for the self-contained Lean 4 formalization.

## Reproducing the verification

```bash
lean conjectures/A210445/A210445.lean
```

## Novelty check (2026-11-26)

- Checked `A210445.seq` in `oeis/oeisdata` (last edited May 30 2026): conjecture is still listed as open.
- Checked `https://tadamcz.com/oeis-open/`: `A210445` is not listed.
- Web search for `"A210445"` and `"k*n is practical"` / `"a(n) < n/2 for all n>47"`: no prior proof found.
