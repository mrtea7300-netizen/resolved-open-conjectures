# Ramanujan's prime-counting inequality: all integer counterexamples (given RH)

**Inequality.** Ramanujan's inequality is π(x)² < (e·x/log x)·π(x/e). An integer x ≥ 2 is a **counterexample**
when π(x)² ≥ e·x·π(x/e)/log x. OEIS A091886 lists the integers that satisfy the inequality; its b-file has
10000 terms. The complement, the set of counterexamples, is not in the OEIS: no sequence in the local mirror
cites A091886.

**Conditional theorem.** A. W. Dudek and D. J. Platt, *On solving a curious inequality of Ramanujan*, Exp. Math.
24 (2015) 289–294 (arXiv:1407.1901), Theorem 1.3: assuming RH, **the largest integer counterexample is
x = 38358837682.** The proof has two parts:
- Lemma 3.2 uses RH, through Schoenfeld's bound, and covers x ≥ 1.15·10¹⁶.
- Lemma 3.4 is an unconditional computation that covers [10¹¹, 1.15·10¹⁶].

Before that, Galway had found that the largest *prime* counterexample below 10¹¹ is 38358837677.

**RH.** RH has been proved (Alpöge, 2026-11-20; the Lean FRO/Mathlib certification of `RiemannHypothesis`). Only
RH for ζ is used here.

**What was missing.** The literature gives only the largest counterexamples. The full set below 3.84·10¹⁰ had not
been enumerated in any source I checked: Dudek–Platt, Hassani, Axler, Platt–Trudgian, Johnston, or the OEIS
entry. Its size was not published either.

## Result

Every integer 2 ≤ x ≤ 10¹¹ was enumerated. The counterexamples are exactly the union of the **107,146 maximal
runs** in `counterexample_runs.txt`, one run "lo hi" per line, both ends included. In total:

- **564,384,969** integer counterexamples, the first being 2 and the last **38358837682**;
- **25,816,213** of them are prime, the last being **38358837677**;
- the longest run is [2563422403, 2607582810], which is 44,160,408 consecutive integers.

With Dudek–Platt and RH, **this is the complete list.** Ramanujan's inequality holds for every integer
x ≥ 38358837683. `decade_counts.txt` gives the counts up to 10ⁿ. They are constant for n ≥ 11, so each column is a
finite, complete sequence: 6, 25, 137, 1951, 18287, 179847, 1641673, 14634007, 83241066, 416968101, 564384969 for all
counterexamples, and 4, 14, 48, 323, 2076, 15087, 112336, 858256, 4355850, 19680636, 25816213 for the primes.

The enumeration on [2, 10¹¹] does not use RH. RH is needed only for x > 1.15·10¹⁶. Unconditionally the inequality
is known for 38358837683 ≤ x ≤ e¹⁰³ (Platt–Trudgian; Johnston) and for x > e³⁶⁰⁴ (Cully-Hugill–Johnston). The range
between e¹⁰³ and e³⁶⁰⁴ still needs RH.

A complete b-file is not practical, because there are 5.6·10⁸ terms. The runs file encodes the whole set exactly.

## Method and checks

- **`ramanujan.c`** (about 18 min to 10¹¹ on one core at nice 19). It runs two independent segmented sieves:
  - one gives the primes p, where π(x) jumps at x = p;
  - the other gives the primes q, where π(⌊x/e⌋) jumps at x = ⌊q·e⌋+1. The value ⌊q·e⌋ is computed in `__float128`.
    The smallest observed distance of q·e from an integer is 8.2·10⁻¹¹, far above the rounding error.

  Between jumps, (π(x), π(x/e)) is constant and e·x·π(x/e)/log x is increasing. So the counterexamples in each block
  form an initial run, which is scanned. The inequality is tested in long double, and in `__float128` when the
  relative gap is below 10⁻¹². That happened 760 times and was never closer than 10⁻²⁸. Output checks:
  π(10¹¹) = 4118054813 (the known value); last counterexample 38358837682 (Dudek–Platt); last prime
  counterexample 38358837677 (Galway).
- **`brute2.c`** is an independent re-enumeration to 4·10¹⁰ (about 7 min). It is written separately, with a
  bit-packed sieve, ⌊x/e⌋ from an exact 90-bit fixed-point accumulator, and the inequality tested at **every**
  integer, without the monotonicity shortcut. Its runs file is **byte-identical** to the part of
  `counterexample_runs.txt` up to 4·10¹⁰, and its counts are the same. It also reports π(4·10¹⁰) = 1711955433.
- **`lucy_check.c`** computes π with the Lucy_Hedgehog O(x^{3/4}) method, which uses no sieve of [1, x]. It
  rechecked 1355 boundary points: lo−1, lo, hi and hi+1 for the first 20 runs, the last 20 runs, the longest run and
  300 random runs, plus x = 38358837683..38358837699, 4·10¹⁰ and 10¹¹. There were 0 mismatches. `make_sample.py`
  builds the point list.
- **`verify.py`** uses only the standard library (`python3 verify.py counterexample_runs.txt 2000000 --lucy`,
  about 2 min). It:
  - checks that the runs are sorted, disjoint and maximal;
  - re-derives every counterexample ≤ 2·10⁶ by brute force (331,754 of them, identical) using 50-digit Decimal
    arithmetic;
  - recomputes π(x) and π(⌊x/e⌋) with a pure-Python Lucy count at the ends of the last two runs and just outside
    them. Output is in `verify.log`.

Commands:

```
gcc -O2 -o ramanujan ramanujan.c -lm -lquadmath && ./ramanujan 100000000000 counterexample_runs.txt
gcc -O2 -o brute2 brute2.c -lm && ./brute2 40000000000 runs_4e10.txt
gcc -O2 -o lucy_check lucy_check.c -lm -lquadmath
python3 make_sample.py counterexample_runs.txt | cut -d' ' -f1 | ./lucy_check
python3 verify.py counterexample_runs.txt 2000000 --lucy
```

Suggested OEIS additions (not submitted):
- a comment on A091886 that, by Dudek–Platt and the proof of RH, its complement is finite with 564384969
  elements in 107146 runs;
- the two finite sequences in `decade_counts.txt`, with keywords `fini,full`;
- possibly the sequence of run starts, which has 107146 terms.

sets were never enumerated
