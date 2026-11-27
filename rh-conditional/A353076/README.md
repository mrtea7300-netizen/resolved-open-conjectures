# A353076 is finite (given RH): the complete list has 884 terms

**Sequence.** A353076 lists the odd k with σ(k) > (e^γ/2)·k·log log k.

**Conditional theorem.** L. C. Washington and A. Yang, *Analogues of the Robin–Lagarias criteria for the Riemann
hypothesis*, IJNT 17 (2021) 843–870 (arXiv:2008.04787). They prove that RH holds **if and only if**
σ(n) < (e^γ/2)·n·log log n for every odd n ≥ c₀, where c₀ = 3⁴·5³·7²·11·13·…·67 = 18565284664427130919514350125
(this is A110464(24)).

**RH.** Mathlib's `RiemannHypothesis` now has a formal proof, announced by L. Alpöge on 2026-11-20. The Lean FRO and
the Mathlib Initiative state that the proved theorem is exactly Mathlib's statement
(<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>). Only RH for ζ is used here.

**What was missing.** Given the theorem, every term is below c₀. Washington and Yang checked only the 23 oddly
colossally abundant numbers below c₀ and left the other odd n < c₀ open; the OEIS b-file stops at 4.06·10⁹
(470 terms). So the full list was not known.

## Result

Every odd k < c₀ was enumerated. Exactly **884** odd k satisfy the inequality. The largest is

  **a(884) = 277093800961598968947975375 = c₀/67 = 3⁴·5³·7²·11·13·…·61**.

Together with Washington–Yang and RH, **A353076 is finite and `b353076_full_884.txt` is the full sequence.**
The enumeration does not use RH. Unconditionally, it sharpens Washington–Yang to: RH ⟺ no odd exception above
2.77·10²⁶.

## Method and checks

- **`oddrobin2.c`** (about 5 s). A depth-first search over odd prime-power factorizations k < c₀. A branch is
  pruned when even the best possible completion cannot reach the target. The best completion uses the next primes
  in order, each contributing its maximal abundancy p/(p−1), plus a tail factor for primes beyond the table. That
  bound is optimal because swapping in a smaller unused prime raises p/(p−1) and lowers the product. Run summary:
  24,283,674 nodes, 0 borderline values, 0 incomplete branches.
- **`oddrobin2s.c`** is the same search with a safety margin on the pruning test. It gives an identical list.
- **`oddrobin3.c`** (about 2.5 min) is an independent enumerator in `__float128`. It uses a different bound: at most
  r = ⌊log(c₀/v)/log p_j⌋ more distinct primes fit. It gives an identical list (31,643,475 nodes).
- **`brute.c`** is a σ sieve to 2·10⁷. It gives the same 334 terms.
- The count up to 4.06·10⁹ is 470, matching the existing OEIS b-file.
- **`verify_terms.py`** uses only the standard library. It recomputes σ exactly for all 884 terms and checks the
  inequality with 60-digit logarithms; the smallest relative margin is 2.35·10⁻⁵. It also re-derives every term
  ≤ 3·10⁶ by brute force.
- Both enumerators were re-run independently on 2026-11-27 and reproduced the 884 terms exactly.

Commands:

```
gcc -O2 -o oddrobin2 oddrobin2.c -lm && ./oddrobin2 18565284664427130919514350125 out2.txt
gcc -O2 -o oddrobin3 oddrobin3.c -lm -lquadmath && ./oddrobin3 18565284664427130919514350125 out3.txt
python3 verify_terms.py b353076_full_884.txt
```

Suggested OEIS edit (not submitted): add keywords `fini,full`, add the b-file for n = 1..884, and add a comment
citing Washington–Yang together with the 2026 proof of RH.
