# A350299 is finite (given RH): the 11 listed terms are the whole sequence

**Sequence.** A350299 lists the k > 1 with G(k) > G(m) for all m > k, where G(k) = σ(k)/(k·log log k). The OEIS
data is 3, 4, 6, 12, 24, 60, 120, 180, 360, 2520, 5040, with keyword `nonn` only: neither `fini` nor `full` is set.

**Argument.** It uses one unconditional theorem and one theorem that is now proved:
- Gronwall's theorem, which is unconditional: limsup G = e^γ.
- Robin's theorem (1984), together with the proof of RH (Alpöge 2026; Lean/Mathlib `RiemannHypothesis`): G(m) < e^γ
  for every m > 5040.

From these:
- If G(k) < e^γ, then some m > k has G(m) > G(k), so k is not a term. In particular no k > 5040 is a term.
- If k ≤ 5040 and G(k) > e^γ, then every m > 5040 satisfies G(m) < G(k). So k is a term exactly when G(k) > G(m)
  for all k < m ≤ 5040.
- G(k) = e^γ does not occur for any k ≤ 5040 (checked).

Hence A350299 = {k ≤ 5040 : G(k) > e^γ and G(k) > max_{k<m≤5040} G(m)}.

`verify_A350299.py` uses only the standard library and computes this set exactly with 40-digit Decimal arithmetic.
It gives the 11 known terms, so the sequence is **full and finite** and its last term is 5040. No new terms were
found; the only missing items are the keywords and a comment.

The same reasoning settles A196229, which has 27 terms indexed by A067698. A067698 itself is already settled.
