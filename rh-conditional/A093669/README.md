# Complete Classification of $N = ab + bc + ca$: OEIS A093669, A093670, and A025052 (given Dirichlet GRH)

- **OEIS:** [A093669](https://oeis.org/A093669), [A093670](https://oeis.org/A093670), [A025052](https://oeis.org/A025052)
- **Status:** `proof (draft)`, assuming the Riemann Hypothesis for Dirichlet $L$-functions (`DirichletLNonvanishingRightOfHalf`), which has a Lean-checked proof (Alpöge 2026, not yet refereed). *(Note: the finiteness and completeness of `A093669` alone is also unconditional via Watkins 2004 / Arno 1992 for $h \le 4$; `A093670` and `A025052` genuinely require Dirichlet GRH via completeness of Euler's 65 idoneal numbers.)*

---

## Verbatim Statements (from `oeis/oeisdata` mirror)

- **A093669** (rev. `#11`, Nov 14 2021):
  > **Name:** Numbers having a unique representation as `ab+ac+bc`, with `0 < a < b < c`.  
  > **Data:** `11, 14, 17, 19, 20, 27, 32, 34, 36, 43, 46, 49, 52, 64, 67, 73, 82, 97, 100, 142, 148, 163, 193`  
  > **Comment:** `Are there more terms?` / `No more terms < 10^6.`
- **A093670** (rev. `#3`, Mar 30 2012):
  > **Name:** Numbers having a unique representation as `ab+ac+bc`, with `1 <= a <= b <= c`.  
  > **Data:** `3, 5, 7, 8, 9, 12, 13, 14, 16, 25, 28, 34, 37, 46, 82, 142`  
  > **Comment:** `Are there more terms?`
- **A025052** (rev. `#47`, Oct 22 2025):
  > **Name:** Numbers not of form `a*b + b*c + c*a` for `1<=a<=b<=c` (probably the list is complete).  
  > **Data:** `1, 2, 4, 6, 10, 18, 22, 30, 42, 58, 70, 78, 102, 130, 190, 210, 330, 462`

---

## Main Theorem

Let $r_{\mathrm{strict}}(N) = \#\{(a,b,c) \in \mathbb{Z}^3 : 0 < a < b < c,\; ab + bc + ca = N\}$ and $r_{\mathrm{all}}(N) = \#\{(a,b,c) \in \mathbb{Z}^3 : 1 \le a \le b \le c,\; ab + bc + ca = N\}$.

1. **A093669 (complete, 23 terms — also unconditional via Watkins 2004 / Arno 1992):**
   $$\{N \ge 1 : r_{\mathrm{strict}}(N) = 1\} = \{11, 14, 17, 19, 20, 27, 32, 34, 36, 43, 46, 49, 52, 64, 67, 73, 82, 97, 100, 142, 148, 163, 193\}.$$
2. **A093670 (complete, 16 terms — assuming Dirichlet GRH):**
   $$\{N \ge 1 : r_{\mathrm{all}}(N) = 1\} = \{3, 5, 7, 8, 9, 12, 13, 14, 16, 25, 28, 34, 37, 46, 82, 142\}.$$
3. **A025052 (complete, 18 terms — assuming Dirichlet GRH; Borwein–Choi 2000):**
   $$\{N \ge 1 : r_{\mathrm{all}}(N) = 0\} = \{1, 2, 4, 6, 10, 18, 22, 30, 42, 58, 70, 78, 102, 130, 190, 210, 330, 462\}.$$

---

## Proof Idea (full details in [`proof.md`](proof.md))

1. **Exact Bijection:** The map $(a, b, c) \mapsto (a + b,\; 2a,\; a + c)$ is a bijection between strict triples $0 < a < b < c$ with $ab + bc + ca = N$ and strictly reduced, non-ambiguous positive-definite binary quadratic forms $(A, 2k, C)$ of discriminant $-4N$ with $0 < 2k < A < C$.
2. **Content Decomposition:** Grouping by content $d = \gcd(A, 2k, C)$ yields
   $$r_{\mathrm{strict}}(N) = \sum_{\substack{d \ge 1 \\ d^2 \mid 4N,\; -4N/d^2 \equiv 0,1 \pmod 4}} \frac{h(-4N/d^2) - g(-4N/d^2)}{2},$$
   where $h(\Delta) = |\mathrm{Cl}(\Delta)|$ and $g(\Delta) = |\mathrm{Cl}(\Delta)[2]|$.
3. **Why $r_{\mathrm{strict}}(N) = 1 \implies h(-4N) \in \{3, 4\}$:** For every suborder $\mathcal{O}_{-4N} \subseteq \mathcal{O}_{-4N/d^2}$, the natural map $\mathrm{Cl}(-4N) \twoheadrightarrow \mathrm{Cl}(-4N/d^2)$ is surjective (Cox, Thm 7.24). Hence if $h(-4N) = g(-4N)$ (exponent dividing $2$), then every quotient also has exponent dividing $2$, forcing $r_{\mathrm{strict}}(N) = 0$. Thus $r_{\mathrm{strict}}(N) = 1$ forces $h(-4N) - g(-4N) = 2$. Since $g(-4N) \mid h(-4N)$, we obtain $g(-4N) \mid 2$, so $(h(-4N), g(-4N)) \in \{(3, 1), (4, 2)\}$.
4. **Finite Exhaustion:**
   - Every imaginary quadratic order $\mathcal{O}_{-4N}$ with $h(-4N) \in \{3, 4\}$ has fundamental discriminant $D_0$ with $h(D_0) \le 4$ (97 fundamental discriminants, $|D_0| \le 1555$ — unconditionally by Arno 1992 / Watkins 2004, or under Dirichlet GRH via Lamzouri–Li–Soundararajan 2015 Thm 1.5). Only **52** integers $N \le 253$ satisfy $h(-4N) \in \{3, 4\}$; exactly **23** have $r_{\mathrm{strict}}(N) = 1$.
   - For `A093670` and `A025052`, any $N$ with $r_{\mathrm{strict}}(N) = 0$ has $\mathrm{Cl}(-4N)$ of exponent dividing $2$ (Euler's idoneal numbers). Under Dirichlet GRH (`DirichletLNonvanishingRightOfHalf` for real quadratic characters $L(s, \chi_D)$), Weinberger (1973, Thm 1) / Kani (2011, Cor 23) proves Euler's list of 65 idoneal numbers (max $1848$) is complete. Checking $r_{\mathrm{all}}(N)$ on the 65 idoneal numbers plus the 23 terms of `A093669` yields the exact 18 terms of `A025052` and 16 terms of `A093670`.

---

## Reproducing & Formal Verification

- **Python verification** (reproduces all 3 OEIS sequences, verifies the bijection up to $N = 2000$, checks all 97 fundamental discriminants $h \le 4$, all 52 order candidates $h(-4N) \in \{3,4\}$, and all 65 Euler idoneal numbers):
  ```bash
  python verify.py
  ```
- **Zero-dependency Lean 4 formalization** ([`A093669.lean`](A093669.lean) — proves the exact bijection $\Phi / \Psi$ and kernel-verifies the complete classifications of `A025052`, `A093669`, and `A093670` from the two finite candidate lists):
  ```bash
  lean A093669.lean
  ```
