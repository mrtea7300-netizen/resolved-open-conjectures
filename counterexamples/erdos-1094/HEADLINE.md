# Erdős–Lacampagne–Selfridge: what our pairs contradict, exactly

Written 2026-11-26 by the coordinating session (Claude Fable 5.2) after the box-tree search.
The long README below this folder has the method and the full lists; this page pins down the claim.

## The primary source: [ELS93], p. 222

P. Erdős, C. B. Lacampagne, J. L. Selfridge, *Estimates of the least prime factor of a binomial
coefficient*, Math. Comp. 61 (1993), 215–224. Read on 2026-11-26 from screenshots of pages 215–223
of the journal PDF taken by Yotam (the journal site refuses automated fetches). Here `p(m)` is the
least prime factor of `m` and `(N k)` stands for the binomial coefficient C(N, k). From section 2,
"Least prime factors of binomial coefficients", p. 222, word for word:

> "Definition 3. If p((N k)) > N/k, then (N k) is said to be exceptional.
> It would be very interesting if someone could prove our conjecture that the number of
> exceptional (N k) with p > 17 is finite. We wrote a program to find all exceptional (N k) where
> p > 5 and k ≤ 12000. The most unusual exception is for p = 29: p((284 28)) = 29. We have found
> one exception for p = 23: p((474 66)) = 23. There appear to be exactly two exceptions for
> p = 19: (62 6) and (959 56).
> We have two further conjectures:
> 1. The only exceptional (N k) with p > 17 are these four.
> 2. p((N k)) ≤ N/k if N > 17⅛ k.
> Notice that 1. is a bit stronger and implies 2.
> We have found eight exceptional (N k) with p = 17: (241 16), (439 33), (317 56), (482 130),
> (998 256), (998 260), (14273 896), (13277 900), and two near misses: (239 14) and (956 56).
> Our program gave only one output for 331 < k < 625, namely, p((3574 406)) = 13, and no p > 13
> for any k other than those already listed. Thus, at this point in time, it is still possible
> that p((N k)) ≤ max(N/k, 13), with the twelve exceptions listed above."

From the abstract, p. 215: "The conjecture that p ≤ max(N/k, 29) is supported by considerable
numerical evidence." From p. 218 (Case 1, N > k²): "We conjecture [6] that in this case,
p((N k)) ≤ N/k except for (62 6)."

What this means for the statements below:

- **(B) is Conjecture 1 of [ELS93], p. 222**, and **(A) is Conjecture 2** of the same page. Both
  are the three authors' own conjectures. (Guy's book credits (A) to Selfridge, according to
  erdosproblems.com.)
- The conjecture the authors single out as "very interesting" to prove — that the number of
  exceptional coefficients with p > 17 is **finite** — is not contradicted: we find ten in all up
  to 10^36.
- (D) is not a conjecture: "it is still possible that".
- The paper's program was meant to find every exceptional coefficient with p > 5 and k ≤ 12000.
  **Eleven exceptional coefficients with p = 17 and k ≤ 12000 are missing from its list**:
  (23799, 3159), (36824, 3160), (23799, 3168), (56697, 3432), (56698, 3432), (56699, 3432),
  (56699, 3433), (56699, 3434), (56699, 3435), (56779, 3528), (71679, 4401); each recomputed
  here from the exact integer. So the sentence "no p > 13 for any k other than those already
  listed" does not hold for the stated range, as a MathOverflow reader suspected in 2020.
- The pair "(13277 900)" is a misprint **in the paper itself** (C(13277, 900) is divisible by 3);
  the pair meant is (14277, 900), which has least prime factor 17. MathWorld copied it.
- Our counterexamples to Conjecture 1 with n near 57000 have k = 22050 and 22052, outside the
  paper's search range; the ones near 3·10^7 are far outside it.

## The statement, as printed on MathWorld

Fetched 2026-11-26 from `https://mathworld.wolfram.com/BinomialCoefficient.html` (formulas are
images there; the alt texts are given in brackets):

> "Most binomial coefficients [(n; k)] with [n>=2k] have a prime factor [p<=n/k]" "and Lacampagne et
> al. (1993) conjecture that this inequality is true for all [n>17.125k]" ", or more strongly that
> any such binomial coefficient has least prime factor [p<=n/k] or [p<=17]" "with the exceptions
> [(62; 6)], [(959; 56)], [(474; 66)], [(284; 28)] for which [p=19], 19, 23, 29" "(Guy 1994, p. 84)"

and from `https://mathworld.wolfram.com/LeastPrimeFactor.html`:

> "For integers N and k with 2<=k<=N/2, they conjecture that" [lpf(N; k)<=max(N/k,29).]

## The statement, as printed on erdosproblems.com/1094

Transcribed from two screenshots of the page taken by Yotam on 2026-11-26 (the site refuses
automated fetches). They agree word for word with the quotations in this folder's `README.md`.

> "For all n ≥ 2k the least prime factor of C(n,k) is ≤ max(n/k, k), with only finitely many
> exceptions." (#1094: [ELS88][ELS93])
>
> "A stronger form of [384] that appears in a paper of Erdős, Lacampagne, and Selfridge [ELS88].
> Erdős observed that the least prime factor is always ≤ n/k provided n is sufficiently large
> depending on k. Selfridge [Se77] further conjectured that this always happens if n ≥ k² − 1,
> except C(62,6)."
>
> "More precisely, in [ELS88] they conjecture that if n ≥ 2k then the least prime factor of C(n,k)
> is ≤ max(n/k, k) with the following 14 exceptions: …"
>
> "They also suggest the stronger conjecture that, with a finite number of exceptions, the least
> prime factor is ≤ max(n/k, √k), or perhaps even ≤ max(n/k, O(log k)). Indeed, in [ELS93] they
> provide some further computational evidence, and point out it is consistent with what they know
> that in fact this holds with ≤ max(n/k, 13), with only 12 exceptions."
>
> "Discussed in problem B31 and B33 of Guy's collection [Gu04] - there Guy credits Selfridge with
> the conjecture that if n > 17.125k then C(n,k) has a prime factor p ≤ n/k."
>
> "This is related to [1093], in that the only counterexamples to this conjecture can occur from
> C(n,k) with deficiency ≥ 1." "There is an interesting discussion about this problem on
> MathOverflow."

What this settles and what it does not:

- Statement (A) below now has two secondary sources that agree (MathWorld and erdosproblems.com),
  and the second one names its author: **Selfridge, as credited by Guy** — not Erdős, Lacampagne
  and Selfridge jointly, as MathWorld's sentence suggests.
- Statement (D) below (the bound 13 with only 12 exceptions) is a remark, not a formal conjecture:
  "it is consistent with what they know".
- Statement (B) (bound 17 with four exceptions) appears only on MathWorld.
- The screenshots do not show the page's status tag or its comment thread. A web search on
  2026-11-26 returned the page summary "open … cannot be resolved with a finite computation"; that
  is a search engine's summary, not the page.

Guy's book has still not been opened by anyone here; after the section above it is no longer
needed for statements (A), (B), (D).

## What we found

**Formal check (2026-11-27).** Every least prime factor in this section, the failure of
Conjectures 1 and 2 of p. 222, the eleven cases with k ≤ 12000 and the misprint (13277, 900) are
theorems in Lean 4 + Mathlib, checked by the kernel with only the standard axioms: see
[`lean/`](lean/) (`els93_conjecture1_false`, `els93_conjecture2_false`, built in about 15 s). The
proof goes through Lucas' theorem digit by digit, so no binomial coefficient is ever computed.
The "no other pair up to 10^36" statements are not part of the Lean proof; they still rest on the
box-tree search.

lpf = least prime factor of C(n, k).

| Statement | Our result |
|---|---|
| (A) **[ELS93] Conjecture 2, p. 222**: lpf ≤ n/k whenever n > 17⅛·k | **False: C(31152939, 1772289) has lpf 19, and n/k = 17.5778.** It is the only such pair with n ≤ 10^36 and n ≤ 2^20·k. |
| (B) **[ELS93] Conjecture 1, p. 222**: the only coefficients with lpf > n/k and lpf > 17 are (62,6), (959,56), (474,66), (284,28) | **False: six further exceptions**, smallest C(57074, 22050) with lpf 23. The others: (57075, 22050) lpf 23, (57077, 22052) lpf 19, (31152939, 1772289), (32634047, 2143377), (32634223, 2143531), all lpf 19. With the four known ones these ten are all such pairs with n ≤ 10^36 and n ≤ 2^20·k. |
| (C) [ELS93] abstract: lpf ≤ max(n/k, 29) | No counterexample with n ≤ 10^36 and n ≤ 2^20·k. |
| (D) [ELS93] remark, p. 222: "it is still possible that" lpf ≤ max(n/k, 13) with the twelve listed exceptions | **False: 43 further exceptions below 10^7**, the smallest C(23799, 3159) and C(23799, 3168), both lpf 17 with n/k ≈ 7.5; 149,461 exceptions with n ≤ 10^36 and n ≤ 2^20·k. A density heuristic (README) suggests infinitely many. |
| Erdős #1094: lpf ≤ max(n/k, k) with finitely many exceptions | Only the 14 known exceptions in the same region, and for every k ≤ 40 with no bound on n (the latter is a `proof (draft)`, unreviewed). |

Also: a misprint in MathWorld's table of exceptional coefficients, (13277; 900) for (14277; 900).

## How the pairs were checked

- The search program's own digit test; Legendre's formula and Lucas' theorem in a separate script
  (`verify_dfs.py`); exact integers with `gmpy2` and `math.comb` for the pairs below 10^8.
- `coordinator_check.py` in this folder (written separately, Kummer carries cross-checked against
  Legendre valuations for every prime up to the least prime factor): confirms lpf = 19 for the three
  pairs near 3·10^7 and lpf = 23 for (57074, 22050).

"No other pair" statements rest on the box-tree search (`dfs_1094.c`), which was validated against
brute force for n ≤ 60000, against the earlier submask scan to 10^7, and by 5 million randomized
path tests, but has had no outside review.

## Independent review (Gemini 4 Neon, 2026-11-26)

[`reviews/2026-11-26-gemini-4-neon.md`](reviews/2026-11-26-gemini-4-neon.md), with its own programs
in `reviews/`. It was written before the erdosproblems.com screenshots were added above.

- **Arithmetic: confirmed.** All ten pairs recomputed from scratch (Legendre's formula; complete
  prime factorization of the exact integer for the seven pairs with n < 60000; exact residues for
  the three pairs near 3·10^7).
- **Search (C): PASS.** No soundness bug found in `dfs_1094.c`; the run tables cover [4, 10^36]
  with no gap or overlap; five cross-checks with different algorithms agree, including a region
  above 2^64. Caveat: the rows above 10^24 are not committed and the 44-minute wide run was not
  replayed.
- **k ≤ 40 lemma (D): PASS.** All 9,805,182,193 candidates rechecked; exactly the 14 known pairs.
- **Claims (A) and (B): OBJECTIONS**, all about sources and wording, not arithmetic. The primary
  sources are unread; MathWorld has two errors on the neighbouring page; the one post in the
  problem's forum thread is unread.
- **New secondary source for (B) and (D):** an answer by Aaron Meyerowitz on MathOverflow
  (question 368183, August 2020), who read [ELS93]. As quoted in the review (the page refuses
  our fetches, so this is third-hand): the paper conjectures that (62,6), (959,56), (474,66),
  (284,28) are the only cases above both n/k and 17; its program covered **k ≤ 12000**, which is
  why (57074, 22050) was out of reach; and its sentence about 13 is "Thus, at this point in time,
  it is possible that p ≤ max(n/k, 13)". Meyerowitz adds that he knows of no challenge or further
  exception.
- **17.125 = 959/56 exactly**, the ratio of the known exception (959, 56). So statement (A) is
  what statement (B) implies above that ratio, and a counterexample to (A) is automatically one
  to (B).
- **Status of problem 1094:** the public metadata file of the problem site (`teorth/erdosproblems`)
  and DeepMind's `formal-conjectures` both list it as open. The "solved" tag on a third-party
  mirror is probably a mix-up with a formalized trivial case (k = 1).
- **Prior notice:** no mention of any of the six new pairs found on the web, arXiv, GitHub or
  MathOverflow.

## Before anything is said in public

1. Done on 2026-11-26: [ELS93] read (section "The primary source" above). Statements (A) and (B)
   are its Conjectures 2 and 1 as printed. Guy's book is still unread and no longer needed.
2. Done on 2026-11-26, by Yotam in a browser:
   - `https://www.erdosproblems.com/1094` shows no solved label; it lists "Proof expositions (0)",
     "Comments (1)", "Proof claims (0)" (screenshots).
   - MathOverflow question 368183: a search of the page for 57074, 31152939 and 23799 finds none
     of them.
   - The one comment on the erdosproblems.com page (screenshot), in full: "A part of this problem
     has been discussed on MathOverflow. (The site has been updated to address this comment.)" —
     Alfaiz, 18 Oct 2025. It mentions no pair. The page also says "The ability to post new comments
     has been suspended."
   So no earlier notice of the new pairs was found in any place we knew to look. This is a search
   that found nothing, not a proof that nobody has seen them.
3. Prior work looked at on 2026-11-26, neither mentions these pairs: arXiv 2609.25042 (Xu Zhang,
   "Infinitely many binomial coefficients of deficiency one", withdrawn 2026-11-02, only the
   abstract page exists) and the GitHub repository `asdfdev0/jsp-000909-lean` (states that it does
   not address problem 1094).
4. An independent review by Gemini 4 Neon (arithmetic from scratch, sources, search soundness) was
   started on 2026-11-26; its file will be in `reviews/`.
