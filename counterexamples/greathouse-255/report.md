# Reporting drafts — Greathouse's 255 conjecture

Nothing below has been sent or submitted. `<SIGNER>`, `<NAMES>`, `<DATE>`, `<LINK TO PUBLIC CODE>` are placeholders.

**Update 2026-11-27:** the smallest counterexample is n = 275984581255575 = 3·5²·241·257·59411893 (n ≡ 15 mod 17, 1127 pairs, certificate `data/certificate_275984581255575.txt`); every odd n below 285873023221760 was checked. Lead with this number in anything sent. The drafts below were written for 949806618679575 and must be updated first: replace the number, its factorisation, 13 → 15 (mod 17), 1224 → 1127 pairs, n ≡ 6 mod 7 → n ≡ 2 mod 7, and the last sentence of the email by n = 275984581254517 + 2 + 2^5 + 2^10. The current wording for a public post is in the private repo README.

| Channel | State |
|---|---|
| OEIS A156695 comment | draft below, not submitted |
| Email to Charles R Greathouse IV (author of the entry and of the conjecture) | draft below, not sent |
| Live OEIS page re-read for novelty | not done (one manual page view, see `docs/OEIS_ACCESS.md`) |

## OEIS comment draft (A156695)

> The conjecture that all terms greater than 5 are divisible by 255 is false: 949806618679575 = 3^2 * 5^2 * 241 * 257 * 68155751 is a term and is congruent to 13 (mod 17). For each of the 1224 pairs 1 <= a <= b with 2^a + 2^b < 949806618679575, the number 949806618679575 - 2^a - 2^b is composite (explicit divisors at <LINK TO PUBLIC CODE>). It was found by searching the residue class 0 (mod 3*5*241*257), 6 (mod 7); it is not known to be the smallest such term. It is still the sum of a prime and three positive powers of two: 949806618679561 + 2 + 4 + 8. - _<SIGNER>_, <DATE>

## Email draft

Subject: A term of A156695 not divisible by 255

Dear Dr. Greathouse,

In the comments of OEIS A156695 you conjecture that every term greater than 5 is divisible by 255. We found a term that is not:

    n = 949806618679575 = 3^2 * 5^2 * 241 * 257 * 68155751,   n = 13 (mod 17).

For all 1224 pairs 1 <= a <= b with 2^a + 2^b < n, the number n - 2^a - 2^b is composite. We checked this with PARI's isprime and with sympy, and the attached file lists a proper divisor of each of the 1224 numbers, so the claim can be checked without any primality test.

How we found it: for n = 0 mod 3, 5, 17, 257 the pairs (a, b) removed by each prime are disjoint, which is why multiples of 255 dominate. Replacing 17 by 241 (where 2 has order 24) and adding n = 6 mod 7 gives the class n = 5574330 mod 6503385, which a simple prime-count heuristic ranks best among classes with 17 not dividing n. We scanned every odd n in that class. We have not searched other classes, so we do not claim this is the smallest such term.

The weaker statement in your comment is not affected: n = 949806618679561 + 2 + 4 + 8.

Code and the certificate: <LINK TO PUBLIC CODE>

Best regards,
<NAMES>
