# A094960 is complete: a prime just above sqrt(n) with digit sum at least p

Status: **proof (reviewed)** — written by Claude (Fable 5.2) on 2026-11-26. Four adversarial
reviews are in `reviews/`: Claude Fable 5.2 (PASS WITH MINOR FIXES) and Gemini 4 Neon three times
(OBJECTIONS, OBJECTIONS, PASS). All objections are applied; the two that mattered concerned the
source of the upper bound (P2) and are described in section 5. No human has reviewed it.
Every step below is proved in the text, cited, or computed by a program in this folder.
Words in capitals (`GAP:`, `UNVERIFIED CITATION:`) mark what a reader must not take on trust;
they are collected in section 8.

Notation. `p` is always a prime unless said otherwise. `s_p(n)` is the sum of the base-`p`
digits of the integer `n >= 0`. `pi(x)` is the number of primes `<= x`. `ln` is the natural
logarithm. `v_p` is the `p`-adic valuation on the rationals. `C(n,k)` is a binomial coefficient.
`B_j` are the Bernoulli numbers (`t/(e^t - 1) = sum B_j t^j / j!`, so `B_1 = -1/2`) and

    B_n(x) = sum_{k=0..n} C(n,k) B_{n-k} x^k                                   (0.1)

are the Bernoulli polynomials (this is formula (2) of [K23]).

## 0. Results

For `j = 0, 1, 2, 3` let `E_j` be the following finite sets (they are the output of the finite
check, section 6):

- `E_0` = {1, 2, 4, 6, 10, 11, 12, 15, 16, 28, 29, 30, 35, 36, 58, 59, 60, 69, 70, 78, 79, 80, 174,
  190, 191, 192} (26 numbers, largest 192);
- `E_1` = {1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 20, 24, 27, 28, 29, 30, 34, 35, 36, 48, 54,
  56, 57, 58, 59, 60, 68, 69, 70, 77, 78, 79, 80, 120, 144, 173, 174, 176, 189, 190, 191, 192, 208,
  390, 414, 1080} (50 numbers, largest 1080);
- `E_2` = {1, ..., 16, 18, 19, 20, 23, 24, 26, 27, 28, 29, 30, 33, 34, 35, 36, 40, 42, 47, 48, 50, 53,
  ..., 60, 64, 66, 67, 68, 69, 70, 76, ..., 80, 90, 108, 119, 120, 143, 144, 154, 172, ..., 176,
  188, ..., 192, 207, 208, 389, 390, 413, 414, 504, 1036, 1079, 1080} (81 numbers, largest 1080;
  the full list is in `data/finite_check_1_1800000000.txt`);
- `E_3` = {1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 15, 16, 23, 24, 28, 29, 30, 35, 36, 47, 48, 58, 59, 60,
  69, 70, 78, 79, 80, 119, 120, 174, 190, 191, 192} (35 numbers, largest 192).

**Theorem 1.** Let `n >= 1` be an integer.

- (a) If `n` is not in `E_0` (in particular if `n >= 193`), there is a prime `p > sqrt(n)` with
  `s_p(n) >= p`.
- (b) If `n` is not in `E_1` (in particular if `n >= 1081`), there is a prime `p > sqrt(n)` with
  `s_p(n) >= p` and `p` not dividing `n + 1`.
- (c) If `n` is not in `E_2` (in particular if `n >= 1081`), there is a prime `p > sqrt(n)` with
  `s_p(n) >= p` and `p` not dividing `(n + 1)(n + 2)`.
- (d) If `n` is not in `E_3` (in particular if `n >= 193`), there is a prime `p` with
  `s_p(n) >= p` and `p > (n + 1)/sqrt(n)`.

For `n` in `E_j` no such prime exists (this is part of the computation, not needed below).

**Corollary A (A094960; [K23] Conjecture 1(ii)).** The derivative `B_k'(x)` has only integer
coefficients if and only if `k` is one of 1, 2, 4, 6, 10, 12, 28, 30, 36, 60.

**Corollary B ([K17] Conjecture 1; [K23] Conjecture 2(i)).** For every `n > 192` the greatest
prime `P` with `s_P(n) >= P` satisfies `P > sqrt(n)` and `(n + 1)/P < sqrt(n)`. The bound 192 is
best possible (192 is in `E_0`).

**Corollary C (Alekseyev's conjecture in A094960).** For every integer `k > 78` there is a prime
`p >= 3` such that the sum of the last two base-`p` digits of `k` is at least `p`.

**Corollary D (A366169; first half of [K23] Conjecture 15).** `B_k''(x)` has only integer
coefficients if and only if `k` is one of the 29 terms 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15,
16, 21, 25, 28, 29, 30, 31, 36, 37, 55, 57, 60, 61, 70, 121, 190.

**Corollary E (second half of [K23] Conjecture 15).** `B_k'''(x)` has only integer coefficients if
and only if `k` is in Kellner's set `S_3` = {1-18, 20-22, 25, 26, 28-32, 35-38, 42, 50, 52, 55-58,
60-62, 66, 70-72, 78, 80, 92, 110, 121, 122, 156, 176, 177, 190, 191, 210, 392}.

**Corollary F (A195441 comment; [K23] Conjecture 11).** For `n >= 1`,
`denominator(B_n(x) - B_n) = rad(n + 1)` if and only if `n` is in {3, 5, 8, 9, 11, 27, 29, 35, 59}.

The numbering of [K23] is the same in arXiv:2310.01325v2 and in the journal version (see
section 7).

Outline. Section 1 turns "there is a prime with `s_p >= p`" into "a coefficient is not an
integer" (Lucas and von Staudt–Clausen; this replaces any use of the product formulas of Kellner
and Sondow). Sections 2–4 show by elementary algebra that among the primes `p = F + s` just above
`F = floor(sqrt(n))` only few can fail `s_p(n) >= p`: at most one per value of
`c = floor((s^2 + n - F^2)/p)`. Section 5 counts primes with explicit bounds for `pi(x)` and
gives the threshold `F >= 60184`. Section 6 is the finite check of all `n < 60184^2`.

## 1. From a digit condition to a non-integral coefficient

**Fact 1.1 (derivatives).** For `n >= 1`, `B_n'(x) = n B_{n-1}(x)`; hence for `n >= i >= 1` the
`i`-th derivative is `B_n^{(i)}(x) = n(n-1)...(n-i+1) B_{n-i}(x)`.

Proof. Differentiate (0.1) term by term and use `k C(n,k) = n C(n-1,k-1)`:
`B_n'(x) = sum_{k=1..n} n C(n-1,k-1) B_{(n-1)-(k-1)} x^{k-1} = n B_{n-1}(x)`. Induct on `i`. ∎

**Fact 1.2 (Lucas).** Let `p` be prime and let `m = sum m_i p^i`, `j = sum j_i p^i` be base-`p`
expansions (`0 <= m_i, j_i <= p-1`). Then `C(m,j) ≡ prod_i C(m_i, j_i) (mod p)`.

Proof. In `F_p[x]`, `(1+x)^p = 1 + x^p`, so `(1+x)^{p^i} = 1 + x^{p^i}` and
`(1+x)^m = prod_i (1 + x^{p^i})^{m_i}`. The coefficient of `x^j` on the left is `C(m,j)`. On the
right, by uniqueness of the base-`p` expansion of `j` (each factor contributes an exponent
`t_i p^i` with `0 <= t_i <= m_i <= p-1`), it is `prod_i C(m_i, j_i)`. ∎

**Fact 1.3 (von Staudt–Clausen; cited).** For every even `j >= 2`, `B_j + sum_{(q-1) | j} 1/q` is
an integer, the sum being over the primes `q` with `(q-1) | j`. This is the theorem as stated in
[K23], section 2 (with references to Clausen 1840 and von Staudt 1840); it is in every textbook
on Bernoulli numbers. Consequence: if `p` is prime, `j >= 2` is even and `(p-1) | j`, then
`v_p(B_j) = -1`. (Indeed `B_j = N - 1/p - sum_{q != p} 1/q` with `N` an integer, and every term
except `1/p` has `v_p >= 0`.)

**Lemma 1.** Let `p >= 3` be prime and `m >= 1`. Let `a, b` be the last two base-`p` digits of
`m`, that is `m = M p^2 + a p + b` with `M >= 0` and `0 <= a, b <= p-1`. Assume `a + b >= p` and
put `j = (a+1)(p-1)`. Then `j` is even, `4 <= j <= m-1`, and

- (i) `v_p( C(m,j) B_j ) = -1`. So the coefficient of `x^{m-j}` in `B_m(x) - B_m` has `p` in its
  denominator, and `p` divides `denominator(B_m(x) - B_m)`.
- (ii) `v_p( C(m-1,j) B_j ) = -1`. So for every `i >= 1` such that `p` does not divide
  `m(m+1)...(m+i-1)`, the `i`-th derivative of `B_{m+i-1}(x)` has a coefficient that is not an
  integer.

Proof. From `a + b >= p` and `a, b <= p-1` we get `a >= 1` and `b >= 1`. Since `p - 1` is even
and `a + 1 >= 2`, `j` is even and `j >= 2(p-1) >= 4`. Write `j = a p + (p-1-a)`; as
`0 <= p-1-a <= p-2` and `1 <= a <= p-1`, the base-`p` digits of `j` are `(a, p-1-a)` and all
higher digits are 0. Also `m - 1 - j >= (a p + b) - 1 - a p - (p-1-a) = a + b - p >= 0`, so
`j <= m-1`.

The digits of `m` are `(..., a, b)` and those of `m - 1` are `(..., a, b-1)` (no borrow because
`b >= 1`). By Fact 1.2, the higher digits of `j` being 0,

    C(m, j)   ≡ C(a,a) C(b,   p-1-a) = C(b,   p-1-a)   (mod p),
    C(m-1, j) ≡ C(a,a) C(b-1, p-1-a) = C(b-1, p-1-a)   (mod p).

Here `0 <= p-1-a <= b-1 <= b <= p-1` (because `a + b >= p`), so both right-hand sides are binomial
coefficients `C(u,w)` with `0 <= w <= u <= p-1`; they divide `u!`, which is prime to `p`, so they
are not divisible by `p`. Hence `v_p(C(m,j)) = v_p(C(m-1,j)) = 0`. By Fact 1.3, `v_p(B_j) = -1`
(`j` even, `j >= 2`, `(p-1) | j`). This gives the two valuations.

(i) By (0.1) the coefficient of `x^{m-j}` in `B_m(x)` is `C(m, m-j) B_j = C(m,j) B_j`, and
`m - j >= 1`, so it is a coefficient of `B_m(x) - B_m`.

(ii) By Fact 1.1 with `n = m+i-1`, `B_{m+i-1}^{(i)}(x) = (m+i-1)(m+i-2)...m · B_{m-1}(x)`. The
coefficient of `x^{m-1-j}` in `B_{m-1}(x)` is `C(m-1,j) B_j` (and `m-1-j >= 0`). The integer
factor is prime to `p` by hypothesis, so this coefficient of the derivative has `v_p = -1`. ∎

Remarks. (1) For `i = 1` the hypothesis "`p` does not divide `m`" is automatic (`b >= 1`).
(2) If `p > sqrt(m)` then `m < p^2`, so `M = 0` and `a + b = s_p(m)`: the hypothesis of Lemma 1
is exactly `s_p(m) >= p`. (3) Lemma 1 is the "easy half" of the product formulas
`denominator(B_n(x) - B_n) = prod_{s_p(n) >= p} p` ([K23] formula (8), from [K17], [KS17]) and
`denominator(B_n^{(k)}(x)) = prod_{p ∤ n(n-1)...(n-k+1), s_p(n-k+1) >= p} p` ([K23] Theorem 13).
Those formulas are **not used** in this proof. `check_bernoulli.py` confirms them, and Lemma 1,
against actual polynomials for all indices up to 1100 (Lemma 1: all `m <= 300`).

## 2. The two digits of n in a base just above sqrt(n)

Throughout sections 2–4, `n >= 1` is an integer, `F = floor(sqrt(n))` and `e = n - F^2`, so
`F >= 1` and `0 <= e <= 2F` (because `F^2 <= n < (F+1)^2`). For an integer `s >= 1` put

    p = F + s   (NOT assumed prime in this section),
    c = c(s) = floor( (s^2 + e) / p ),   b = b(s) = s^2 + e - c p,   a = a(s) = F - s + c.

Note that an integer `p` satisfies `p > sqrt(n)` if and only if `p >= F + 1`.

**Lemma 2.** For every `s >= 1`: `n = a p + b`, `0 <= b <= p-1` and `0 <= a <= p-1`. Hence
`a = floor(n/p)` and `b = n mod p`; if `p` is prime, `(a, b)` are the base-`p` digits of `n`
and `s_p(n) = a + b`. Moreover

    a + b >= p   if and only if   b >= 2s - c.                                  (2.1)

Proof. `(F+s)(F-s) = F^2 - s^2`, so `n = F^2 + e = p(F-s) + s^2 + e = p(F-s+c) + b = a p + b`.
`0 <= b <= p-1` by the definition of `c` as a floor. So `a = floor(n/p) >= 0`, and
`n < (F+1)^2 <= p^2` gives `a <= p-1`. Finally `a + b - p = (F - s + c) + b - (F + s) = b - (2s - c)`. ∎

Call `s` **failing** (for `n`) if `a + b < p`, i.e. by (2.1) and `b >= 0`, if

    0 <= s^2 + e - c(F + s) <= 2s - c - 1,   where c = c(s).                    (2.2)

**Lemma 3.** If `s_1 < s_2` are both failing and `c(s_1) = c(s_2)`, then `s_2 = s_1 + 1`.

Proof. Let `c` be the common value, `f(s) = s^2 + e - c(F+s)` and `d = s_2 - s_1 >= 1`. By (2.2),
`f(s_1) >= 0`, `f(s_2) <= 2 s_2 - c - 1`, and `2 s_1 - c - 1 >= f(s_1) >= 0`, i.e.

    c <= 2 s_1 - 1.                                                              (3.1)

Now `f(s_2) - f(s_1) = (s_2^2 - s_1^2) - c(s_2 - s_1) = d (s_1 + s_2 - c)`, so

    d (s_1 + s_2 - c) <= f(s_2) <= 2 s_2 - c - 1.

Put `W = 2 s_2 - c`; then `s_1 + s_2 - c = W - d` and the inequality reads `d(W - d) <= W - 1`,
i.e. `(d - 1) W <= d^2 - 1 = (d-1)(d+1)`. If `d >= 2` this gives `W <= d + 1`, that is
`2 s_2 - c <= s_2 - s_1 + 1`, i.e. `s_1 + s_2 <= c + 1 <= 2 s_1` by (3.1), i.e. `s_2 <= s_1`:
a contradiction. Hence `d = 1`. ∎

**Lemma 4.** Let `F >= 2` and let `S >= 1` be an integer. Put

    K(F,S) = floor( (S^2 + 2F) / (F + S) ).

(The letter `K` is used to avoid a clash with the binomial coefficients `C(n,k)`.) Then the number
of primes `p` with `F < p <= F + S` and `s_p(n) < p` is at most `K(F,S) + 1`.

Proof. (1) For `1 <= s <= S` we have `0 <= c(s) <= K(F,S)`. Indeed `c(s) >= 0`, and
`c(s) <= (s^2 + e)/(F+s) <= h(s)` with `h(s) = (s^2 + 2F)/(F+s)`. The function `h` is increasing
on the positive integers: the numerator of `h(s+1) - h(s)` is

    ((s+1)^2 + 2F)(F+s) - (s^2 + 2F)(F+s+1) = (2s+1)(F+s) - (s^2 + 2F) = s^2 + 2sF + s - F > 0

for `s >= 1`. So `c(s) <= h(S)`, and `c(s)` is an integer, so `c(s) <= floor(h(S)) = K(F,S)`.

(2) Each value of `c` is taken by at most one failing `s` with `F + s` prime. Indeed two such
`s_1 < s_2` would satisfy `s_2 = s_1 + 1` by Lemma 3, so `F + s_1 >= 3` and `F + s_1 + 1` would be
consecutive integers that are both prime, which is impossible.

(3) By Lemma 2, a prime `p = F + s` in `(F, F+S]` has `s_p(n) < p` exactly when `s` is failing.
By (1) and (2) there are at most `K(F,S) + 1` such primes. ∎

## 3. Primes that must be avoided for other reasons

**Lemma 5.** Let `F >= 1` and `F^2 <= n <= F^2 + 2F`.

- (i) For `u` in {1, 2}, at most one prime `p > F` divides `n + u`.
- (ii) Every integer `p >= F + 2` satisfies `p > (n+1)/sqrt(n)`.

Proof. (i) Two distinct primes `p < q`, both `> F`, dividing `n + u` would give
`n + u >= p q >= (F+1)(F+2) = F^2 + 3F + 2 > F^2 + 2F + 2 >= n + u`. (ii) Let `x = sqrt(n)`, so
`F <= x < F + 1`. The claim `p x > x^2 + 1` follows from `q(x) = -x^2 + (F+2)x - 1 > 0`. As `q` is
concave, `q(F) = 2F - 1 > 0` and `q(F+1) = F > 0`, we have `q > 0` on `[F, F+1]`. ∎

**Proposition 6.** Let `F >= 2`, let `S >= 1` and `r >= 0` be integers, and suppose

    pi(F + S) - pi(F) >= K(F,S) + 2 + r.                                        (6.1)

Then for every `n` with `floor(sqrt(n)) = F` and every set `X` of at most `r` primes, there is a
prime `p` with `F < p <= F + S`, `p` not in `X`, and `s_p(n) >= p`.

Proof. The interval `(F, F+S]` contains at least `K(F,S) + 2 + r` primes, at most `K(F,S) + 1` of
them have `s_p(n) < p` (Lemma 4), and at most `r` are in `X`. ∎

## 4. What is needed from the primes

By Proposition 6 and Lemma 5, Theorem 1 holds for all `n` with `floor(sqrt(n)) = F` as soon as
(6.1) holds for this `F`, some `S`, and `r = 2`:

- (a): `X` empty;
- (b), (c): `X` = the primes `> F` dividing `(n+1)(n+2)`, at most 2 by Lemma 5(i);
- (d): `X = {F + 1}`; the prime found is `>= F + 2`, hence `> (n+1)/sqrt(n)` by Lemma 5(ii).

(With `S = floor(sqrt(F))` one has `K(F,S) <= 2`, so "4 primes in `(F, F + sqrt(F)]`" would do for
(a); that is a Legendre-type statement which is not known. A longer window is needed.)

## 5. Counting primes: (6.1) holds for every F >= 60184

**Cited inequalities.**

- (P1) `pi(x) >= x/(ln x - 1)` for `x >= 5393`.
- (P2) `pi(x) <= x/(ln x - 1.107)` for `x >= 60184`.

**Proof of (P1)** (a refereed theorem plus a finite computation).

- For `x >= 468049`: C. Axler, *New bounds for the prime counting function*, Integers 16 (2016),
  #A22 (arXiv:1409.1780), Corollary 3.5, last column of the table (`a = b = c = d = 0`,
  `x_0 = 468049`): "If `x >= x_0`, then `pi(x) > x/(log x - 1 - 1/log x - a/log^2 x - b/log^3 x -
  c/log^4 x - d/log^5 x)`", i.e. `pi(x) > x/(ln x - 1 - 1/ln x)` for `x >= 468049`. Since
  `0 < ln x - 1 - 1/ln x < ln x - 1` there, this implies (P1). (Opened: the arXiv TeX source, where
  the table is unambiguous, and the journal PDF. Axler's later paper, Integers 18 (2018) #A61,
  p. 2, restates it as its inequality (1.7), "for every `x >= 468 049`", citing
  "[2, Corollary 3.5]".)
- For `5393 <= x < 468049`: computation. `threshold_test.py`, step (b0), sieves the primes and
  checks `pi(m) >= (m+1)/(ln(m+1) - 1)` for every integer `m` with `5393 <= m <= 468048`. This
  gives `pi(x) >= x/(ln x - 1)` for every real `x` in `[m, m+1)`, because `pi` is constant on
  `[m, m+1)` and `x/(ln x - 1)` is increasing for `x > e^2` (derivative
  `(ln x - 2)/(ln x - 1)^2`). Result: true for all these `m`; the smallest margin is 0.0411, at `m = 5398`
  (double precision, rounding error below `10^-9`). The referee's independent sieve
  (`reviews/2026-11-26-claude-fable-5-2/axler_lb.py`, `ref_threshold.py`) confirms it.

**Proof of (P2)** (a refereed theorem plus a finite computation; rewritten twice on 2026-11-26,
see the corrections below).

- For `x >= 468049`: C. Axler, *New estimates for some functions defined over primes*, Integers 18
  (2018), #A52, Theorem 2 (inequality (1.12), p. 4 of the journal PDF): "For every `x >= 49`, we
  have `pi(x) < x/(log x - 1 - 1/log x - 3.15/log^2 x - 12.85/log^3 x - 71.3/log^4 x - 463.2275/log^5 x - 4585/log^6 x)`". For `x >= 468049` we have `ln x >= 13.0563 > 13`, so the six correction
  terms add up to at most `1/13 + 3.15/13^2 + 12.85/13^3 + 71.3/13^4 + 463.2275/13^5 + 4585/13^6
  = 204859303/1930723600 = 0.1061049... < 0.107`. Hence the denominator is at least
  `ln x - 1.107 > 0`, which gives (P2). (This deduction is `axlerUpper_of_thm2` in
  `lean/Kellner/Cited.lean`.)
- For `60184 <= x < 468049`: computation. `threshold_test.py`, step (b), sieves the primes and
  checks `pi(m) <= m/(ln m - 1.107)` for every integer `m` from 60184 to 21000010. This gives
  (P2) for every real `x` in `[m, m+1)`, because `pi` is constant there and `x/(ln x - 1.107)` is
  increasing for `x > e^2.107`. Result: true for all these `m`. The Lean formalization does not
  need this range at all: it covers every `F < 468049` by the kernel computation.

**Correction (2026-11-26).** Earlier versions of this draft took (P2) from the last statement of
Axler's Corollary 3.4: "If `x >= 5.43`, then `pi(x) < x/(log x - 1 - 1.17/log x)`". That statement
is **false as printed**: for example `pi(59753) = 6041 > 6040.79`, and it fails at `x = 10^8` by
145 and at `x = 10^9` by 440 (recomputed with `sympy.primepi`). Axler's corrigendum (dated
January 18, 2018, linked beside the paper on the journal's volume page) replaces `5.43` by
`2634800823`. The error was found by the Gemini 4 Neon review
(`reviews/2026-11-26-gemini-4-neon-axler-match.md`); the first review and the author had both
read the corollary in the paper and missed the corrigendum. (P2) itself is unaffected: it is
weaker than the false statement only above `x = 60184`, and it is true on the whole range tested.

**Second correction (2026-11-26).** For a few hours this draft then took (P2) from Theorem 1.3 of
the same 2016 paper ("If `x >= e^3.804`, then `pi(x) < x/(log x - 1 - 1/log x - 3.35/log^2 x -
12.65/log^3 x - 71.7/log^4 x - 466.1275/log^5 x - 3489.8225/log^6 x)`"), and said that its proof
was complete. That was wrong about the proof. Axler writes in the 2018 paper (#A52, Remark, p. 9):
"In [2, Theorem 1.3], the present author claimed that the inequality (3.6) held for every
`x >= e^3.804`. Fortunately, this is really the case. However, there was a mistake in the first
part of the proof, where it was claimed that the inequality (3.6) was valid for every
`x >= 10^14`. In the current paper, we filled the gap by proving Theorem 2." So the statement of
Theorem 1.3 stands, but the proof to rely on is that of Theorem 2 of the 2018 paper, which is
what is cited above. Found by the second Gemini 4 Neon review
(`reviews/2026-11-26-gemini-4-neon-rereview.md`); the Remark and Theorem 2 were then read in the
journal PDF by the author of this correction. The journal's volume page lists no corrigendum
beside #A52 (looked at on 2026-11-26).

**What Theorem 2 of the 2018 paper itself rests on** (from the third Gemini review,
`reviews/2026-11-26-gemini-4-neon-review3.md`, and Axler's 2024 paper, read in the journal PDF).
For large `x` its proof uses explicit estimates for Chebyshev's function taken from Dusart's 2018
paper. C. Axler, *Effective estimates for some functions defined over primes*, Integers 24 (2024),
#A34, p. 6–7, reports: "Broadbent et al. [12, p. 2299] pointed out that the main theorem of [59]
is incorrect and thus bounds claimed in [30] are likely affected", and then recovers them from
later work: "Proposition 2. The explicit values for ε given in [30, Table 1] are correct." and
"Proposition 3. The inequalities (25)–(28) for Chebyshev's ϑ-function are correct." The same
paper proves a sharper upper bound of the same shape: "Theorem 2. Let a5 = 461.364417856444 and
a6 = 4331.1. Then for every `x >= 48`, we have `pi(x) < x/(log x - 1 - 1/log x - 3.024334/log^2 x
- 12.975666/log^3 x - 71.048668/log^4 x - a5/log^5 x - a6/log^6 x)`." Its six correction terms
are smaller than those of the 2018 theorem whenever `log x > 1` (the difference is
`0.125666/L^2 - 0.125666/L^3 + 0.251332/L^4 + 1.863082143556/L^5 + 253.9/L^6 > 0` for `L > 1`),
so the 2024 theorem implies the 2018 one for `x >= 49`, and directly gives (P2) for
`x >= 468049` (tail at `ln x = 13`: `0.10535... < 0.107`). So (P2) has a published proof that
does not pass through the theorem found incorrect. For the lower bound (P1), Corollary 3.5 of the
2016 paper follows from its Theorem 1.4 above 1332479531 and from a computer check below; the
third review repeated that computer check on the whole range with no failure and reports that
the 2024 paper (Theorem 4) covers the range above. Nobody here has audited those proofs line by
line.

Historical source for both. P. Dusart, *Estimates of some functions over primes without R.H.*,
arXiv:1002.0442v1 (2010, an unrefereed preprint), Theorem 6.9, second displayed line, reads (TeX
source): "`x/(ln x - 1) <= pi(x) <= x/(ln x - 1.1)`", the left inequality for `x >= 5 393` and the
right one for `x >= 60 184`. This contains (P1) and implies (P2) (`ln x - 1.107 < ln x - 1.1`).
It is where the threshold 60184 comes from, but the proof no longer depends on it. See section 8.

**Proposition 7.** Let `F >= 60184` be an integer, `L = ln F` and `S = floor(F/(2L))`. Then
`pi(F + S) - pi(F) >= K(F,S) + 4`, i.e. (6.1) holds with `r = 2`.

Proof. Put `t = S/F`. Numerical facts used (recomputed by `threshold_test.py`, part (a)):
`L >= ln 60184 = 11.00516... > 11.005`.

*Size of t.* `F/(2L) - 1 < S <= F/(2L)`, so

    1/(2L) - 1/F < t <= 1/(2L) < 0.05,    and S >= 1.                           (7.1)

(`S >= 1` because `F/(2L) > 2` for `F >= 60184`: the function `x/ln x` is increasing for `x > e`
and `60184/(2 · 11.01) > 2733`.)

*Lower bound for pi(F+S).* `F + S >= 5393`, so by (P1), `pi(F+S) >= (F+S)/(ln(F+S) - 1)`. Since
`ln(F+S) = L + ln(1+t) <= L + t` and `ln(F+S) - 1 > 0`,

    pi(F + S) >= F (1 + t) / (L + t - 1).

*Upper bound for pi(F).* By (P2), `pi(F) <= F/(L - 1.107)`.

*Difference.* Both denominators are positive, so

    pi(F+S) - pi(F) >= F · [ (1+t)(L - 1.107) - (L + t - 1) ] / D = F · N / D,

where `D = (L + t - 1)(L - 1.107)` and, expanding,
`N = (L - 1.107 + tL - 1.107 t) - (L + t - 1) = t (L - 2.107) - 0.107`.

By (7.1) and `L - 2.107 > 0`:

    N > (L - 2.107)(1/(2L) - 1/F) - 0.107 = 0.393 - 1.0535/L - (L - 2.107)/F.

Here `1.0535/L <= 1.0535/11.005 < 0.09573`, and `(L - 2.107)/F < (ln F)/F <= (ln 60184)/60184
< 0.00019` (the function `(ln x)/x` is decreasing for `x > e`). Hence

    N > 0.393 - 0.09573 - 0.00019 > 0.297.

By (7.1), `0 < L + t - 1 < L - 0.95 < L` and `0 < L - 1.107 < L`, so `0 < D < L^2`. Therefore

    pi(F + S) - pi(F) > 0.297 · F / L^2.                                        (7.2)

*Upper bound for K(F,S).* `K(F,S) <= (S^2 + 2F)/(F+S) <= S^2/F + 2 = t^2 F + 2 <= F/(4 L^2) + 2`
by (7.1).

*Conclusion.* It suffices that `0.297 F/L^2 >= F/(4L^2) + 6`, i.e. `0.047 · F/(ln F)^2 >= 6`.
The function `x/(ln x)^2` is increasing for `x > e^2` (its derivative is `(ln x - 2)/(ln x)^3`),
and `60184/(ln 60184)^2 > 496`. So `0.047 · F/(ln F)^2 > 23.3 >= 6`. Together with (7.2),
`pi(F+S) - pi(F) > K(F,S) + 4`. ∎

(The margin is large: at `F = 60184` the interval `(F, F+2734]` contains 234 primes while
`K + 4 = 124`. `threshold_test.py` compares the actual counts, the bound (7.2) and `K + 4` for
every `F` from 60184 to `2·10^7`; with this choice of `S` the last `F` for which (6.1) with
`r = 2` fails is 1753.)

**Corollary 8.** Theorem 1 holds for every `n >= 60184^2 = 3 622 113 856`, with a prime `p` in
`(F, F + F/(2 ln F)]`, `F = floor(sqrt(n))`. (No such `n` is in any `E_j`.)

Proof. `n >= 60184^2` gives `F >= 60184`. Apply Proposition 7 and section 4. ∎

## 6. The finite check: 1 <= n < 60184^2

**Proposition 9 (computation).** For every integer `n` with `1 <= n < 3 622 113 856` and each
`j` in {0, 1, 2, 3}: if `n` is not in `E_j`, there is a prime `p` with
`sqrt(n) < p <= min(n, 400000)`, `s_p(n) >= p`, and

- `j = 1`: `p` does not divide `n + 1`;
- `j = 2`: `p` does not divide `(n + 1)(n + 2)`;
- `j = 3`: `p^2 n > (n + 1)^2`.

For `n` in `E_j` there is no prime `p > sqrt(n)` at all with these properties.

How it was checked. `finite_check.c` loops over all `n`. For each `n` it runs through the primes
`p > floor(sqrt(n))` in increasing order (sieved up to 400000), computes `s_p(n)` by repeated
division — it does not use section 2 — and tests the four conditions with exact integer
arithmetic (128-bit for `j = 3`). An `n` is reported as an *exception* only when `n <= 400000`
and every prime `p <= n` has been tried (for `p > n`, `s_p(n) = n < p`); an `n > 400000` without
witness would be printed as `UNRESOLVED`, and none was.

- Run on 2026-11-26: ranges `[1, 1800000000)` and `[1800000000, 3622113856)`, 22 s each, one core
  each of an AMD Ryzen 5 7600X, gcc 13.3.0 under WSL2 (`run_finite_check.sh`). Outputs:
  `data/finite_check_1_1800000000.txt`, `data/finite_check_1800000000_3622113856.txt`.
- Result: 0 unresolved; exceptions exactly `E_0`, `E_1`, `E_2`, `E_3` (26, 50, 81, 35 numbers;
  largest 192, 1080, 1080, 192).
- Hardest cases: the witness is the first prime above `sqrt(n)` for 99.95 % of all `n`, and never
  later than the 3rd for `n > 1.8·10^9`. The largest offset `p - floor(sqrt(n))` of the smallest
  witness is 117 for `j = 0` (at `n = 1037`, `p = 149`) and 141 for `j = 1, 2`; above
  `n = 1.8·10^9` it is 100 (`n = 3456203588`, `p = 58889`, the second prime above `sqrt(n)`).
- Independent re-implementations. (i) `verify_small.py` (Python, different code) reproduces for
  `n <= 2 000 000` the same exceptions, the same largest offsets and the same checksums (sum of
  the witness primes) as the C program. (ii) On the **full range**, the referee's program
  `reviews/2026-11-26-claude-fable-5-2/ref_finite.c` (differently structured: outer loop over
  `F`, the two digits for the first prime carried incrementally, division-based digit sums for
  later primes, no 128-bit arithmetic) gives, on both ranges, the identical exception lines
  (I re-ran `diff` on the sorted `exception` lines of `data/finite_check_*.txt` and
  `reviews/.../ref_*.txt`: no difference) and the identical checksums for all four conditions:

  | range | j=0 | j=1 | j=2 | j=3 |
  |---|---|---|---|---|
  | `[1, 1800000000)` | 50926156701070 | 50926157487247 | 50926158279836 | 50926156799096 |
  | `[1800000000, 3622113856)` | 94432704322324 | 94432704688022 | 94432705056210 | 94432704362856 |

  The checksum is the sum over all `n` of the smallest witness prime, so the two programs agree
  on (essentially) every witness, not only on the exceptions.
- Beyond what the proof needs: `ref_finite.c` was also run by the referee on
  `60184^2 <= n < 678408^2 = 460 237 414 464` (`reviews/.../ref_ext_a.txt`, `ref_ext_b.txt`):
  0 exceptions and 0 unresolved for all four conditions, the 3rd prime above `sqrt(n)` always
  suffices, largest offset 138. Only that one program has covered this extra range; the proof
  does not use it.

**Proof of Theorem 1.** For `n >= 60184^2`: Corollary 8. For `n < 60184^2`: Proposition 9; in case
(d) note that `p^2 n > (n+1)^2` is `p > (n+1)/sqrt(n)`. The "in particular" clauses hold because
the largest elements of `E_0, E_1, E_2, E_3` are 192, 1080, 1080, 192. ∎

## 7. The corollaries

Small indices are decided by `check_bernoulli.py`, which builds `B_k(x)` for `1 <= k <= 1100`
from (0.1) in exact rational arithmetic, differentiates, and finds: `B_k'` integral exactly for
the 10 values of Corollary A; `B_k''` integral exactly for the 29 values of Corollary D; `B_k'''`
integral exactly for the 59 values of Corollary E; `denominator(B_n(x) - B_n) = rad(n+1)` exactly
for the 9 values of Corollary F (`1 <= n <= 1100`). The same script reproduces the data sections
of A094960, A195441, A324370, A366168, A366169.

**Proof of Corollary A.** Let `k >= 193`. By Theorem 1(a) there is a prime `p > sqrt(k)` with
`s_p(k) >= p`; then `p >= 14`, so `p >= 3`, and `k < p^2`, so the last two digits `a, b` of `k`
are all its digits and `a + b >= p`. Lemma 1(ii) with `m = k`, `i = 1` (`p` does not divide `k`
because `b >= 1`) shows that `B_k'(x)` has a non-integral coefficient. For `k <= 192` the
computation above applies. ∎

(Alternatively: Theorem 1(a) is [K23] Conjecture 2(i), and [K23] Theorem 3 states that
Conjecture 2(i) implies Conjecture 1(ii).)

**Proof of Corollary B.** In [K17] (before Conjecture 1), `p_n` (written with a fraktur p) is the
product of the primes `p` with `s_p(n) >= p`, `P(p_n)` is its greatest prime factor and
`lambda*_n = (n+1)/P(p_n)`; Conjecture 1 of [K17] reads "`P(p_n) > sqrt(n)`,
`lambda*_n < sqrt(n)` (`n > 192`)". [K23] Conjecture 2(i) reads "`D^+_n > 1` for `n > 192`",
where `D^+_n` is the product of the primes `p > sqrt(n)` with `s_p(n) >= p`. For `n >= 193`,
Theorem 1(d) gives a prime `p` with `s_p(n) >= p` and `p > (n+1)/sqrt(n) > sqrt(n)`; the greatest
such prime `P` is `>= p`. So `P > sqrt(n)`, `D^+_n > 1` and `(n+1)/P < sqrt(n)`. ∎

**Proof of Corollary C.** For `k >= 193` take the prime of Theorem 1(a): `p >= 3`, `k < p^2`, and
the last two digits sum to `s_p(k) >= p`. For `79 <= k <= 192`, `verify_small.py` finds such a
prime directly (its last line lists the `k <= 1000` without one: 1, 2, 3, 4, 6, 10, 11, 12, 15, 28,
29, 30, 36, 58, 60, 78). ∎

**Proof of Corollary D.** Let `k >= 1082` and `m = k - 1 >= 1081`. By Theorem 1(b) there is a
prime `p > sqrt(m)` with `s_p(m) >= p` and `p` not dividing `m + 1`; as before `p >= 3`, the two
digits of `m` satisfy `a + b >= p`, and `p` does not divide `m`. Lemma 1(ii) with `i = 2` shows
that `B_{m+1}''(x) = B_k''(x)` is not integral. For `k <= 1081` the computation applies. ∎

**Proof of Corollary E.** Let `k >= 1083` and `m = k - 2 >= 1081`. Theorem 1(c) gives `p` with
`p` not dividing `m(m+1)(m+2)`; Lemma 1(ii) with `i = 3` shows that `B_{m+2}'''(x) = B_k'''(x)` is
not integral. For `k <= 1082` the computation applies. ∎

**Proof of Corollary F.** Let `n >= 1081`. Theorem 1(b) gives a prime `p > sqrt(n)`, `p >= 3`,
with `a + b = s_p(n) >= p` and `p` not dividing `n + 1`. By Lemma 1(i), `p` divides
`denominator(B_n(x) - B_n)`, and `p` does not divide `rad(n+1)`; so the two numbers differ. For
`n <= 1080` the computation applies. ∎

What the statements are, in the sources (all opened). The numbering of [K23] was read from the
arXiv v2 HTML rendering and from the J. Integer Seq. PDF (Article 24.2.8, opened 2026-11-26): the
two agree — Conjectures 1, 2, Theorem 3, Corollary 4, Theorem 5, Remark 6, Theorem 7, Corollary 8,
Theorems 9, 10, Conjecture 11, Theorems 12, 13, 14, Conjecture 15, Lemmas 16–18; formulas (2) and
(8) are as quoted in section 1.

- [K23] Conjecture 1: "(i) The set S-bar is finite. (ii) We have S-bar = S", with
  `S = {1, 2, 4, 6, 10, 12, 28, 30, 36, 60}` and `S-bar = {n >= 1 : B_n'(x) in Z[x]}`.
- [K23] Conjecture 2 (= [K17] Conjectures 1, 2): "(i) We have `D^+_n > 1`, respectively,
  `omega(D^+_n) > 0` for `n > 192`. (ii) [an asymptotic formula]".
- [K23] Theorem 3: "Conjecture 2(i) and (ii) imply Conjecture 1(ii) and (i), respectively."
  Corollary 4 (Bordellès, Luca, Moree, Shparlinski): 2(ii) is true, so 1(i) is true. The text
  adds: "Unfortunately, their methods do not lead to an explicit or computable bound n_0" and
  "it is still an open task to establish Conjectures 1(ii) and 2(i)."
- [K23] Theorem 9: "`B_n'(x)` in `Z[x]` if and only if `D^⊥_n = 1`", where `D^⊥_n` is the product
  of the primes `p` not dividing `n` with `s_p(n) >= p` (A324370).
- [K23] Conjecture 11: "R-bar = R", `R-bar = {n >= 1 : D_n = rad(n+1)}`,
  `R = {3,5,8,9,11,27,29,35,59}`, `D_n = denom(B_n(x) - B_n)`.
- [K23] Conjecture 15: "S-bar_2 = S_2 and S-bar_3 = S_3" (sets as in Corollaries D, E).
- [KS17] Theorems 1, 2: with `d_n` the denominator of `S_n(x) = (B_{n+1}(x) - B_{n+1})/(n+1)` and
  `q_n = d_n/(n+1)`: `q_n = prod_{p <= M_n, s_p(n+1) >= p} p`, where `M_n = (n+2)/2` for even `n`
  and `(n+2)/3` for odd `n`. (Index shift: `q_n = D_{n+1}` = A195441(n).) Not used above.

## 8. What depends on what, and what is not verified

The proof of Theorem 1 and of all corollaries uses only:

1. Elementary algebra (sections 1–4), proved in the text. Lucas's theorem is proved in the text.
2. The von Staudt–Clausen theorem (Fact 1.3). Classical; quoted from [K23], section 2.
   `UNVERIFIED CITATION:` I did not open Clausen (1840), von Staudt (1840) or a textbook. On
   2026-11-26 I tried to open Hardy and Wright, *An Introduction to the Theory of Numbers*
   (the archive.org copies are lending-only) and failed; the referee could not open one either.
   The theorem number usually given, Hardy–Wright Theorem 118, is from memory. A person should
   check a textbook; nobody doubts the theorem.
3. The explicit bounds (P1), (P2) for `pi(x)`, from two refereed open-access papers of Axler.
   The 2016 paper (#A22) was opened (arXiv TeX source and journal PDF) by the author and by the
   first referee; the 2018 paper (#A52) was opened (journal PDF) by the author and by the Gemini
   reviewers, not by the first referee:
   - (P1) for `x >= 468049`: Axler, Integers 16 (2016) #A22, Corollary 3.5; for
     `5393 <= x < 468049`: the computation `threshold_test.py`, step (b0) (a proof step, not a
     sanity check: it covers every real `x` in the range, with margin at least 0.04).
   - (P2) for `x >= 468049`: Axler, Integers 18 (2018) #A52, Theorem 2; for
     `60184 <= x < 468049`: the computation `threshold_test.py`, step (b). (Not Corollary 3.4 of
     the 2016 paper, whose last statement was corrected by Axler in 2018, and not Theorem 1.3 of
     the 2016 paper, whose proof has a gap that Theorem 2 closes; see the corrections in section 5.)
   - Caveat that cannot be removed here: neither I nor the referee audited Axler's proofs (which
     in turn build on explicit estimates of Dusart).
   - Historical source: Dusart, arXiv:1002.0442v1, Theorem 6.9 (preprint; "6.9" obtained by
     counting the theorem-like environments in the TeX source, confirmed by the referee).
     `UNVERIFIED CITATION:` the refereed version, P. Dusart, *Explicit estimates of some
     functions over primes*, Ramanujan J. 45 (2018), 227–251, and Dusart's 1999 note (C. R.
     Math. Acad. Sci. Soc. R. Can. 21, 53–59; credited for (P1) by Axler 2018, p. 2) were not
     opened (paywall). The proof does not depend on them.
   - Additional numerical check: `threshold_test.py` confirms (P1) for all real `x` in
     `[5393, 2.1·10^7)` and (P2) for all real `x` in `[60184, 2.1·10^7]`; the referee's sieve
     does so up to `10^8` and reports both ranges sharp (failures at 5392 and 60183).
4. Four computations: `finite_check.c` (Proposition 9; repeated by `ref_finite.c`),
   `check_bernoulli.py` (indices up to 1100; repeated by the referee's `ref_bern.py`),
   `threshold_test.py` steps (b0) and (b) ((P1) on `[5393, 468049)`, (P2) on `[60184, 468049)`), and the `79 <= k <= 192` line of
   `verify_small.py` (Corollary C only).

Nothing from [K17], [K23], [KS17] or Bordellès–Luca–Moree–Shparlinski is used in the proof; they
only supply the statements of the conjectures.

Remaining weak points, in the order a reviewer should attack them:

- Lemma 3 and Lemma 4 (the count "at most one failing prime per value of `c`") are the heart of
  the argument and are new as far as I know. `lemma_test.py` tested them on 64 040 values of `n`
  (all `n <= 60000` with every `s <= 3F + 5`, 4000 random `n < 10^12`, and `F` near 60184):
  no failure, and the bound of Proposition 6 was never exceeded. The referee re-derived them and
  tested 42 922 further values with separate code: no violation.
- The reviews required by `CONTRIBUTING.md` are done (four, the last one by a different model
  family and a pass). No human has reviewed the proof.
- Citations still marked `UNVERIFIED CITATION:` — von Staudt–Clausen in a textbook (item 2), and
  the two Dusart papers (item 3; no longer needed).
- A fallback that avoids Axler and Dusart, not carried out: Schoenfeld's
  `|theta(x) - x| < x/(40 ln x)` for `x >= 678407` (Math. Comp. 30 (1976); `UNVERIFIED
  CITATION:` from memory, not opened) gives about `0.45 F/ln^2 F` primes in the window, enough
  for (6.1), with a finite check up to `678407^2`. The referee's run to `678408^2` (section 6)
  covers that range, but with one program only.
- Novelty (not a mathematical gap): see `README.md`. Neither the author nor the referee found a
  prior proof (the referee also viewed the live OEIS entry), but the argument is short, so the
  search should be repeated by a human (MathSciNet, zbMATH, "cited by" lists) before anything
  is announced.

## References

- [K23] B. C. Kellner, *On the finiteness of Bernoulli polynomials whose derivative has only
  integral coefficients*, J. Integer Seq. 27 (2024), Article 24.2.8; arXiv:2310.01325v2.
- [K17] B. C. Kellner, *On a product of certain primes*, J. Number Theory 179 (2017), 126–141;
  arXiv:1705.04303.
- [KS17] B. C. Kellner and J. Sondow, *Power-sum denominators*, Amer. Math. Monthly 124 (2017),
  695–709; arXiv:1705.03857.
- P. Dusart, *Estimates of some functions over primes without R.H.*, arXiv:1002.0442 (2010).
- C. Axler, *New bounds for the prime counting function*, Integers 16 (2016), #A22; arXiv:1409.1780.
  With a corrigendum dated January 18, 2018 (to Corollary 3.4), linked on the journal's volume page.
- C. Axler, *Effective estimates for some functions defined over primes*, Integers 24 (2024), #A34.
  (Propositions 2 and 3 recover the estimates the 2018 proof depends on; Theorem 2 is a sharper
  upper bound that implies Theorem 2 of the 2018 paper.)
- C. Axler, *New estimates for some functions defined over primes*, Integers 18 (2018), #A52.
  (Theorem 2 is the upper bound used for (P2); the Remark on p. 9 reports the gap in the proof of
  Theorem 1.3 of the 2016 paper.)
- C. Axler, *Estimates for pi(x) for large values of x and Ramanujan's prime counting inequality*,
  Integers 18 (2018), #A61.
