#!/usr/bin/env python3
"""Numerical tests around the threshold F0 = 60184 of proof.md, Proposition 7.
Steps (b0) and (b) are PROOF STEPS of proof.md, section 5; the rest is not part of the proof.

 (a) the constants used in the proof of Proposition 7, recomputed;
 (b0) PROOF STEP (proof.md, section 5, (P1) on the finite range): for every integer m with
        5393 <= m <= 468048,   pi(m) >= (m+1)/(ln(m+1) - 1),
      hence pi(x) >= x/(ln x - 1) for every real x in [5393, 468049)  (pi is constant on [m, m+1)
      and x/(ln x - 1) is increasing for x > e^2).  The smallest margin is printed; it is about
      0.04, far above the rounding error of double precision (about 1e-12 here).
 (b) the two prime-counting inequalities, checked for every real x in [60184, XMAX]:
        pi(x) >= x/(ln x - 1)          (cited for x >= 5393; also checked from 5393)
        pi(x) <= x/(ln x - 1.107)      PROOF STEP on [60184, 468049) (proof.md, section 5, (P2));
                                       above 468049 it follows from Axler 2018 (#A52), Theorem 2
 (c) for every integer F in [2, FMAX], with S = floor(F/(2 ln F)) and C = floor((S^2+2F)/(F+S)):
        actual  pi(F+S) - pi(F)   against the needed  C + 2 + j  (j = 0, 1, 2)
        and against the analytic lower bound 0.297 F / ln^2 F of the proof (for F >= F0).

Usage:  python threshold_test.py [FMAX]     (default 20000000; about 30 s, needs numpy)
"""
import sys
import math
import numpy as np

FMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
F0 = 60184
KAPPA = 1.107

# ---------------------------------------------------------------- (a) constants
L0 = math.log(F0)
print("(a) constants of Proposition 7")
print(f"    ln(60184)                         = {L0:.6f}   (proof uses >= 11.005)")
print(f"    1.0535/11.005                     = {1.0535 / 11.005:.6f}   (proof uses < 0.09573)")
print(f"    ln(F0)/F0                         = {L0 / F0:.7f}  (proof uses < 0.00019)")
print(f"    0.393 - 0.09573 - 0.00019         = {0.393 - 0.09573 - 0.00019:.5f}   (proof uses > 0.297)")
print(f"    F0/ln(F0)^2                       = {F0 / L0 ** 2:.3f}   (proof uses > 496)")
print(f"    0.047 * 496                       = {0.047 * 496:.3f}    (needs >= 4 + j, j <= 2)")
_t13 = 1 / 13 + 3.15 / 13 ** 2 + 12.85 / 13 ** 3 + 71.3 / 13 ** 4 + 463.2275 / 13 ** 5 + 4585 / 13 ** 6
print(f"    Axler 2018 Thm 2 tail at ln x = 13    = {_t13:.7f}   (proof uses < 0.107, for x >= 468049)")
print(f"    F0/(2 ln F0)                      = {F0 / (2 * L0):.2f}")

# ---------------------------------------------------------------- sieve
N = FMAX + FMAX // 20 + 10
sv = np.ones(N + 1, dtype=np.uint8)
sv[:2] = 0
for i in range(2, math.isqrt(N) + 1):
    if sv[i]:
        sv[i * i::i] = 0
pi = np.cumsum(sv, dtype=np.int64)          # pi[m] = number of primes <= m
print(f"    sieve to {N}: pi({N}) = {pi[N]}")

# ---------------------------------------------------------------- (b) cited inequalities
# pi is constant on [m, m+1) and both right-hand sides are increasing for x >= 60184 (x/(ln x - k)
# has derivative (ln x - k - 1)/(ln x - k)^2 > 0), so
#   lower bound for all real x in [m, m+1)  <=  pi(m) >= (m+1)/(ln(m+1) - 1)
#   upper bound for all real x in [m, m+1)  <=  pi(m) <= m/(ln m - 1.107)
AX = 468049                                  # Axler 2016, Corollary 3.5, last column: x0 = 468049
if N > AX:
    m = np.arange(5393, AX, dtype=np.float64)                    # m = 5393 .. 468048
    marg = pi[5393:AX] - (m + 1) / (np.log(m + 1) - 1.0)
    k = int(np.argmin(marg))
    print("(b0) PROOF STEP: pi(m) >= (m+1)/(ln(m+1) - 1) for every integer m in [5393, 468048], i.e.")
    print(f"     pi(x) >= x/(ln x - 1) for every real x in [5393, 468049): {bool((marg >= 0).all())};"
          f"  smallest margin {float(marg[k]):.4f} at m = {5393 + k}")
    mm = np.arange(5380, 5393, dtype=np.float64)
    print("     (sharpness: the same test fails at m =",
          [int(v) for v in mm[pi[5380:5393] < (mm + 1) / (np.log(mm + 1) - 1.0)]], "below 5393)")
print("(b) cited inequalities for pi(x)")
for lo in (5393, F0):
    m = np.arange(lo, N, dtype=np.float64)
    low_ok = pi[lo:N] >= (m + 1) / (np.log(m + 1) - 1.0)
    print(f"    pi(x) >= x/(ln x - 1) for all real x in [{lo}, {N}): {bool(low_ok.all())}"
          + ("" if low_ok.all() else f"  first failure near x = {lo + int(np.argmin(low_ok))}"))
m = np.arange(F0, N + 1, dtype=np.float64)
for kappa in (1.1, KAPPA):
    up_ok = pi[F0:N + 1] <= m / (np.log(m) - kappa)
    print(f"    pi(x) <= x/(ln x - {kappa}) for all real x in [{F0}, {N}]: {bool(up_ok.all())}")
if N >= AX:
    m = np.arange(F0, AX, dtype=np.float64)                      # m = 60184 .. 468048
    marg = m / (np.log(m) - KAPPA) - pi[F0:AX]
    k = int(np.argmin(marg))
    print(f"    PROOF STEP: pi(x) <= x/(ln x - {KAPPA}) for every real x in [{F0}, {AX}): "
          f"{bool((marg >= 0).all())};  smallest margin {float(marg[k]):.4f} at m = {F0 + k}")
else:
    print(f"    WARNING: FMAX too small, the proof step (P2) on [{F0}, {AX}) was NOT checked")
m = np.arange(F0 - 5, F0 + 1, dtype=np.float64)
print("    just below 60184, pi(m) - m/(ln m - 1.1) for m = 60179..60184:",
      np.round(pi[F0 - 5:F0 + 1] - m / (np.log(m) - 1.1), 3).tolist())

# ---------------------------------------------------------------- (c) the counting inequality
F = np.arange(2, FMAX + 1, dtype=np.int64)
L = np.log(F.astype(np.float64))
S = np.floor(F / (2 * L)).astype(np.int64)
S = np.maximum(S, 1)
count = pi[F + S] - pi[F]
C = (S * S + 2 * F) // (F + S)
print("(c) pi(F+S) - pi(F) against C + 2 + j, with S = floor(F/(2 ln F))")
for j in (0, 1, 2):
    margin = count - (C + 2 + j)
    bad = np.nonzero(margin < 0)[0]
    last_bad = int(F[bad[-1]]) if len(bad) else None
    sel = F >= F0
    k = int(np.argmin(margin[sel]))
    print(f"    j={j}: last F <= {FMAX} with too few primes: {last_bad};  "
          f"for F >= {F0}: min margin {int(margin[sel][k])} at F = {int(F[sel][k])}")
sel = F >= F0
lb = 0.297 * F[sel] / L[sel] ** 2
print(f"    analytic lower bound 0.297 F/ln^2 F <= actual count for all F in [{F0}, {FMAX}]: "
      f"{bool((count[sel] >= lb).all())};  min(actual/bound) = {float((count[sel] / lb).min()):.3f}")
ub = F[sel] / (4 * L[sel] ** 2) + 2
print(f"    C <= F/(4 ln^2 F) + 2 for all F in [{F0}, {FMAX}]: {bool((C[sel] <= ub).all())}")
print("    sample rows (F, S, C, primes in (F, F+S], 0.297 F/ln^2 F):")
for f in sorted({f for f in (F0, F0 + 1, 10 ** 5, 10 ** 6, 10 ** 7, FMAX) if f <= FMAX}):
    i = f - 2
    print(f"      {f:>9} {int(S[i]):>7} {int(C[i]):>6} {int(count[i]):>7} {0.297 * f / math.log(f) ** 2:>10.1f}")
