"""Step 4 of proof.md: the GRH bound leaves only |D| < 2*10^11 for exponent dividing 3.

Bach-Sorenson (Math. Comp. 65 (1996), Theorem 5.1, Table 3, column n = 2): for a quadratic
field E with discriminant of absolute value Delta and log Delta in a row's range, there is a
prime p split in E with  p <= (A log Delta + 2 B + C)^2  (since n = deg E = 2).

If Cl(D) has exponent dividing 3, every split prime q has 4 q^3 >= |D| (proof.md, Lemma 1).
So it suffices that   F(L) = L - log 4 - 6 log(A L + 2B + C) > 0   for L = log|D| >= log(2*10^11).

Within one row F is increasing as soon as A L + 2B + C > 6A (derivative 1 - 6A/(AL+2B+C)),
so it suffices to check F > 0 and A L + 2B + C > 6A at the left end of each row, and at the
right end too where a row boundary is involved (to be safe about which row applies there).
Computed with 50-digit decimals.
"""
from decimal import Decimal as Dm, getcontext

getcontext().prec = 50

# (L_lo, L_hi, A, B, C) for n = 2, Bach-Sorenson Table 3, rows with log Delta >= 25
ROWS = [
    (25, 100, "1.881", "0.34", "5.5"),
    (100, 1000, "1.446", "0.23", "6.8"),
    (1000, 10000, "1.125", "0.63", "10.9"),
    (10000, 100000, "1.032", "0.44", "20.2"),
    (100000, None, "1.008", "-0.06", "47.7"),
]

L_START = 2 * Dm(10) ** 11
L_START = L_START.ln()          # log(2*10^11) = 26.02...


def F(L, A, B, C):
    return L - Dm(4).ln() - 6 * (A * L + 2 * B + C).ln()


ok = True
for lo, hi, A, B, C in ROWS:
    A, B, C = Dm(A), Dm(B), Dm(C)
    pts = [max(Dm(lo), L_START)] + ([Dm(hi)] if hi else [])
    for L in pts:
        val = F(L, A, B, C)
        mono = A * L + 2 * B + C > 6 * A
        print(f"row {lo}-{hi}: L = {float(L):10.4f}  F = {float(val):14.6f}  monotone: {mono}")
        ok = ok and val > 0 and mono

# the threshold itself, for the record (row 25-100)
A, B, C = Dm("1.881"), Dm("0.34"), Dm("5.5")
lo, hi = Dm(25), Dm(30)
for _ in range(200):
    mid = (lo + hi) / 2
    if F(mid, A, B, C) > 0:
        hi = mid
    else:
        lo = mid
print(f"F changes sign at L = {float(hi):.6f}, |D| = {float(hi.exp()):.6e}")
print("ALL CHECKS PASS" if ok else "CHECK FAILED")
