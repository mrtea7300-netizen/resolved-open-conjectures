#!/usr/bin/env python3
"""Independent Python re-implementation of finite_check.c on [1, NMAX], compared line by line with
data/finite_check_1_2000001.txt (exceptions, largest offset, checksum of witness primes).

It also re-derives, for the exceptions (the only n for which no prime p > sqrt(n) works), which k are
members of the three sets according to the FULL digit-sum criteria (all primes p <= n), so that the
link "exceptions of the finite check" -> "known terms" is visible in one place.  The authoritative
decision for small k is check_bernoulli.py (actual polynomials).

Usage:  python verify_small.py [NMAX]     (default 2000000, about 1 minute)
"""
import sys
from math import isqrt
from bisect import bisect_right

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000
JMAX = 4          # conditions j = 0..3 exactly as in finite_check.c


def primes_upto(n):
    sv = bytearray([1]) * (n + 1)
    sv[:2] = b"\0\0"
    for i in range(2, isqrt(n) + 1):
        if sv[i]:
            sv[i * i::i] = bytearray(len(sv[i * i::i]))
    return [i for i in range(n + 1) if sv[i]]


PR = primes_upto(400_000)


def digit_sum(n, p):
    s = 0
    while n:
        n, r = divmod(n, p)
        s += r
    return s


exceptions = [[] for _ in range(JMAX)]
checksum = [0] * JMAX
max_off = [0] * JMAX
for n in range(1, NMAX + 1):
    F = isqrt(n)
    i = bisect_right(PR, F)
    need = set(range(JMAX))
    while need and i < len(PR) and PR[i] <= n:
        p = PR[i]
        i += 1
        if digit_sum(n, p) < p:
            continue
        okc = [True, (n + 1) % p != 0, (n + 1) % p != 0 and (n + 2) % p != 0,
               p * p * n > (n + 1) ** 2]
        for j in sorted(need):
            if okc[j]:
                need.discard(j)
                checksum[j] += p
                max_off[j] = max(max_off[j], p - F)
    for j in need:
        exceptions[j].append(n)

ok = True
ref = {}
try:
    for line in open("data/finite_check_1_2000001.txt"):
        if line.startswith("summary"):
            d = dict(kv.split("=") for kv in line.split()[1:])
            ref[int(d["j"])] = d
except FileNotFoundError:
    pass
for j in range(JMAX):
    print(f"j={j}: {len(exceptions[j])} exceptions, largest {exceptions[j][-1]}, "
          f"max_offset {max_off[j]}, checksum {checksum[j]}")
    print("   ", exceptions[j])
    if NMAX == 2_000_000 and j in ref:
        same = (int(ref[j]["exceptions"]) == len(exceptions[j])
                and int(ref[j]["largest_exception"]) == exceptions[j][-1]
                and int(ref[j]["max_offset"]) == max_off[j]
                and int(ref[j]["checksum"]) == checksum[j] % 2 ** 64)
        ok &= same
        print("    matches finite_check.c output:", same)


# Full criteria (all primes), for the exceptional n only.
def has_any_witness(n, j):
    return any(digit_sum(n, p) >= p and all((n + u) % p for u in range(j + 1))
               for p in PR if p <= n)


names = ["B_k'  integral (A094960), k = n", "B_k'' integral (A366169), k = n+1",
         "B_k''' integral (Kellner's S_3), k = n+2"]
for j in range(3):
    members = [n + j for n in exceptions[j] if not has_any_witness(n, j)]
    print(f"{names[j]}: members with n among the exceptions:", members)
print("Kellner's R (denom(B_n(x)-B_n) = rad(n+1)), candidates among the j=1 exceptions:",
      [n for n in exceptions[1]
       if all(((n + 1) % p == 0) == (digit_sum(n, p) >= p) for p in PR if p <= n + 1)])

# Kellner 2017, Conjecture 1, second half: lambda*_n = (n+1)/P(p_n) < sqrt(n), where P(p_n) is the
# GREATEST prime with s_p(n) >= p.  Exceptions of condition j=3, re-examined with the greatest prime.
def greatest(n):
    return max([p for p in PR if p <= n and digit_sum(n, p) >= p], default=1)


print("n with lambda*_n >= sqrt(n), among the j=3 exceptions:",
      [n for n in exceptions[3] if greatest(n) ** 2 * n <= (n + 1) ** 2])

# Alekseyev's conjecture (A094960, comment of Jun 04 2012): for every k > 78 there is a prime p >= 3
# such that the sum of the last two base-p digits of k is at least p.
def last_two(k):
    return any((k // p) % p + k % p >= p for p in PR if 3 <= p <= k)


print("k <= 1000 with no prime p >= 3 whose last two base-p digits of k sum to >= p:",
      [k for k in range(1, 1001) if not last_two(k)])
print("OK" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
