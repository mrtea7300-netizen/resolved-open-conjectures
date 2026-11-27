# smallest s with  P_N^{(s)} = sum mu(c) (H + G^2/12 + s G) x(c) <= 0 on monotone x  (exact flow, bisection)
import sys
from fractions import Fraction as Fr
from k4 import mu, g, h, feas, comps_of
sys.setrecursionlimit(100000)
ALL = lambda c, t, p: True
for N in range(5, int(sys.argv[1]) + 1):
    comps = comps_of(N)
    R = [mu(c) * (sum(map(h, c)) + sum(map(g, c)) ** 2 / 12) for c in comps]
    Lf = [mu(c) * sum(map(g, c)) for c in comps]
    assert sum(R) == 0 and sum(Lf) == 0
    ok = lambda s: feas(comps, [r + s * l for r, l in zip(R, Lf)], ALL)
    lo, hi = Fr(0), Fr(N, 12)
    assert ok(hi)
    if ok(lo): print(N, 'threshold <= 0'); continue
    for _ in range(40):
        mid = (lo + hi) / 2
        if ok(mid): hi = mid
        else: lo = mid
    print('N=%d  s0 ~ %.9f   N/12=%.6f  N/12-s0=%.9f  s0 as fraction guess %s' % (N, hi, N / 12, N / 12 - float(hi), Fr(hi).limit_denominator(5000)), flush=True)
