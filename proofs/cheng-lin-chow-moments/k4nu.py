# nu-version (all blocks weighted w, no special last block): is
#   sum_p nu(p) (H + G^2/12 + s G)(p) y(p) <= 0  for monotone y >= 0  at s = n/12 - 1/15 ?   exact flow with free sink.
import sys, io, contextlib
from fractions import Fraction as Fr
with contextlib.redirect_stdout(io.StringIO()):
    from k4 import g, h, comps_of, w
from k4rem_flow import feas_sink
sys.setrecursionlimit(100000)
def nu(p):
    r = Fr(1)
    for n in p: r *= w(n)
    return r
for delta in (Fr(0), Fr(1, 1000)):
    out = []
    for n in range(2, int(sys.argv[1]) + 1):
        comps = comps_of(n); s = Fr(n, 12) - Fr(1, 15) - delta
        a = [nu(p) * (sum(map(h, p)) + Fr(sum(map(g, p))) ** 2 / 12 + s * sum(map(g, p))) for p in comps]
        out.append('%d:%s' % (n, 'ok' if sum(a) <= 0 and feas_sink(comps, a, lambda c, t, p: p in (2, 3, 4)) else 'FAIL'))
    print('s = n/12 - 1/15 - %s, left peels 2,3,4 only: %s' % (delta, ' '.join(out)), flush=True)
