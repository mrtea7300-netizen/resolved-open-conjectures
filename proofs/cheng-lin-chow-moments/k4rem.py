# k=4: after the nu-version theorem (prefix part handled exactly, only base slack kept), is the
# remaining linear form <= 0 on monotone x?   exact flow test.
import sys
from fractions import Fraction as Fr
from k4 import g, h, feas, comps_of, w
sys.setrecursionlimit(100000)
rho = lambda n: h(n) + g(n) ** 2 / 12
wt = lambda n: n * w(n)
def nu(p):
    r = Fr(1)
    for n in p: r *= w(n)
    return r
def rem(c, s):
    m = c[-1]; q = c[:-1]
    v = wt(m) * nu(q) * (rho(m) + s * g(m))
    if q and q[-1] in (2, 3, 4):
        p = q[:-1]; j = q[-1]
        cj = {2: (s + g(m) / 6 + Fr(sum(map(g, p))) / 6 - Fr(1, 10)) / 2, 3: Fr(1, 30), 4: Fr(1, 80)}[j]
        v -= wt(m) * nu(p) * cj
    return v
FAM = {'all': lambda c, t, p: True,
       'last block only': lambda c, t, p: t == len(c) - 1,
       'last block, piece 2,3 or rest 2,3,4': lambda c, t, p: t == len(c) - 1 and (c[t] - p in (2, 3) or p in (2, 3, 4)),
       'last two blocks': lambda c, t, p: t >= len(c) - 2}
for name, edge in FAM.items():
    out = []
    for N in range(5, int(sys.argv[1]) + 1):
        comps = comps_of(N); s = Fr(N, 12)
        a = [Fr(rem(c, s)) for c in comps]; tot = sum(a)
        bad = [(c, type(rem(c, s))) for c in comps if not isinstance(rem(c, s), (Fr, int))]
        if bad: print(bad[:3])
        if tot > 0: out.append('%d:sum>0' % N); continue
        # sum may be negative (slack): add a free sink reachable from everything = allow x >= 0;
        # emulate by testing a(F) <= 0 through an extra node: put the deficit on the finest composition? no:
        # use exact criterion with an added super-sink connected from every node.
        comps2 = comps + [('SINK',)]
        a2 = a + [-tot]
        idx_edge = edge
        out.append('%d:%s' % (N, 'ok' if feas2(comps, a, edge) else 'FAIL') if False else '%d:%s(sum=%.3g)' % (N, 'ok' if __import__('k4rem_flow').feas_sink(comps, a, edge) else 'FAIL', float(tot)))
    print('%-40s %s' % (name, ' '.join(out)), flush=True)
