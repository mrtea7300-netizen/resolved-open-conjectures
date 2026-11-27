# negative controls for certify_small_n.certify: each must raise
import runpy, sys, io, contextlib
from decimal import Decimal as D
src = open('certify_small_n.py').read().split("log = []")[0]
g = {}; exec(src, g)
d9 = g['data'](9)
for (A, B, s) in [(0, 1, +1), (0, "0.0023365", -1), ("0.0023362", 1, +1), (0, "0.5", -1)]:
    try:
        c = g['certify'](d9, A, B, s); print("NOT raised (BAD)", A, B, s, c)
    except RuntimeError as e:
        print("raised as expected:", (A, B, s), e)
# dense float sampling consistency
import math
P = [2,3,5,7,11,13,17,19,23]
def Qf(a): return 9*23**a - (1+a)*sum(p**a for p in P)
print("cells n=9 left:", g['certify'](d9, 0, "0.0023363", -1))
