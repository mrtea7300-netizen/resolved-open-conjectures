"""Certificate for one n: for every pair 1 <= a <= b with m = n - 2^a - 2^b >= 2, print a proper divisor of m.
Usage: python certificate.py N > data/certificate_N.txt ; python certificate.py --check data/certificate_N.txt"""
import sys
from sympy import factorint
if sys.argv[1]=='--check':
    lines=[l.split() for l in open(sys.argv[2]) if l[0]!='#']
    n=int(lines[0][1]); rows=lines[1:]
    want=[(a,b) for a in range(1,n.bit_length()+1) for b in range(a,n.bit_length()+1) if n-(1<<a)-(1<<b)>=2]
    assert [(int(r[0]),int(r[1])) for r in rows]==want, "pair list incomplete"
    for a,b,m,d in rows:
        a,b,m,d=int(a),int(b),int(m),int(d)
        assert m==n-(1<<a)-(1<<b) and 1<d<m and m%d==0,(a,b)
    print("OK: n =",n,"odd:",n%2==1,"; n mod 255 =",n%255,";",len(rows),"pairs, each m has the listed proper divisor")
else:
    n=int(sys.argv[1]); print("# a b m=n-2^a-2^b smallest_prime_factor_of_m"); print("n",n)
    for a in range(1,n.bit_length()+1):
        for b in range(a,n.bit_length()+1):
            m=n-(1<<a)-(1<<b)
            if m<2: continue
            d=min(factorint(m)); assert d<m,("PRIME",a,b,m)
            print(a,b,m,d)
