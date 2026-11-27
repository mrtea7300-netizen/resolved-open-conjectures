import math, sys
from sympy import factorint
# primes with small multiplicative order of 2
ords={}
for d in range(2,73):
    for q in factorint((1<<d)-1, limit=10**7):
        if q<10**7 and q not in ords: ords[q]=d
primes=sorted(ords)
def run(L, mode, lam):
    pairs=[(a,b) for a in range(1,L) for b in range(a,L)]
    npairs=len(pairs)
    pw={q:[pow(2,a,q) for a in range(L)] for q in primes}
    # kill masks
    masks={}
    for q in primes:
        d={}
        for i,(a,b) in enumerate(pairs):
            r=(pw[q][a]+pw[q][b])%q
            d[r]=d.get(r,0)|(1<<i)
        masks[q]=d
    full=(1<<npairs)-1
    def allowed(q,r):
        if mode=='any': return True
        if mode=='no17': return not (q==17 and r==0) and not (q in (3,5) and r!=0)
        if mode=='no5': return not (q==5 and r==0)
        if mode=='no3': return not (q==3 and r==0)
    def cost(ch):
        dead=0; corr=2.0; lq=0.0
        for q,r in ch.items():
            dead|=masks[q][r]; corr*=q/(q-1); lq+=math.log(q)
        surv=npairs-bin(dead).count('1')
        E=surv*corr/(L*math.log(2))
        return E+lam*lq, E, lq, surv
    ch={}
    if mode=='no17': ch={3:0,5:0}
    best=cost(ch)
    improved=True
    while improved:
        improved=False
        for q in primes:
            cur=ch.get(q)
            opts=[None]+[r for r in masks[q] if allowed(q,r)]
            bq=(best,cur)
            for r in opts:
                c2=dict(ch)
                if r is None: c2.pop(q,None)
                else: c2[q]=r
                if mode=='no17' and (c2.get(3)!=0 or c2.get(5)!=0): continue
                c=cost(c2)
                if c[0]<bq[0][0]-1e-9: bq=(c,r)
            if bq[1]!=cur:
                if bq[1] is None: ch.pop(q,None)
                else: ch[q]=bq[1]
                best=bq[0]; improved=True
    return best, ch
for L in (44,54,63,80,100):
    for mode in ('any','no17','no5','no3'):
        for lam in (1.0,0.5,0.25):
            (J,E,lq,surv),ch=run(L,mode,lam)
            cand=L*math.log(2)-lq-math.log(2)  # ln(#odd candidates below 2^L in class)
            print("L=%3d %-5s lam=%.2f  E=%6.2f lnQ=%6.2f surv=%4d  ln(cands)=%6.2f  ln(expected hits, all cands)=%7.2f  Q-primes=%s"%(L,mode,lam,E,lq,surv,cand,cand-E,sorted(ch.items())))
    sys.stdout.flush()
