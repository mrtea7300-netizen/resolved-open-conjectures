import numpy as np, math
def sieve(N):
    s=np.ones(N+1,bool); s[:2]=0
    for i in range(2,int(N**.5)+1):
        if s[i]: s[i*i::i]=0
    return np.nonzero(s)[0]
P=sieve(3*10**5).astype(float)
NMAX=20000
P=P[:NMAX]
alphas=np.concatenate([np.linspace(1e-4,1,400),np.linspace(1,12,1101)[1:]])
for a in alphas:
    t=int(2*math.ceil(a-1e-12)**2+math.ceil(a-1e-12)+6)
    u=(P/P[-1])  # not used
    # compute mean p_k^a / p_n^a in a stable way: cumulative sum of (p_k/p_max)^a
    w=np.exp(a*(np.log(P)-math.log(P[-1])))
    cs=np.cumsum(w)
    n=np.arange(1,NMAX+1)
    lhs=cs/n
    rhs=w/(a+1)
    bad=np.nonzero((lhs>=rhs*(1-1e-12))&(n>=t))[0]
    if len(bad): print(round(a,5),t,(bad+1)[:10])
