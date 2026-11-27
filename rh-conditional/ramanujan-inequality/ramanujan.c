/* Enumerate all integers x in [2, X] with  pi(x)^2 >= e*x*pi(x/e)/log(x)
   (failures of Ramanujan's prime-counting inequality).
   Two independent segmented Eratosthenes sieves deliver the primes p (pi(x) jumps at x=p)
   and q (pi(floor(x/e)) jumps at x = floor(q*e)+1).  Between consecutive jump points the pair
   (a,b) = (pi(x), pi(x/e)) is constant and e*x*b/log x is increasing (x>=3), so the failing x of
   each such block form an initial run; we scan it.  Output: maximal runs "lo hi" (inclusive).
   Usage: ./ramanujan X out_intervals.txt                                                       */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <quadmath.h>
typedef unsigned long long u64; typedef __int128 i128;
#define SEG (1<<19)                      /* odd numbers per segment */
static uint32_t *bp; static int nbp;     /* base primes (odd) */
typedef struct { u64 lo; unsigned char s[SEG]; long idx; u64 lim; u64 *nxt; int first; } gen;
static void seg_fill(gen *g){             /* segment covers odd numbers lo, lo+2, ..., lo+2*(SEG-1) */
  memset(g->s,1,SEG);
  u64 hi = g->lo + 2ULL*SEG;              /* exclusive */
  for(int i=0;i<nbp;i++){ u64 p=bp[i]; if(p*p>=hi) break;
    u64 m=g->nxt[i]; while(m<hi){ g->s[(m-g->lo)>>1]=0; m+=2*p; } g->nxt[i]=m; }
  if(g->lo==1) g->s[0]=0;                 /* 1 not prime */
  g->idx=0; }
static void gen_init(gen *g,u64 lim){ g->lo=1; g->lim=lim; g->nxt=malloc(sizeof(u64)*nbp);
  for(int i=0;i<nbp;i++){ u64 p=bp[i]; g->nxt[i]=p*p; } g->first=1; seg_fill(g); }
static u64 gen_next(gen *g){             /* next prime, 2 first; returns ~0 past lim */
  if(g->first){ g->first=0; return 2; }
  for(;;){ while(g->idx<SEG){ long i=g->idx++; if(g->s[i]){ u64 v=g->lo+2ULL*i; return v>g->lim? ~0ULL : v; } }
    g->lo+=2ULL*SEG; if(g->lo>g->lim) return ~0ULL; seg_fill(g); } }
static const long double EL = 2.718281828459045235360287471352662497757L;
static __float128 EQ;
static long nflag=0, nquad=0;
/* returns 1 if x fails (a^2 >= e x b / log x) */
static int fails(u64 x,u64 a,u64 b){
  if(b==0) return 1;
  long double r = EL*(long double)x*(long double)b/logl((long double)x);
  long double L = (long double)a*(long double)a;
  long double d = L-r;
  if(fabsl(d) > 1e-12L*r) return d>=0;
  nquad++;
  __float128 rq = EQ*(__float128)x*(__float128)b/logq((__float128)x);
  __float128 Lq = (__float128)a*(__float128)a;
  __float128 dq = Lq-rq;
  if(fabsq(dq) < 1e-28Q*rq){ nflag++; fprintf(stderr,"FLAG x=%llu a=%llu b=%llu\n",x,a,b); }
  return dq>=0; }
int main(int argc,char**argv){
  u64 X=strtoull(argv[1],0,10); FILE*out=fopen(argv[2],"w");
  EQ = expq(1.0Q);
  u64 r=(u64)sqrt((double)X)+2; char*c=calloc(r+1,1); bp=malloc(sizeof(uint32_t)*r); nbp=0;
  for(u64 i=3;i<=r;i+=2) if(!c[i]){ bp[nbp++]=i; for(u64 j=i*i;j<=r;j+=2*i) c[j]=1; }
  gen *A=malloc(sizeof(gen)), *B=malloc(sizeof(gen));
  gen_init(A,X); gen_init(B,(u64)(X/2.718281828459045)+10);
  u64 a=0,b=0; u64 p=gen_next(A); u64 q=gen_next(B);
  /* event for q: x_q = floor(q*e)+1 */
  #define QEV(q) ((q)==~0ULL? ~0ULL : (u64)floorq((__float128)(q)*EQ)+1)
  u64 xq=QEV(q);
  u64 x=2; u64 runlo=0, runhi=0; int inrun=0; u64 nfail=0, nruns=0, lastfail=0, nblocks=0, npf=0, lastpf=0, dec=10;
  long double fracmin=1;
  while(x<=X){
    /* apply events at x */
    int xprime=(p==x);
    while(p<=x){ a++; p=gen_next(A); }
    while(xq<=x){ b++; 
      __float128 t=(__float128)q*EQ; __float128 fr=t-floorq(t); if(fr<fracmin) fracmin=fr; if(1-fr<fracmin) fracmin=1-fr;
      q=gen_next(B); xq=QEV(q); }
    u64 t = p<xq? p:xq; if(t>X+1) t=X+1;   /* block [x, t) */
    nblocks++;
    u64 y=x;
    while(y<t && fails(y,a,b)) y++;
    if(y>x){ /* failing run [x, y-1] */
      if(inrun && runhi+1==x) runhi=y-1;
      else { if(inrun){ fprintf(out,"%llu %llu\n",runlo,runhi); nruns++; } runlo=x; runhi=y-1; inrun=1; }
      nfail+=y-x; lastfail=y-1; if(xprime){ npf++; lastpf=x; } }
    while(dec<=X && t>dec){ /* all x<=dec processed? block [x,t) covers dec iff x<=dec<t */
      u64 extra = (y>x && dec>=x)? ((dec< y? dec: y-1) - x + 1) : 0;
      u64 extrap = (xprime && y>x && dec>=x)? 1:0;
      fprintf(stderr,"DEC %llu failures<=dec=%llu primefail<=dec=%llu\n",dec,nfail-(y-x>0? (y-x):0)+extra,npf-(xprime&&y>x?1:0)+extrap); dec*=10; }
    x=t;
  }
  if(inrun){ fprintf(out,"%llu %llu\n",runlo,runhi); nruns++; }
  fclose(out);
  printf("X=%llu pi(X)=%llu pi(X/e)=%llu failures=%llu runs=%llu last=%llu blocks=%llu quadchecks=%ld flags=%ld min|frac(q*e)|=%.3Le primefail=%llu lastprimefail=%llu\n",
    X,a,b,nfail,nruns,lastfail,nblocks,nquad,nflag,fracmin,npf,lastpf);
  return 0; }
