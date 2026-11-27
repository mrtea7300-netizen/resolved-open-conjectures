/* Independent re-enumeration: bit-packed odd-only segmented sieve (separate code from ramanujan.c),
   pi(x) and pi(floor(x/e)) taken from two running counters over a single prime-flag stream that is
   kept in a ring of segments; the predicate pi(x)^2 >= e x pi(x/e)/log x is evaluated at EVERY
   integer x in [2,X] (no monotonicity shortcut).  floor(x/e) is maintained incrementally with an
   exact 128-bit fixed-point accumulator.  Prints counts per decade and writes the runs.
   Usage: ./brute2 X runs.txt                                                                      */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
static uint64_t *bits; static u64 NB;   /* full odd-only bitset of primality up to Y = X/e+2 (for pi(x/e)) */
static uint32_t *bp; static int nbp;
#define SEGW (1<<16)                    /* 64-bit words per segment -> 2^23 odd numbers */
static void sieve_seg(uint64_t *w, u64 lo /*odd*/, u64 nw){ /* bit i <-> lo+2i ; 1 = prime */
  memset(w,0xff,nw*8); u64 hi=lo+2*64*nw;
  for(int i=0;i<nbp;i++){ u64 p=bp[i]; if(p*p>=hi) break;
    u64 s=p*p; if(s<lo){ s=((lo+p-1)/p)*p; if(!(s&1)) s+=p; }
    for(u64 m=s;m<hi;m+=2*p){ u64 k=(m-lo)>>1; w[k>>6]&=~(1ULL<<(k&63)); } }
  if(lo==1) w[0]&=~1ULL; }
int main(int argc,char**argv){
  u64 X=strtoull(argv[1],0,10); FILE*out=fopen(argv[2],"w");
  u64 r=(u64)sqrtl((long double)X)+2; char*c=calloc(r+1,1); bp=malloc(4*r); nbp=0;
  for(u64 i=3;i<=r;i+=2) if(!c[i]){ bp[nbp++]=i; for(u64 j=i*i;j<=r;j+=2*i) c[j]=1; }
  /* 1/e as 0.64 fixed point (u128 with 64 fractional bits not enough? use 2^-120 scale -> 2^-90 used) */
  /* inv_e = floor(2^120 / e) computed from 40-digit decimal */
  const char *ie="0.3678794411714423215955237701614608674458111310317678345078368016974614957448998033571472743";
  /* parse into u128 fixed point with 90 fractional bits by long division */
  u128 F=0; { /* F = floor(frac * 2^120): multiply decimal fraction by 2 repeatedly */
    int dig[120]; int nd=0; for(const char*s=ie+2;*s;s++) dig[nd++]=*s-'0';
    for(int bit=0;bit<90;bit++){ int carry=0; for(int i=nd-1;i>=0;i--){ int v=dig[i]*2+carry; dig[i]=v%10; carry=v/10; } F=(F<<1)|carry; } }
  u64 Y=(u64)(X*0.36787944117144233)+3; NB=(Y/2)/64+2; bits=malloc(NB*8);
  for(u64 w=0; w<NB; w+=SEGW){ u64 nw = (NB-w<SEGW)? NB-w : SEGW; sieve_seg(bits+w, 1+128*w, nw); }
  #define ISP_SMALL(v) ((v)==2 || (((v)&1) && (bits[((v)>>1)>>6]>>(((v)>>1)&63)&1)))
  uint64_t *seg=malloc(SEGW*8); u64 seglo=1; sieve_seg(seg,seglo,SEGW); u64 seghi=seglo+128ULL*SEGW;
  u64 a=0,b=0,xe=0; u128 acc=0; /* acc = x * F (fixed point, 90 bits; x<2^37 so no overflow); floor(x/e) = acc>>90 */
  u64 nfail=0,npf=0,runlo=0,runhi=0,nruns=0,dec=10; int inrun=0;
  const double E=2.718281828459045;
  for(u64 x=1;x<=X;x++){
    int isp;
    if(x==2) isp=1; else if(!(x&1)) isp=0; else { while(x>=seghi){ seglo=seghi; sieve_seg(seg,seglo,SEGW); seghi=seglo+128ULL*SEGW; }
      u64 k=(x-seglo)>>1; isp=(seg[k>>6]>>(k&63))&1; }
    a+=isp; acc+=F; u64 nxe=(u64)(acc>>90); while(xe<nxe){ xe++; if(ISP_SMALL(xe)) b++; }
    if(x<2) continue;
    int f;
    if(b==0) f=1; else { double rr=E*(double)x*(double)b/log((double)x); double L=(double)a*(double)a; double d=L-rr;
      if(fabs(d)>1e-9*rr) f=d>=0; else { long double r2=2.718281828459045235360287471352662L*(long double)x*b/logl((long double)x);
        f = (long double)a*(long double)a - r2 >= 0; } }
    if(f){ nfail++; if(isp) npf++; if(inrun && runhi+1==x) runhi=x; else { if(inrun){fprintf(out,"%llu %llu\n",runlo,runhi);nruns++;} runlo=runhi=x; inrun=1; } }
    if(x==dec){ fprintf(stderr,"DEC %llu failures<=dec=%llu primefail<=dec=%llu\n",dec,nfail,npf); dec*=10; }
  }
  if(inrun){fprintf(out,"%llu %llu\n",runlo,runhi);nruns++;}
  fclose(out);
  printf("X=%llu pi(X)=%llu pi(floor(X/e))=%llu failures=%llu primefail=%llu runs=%llu lastrun=%llu..%llu\n",X,a,b,nfail,npf,nruns,runlo,runhi);
  return 0; }
