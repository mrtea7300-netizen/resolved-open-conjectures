/* All odd k < N0 with sigma(k)/k > (e^gamma/2) log log k   (OEIS A353076), N0 given as decimal string.
   DFS over prime-power factorizations, primes increasing. Prune with max possible further abundancy:
   consecutive next primes while product fits, plus a tail factor for primes beyond the table. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
static u128 N0; static long double C, lN0; static u64 *P; static int NP; static long double *lgP;
static long cnt=0, border=0, incomplete=0, nodes=0; static u128 maxk=0; static FILE*out;
static void p128(FILE*f,u128 x){ char b[64]; int i=63; b[i]=0; if(!x){fputs("0",f);return;} while(x){b[--i]='0'+(int)(x%10); x/=10;} fputs(b+i,f); }
static long double bound_extra(int i,long double logrem){ long double f=1; while(i<NP && logrem>=lgP[i]){ f*=(long double)P[i]/(P[i]-1); logrem-=lgP[i]; i++; }
  if(i>=NP && logrem>0) f*=expl(logrem/lgP[NP-1]/(long double)(P[NP-1]-1)); return f; }
static void dfs(u128 v,long double a,int i){
  nodes++;
  if(v>1){ long double t=C*logl(logl((long double)v)); long double d=a-t;
    if(fabsl(d)<1e-15L*t) border++;
    if(d>0){ cnt++; if(v>maxk)maxk=v; if(out){p128(out,v);fputc('\n',out);} } }
  long double lv=logl((long double)v);
  for(int j=i;;j++){
    if(j>=NP){ /* ran out of table primes: is a larger prime still possibly useful? */
      long double ub=a*bound_extra(NP,lN0-lv); long double vm=(long double)v*P[NP-1];
      if(v*(u128)P[NP-1] < N0 && ub > C*logl(logl(vm))) incomplete++;
      break; }
    u64 p=P[j]; if(v*(u128)p >= N0) break;
    long double ub=a*bound_extra(j,lN0-lv); long double vm=(long double)v*p;
    if(ub <= C*logl(logl(vm<16?16:vm))) break;
    u128 w=v; long double sp=1,pk=1;
    while(w*(u128)p < N0){ w*=p; pk/=(long double)p; sp+=pk; dfs(w,a*sp,j+1); }
  }
}
int main(int argc,char**argv){
  N0=0; for(char*c=argv[1];*c;c++) N0=N0*10+(*c-'0'); lN0=logl((long double)N0);
  C=expl(0.57721566490153286060651209008L)/2; out=argc>2?fopen(argv[2],"w"):NULL;
  int lim=argc>3?atoi(argv[3]):3000000; char*s=calloc(lim+1,1); P=malloc(8*(size_t)lim); lgP=malloc(sizeof(long double)*(size_t)lim);
  for(long i=2;i<=lim;i++) if(!s[i]){ if(i>2){P[NP]=i;lgP[NP]=logl((long double)i);NP++;} for(long j=i*i;j<=lim;j+=i)s[j]=1; }
  dfs(1,1.0L,0);
  printf("N0="); p128(stdout,N0); printf(" terms=%ld max=",cnt); p128(stdout,maxk); printf(" nodes=%ld borderline=%ld incomplete_branches=%ld\n",nodes,border,incomplete);
  return 0;
}
