/* Independent check (different bound, __float128): odd k < N0 with sigma(k)/k > (e^g/2) loglog k.
   Bound: after choosing prefix v with largest prime index j-1, at most r = floor(log(N0/v)/log P[j]) more distinct primes fit;
   each contributes at most P[j+i]/(P[j+i]-1); prune if a*prod_{i<r} P[j+i]/(P[j+i]-1) < need*(1-1e-20). */
#include <stdio.h>
#include <stdlib.h>
#include <quadmath.h>
typedef unsigned __int128 u128; typedef unsigned long long u64;
static u128 N0; static __float128 Cq; static u64*P; static int NP; static long cnt=0,nodes=0; static FILE*out;
static void p128(FILE*f,u128 x){ char b[64]; int i=63; b[i]=0; while(x){b[--i]='0'+(int)(x%10); x/=10;} fputs(b+i,f); }
static void dfs(u128 v,__float128 a,int i){
  nodes++;
  if(v>1){ __float128 t=Cq*logq(logq((__float128)v)); if(a>t){cnt++; p128(out,v); fputc('\n',out);} }
  for(int j=i;j<NP;j++){
    u64 p=P[j]; if(v*(u128)p>=N0) break;
    int r=(int)floorq(logq((__float128)N0/(__float128)v)/logq((__float128)p)); __float128 ub=a;
    for(int q=0;q<r && j+q<NP;q++) ub*=(__float128)P[j+q]/(P[j+q]-1);
    if(j+r>NP){ fprintf(stderr,"table too small\n"); exit(3);} 
    __float128 vm=(__float128)v*p; if(vm<16) vm=16;
    if(ub < Cq*logq(logq(vm))*(1-1e-20Q)) break;
    u128 w=v; __float128 sp=1,pk=1;
    while(w*(u128)p<N0){ w*=p; pk/=p; sp+=pk; dfs(w,a*sp,j+1); }
  }
}
int main(int c,char**v){ N0=0; for(char*s=v[1];*s;s++) N0=N0*10+(*s-'0'); Cq=expq(0.5772156649015328606065120900824024Q)/2; out=fopen(v[2],"w");
  int lim=3000000; char*s=calloc(lim+1,1); P=malloc(8*(size_t)lim);
  for(long i=2;i<=lim;i++) if(!s[i]){ if(i>2) P[NP++]=i; for(long j=i*i;j<=lim;j+=i) s[j]=1; }
  dfs(1,1,0); fclose(out); printf("terms=%ld nodes=%ld\n",cnt,nodes); return 0; }
