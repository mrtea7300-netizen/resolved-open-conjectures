#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int c,char**v){ long N=atol(v[1]); double *s=calloc(N+1,sizeof(double));
 for(long d=1; d<=N; d+=2) for(long m=d; m<=N; m+=2*d) s[m]+=d;   /* odd m only, odd divisors */
 long cnt=0; long double C=expl(0.5772156649015328606L)/2;
 for(long n=3;n<=N;n+=2){ if((long double)s[n] > C*n*logl(logl((long double)n))) {cnt++; printf("%ld\n",n);} }
 fprintf(stderr,"brute N=%ld count=%ld\n",N,cnt); return 0; }
