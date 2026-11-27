/* Independent check: for each x read from stdin, compute pi(x) and pi(floor(x/e)) with the
   Lucy_Hedgehog / Legendre-type O(x^(3/4)) prime-counting algorithm (no sieve of [1,x]),
   then print "x pi(x) pi(x/e) F" with F=1 iff pi(x)^2 >= e*x*pi(x/e)/log x (evaluated in __float128). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <quadmath.h>
typedef long long ll;
static ll pi_lucy(ll n){
  if(n<2) return 0;
  ll r=(ll)sqrtl((long double)n); while(r*r>n) r--; while((r+1)*(r+1)<=n) r++;
  ll *S=malloc(sizeof(ll)*(r+2)), *L=malloc(sizeof(ll)*(r+2)); /* S[v]=count for v<=r, L[i]=count for n/i */
  for(ll v=1;v<=r;v++) S[v]=v-1;
  for(ll i=1;i<=r;i++) L[i]=n/i-1;
  for(ll p=2;p<=r;p++){ if(S[p]==S[p-1]) continue; ll sp=S[p-1]; ll p2=p*p;
    ll lim = r < n/p2 ? r : n/p2;
    for(ll i=1;i<=lim;i++){ ll d=i*p; ll val = (d<=r)? L[d] : S[n/d]; L[i]-= val-sp; }
    for(ll v=r; v>=p2; v--) S[v]-= S[v/p]-sp; }
  ll res=L[1]; free(S); free(L); return res; }
int main(){ ll x; __float128 E=expq(1.0Q);
  while(scanf("%lld",&x)==1){ ll xe=(ll)floorq((__float128)x/E);
    ll a=pi_lucy(x), b=pi_lucy(xe);
    int F; if(b==0) F=1; else { __float128 d=(__float128)a*a - E*(__float128)x*b/logq((__float128)x); F = d>=0; }
    printf("%lld %lld %lld %d\n",x,a,b,F); fflush(stdout);} return 0; }
