import sys
from sympy import isprime, factorint
n=int(sys.argv[1])
assert n%2==1
L=n.bit_length()
cnt=0; primes=[]
least={}
for a in range(1,L+1):
    for b in range(a,L+1):
        m=n-(1<<a)-(1<<b)
        if m<2: continue
        cnt+=1
        if isprime(m): primes.append((a,b,m))
print("n =",n,"=",factorint(n))
print("n mod 3,5,17,255 =",n%3,n%5,n%17,n%255)
print("pairs (a<=b, m>=2) checked:",cnt," primes found:",len(primes),primes[:5])
