from fractions import Fraction as F
from math import factorial as fac
import itertools
k=5
def mono_int(a):
    n=1
    for x in a: n*=fac(x)
    return F(n,fac(k+sum(a)))
def dir_slack(a,beta):
    n=len(a); num=1
    for x in a: num*=fac(x)
    num*=fac(beta)
    return F(num,fac(n+sum(a)+beta))
def numer(p,q):
    tot=F(0); pq=[p[i]+q[i] for i in range(k)]
    for i in range(k):
        rem=pq[:i]+pq[i+1:]
        tot+=F(1,(p[i]+1)*(q[i]+1))*dir_slack(rem,p[i]+q[i]+2)
    return tot
def denom(p,q): return mono_int([p[i]+q[i] for i in range(k)])
orb={():14960,(1,):-40392,(1,1):62832,(1,1,1):-39984,(2,):59136,(2,1):-43197,(3,):-31416}
def orbit(m): return tuple(sorted([x for x in m if x>0],reverse=True))
mons=set()
for deg in range(4):
    for c in itertools.combinations_with_replacement(range(k),deg):
        e=[0]*k
        for j in c: e[j]+=1
        mons.add(tuple(e))
mons=sorted(mons)
co={m:orb[orbit(m)] for m in mons}
N=sum(F(co[p])*F(co[q])*numer(p,q) for p in mons for q in mons)
D=sum(F(co[p])*F(co[q])*denom(p,q) for p in mons for q in mons)
R=N/D
print("numerator   =",N)
print("denominator =",D)
print("ratio       =",R,"=",float(R))
print("ratio > 2 ?",R>2)
print("matches 12048682945/6016885374 ?", R==F(12048682945,6016885374))
