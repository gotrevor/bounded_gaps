import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
from math import factorial as fac
import itertools, time

def inertia_pos(B):
    n=len(B); A=[[F(B[i][j]) for j in range(n)] for i in range(n)]
    d=[F(0)]*n
    for j in range(n):
        if A[j][j]==0:
            sw=next((kk for kk in range(j,n) if A[kk][kk]!=0),None)
            if sw is None: d[j]=F(0); continue
            if sw!=j:
                A[j],A[sw]=A[sw],A[j]
                for r in range(n): A[r][j],A[r][sw]=A[r][sw],A[r][j]
        d[j]=A[j][j]
        for i in range(j+1,n):
            f=A[i][j]/d[j]
            for c in range(j,n): A[i][c]-=f*A[j][c]
    return sum(1 for x in d if x>0)

g00=M.g(0,0)
def precompute(orbs):
    """Per (a,b): list of (T, W, Gocc) over matchings — k-independent."""
    n=len(orbs); cache={}
    for ia in range(n):
        for ib in range(n):
            lam,mu=orbs[ia],orbs[ib]; rl,rm=len(lam),len(mu)
            lst=[]
            for Mp in M.matchings(rl,rm):
                pl={a for a,_ in Mp}; pm={b for _,b in Mp}
                t=len(Mp); T=rl+rm-t; W=1; Gocc=F(0)
                for a,b in Mp: W*=fac(lam[a]+mu[b]); Gocc+=M.g(lam[a],mu[b])
                for a in range(rl):
                    if a not in pl: W*=fac(lam[a]); Gocc+=M.g(lam[a],0)
                for b in range(rm):
                    if b not in pm: W*=fac(mu[b]); Gocc+=M.g(0,mu[b])
                lst.append((T,W,Gocc))
            cache[(ia,ib)]=lst
    return cache

def gram_at(orbs,cache,K):
    n=len(orbs); au=[M.aut(o) for o in orbs]; sz=[sum(o) for o in orbs]
    A=[[F(0)]*n for _ in range(n)]; Mm=[[F(0)]*n for _ in range(n)]
    for ia in range(n):
        for ib in range(n):
            Sden=F(0);Snum=F(0)
            for (T,W,Gocc) in cache[(ia,ib)]:
                f=M.ff(K,T); Sden+=f*W; Snum+=f*W*(Gocc+(K-T)*g00)
            dd=au[ia]*au[ib]*fac(K+sz[ia]+sz[ib]); nn=au[ia]*au[ib]*fac(K+sz[ia]+sz[ib]+1)
            Mm[ia][ib]=F(Sden,1)/dd; A[ia][ib]=F(Snum,1)/nn
    return A,Mm

print("Mapping (k,D) feasibility for M_k(D) > 4  [n=#orbits]", flush=True)
for D in (4,5,6,7,8):
    orbs=M.partitions_upto(D); n=len(orbs)
    t=time.time(); cache=precompute(orbs); tp=time.time()-t
    row=[]
    for K in (50,54,60,70,80,90,105,120,150,200,300):
        A,Mm=gram_at(orbs,cache,K)
        B=[[A[i][j]-4*Mm[i][j] for j in range(n)] for i in range(n)]
        ok = inertia_pos(B)>=1
        row.append(f"k{K}:{'Y' if ok else '.'}")
    print(f"D={D} n={n} (prep {tp:.1f}s): "+" ".join(row), flush=True)
