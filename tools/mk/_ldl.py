import sys; sys.argv=['x']
import mk_sym as M
from fractions import Fraction as F
from math import lcm

def ldl_inertia(B):
    """Exact symmetric LDL^T with diagonal pivoting skip. Returns (pos,neg,zero)
    pivot counts (= inertia by Sylvester) and an exact witness vector v with
    v^T B v > 0 if a positive pivot exists."""
    n=len(B)
    # work on a rational copy; symmetric Gaussian elimination tracking L
    A=[[F(B[i][j]) for j in range(n)] for i in range(n)]
    L=[[F(1) if i==j else F(0) for j in range(n)] for i in range(n)]
    d=[F(0)]*n
    piv_order=list(range(n))
    for j in range(n):
        if A[j][j]==0:
            # find a k>j with A[k][k]!=0 to swap (simple symmetric pivot)
            sw=next((k for k in range(j,n) if A[k][k]!=0),None)
            if sw is None:
                d[j]=F(0); continue
            if sw!=j:
                A[j],A[sw]=A[sw],A[j]
                for r in range(n): A[r][j],A[r][sw]=A[r][sw],A[r][j]
                piv_order[j],piv_order[sw]=piv_order[sw],piv_order[j]
        d[j]=A[j][j]
        for i in range(j+1,n):
            f=A[i][j]/d[j]
            L[i][j]=f
            for c in range(j,n):
                A[i][c]-=f*A[j][c]
    pos=sum(1 for x in d if x>0); neg=sum(1 for x in d if x<0); zero=sum(1 for x in d if x==0)
    # witness for a positive pivot index jp: solve L^T y = e_jp -> v, then v^T B v = d[jp]>0
    wit=None
    jp=next((j for j in range(n) if d[j]>0),None)
    if jp is not None:
        # L is unit lower triangular in permuted coords; solve L^T y = e_jp
        y=[F(0)]*n; y[jp]=F(1)
        for i in range(n-1,-1,-1):
            s=y[i]
            for k in range(i+1,n): s-=L[k][i]*y[k]
            y[i]=s  # L[i][i]=1
        # map back through pivot permutation to original coordinate order
        v=[F(0)]*n
        for newpos,orig in enumerate(piv_order): v[orig]=y[newpos]
        wit=v
    return pos,neg,zero,wit

for K in (50,54):
    D=7; orbs=M.partitions_upto(D); n=len(orbs)
    A,Mm=M.reduced_closed(orbs,K)
    B=[[A[i][j]-4*Mm[i][j] for j in range(n)] for i in range(n)]
    pos,neg,zero,wit=ldl_inertia(B)
    print(f"k={K} deg7 #orb={n}: inertia(A-4M) = (+{pos}, -{neg}, 0:{zero})  => M_{K}>4: {pos>=1}")
    if wit is not None:
        val=sum(wit[i]*B[i][j]*wit[j] for i in range(n) for j in range(n))
        Nr=sum(wit[i]*A[i][j]*wit[j] for i in range(n) for j in range(n))
        Dr=sum(wit[i]*Mm[i][j]*wit[j] for i in range(n) for j in range(n))
        L=1
        for x in wit:
            if x!=0: L=lcm(L,x.denominator)
        iv=[int(x*L) for x in wit]
        print(f"   EXACT witness: v^T(A-4M)v = {val} > 0  (={float(val):.4e})")
        print(f"   witness Mk ratio = {Nr/Dr} = {float(Nr/Dr):.6f}")
        print(f"   integer orbit coeffs (x{L}): {dict(zip(orbs,iv))}")
