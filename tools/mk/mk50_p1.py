# M_k lower bound over the sub-family F = g(P1), P1=sum t_i, g poly of degree D.
# M = k*J/Den,  Den = 1/(k-1)! * sum_{d,e} a_d a_e/(k+d+e)
# h(w)=int_w^1 g = sum_d a_d/(d+1)(1-w^{d+1});  J=1/(k-2)! int_0^1 h(w)^2 w^{k-2}dw
from fractions import Fraction as F
from math import factorial as fac
def solve(k,D):
    # Den matrix B[d][e] = 1/(k-1)! * 1/(k+d+e)
    B=[[F(1,fac(k-1))*F(1,k+d+e) for e in range(D+1)] for d in range(D+1)]
    # h(w) as coeffs over w^j: constant part c0=sum_d a_d/(d+1); minus sum_d a_d/(d+1) w^{d+1}
    # represent h in terms of a: h = sum_d a_d * p_d(w), p_d(w)=1/(d+1)*(1 - w^{d+1})
    # J = 1/(k-2)! * int_0^1 (sum_d a_d p_d)^2 w^{k-2} dw = sum_{d,e} a_d a_e * Aentry
    # int_0^1 p_d p_e w^{k-2} dw : p_d p_e = 1/((d+1)(e+1)) (1 - w^{d+1})(1-w^{e+1})
    #   = 1/((d+1)(e+1)) [1 - w^{d+1} - w^{e+1} + w^{d+e+2}]
    # int_0^1 w^{k-2+m} = 1/(k-1+m)
    def I(m): return F(1,k-1+m)
    A=[[F(1,fac(k-2))*F(k)*F(1,(d+1)*(e+1))*(I(0)-I(d+1)-I(e+1)+I(d+e+2)) for e in range(D+1)] for d in range(D+1)]
    # max generalized eigenvalue via float power iteration
    n=D+1
    def gs(M,b):
        Au=[[float(M[i][j]) for j in range(n)]+[float(b[i])] for i in range(n)]
        for c in range(n):
            piv=max(range(c,n),key=lambda r:abs(Au[r][c])); Au[c],Au[piv]=Au[piv],Au[c]; pv=Au[c][c]
            for r in range(n):
                if r!=c and Au[r][c]!=0:
                    f=Au[r][c]/pv
                    for j in range(c,n+1): Au[r][j]-=f*Au[c][j]
        return [Au[i][n]/Au[i][i] for i in range(n)]
    def mv(M,v): return [sum(float(M[i][j])*v[j] for j in range(n)) for i in range(n)]
    v=[1.0]*n
    for _ in range(400):
        w=gs(B,mv(A,v)); nrm=max(abs(x) for x in w) or 1.0; v=[x/nrm for x in w]
    num=sum(v[i]*float(A[i][j])*v[j] for i in range(n) for j in range(n))
    den=sum(v[i]*float(B[i][j])*v[j] for i in range(n) for j in range(n))
    return num/den
for D in range(1,7):
    print(f"k=50  F=g(P1) deg {D}:  M_50 >= {solve(50,D):.5f}")
