"""Exact verification of a lower bound on min y_A.P for H.12 over all quantum instruments (H.15.9(C')).
Input: numerical dual (h12_dual_{ns,ppt}.pkl).  All dual matrices are rounded to Gaussian rationals (denominator 2^30) and made
exactly Hermitian.  For any feasible Z of the relaxation (which contains every product of instruments):
   y.P = sum_x Tr Lam_x + sum_{x,c} Tr[S_xc Z_xc] + sum_{x,c,k} Tr[Y_xck Z_xc^{T_k}],   S_xc := W_xc - Lam_x - (equality terms) - sum_k Y^{T_k}
(the equality terms vanish on feasible Z: Tr[(G - T_k G) S] = Tr[G (S - T_k S)] = 0 and the x_k-independence terms cancel).
Since Z_xc, Z_xc^{T_k} >= 0 and sum_c Tr Z_xc = 8:  y.P >= sum_x Tr Lam_x + 8 sum_x min_c [ l(S_xc) + sum_k l(Y_xck) ],
where l(A) is a rational t with A - t*1 >= 0, CHECKED EXACTLY (LDL^T of the 16x16 real form, Fractions, all pivots > 0).
W is in Q(i,sqrt2); it is replaced by a rational W' from 60-digit evaluation, |W-W'| entries < 1e-55, contributing < 1e-50 (subtracted)."""
import pickle, sys, numpy as np, itertools as it, re, sympy as sp
from fractions import Fraction as Fr
fn=sys.argv[1]; D=pickle.load(open(fn,'rb')); DEN=2**30
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
Hs=sp.Matrix(8,8,lambda a,b:(-1)**par(a&b))/sp.sqrt(8); phs=sp.Matrix([0,0,0,1/sp.sqrt(2),(1-sp.I)/2,0,0,0])
def q(v): return Fr(str(sp.N(v,60)))
psi=[]
for o in range(8):
    v=sp.expand(Hs*sp.diag(*[sp.I**MT[o][z] for z in range(8)])*Hs*phs); psi.append([(q(sp.re(t)),q(sp.im(t))) for t in v])
y=np.array(eval(re.search(r'\[.*?\]',open('instr2_exact.log').readline()).group()),int).reshape(8,8)
# Gaussian-rational matrices as pairs (Re, Im) of 8x8 lists of Fractions
def rnd(A): A=np.asarray(A); A=(A+A.conj().T)/2; return ([[Fr(round(A[i,j].real*DEN),DEN) for j in range(8)] for i in range(8)],[[Fr(round(A[i,j].imag*DEN),DEN) for j in range(8)] for i in range(8)])
def herm(A): R,I=A; return ([[ (R[i][j]+R[j][i])/2 for j in range(8)] for i in range(8)],[[ (I[i][j]-I[j][i])/2 for j in range(8)] for i in range(8)])
def add(A,B,s=1): return ([[A[0][i][j]+s*B[0][i][j] for j in range(8)] for i in range(8)],[[A[1][i][j]+s*B[1][i][j] for j in range(8)] for i in range(8)])
bits=lambda i:((i>>2)&1,(i>>1)&1,i&1)
def idx(b): return 4*b[0]+2*b[1]+b[2]
def twirl(A,k):  # 1_k (x) Tr_k(A)/2, exact
    out=([[Fr(0)]*8 for _ in range(8)],[[Fr(0)]*8 for _ in range(8)])
    for i in range(8):
        for j in range(8):
            bi,bj=bits(i),bits(j)
            if bi[k]!=bj[k]: continue
            s=[Fr(0),Fr(0)]
            for t in (0,1):
                ii=list(bi); jj=list(bj); ii[k]=t; jj[k]=t
                s[0]+=A[0][idx(ii)][idx(jj)]; s[1]+=A[1][idx(ii)][idx(jj)]
            out[0][i][j]=s[0]/2; out[1][i][j]=s[1]/2
    return out
def ptT(A,k):
    out=([[None]*8 for _ in range(8)],[[None]*8 for _ in range(8)])
    for i in range(8):
        for j in range(8):
            bi,bj=list(bits(i)),list(bits(j)); bi[k],bj[k]=bj[k],bi[k]
            out[0][i][j]=A[0][idx(bi)][idx(bj)]; out[1][i][j]=A[1][idx(bi)][idx(bj)]
    return out
def pd_shift(A,t):   # exact: A - t*1 positive definite?  real form [[R,-I],[I,R]]
    R,I=A; n=16; M=[[None]*n for _ in range(n)]
    for i in range(8):
        for j in range(8):
            M[i][j]=R[i][j]-(t if i==j else 0); M[i+8][j+8]=M[i][j]; M[i][j+8]=-I[i][j]; M[i+8][j]=I[i][j]
    for p in range(n):
        if M[p][p]<=0: return False
        for i in range(p+1,n):
            f=M[i][p]/M[p][p]
            if f: 
                for j in range(p,n): M[i][j]-=f*M[p][j]
    return True
def lowb(A):
    Af=np.array(A[0],float)+1j*np.array(A[1],float); lam=np.linalg.eigvalsh(Af)[0]
    for marg in (1e-7,1e-5,1e-3):
        t=Fr(int(np.floor((lam-marg)*2**24)),2**24)
        if pd_shift(A,t): return t
    raise RuntimeError('no certified lower bound')
pc=lambda c,k:(c>>(2*(2-k)))&3
rest=lambda c,k:tuple(pc(c,j) for j in range(3) if j!=k)
def flip(x,k): b=list(B3[x]); b[k]^=1; return B3.index(tuple(b))
Lam={x:herm(rnd(v)) for x,v in D['Lam'].items()}; Gam={k:herm(rnd(v)) for k,v in D['Gam'].items()}; Del={k:herm(rnd(v)) for k,v in D['Del'].items()}
Y={k:herm(rnd(v)) for k,v in D['Y'].items()}
TG={}
bound=sum(sum(Lam[x][0][i][i] for i in range(8)) for x in range(8)); print('sum Tr Lam (rounded) =',float(bound),flush=True)
for x in range(8):
    worst=None
    for c in range(64):
        a=tuple(pc(c,k)>>1 for k in range(3)); o=tuple(pc(c,k)&1 for k in range(3)); p=psi[B3.index(o)]; w=int(y[x,B3.index(a)])
        W=([[w*(p[i][0]*p[j][0]+p[i][1]*p[j][1]) for j in range(8)] for i in range(8)],[[w*(p[i][1]*p[j][0]-p[i][0]*p[j][1]) for j in range(8)] for i in range(8)])
        S=add(W,Lam[x],-1); m=Fr(0)
        for k in range(3):
            key=(k,x,rest(c,k))
            if key not in TG: TG[key]=add(Gam[key],twirl(Gam[key],k),-1)
            S=add(S,TG[key],-1)
            S=add(S,Del[key],-1) if B3[x][k]==1 else add(S,Del[(k,flip(x,k),rest(c,k))],+1)
            if Y: S=add(S,ptT(Y[x,c,k],k),-1); m+=lowb(Y[x,c,k])
        m+=lowb(S)
        worst=m if worst is None else min(worst,m)
    bound+=8*worst; print('x',x,'min_c [l(S)+sum l(Y)] =',float(worst),flush=True)
bound-=Fr(1,10**40)
print('CERTIFIED (exact rational arithmetic): min over all instruments of y_A.P >=',bound,'=',float(bound))
