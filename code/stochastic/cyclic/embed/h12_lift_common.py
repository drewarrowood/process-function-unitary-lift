# shared setup for h12_lift_dual.py / h12_lift_verify.py (H.12 board, y_A from instr2_exact.log, cost matrices C_v of the lifted-A relaxation)
import numpy as np, itertools as it, re
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/8**.5
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/2**.5; ph[4]=(1-1j)/2
psi=np.array([U[o]@ph for o in range(8)])
y=np.array(eval(re.search(r'\[.*?\]',open('/workspace/pful-graded/code/stochastic/cyclic/embed/instr2_exact.log').readline()).group()),float).reshape(8,8)
# Round 15: optional relabelling so that party LIFTP (0=A,1=B,2=C) becomes the lifted party (position 0).  y_A itself is unchanged;
# only the roles of the parties in the relaxation change.  Default 0 reproduces Round 14 exactly.
import os
LIFTP=int(os.environ.get('LIFTP','0'))
if LIFTP:
    perm=[LIFTP]+[j for j in range(3) if j!=LIFTP]          # new position i holds old party perm[i]
    def pt(t): return tuple(t[perm[i]] for i in range(3))   # old triple -> new triple
    def pidx(i): return B3.index(pt(B3[i]))
    psi2=np.zeros_like(psi); y2=np.zeros_like(y)
    for o in range(8):
        for z in range(8): psi2[pidx(o)][pidx(z)]=psi[o][z]
    for xi in range(8):
        for ai in range(8): y2[pidx(xi),pidx(ai)]=y[xi,ai]
    psi,y=psi2,y2
I2=np.eye(2); Pl=[I2,np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1.,-1])]
def op4(ms):
    M=np.array([[1.]])
    for q in range(4): M=np.kron(M,ms.get(q,I2))
    return M
def twirl_cp(S,q): return sum(op4({q:P})@S@op4({q:P}).conj().T for P in Pl)/4
def emb(W8,first):
    W=W8.reshape(2,2,2,2,2,2)
    E=np.einsum('abcdef,gh->agbcdhef',W,I2) if first==0 else np.einsum('abcdef,gh->gabchdef',W,I2)
    return E.reshape(16,16)
pc=lambda c:(c>>1,c&1)
W={o:np.outer(psi[o],psi[o].conj()) for o in range(8)}
def Cv(cA0,cA1,xb,xc,cB,cC,Wd=None):
    Wd=W if Wd is None else Wd
    (aB,oB),(aC,oC)=pc(cB),pc(cC); Cm=np.zeros((16,16),complex)
    for xa,cA,first in ((0,cA0,0),(1,cA1,1)):
        aA,oA=pc(cA); w=y[B3.index((xa,xb,xc)),B3.index((aA,aB,aC))]
        if w: Cm+=w*emb(Wd[B3.index((oA,oB,oC))],first)/2
    return Cm
