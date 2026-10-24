"""H.15.7d(B''): reproduce the best H.12 point of instr_search2 (seed 3), save it, and verify independently:
(1) correlation recomputed from the process matrix W = Tr_F |V>><<V| (Choi of the purification, past input = H.12 source) and
    instrument Choi operators M_{a|x} = sum_o (E_{a,o|x})^T (x) |o><o|;  (2) row normalisation; (3) the violated inequality y checked
    against all 138,304 deterministic causal strategies (y has entries in (1/64)Z, so this check is exact up to float sums of
    small rationals); (4) robustness LP."""
import sys, numpy as np, itertools as it, json
sys.argv=[sys.argv[0]]
import instr_search2 as S, instr_search as IS
from fractions import Fraction as Fr
B3=IS.B3; Hd=IS.Hd
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U12=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/np.sqrt(2); ph[4]=np.exp(-1j*np.pi/4)/np.sqrt(2)
psis=np.array([U12[o]@ph for o in range(8)])
m=json.load(open('../switchboard/h13/min_cex.json'))['m']
U13=np.array([Hd@np.diag([(-1)**(m[o][x]//2) for x in range(8)])@Hd for o in range(8)])
psiA=np.array([1,1,1,0,0,-1,0,0])/2; psiB=np.array([1,1,1,0,0,0,0,0])/np.sqrt(3); lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
Y=[]
for p in ([[abs((U13[o]@psiA)[i])**2 for i in range(8)] for o in range(8)],[[abs((U13[o]@psiB)[i])**2 for i in range(8)] for o in range(8)],
          [[float(B3[i]==lug(*B3[o])) for i in range(8)] for o in range(8)]):
    Y+=S.images(S.farkas(np.array(p)))
Y=np.unique(np.round(np.array(Y),9),axis=0)
best=S.run('H.12 switchboard (reproduce seed 3)',psis,[3],Y,3)
v,th,sd,r=best; np.save('instr2_h12_best.npy',th)
P=S.corr(psis,th); y=Y[np.argmin(Y@P.ravel())]
# (1) independent recomputation via process matrix, ordering AI1 AO1 AI2 AO2 AI3 AO3
Wt=np.zeros((2,)*12,complex)   # W[ai1,ao1,ai2,ao2,ai3,ao3 ; same]'
psi6=np.zeros((2,)*6,complex)
for o,oo in enumerate(B3):
    for i,ii in enumerate(B3): psi6[ii[0],oo[0],ii[1],oo[1],ii[2],oo[2]]=psis[o][i]
# W = sum_o |psi_o><psi_o| (x) |o><o|  (diagonal in o: F traced out)
W=np.zeros((64,64),complex)
for o,oo in enumerate(B3):
    vec=np.zeros((2,)*6,complex)
    for i,ii in enumerate(B3): vec[ii[0],oo[0],ii[1],oo[1],ii[2],oo[2]]=psis[o][i]
    vv=vec.ravel(); W+=np.outer(vv,vv.conj())
print('Tr W =',np.trace(W).real.round(12))
def Mchoi(E,a):   # E: (4,2,2) POVM, index 2a+o
    M=np.zeros((4,4),complex)
    for o in (0,1): M+=np.kron(E[2*a+o].T,np.diag([1-o,o]))
    return M
P2=np.zeros((8,8))
for xi,x in enumerate(B3):
    Es=[S.povm(th[32*(2*k+x[k]):32*(2*k+x[k]+1)]) for k in range(3)]
    for ai,a in enumerate(B3):
        M=np.kron(np.kron(Mchoi(Es[0],a[0]),Mchoi(Es[1],a[1])),Mchoi(Es[2],a[2]))
        P2[xi,ai]=np.trace(W@M.T).real
print('max |P(einsum) - P(process matrix)| =',np.abs(P-P2).max(),'; rows sum to',P2.sum(1).round(12),'; min entry',P2.min())
VA=IS.A.toarray(); yr=[Fr(float(t)).limit_denominator(64) for t in y]
print('violated inequality: denominators',sorted({q.denominator for q in yr}),'; min over all causal strategies =',(y@VA).min(),
      '; value on P =',y@P2.ravel())
print('robustness LP t =',IS.robust(P2))
