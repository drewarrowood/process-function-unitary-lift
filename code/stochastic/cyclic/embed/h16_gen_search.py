"""Round 16: penalty search over ALL pure processes V: AO(3q) x P(8) -> AI(3q) x F(8), unitary by construction,
validity of Tr_F |V>><<V| imposed by a penalty (Araujo et al. 2015 projector).  Objective: largest relative
violation of a facet in the open orbits, maximised over the source state."""
import itertools as it, numpy as np, gzip, sys, os, torch
torch.set_num_threads(1)
E='./'
seed=int(sys.argv[1]); iters=int(sys.argv[2]); start=sys.argv[3] if len(sys.argv)>3 else 'rand'
rng=np.random.default_rng(seed); torch.manual_seed(seed)
F=E+'../../physics/facets/'
PF=np.load(E+'../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]; A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T; Tn=T/vals.max(0)[:,None]
canon=np.load(E+'../switchboard/h13/xviol.npz')['canon'].astype(int)
OPEN=[int(x) for x in os.environ.get('ORBITS','26,28,30,31,54,57,66,69,75,81').split(',')]
sel=np.isin(canon,OPEN); Ts=torch.tensor(Tn[sel]); cs=canon[sel]
Tl=Ts[:,:64].to(torch.complex128); Tc=Ts[:,64].to(torch.complex128)
I8=torch.eye(8,dtype=torch.complex128)
def forms(V):
    W=V.reshape(8,8,8,8); return torch.einsum('ifos,ifot->iost',W.conj(),W).reshape(64,8,8)
def violations(V):
    P=forms(V); Fm=torch.einsum('fr,rst->fst',Tl,P)+Tc[:,None,None]*I8
    return -torch.linalg.eigvalsh(Fm)[:,0]
# W' on (AI_A,AI_B,AI_C, AO_A,AO_B,AO_C, P8): tensor indices r: iA iB iC oA oB oC s ; c: same primed
def choi(V):
    W=V.reshape(2,2,2,8,2,2,2,8)   # iA iB iC f oA oB oC s
    return torch.einsum('abcfxyzs,ABCfXYZS->abcxyzsABCXYZS',W,W.conj())
def tr_rep(W,axes):  # {}_X : trace over listed axes (0..6) and replace by identity/d
    n=7
    for a in axes:
        d=W.shape[a]
        t=torch.diagonal(W,dim1=a,dim2=a+n).sum(-1)   # removes axes a and a+n
        # reinsert as identity/d
        t=t.unsqueeze(a); t=t.unsqueeze(a+n)
        eye=torch.eye(d,dtype=W.dtype).reshape([d if j==a else 1 for j in range(n)]+[d if j==a else 1 for j in range(n)])
        W=t*eye/d
    return W
IN={0:0,1:1,2:2}; OUT={0:3,1:4,2:5}
def penalty(V):
    W=choi(V); tot=torch.zeros_like(W)
    for ch in it.product(range(3),repeat=3):
        sgn=1.; ax=[]
        for kk,c in enumerate(ch):
            if c==1: sgn=-sgn; ax.append(OUT[kk])
            if c==2: ax+= [IN[kk],OUT[kk]]
        tot=tot+sgn*tr_rep(W,ax)
    D=tot-tr_rep(W,list(range(7)))
    return (D.abs()**2).sum()
if __name__=='__main__':
    from h16_lugboard import board
    th=rng.uniform(0,2*np.pi,30)
    for rev in (0,1):
        Vb=torch.tensor(board(th,rev)); print('board rev',rev,'penalty',float(penalty(Vb)),'viol',float(violations(Vb).max()))
    Hr=rng.normal(size=(64,64))+1j*rng.normal(size=(64,64)); Hr=Hr+Hr.conj().T
    print('random U penalty',float(penalty(torch.linalg.matrix_exp(1j*torch.tensor(Hr)))))
