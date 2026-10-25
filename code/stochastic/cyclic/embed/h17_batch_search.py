"""Round 17 (H.24.1, achievable side): massively parallel local search for min y_A.P on H.12 over all products of
4-outcome qubit POVMs {E^k_{a,o|x}} (by H.15.7d these exhaust all local instruments on this board, ancillas included).
Each POVM is E_j = S^{-1/2} A_j^dag A_j S^{-1/2}, S = sum A_j^dag A_j, A_j complex 2x2 (or 1x2 = rank-one) free parameters.
Batched Adam over many random starts in torch.  Usage: h17_batch_search.py seed batch rounds [rank1]   [NUMERICAL]"""
import sys, re, itertools as it, numpy as np, torch
torch.set_num_threads(2)
seed,BATCH,ROUNDS=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]); R1='rank1' in sys.argv
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/8**.5
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/2**.5; ph[4]=(1-1j)/2
psi=np.array([U[o]@ph for o in range(8)])
y=np.array(eval(re.search(r'\[.*?\]',open('instr2_exact.log').readline()).group()),float).reshape(8,8)
PS=torch.tensor(psi.reshape(2,2,2,2,2,2),dtype=torch.complex128)        # (oA,oB,oC,i,j,k)
Y=torch.tensor(y.reshape(2,2,2,2,2,2),dtype=torch.float64)              # (xA,xB,xC,aA,aB,aC)
def povms(th):   # th: (B,3,2,4,r,2) complex -> E (B,3,2,4,2,2) with E[...,c] for c=2a+o
    A=th; E=torch.einsum('...jri,...jrl->...jil',A.conj(),A); S=E.sum(-3)
    w,V=torch.linalg.eigh(S); Si=V@torch.diag_embed(w.clamp_min(1e-12)**-.5).to(V.dtype)@V.conj().transpose(-1,-2)
    return torch.einsum('...il,...jlm,...mn->...jin',Si,E,Si)
def value(E):
    EA=E[:,0].reshape(-1,2,2,2,2,2); EB=E[:,1].reshape(-1,2,2,2,2,2); EC=E[:,2].reshape(-1,2,2,2,2,2)   # (B,x,a,o,i,l)
    P=torch.einsum('pqrijk,bxapil,bycqjm,bzdrkn,pqrlmn->bxyzacd',PS.conj(),EA,EB,EC,PS).real
    return (P*Y).sum((1,2,3,4,5,6))
g=torch.Generator().manual_seed(seed); best=9; r=1 if R1 else 2
for rd in range(ROUNDS):
    th=(torch.randn(BATCH,3,2,4,r,2,generator=g,dtype=torch.float64)+1j*torch.randn(BATCH,3,2,4,r,2,generator=g,dtype=torch.float64)).requires_grad_()
    opt=torch.optim.Adam([th],lr=0.05)
    for st in range(1500):
        opt.zero_grad(); v=value(povms(th)); v.sum().backward(); opt.step()
        if st==1000:
            for gp in opt.param_groups: gp['lr']=0.01
    v=value(povms(th)).detach(); i=int(v.argmin()); vals=np.sort(v.numpy())
    if v[i]<best: best=float(v[i]); torch.save(povms(th)[i].detach(),f'/tmp/r17/batch_best_{seed}{"_r1" if R1 else ""}.pt')
    print(f'seed {seed} round {rd}: min {vals[0]:.6f}, 5 smallest {np.round(vals[:5],5).tolist()}, frac within 1e-3 of min {(vals<vals[0]+1e-3).mean():.3f}; best {best:.6f}',flush=True)
