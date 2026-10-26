"""Round 22 (H.29.3): general three-qubit PHASE processes D_o = diag(exp(i phi(o,z))) read in SU(2) frames, with the exact
validity condition of h22_copp.py.  The one-party conditions (S = {k}) say that phi has no o_k z_k interaction, so up to
o-independent phases (absorbed in psi) and z-independent phases (irrelevant), phi is a combination of the 12 mixed monomials
   o_k z_j (6),  o_k z_j z_l (3),  o_j o_k z_l (3)          ({j,k,l} = {0,1,2})
with real coefficients.  PF phase boards use only the first 9; the 3 monomials o_j o_k z_l are new.  We search the 12-torus
x frames x psi for valid points (pen = 0) minimising the facet.  usage: MODE(scan|search) ORBS seed NSTART"""
import sys, time, itertools as it, numpy as np, torch
from h22_copp import pen, facet_M
from h20_common import Tn, REP, canon, B3
torch.set_num_threads(1); torch.set_default_dtype(torch.float64)
MONO=[]
for k in range(3):
    for j in range(3):
        if j!=k: MONO.append(((k,),(j,)))
for k in range(3):
    j,l=[x for x in range(3) if x!=k]; MONO.append(((k,),(j,l)))
for l in range(3):
    j,k=[x for x in range(3) if x!=l]; MONO.append(((j,k),(l,)))
Mz=torch.tensor([[[float(all(B3[o][a] for a in m[0]) and all(B3[z][b] for b in m[1])) for z in range(8)] for o in range(8)] for m in MONO])  # [12,o,z]
def su2(t):
    a,b,c=t[0],t[1],t[2]
    return torch.stack([torch.stack([torch.cos(a)*torch.exp(1j*b), -torch.sin(a)*torch.exp(-1j*c)]),
                        torch.stack([torch.sin(a)*torch.exp(1j*c), torch.cos(a)*torch.exp(-1j*b)])])
def U_of(x):   # x: 12 coefficients, 9 frame angles
    phi=torch.einsum('m,moz->oz',x[:12],Mz); D=torch.exp(1j*phi)
    E=torch.kron(torch.kron(su2(x[12:15]),su2(x[15:18])),su2(x[18:21]))
    return E[None,:,:]*D[:,None,:]
if __name__=='__main__':
    mode=sys.argv[1]; ORBS=[int(a) for a in sys.argv[2].split(',')] if sys.argv[2]!='-' else []; seed=int(sys.argv[3]); NS=int(sys.argv[4])
    rng=np.random.default_rng(seed); t0=time.time()
    if mode=='scan':   # minimise pen alone from random starts; report the valid points' active monomials
        sols=[]
        for r in range(NS):
            x=torch.tensor(rng.uniform(-np.pi,np.pi,21),requires_grad=True)
            opt=torch.optim.LBFGS([x],max_iter=500,line_search_fn='strong_wolfe',tolerance_grad=1e-14,tolerance_change=1e-18)
            def clo():
                opt.zero_grad(); v=pen(U_of(x)); v.backward(); return v
            opt.step(clo); pv=float(pen(U_of(x.detach())))
            if pv<1e-16: sols.append(np.mod(x.detach().numpy()[:12]+np.pi,2*np.pi)-np.pi)
        sols=np.array(sols); print(f'{len(sols)}/{NS} starts reach pen<1e-16')
        if len(sols):
            new=np.abs(np.mod(sols[:,9:]+np.pi,2*np.pi)-np.pi)
            print('fraction of valid points with all o_j o_k z_l coefficients = 0 mod 2pi (|c|<1e-6):',np.mean((new<1e-6).all(1)))
            print('distinct values of the o_j o_k z_l coefficients /pi (rounded 1e-4):',sorted({tuple(np.round(r/np.pi,4)) for r in sols[:,9:]})[:20])
            print('distinct values of the 9 PF-type coefficients /pi mod 2 (rounded 1e-3), first 10:',sorted({tuple(np.round(np.mod(r/np.pi,2),3)) for r in sols[:,:9]})[:10])
        sys.exit()
    for orb in ORBS:
        f=REP[orb] if orb in REP else int(np.where(canon==orb)[0][0])
        Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64]); best=(9,9,None); hits=0
        for r in range(NS):
            x=torch.tensor(rng.uniform(-np.pi,np.pi,21),requires_grad=True); ps=torch.tensor(rng.normal(size=16),requires_grad=True)
            for mu in (1,10,100,1e3,1e4,1e5):
                opt=torch.optim.LBFGS([x,ps],max_iter=200,line_search_fn='strong_wolfe',tolerance_grad=1e-13,tolerance_change=1e-16)
                def clo():
                    opt.zero_grad(); U=U_of(x); psi=torch.complex(ps[:8],ps[8:])
                    v=torch.vdot(psi,facet_M(U,Tf,cf)@psi).real/torch.vdot(psi,psi).real+mu*pen(U); v.backward(); return v
                opt.step(clo)
            opt=torch.optim.LBFGS([x],max_iter=300,line_search_fn='strong_wolfe',tolerance_grad=1e-15,tolerance_change=1e-20)
            def clo2():
                opt.zero_grad(); v=pen(U_of(x)); v.backward(); return v
            opt.step(clo2)
            U=U_of(x.detach()); v=float(torch.linalg.eigvalsh(facet_M(U,Tf,cf))[0]); pv=float(pen(U))
            ok=pv<1e-14; hits+=ok and v<-1e-8
            if ok and v<best[0]: best=(v,pv,x.detach().numpy().copy()); np.save(f'/tmp/r22/pp_o{orb}_s{seed}.npy',best[2])
        b=best[2]; nz=None if b is None else np.round(np.mod(b[9:12]/np.pi+1,2)-1,4)
        print(f'orbit {orb} facet {f}: best lam {best[0]:.6e} (pen {best[1]:.1e}); valid starts below -1e-8: {hits}/{NS}; o_j o_k z_l coeffs/pi at best: {nz}; {time.time()-t0:.0f}s',flush=True)
