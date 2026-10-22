# Appendix H(C): counterexample hunt from the unitary side.
# Optimise a 64x64 unitary U : O(x)P -> I(x)F (P=F=C^8, source |0>) for (i) purity under random local
# unitaries with qubit ancillas, (ii) classicality of the induced process W, (iii) violation of a PF-hull facet.
import sys, torch, numpy as np, itertools as it, json
torch.set_num_threads(int(sys.argv[3]) if len(sys.argv)>3 else 4)
seed=int(sys.argv[1]); steps=int(sys.argv[2]); torch.manual_seed(seed); np.random.seed(seed)
c=torch.complex128; B3=list(it.product((0,1),repeat=3)); ix={t:n for n,t in enumerate(B3)}
def haar(n,k):
    z=torch.randn(k,n,n,dtype=c); q,r=torch.linalg.qr(z); d=torch.diagonal(r,dim1=1,dim2=2); return q*(d/d.abs()).unsqueeze(1)
def Vfull(Vs):  # Vs: 3 matrices (o_k y_k),(i_k x_k), dim 2*dx
    d=Vs[0].shape[0]//2; T=torch.einsum('ab,cd,ef->acebdf',*Vs)  # (o1y1,o2y2,o3y3,i1x1,...)
    T=T.reshape(2,d,2,d,2,d,2,d,2,d,2,d).permute(0,2,4,1,3,5,6,8,10,7,9,11)
    return T.reshape(8,d**3,8,d**3)  # [o,y,i,x]
# facet orbit 82 representative, p(i|o): p(000|000) <= p(000|001)+p(010|001)+p(000|100)+p(010|110)+p(011|111)
fac=[(1,'000','000')]+[(-1,i,o) for i,o in [('000','001'),('010','001'),('000','100'),('010','110'),('011','111')]]
# random symmetry: party permutation + input/output bit flips (these preserve the PF set)
perm=list(np.random.permutation(3)); fi=np.random.randint(0,2,3); fo=np.random.randint(0,2,3)
def tr(s,fl): b=[int(ch) for ch in s]; b=[b[perm[k]] for k in range(3)]; return tuple(int(b[k]^fl[k]) for k in range(3))
facet=[(s,ix[tr(i,fi)],ix[tr(o,fo)]) for s,i,o in fac]
INIT=sys.argv[4] if len(sys.argv)>4 else 'rand'
if INIT=='lug':
    lug=lambda o:((1-o[1])&o[2],(1-o[2])&o[0],(1-o[0])&o[1])
    U0=np.zeros((8,8,8,8),complex)  # [i,f,o,e]
    for o in B3:
        for e in B3: U0[ix[tuple((lug(o)[k]+e[k])%2 for k in range(3))],ix[o],ix[o],ix[e]]=1
    U0=U0.reshape(64,64)
    # choose the facet image that is tight (=0) at Lugano, if any
    pl=np.zeros((8,8))
    for o in B3: pl[ix[lug(o)],ix[o]]=1
    best=None
    for pm in it.permutations(range(3)):
        for a in it.product((0,1),repeat=3):
            for b in it.product((0,1),repeat=3):
                perm=list(pm); F=[(s_,ix[tr(i,a)],ix[tr(o,b)]) for s_,i,o in fac]
                v=sum(s_*pl[i,o] for s_,i,o in F)
                if abs(v)<1e-12 and best is None: best=F
    facet=best; print('facet tight at Lugano found:',best is not None,flush=True)
H=torch.randn(64,64,dtype=c)*(0.3 if INIT=='rand' else 0.02); H=(H+H.conj().T)/2; H.requires_grad_()
U0=torch.tensor(U0) if INIT=='lug' else torch.eye(64,dtype=c)
opt=torch.optim.Adam([H],lr=0.01 if INIT=='rand' else 0.002)
def stuff(U,nsamp,dx):
    T=U.reshape(8,8,8,8)  # [i,f,o,e]
    loss=0
    for s in range(nsamp):
        Vs=[haar(2*dx,1)[0] for _ in range(3)]; V=Vfull(Vs)
        M=torch.einsum('ifoe,oyix->fyex',T,V).reshape(8*dx**3,8*dx**3)
        loss=loss+((M@M.conj().T-torch.eye(8*dx**3,dtype=c)).abs()**2).sum()
    v=T[:,:,:,0]          # v[i,f,o] = <i,f|U|o,0>
    W=torch.einsum('ifo,jfp->iojp',v,v.conj()).reshape(64,64)  # ((i,o),(i',o'))
    p=torch.diagonal(W).real.reshape(8,8)  # p[i,o]
    off=(W.abs()**2).sum()-(torch.diagonal(W).abs()**2).sum()
    f=sum(s*p[i,o] for s,i,o in facet)
    return loss,off,f,p
for t in range(steps):
    U=U0@torch.matrix_exp(1j*H)
    pur,off,f,p=stuff(U,2,1 if t%2 else 2)
    loss=(pur+10*off-0.3*f) if INIT=='rand' else (100*pur+1000*off-f)
    opt.zero_grad(); loss.backward(); opt.step()
    if t%500==0: print(seed,t,'pur',float(pur),'off',float(off),'facet',float(f),flush=True)
with torch.no_grad():
    U=U0@torch.matrix_exp(1j*H); pur,off,f,p=stuff(U,20,2); pur1,_,_,_=stuff(U,20,1)
out=dict(seed=seed,purity_residual_anc=float(pur),purity_residual_noanc=float(pur1),offdiag=float(off),facet=float(f))
print('FINAL',json.dumps(out),flush=True)
np.save('hunt_U_%d.npy'%seed,U.numpy()); np.save('hunt_p_%d.npy'%seed,p.numpy())
