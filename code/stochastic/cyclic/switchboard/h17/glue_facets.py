"""H.17.17 angle 1: how many corners (outputs o) must a hull facet touch?  A facet g.p + g0 >= 0 is only defined modulo
the affine-hull equalities of conv(PF) (rank 27 on the 64 coordinates p(i|o) plus the constant).  For every facet we
compute the smallest set S of corners such that some equivalent representative g + e (e in the equality space) has all
coefficients outside S equal to zero ("corner support").  Exact in rank arithmetic up to float tolerance 1e-9."""
import gzip, itertools as it, numpy as np
B3=list(it.product((0,1),repeat=3))
Z=np.load('../../../physics/facets/Z.npy').astype(float); PF=np.load('../../pfs744.npy').reshape(744,-1).astype(float)
A1=np.c_[PF,np.ones(744)]; T=np.linalg.lstsq(A1,Z,rcond=None)[0]
L=gzip.open('../../../physics/facets/pf.out.gz','rt').read().split('\n')
k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:')); n=int(L[k].split()[0])
H=np.array([list(map(int,L[k+1+j].split())) for j in range(n)],float); Af,bf=H[:,:37],H[:,37]
g=(T[:64]@Af.T).T.reshape(n,8,8); g0=T[64]@Af.T+bf          # g[f,i,o]
assert (np.einsum('fio,mio->fm',g,PF.reshape(744,8,8))+g0[:,None]).min()>-1e-9
# equality space: vectors (c,c0) with PF@c + c0 = 0  -> null space of A1
u,s,vt=np.linalg.svd(A1); r=(s>1e-9).sum(); E=vt[r:]          # rows: (c[64], c0)
print('facets',n,'equality space dim',E.shape[0])
Ec=E[:,:64].reshape(-1,8,8)                                     # [e,i,o]
best=np.full(n,9); bestS=[None]*n
for m in range(0,9):
    for S in it.combinations(range(8),m):
        out=[o for o in range(8) if o not in S]
        if not out: ok=np.ones(n,bool)
        else:
            Eo=Ec[:,:,out].reshape(E.shape[0],-1)               # rows span allowed corrections on out-coords
            q,rr=np.linalg.qr(Eo.T); keep=np.abs(np.diag(rr))>1e-9 if rr.size else []
            Q=q[:,keep] if len(keep) else np.zeros((Eo.shape[1],0))
            Go=-g[:,:,out].reshape(n,-1)                        # need e_out = -g_out
            res=Go-(Go@Q)@Q.T; ok=np.abs(res).max(1)<1e-7
        new=ok&(best==9); best[new]=m
        for f in np.where(new)[0]: bestS[f]=S
    if (best<9).all(): break
vals,cnt=np.unique(best,return_counts=True)
print('minimal corner support size -> number of facets:',dict(zip(vals.tolist(),cnt.tolist())))
np.save('glue_facets_support.npy',best)
# which facets do the known non-blends violate (min over source states), and how many corners do those facets need?
import json
par=lambda x:bin(x).count('1')&1
m=json.load(open('../h13/min_cex.json'))['m']
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/np.sqrt(8)
U13=[Hd@np.diag([(-1)**(m[o][z]//2) for z in range(8)])@Hd for o in range(8)]
def violated(U,name):
    Pr=np.array([[np.outer(U[o][i].conj(),U[o][i]) for i in range(8)] for o in range(8)])   # P_{o,i} = U^dag|i><i|U
    lm=np.empty(n)
    for f0 in range(0,n,4000):
        M=np.einsum('fio,oiab->fab',g[f0:f0+4000],Pr)+g0[f0:f0+4000,None,None]*np.eye(8)
        lm[f0:f0+4000]=np.linalg.eigvalsh(M)[:,0]
    V=np.where(lm<-1e-9)[0]
    vals,cnt=np.unique(best[V],return_counts=True)
    print(name,': violated facets',len(V),'; corner-support sizes of violated facets:',dict(zip(vals.tolist(),cnt.tolist())),'; min lambda %.4f'%lm.min())
violated(U13,'H.13.2 (4-term)')
violated([np.eye(8)]*8,'sanity: constant identity board (must be 0)')
print('facet 16962 (the H.13.2 certificate) corner support',best[16962],bestS[16962])
