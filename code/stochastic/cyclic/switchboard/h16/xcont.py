"""H.16 goal 5 [numerical]: continuous X-type boards U_o = Hd diag(e^{i th_o(z)}) Hd.  For a never-crossed orbit,
maximise the violation -lambda_min(facet operator) of its representative facet(s), with a quadratic penalty on the
Pauli-rule residual (forbidden Fourier coefficients of e^{i(th_o-th_q)}), from the best Z_8 boards as starts.
Reports (violation, residual); a violation with residual ~1e-12 would be a candidate for exact certification."""
import numpy as np, itertools as it, gzip, sys, json
from scipy.optimize import minimize
orb=int(sys.argv[1]); nstart=int(sys.argv[2])
B3=list(it.product((0,1),repeat=3)); H=np.array([[(-1)**(sum(a*b for a,b in zip(x,y))%2) for y in B3] for x in B3]); Hd=H/8**.5
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
canon=np.load('../h13/xviol.npz')['canon'].astype(int)
fs=np.nonzero(canon==orb)[0]
vals=Zc@Hm[fs,:37].T+Hm[fs,37]; T=np.linalg.lstsq(np.c_[PF.reshape(744,-1),np.ones(744)],vals,rcond=None)[0].T/vals.max(0)[:,None]
BAD=[]
for o in range(8):
    for q in range(o+1,8):
        Dm=o^q; D=[t for t in range(3) if (Dm>>(2-t))&1]
        BAD.append((o,q,[ai for ai,a in enumerate(B3) if all(a[t] for t in D)]))
def boards(th):
    return np.stack([Hd@np.diag(np.exp(1j*th[o]))@Hd for o in range(8)])
def resid(th):
    r=0
    for o,q,bad in BAD:
        c=H[bad]@np.exp(1j*(th[o]-th[q]))/8; r+=np.sum(np.abs(c)**2)
    return r
def violv(th):
    U=boards(th); P=np.einsum('ois,oit->iost',U.conj(),U).reshape(64,8,8)
    return -np.linalg.eigvalsh(np.einsum('fr,rst->fst',T[:,:64],P)+T[:,64,None,None]*np.eye(8))[:,0]
z8=np.load('../h13/xreps_z8.npy').astype(np.int64)
sc=np.array([violv(2*np.pi*b/8).max() for b in z8]); starts=np.argsort(-sc)[:nstart]
out=[]; rng=np.random.default_rng(orb)
for s in starts:
    th=(2*np.pi*z8[s]/8).astype(float); fi=int(np.argmax(violv(th)))
    for mu in [10,100,1e3,1e4,1e5,1e6]:
        f=lambda x:-violv(x.reshape(8,8))[fi]+mu*resid(x.reshape(8,8))
        th=minimize(f,th.ravel()+1e-3*rng.standard_normal(64),method='L-BFGS-B').x.reshape(8,8)
    out.append((float(violv(th)[fi]),float(resid(th)),float(sc[s])))
out.sort(key=lambda x:-x[0])
print('orbit',orb,'start best Z8',float(sc[starts[0]]),'best after (viol,resid,start):',out[:3],flush=True)
