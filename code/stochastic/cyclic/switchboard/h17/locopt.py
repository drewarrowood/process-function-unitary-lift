"""H.17.6 continuous part [numerical]: maximise the never-crossed facet violation over L = L_A (x) L_B (x) L_C in SU(2)^3
applied on the left of Z_4 X-type boards.  The Pauli rule is preserved EXACTLY for every L (so purity is not an issue);
any value clearly above round-off would be a genuine violation, to be certified."""
import sys, json, time
from lib3 import *
from scipy.optimize import minimize
sh=int(sys.argv[1]); ns=int(sys.argv[2]); rng=np.random.default_rng(sh)
T,canon=load_facets(); sel=np.nonzero(np.isin(canon,NC[:-1]))[0]; Ts=T[sel]      # orbit 92 (positivity) excluded
B=np.load('../h13/xreps_z8.npy').astype(np.int64); B=B[(B%2==0).all((1,2))][sh::ns]
Hd=np.array([[(-1)**bin(x&y).count('1') for y in range(8)] for x in range(8)])/8**.5; zeta=np.exp(2j*np.pi/8)
X=np.array([[0,1],[1,0]]);Y=np.array([[0,-1j],[1j,0]]);Z=np.diag([1.,-1])
def su2(a,b,c):
    e=lambda t,P: np.cos(t)*np.eye(2)-1j*np.sin(t)*P
    return e(a,Z)@e(b,Y)@e(c,Z)
def viol(x,U0):
    L=np.kron(np.kron(su2(*x[0:3]),su2(*x[3:6])),su2(*x[6:9]))
    P=projectors(np.einsum('ij,ojk->oik',L,U0))
    return float((-np.linalg.eigvalsh(np.einsum('fr,rst->fst',Ts[:,:64],P)+Ts[:,64,None,None]*np.eye(8))[:,0]).max())
best=-1; t0=time.time()
for n,b in enumerate(B):
    U0=np.stack([Hd@np.diag(zeta**b[o])@Hd for o in range(8)])
    for st in range(2):
        r=minimize(lambda x:-viol(x,U0),rng.uniform(0,np.pi,9),method='Nelder-Mead',options=dict(maxfev=1500,xatol=1e-6,fatol=1e-12))
        if -r.fun>best: best=-r.fun; arg=(int(n*ns+sh),r.x.tolist())
    print(n,len(B),round(time.time()-t0),best,flush=True)
    if time.time()-t0>950: break
print('final best',best); json.dump(dict(best=best,arg=arg),open('locopt_%d.json'%sh,'w'))
