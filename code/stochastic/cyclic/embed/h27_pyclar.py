"""Round 27 (H.34.2): Float64 cross-check of the symmetry-reduced Hermitian SOS (h27_export.py JSON) with the Rust Clarabel (python). usage: problem.json"""
import json, sys, numpy as np, scipy.sparse as sp, clarabel, time
from fractions import Fraction as F
D=json.load(open(sys.argv[1])); nb=[len(b['basis']) for b in D['blocks']]; m=[2*n for n in nb]; sv=[x*(x+1)//2 for x in m]
off=np.cumsum([1]+sv[:-1]); nx=1+sum(sv); r2=1/np.sqrt(2)
def sidx(bi,i,j):
    i,j=min(i,j),max(i,j); return off[bi]+j*(j+1)//2+i,(1.0 if i==j else r2)
I=[];J=[];V=[];b=[]
for ri,row in enumerate(D['rows']):
    acc={}
    for bi,r,s in row['terms']:
        n=nb[bi]; pairs=((r,s,1),(n+r,n+s,1)) if row['part']=='re' else ((n+r,s,1),(r,n+s,-1))
        for i,j,sg in pairs:
            k,cf=sidx(bi,i,j); acc[k]=acc.get(k,0)+sg*cf
    nv=float(F(row['nv']))
    if nv: acc[0]=nv
    for k,v in acc.items():
        if v: I.append(ri);J.append(k);V.append(v)
    b.append(float(F(row['rhs'])))
m0=len(D['rows'])
I+=list(range(m0,m0+nx-1)); J+=list(range(1,nx)); V+=[-1.0]*(nx-1)
A=sp.csc_matrix((V,(I,J)),shape=(m0+nx-1,nx)); bb=np.r_[b,np.zeros(nx-1)]
q=np.zeros(nx); q[0]=-1; P=sp.csc_matrix((nx,nx))
cones=[clarabel.ZeroConeT(m0)]+[clarabel.PSDTriangleConeT(x) for x in m]
st=clarabel.DefaultSettings(); st.verbose=False; st.tol_gap_abs=st.tol_gap_rel=st.tol_feas=1e-10
t=time.time(); s=clarabel.DefaultSolver(P,q,A,bb,cones,st); sol=s.solve()
print(D['orbit'], sol.status, 'gamma*=',sol.x[0], f'{time.time()-t:.1f}s')
