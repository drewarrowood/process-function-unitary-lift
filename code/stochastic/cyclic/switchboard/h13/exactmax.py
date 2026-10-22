"""H.14.3 EXACT per-orbit maximum violation over Z_4 X-type boards and all source states.
For the best (board class, facet) per orbit (from xviol.npz, float screen), the max violation over phi is
-lambda_min(F), F = sum g P_{o,i} + g0 in Q(i)^{8x8}; we give the exact minimal polynomial of lambda_min (sympy)."""
import flint, numpy as np, itertools as it, gzip, sympy as sp, json
from xenum import D4, B3
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(int); Zc=np.load(F+'Z.npy').astype(int)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))])
vals=Zc@Hm[:,:37].T+Hm[:,37]
d=np.load('xviol.npz'); V=d['viol']; canon=d['canon']; R=np.load('xreps.npy').astype(int)
A=sp.Matrix(np.c_[PF.reshape(744,-1),np.ones(744,int)].tolist())
Hd=sp.Matrix(8,8,lambda x,y:(-1)**(sum(a*b for a,b in zip(B3[x],B3[y]))%2))
Tf=np.linalg.lstsq(np.c_[PF.reshape(744,-1),np.ones(744)],vals.astype(float),rcond=None)[0].T
out={}
done={int(l.split()[0]) for l in open('exactmax_part1.log') if l[:1].isdigit()}
for orb in [o for o in np.nonzero(V.max(0)>1e-9)[0] if o not in done]:
    n=int(V[:,orb].argmax()); m=D4[R[n]]
    U=[Hd*sp.diag(*[sp.I**int(x) for x in m[o]])*Hd/8 for o in range(8)]
    Uf=np.array([np.array(u.evalf(),dtype=complex) for u in U])
    P=np.einsum('ois,oit->iost',Uf.conj(),Uf).reshape(64,8,8)
    fs=np.nonzero(canon==orb)[0]; Fm=np.einsum('fr,rst->fst',Tf[fs,:64],P)+Tf[fs,64,None,None]*np.eye(8)
    f=int(fs[np.linalg.eigvalsh(Fm)[:,0].argmin()])
    # exact g: solve A g = vals[:,f] (consistent, rank 38); pick particular solution via sympy
    M=flint.fmpq_mat(744,66,[int(x) for row in np.c_[PF.reshape(744,-1),np.ones(744,int),vals[:,f]] for x in row])
    RR,rk=M.rref(); g=[sp.Integer(0)]*65
    for r in range(rk):
        piv=next(c for c in range(66) if RR[r,c]!=0); assert piv<65; g[piv]=sp.Rational(int(RR[r,65].p),int(RR[r,65].q))
    assert (A*sp.Matrix(g)-sp.Matrix(vals[:,f].tolist())).is_zero_matrix
    Fx=sum((g[r]*(U[r%8].H*sp.Matrix(8,8,lambda a,b:int(a==b==r//8))*U[r%8]) for r in range(64)),sp.zeros(8))+g[64]*sp.eye(8)
    Fx=Fx.applyfunc(sp.expand)
    Mr=flint.fmpq_mat(16,16,[0]*256)
    for i in range(8):
        for j in range(8):
            re,im=sp.re(Fx[i,j]),sp.im(Fx[i,j])
            for (di,dj,v) in ((0,0,re),(8,8,re),(0,8,-im),(8,0,im)):
                q=sp.Rational(v); Mr[i+di,j+dj]=flint.fmpq(int(q.p),int(q.q))
    cpq=Mr.charpoly(); den=1
    for c in cpq.coeffs(): den=den*int(c.q)//__import__('math').gcd(den,int(c.q))
    cpz=flint.fmpz_poly([int(c*den) for c in cpq.coeffs()])
    x=sp.symbols('x'); rng=int(vals[:,f].max()); best=None
    for fac,_ in cpz.factor()[1]:
        P=sp.Poly(list(reversed([int(c) for c in fac.coeffs()])),x)
        for r in P.real_roots():
            if best is None or float(r)<float(best[0]): best=(r,P.as_expr())
    out[int(orb)]=dict(class_=n,facet=f,range=rng,lam_min=str(best[1])+' root '+str(sp.N(best[0],12)),relviol=float(-best[0]/rng))
    print(orb,out[int(orb)],flush=True)
json.dump(out,open('exactmax_z4_part2.json','w'),indent=0)
