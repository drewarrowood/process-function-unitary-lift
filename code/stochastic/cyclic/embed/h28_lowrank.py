"""Round 28 (H.35): low-rank rounding of a Hermitian SOS solve (h27_face.py output, gamma or margin mode) to an exact certificate.
Per weight block: eigenvectors of the numerical Q_b = N G N^dag with eigenvalue > THR are normalised (max entry 1), rationalised
(limit_denominator DEN), scaled to integer vectors w; coefficient mu = rationalised Rayleigh quotient w^T Q w / |w|^4.  Output: an
h27-format certificate (N = integer columns w, G = diag(mu)) at gamma = 0.  Nothing is trusted: verify with h27_chkA.py / h27_chkB.py.
usage: face_out.npz problem.json cert_out.json THR DEN"""
import numpy as np, sys, json, math
from fractions import Fraction as Fr
F=np.load(sys.argv[1]); D=json.load(open(sys.argv[2])); d=F['d']; x=F['x']; thr=float(sys.argv[4]); DEN=int(sys.argv[5])
def unsvec(v,m):
    X=np.zeros((m,m)); k=0
    for j in range(m):
        for i in range(j+1):
            X[i,j]=X[j,i]=v[k]*(1 if i==j else 1/np.sqrt(2)); k+=1
    return X
xo=1; out=[]
for b in range(len(D['blocks'])):
    bl=D['blocks'][b]; n=len(bl['basis']); cols=[]; mus=[]
    if d[b]:
        db=d[b]; m=2*db; s=m*(m+1)//2; X=unsvec(x[xo:xo+s],m); xo+=s
        G=X[:db,:db]+X[db:,db:]+1j*(X[db:,:db]-X[:db,db:]); N=F[f'N{b}']; Q=N@G@N.conj().T
        ev,U=np.linalg.eigh(Q)
        for k in np.where(ev>thr)[0]:
            u=U[:,k]; u=u/u[np.argmax(abs(u))]; assert np.abs(u.imag).max()<1e-4
            w=[Fr(float(t)).limit_denominator(DEN) for t in u.real]; L=1
            for t in w: L=math.lcm(L,t.denominator)
            wi=[int(t*L) for t in w]; wn=np.array(wi,float)
            mu=Fr(float(ev[k]/ (wn@wn) * 1)).limit_denominator(1000)   # lambda u u^T with u unit = lambda/|w|^2 w w^T
            # refine mu: lambda * |u_scaled|... use Rayleigh quotient of Q on w
            mu=Fr(float((wn@Q.real@wn)/(wn@wn)**2)).limit_denominator(1000)
            cols.append(wi); mus.append(mu)
    Nm=[[c[r] for c in cols] for r in range(n)] if cols else [[] for _ in range(n)]
    dd=len(cols)
    out.append(dict(S=bl['S'],wt=bl['wt'],basis=bl['basis'],N=Nm,Gr=[[str(mus[i] if i==j else 0) for j in range(dd)] for i in range(dd)],Gi=[['0']*dd for _ in range(dd)]))
    if cols: print(b,'mus',[str(t) for t in mus],'vec denominators ok')
json.dump(dict(orbit=D['orbit'],facet=D['facet'],gamma='0',blocks=out),open(sys.argv[3],'w'))
