"""Round 28 (H.35): independent floating-point cross-check of an exact diagonal certificate against the facet value itself
(not via h26_hsos.poly): at random (a,t,p), build the 8x8 Hermitian form in psi of sum mu |sum_r w_r v_S[r]|^2 and compare its
smallest eigenvalue with h24_lugsearch.lam (= lambda_min(M) + c).  usage: cert.json[.gz] NPTS seed"""
import sys, json, gzip, numpy as np, torch
from fractions import Fraction as F
import h26_hsos as H
from h24_lugsearch import lam
from h20_common import Tn, canon
torch.set_default_dtype(torch.float64)
op=gzip.open if sys.argv[1].endswith('.gz') else open
C=json.load(op(sys.argv[1],'rt')); B=H.basis(); orb=C['orbit']; f=int(np.where(canon==orb)[0][0])
Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64]); rng=np.random.default_rng(int(sys.argv[3])); err=0
for _ in range(int(sys.argv[2])):
    th=rng.uniform(-np.pi,np.pi,9); a,t,p=th[:3],th[3:6],th[6:]
    u=np.exp(1j*a); xi=[np.array([np.cos(t[k]/2),np.sin(t[k]/2)*np.exp(1j*p[k])]) for k in range(3)]
    Mq=np.zeros((8,8),complex)
    for bl in C['blocks']:
        Nm=bl['N']; d=len(Nm[0]) if Nm and Nm[0] else 0; S=bl['S']
        for c in range(d):
            row=np.zeros(8,complex)
            for r,idx in enumerate(bl['basis']):
                w=Nm[r][c]
                if w==0: continue
                z,aa,m=B[idx]; b=H.B3[aa]; val=w*np.prod([xi[k][b[k]].conj() if (S>>k)&1 else xi[k][b[k]] for k in range(3)])*np.prod([u[k]**m[k] for k in range(3)])
                row[z]+=val
            Mq+=float(F(bl['Gr'][c][c]))*np.outer(row.conj(),row)
    l1=np.linalg.eigvalsh(Mq)[0]; l2=float(lam(torch.tensor(th)[None],Tf,cf)[0]); err=max(err,abs(l1-l2))
print('orbit',orb,'points',sys.argv[2],'max |lambda_min(SOS form) - facet value| =',err)
