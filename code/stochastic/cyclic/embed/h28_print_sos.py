"""Round 28 (H.35): print an exact h27/h28-format certificate as an explicit list of weighted Hermitian squares
p - gamma|psi|^2 prod|xi_k|^2 = sum_terms mu * | sum_r w_r v_S[r] |^2  (only for diagonal G, as produced by h28_lowrank.py).
v_S[r] = psi_z * prod_k xi_k[b_k] (k not in S) or conj(xi_k[b_k]) (k in S) * u^m;  written  psi_z . x0[b0] x1*[b1] ... . u^(m).
usage: cert.json[.gz]"""
import sys, json, gzip
from fractions import Fraction as F
import h26_hsos as H
op=gzip.open if sys.argv[1].endswith('.gz') else open
C=json.load(op(sys.argv[1],'rt')); B=H.basis(); nt=0
print('orbit',C['orbit'],'facet',C['facet'],'gamma',C['gamma'])
for bl in C['blocks']:
    Nm=bl['N']; d=len(Nm[0]) if Nm and Nm[0] else 0
    if d==0: continue
    S=bl['S']; assert all(F(bl['Gr'][i][j])==0 for i in range(d) for j in range(d) if i!=j) and all(F(x)==0 for r in bl['Gi'] for x in r)
    for c in range(d):
        mu=F(bl['Gr'][c][c]); terms=[]
        for r,idx in enumerate(bl['basis']):
            w=Nm[r][c]
            if w==0: continue
            z,a,m=B[idx]; b=H.B3[a]
            xs=' '.join(f"x{k}{'*' if (S>>k)&1 else ''}[{b[k]}]" for k in range(3))
            terms.append(f"{w:+d} psi{z}.{xs}.u^{tuple(m)}")
        nt+=1; print(f"S={S} wt={bl['wt']}  {mu} * | {' '.join(terms)} |^2")
print('total squares',nt)
