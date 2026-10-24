"""H.17.17 Lemma D check [numerical]: on every saved tuned board (tb_*.npz, tb4_*.npz) and every absorbed vertex r, the
refined SH_grp^r test of H.17.11a computed from the full matrices W_o = U_o U_r^dag agrees, pair by pair, with the local
formula of Lemma D, which only uses the class labels, the class-pair supports S_{c,c'} = supp(V_c V_c'^dag) and x(P_o):
  pair (o,q) fails  iff  V_{k(o)} V_{k(q)}^dag is not X-monomial and
                         x(P_o + P_q) + aff X(S_{k(o),k(r)}) + aff X(S_{k(q),k(r)}) contains a vector covering D = o+q."""
import glob, numpy as np
from lib3 import *
def supp(K,tol=1e-9): c=pauli_coeffs(K); return [s for s in range(64) if abs(c[s])>tol]
def aff(xs):
    xs=list(xs); x0=xs[0]; H={0}
    for x in xs: H|={h^x^x0 for h in H}
    return {x0^h for h in H}
files=sorted(glob.glob('tb_*.npz')+glob.glob('tb4_*.npz')); pairs=agree=0; boards_fail_all=0; kmax=0
for f in files:
    U=np.load(f)['U']
    # classes: o,q same class iff U_o U_q^dag is a single Pauli string; P_o relative to the class representative
    cls={}; P={}; rep=[]
    for o in range(8):
        for c,ro in enumerate(rep):
            s=supp(U[o]@U[ro].conj().T)
            if len(s)==1: cls[o]=c; P[o]=s[0]; break
        else: cls[o]=len(rep); rep.append(o); P[o]=0
    kmax=max(kmax,len(rep))
    S={(a,b):supp(U[rep[a]]@U[rep[b]].conj().T) for a in range(len(rep)) for b in range(len(rep))}
    allfail=True
    for r in range(8):
        W=np.einsum('oij,kj->oik',U,U[r].conj()); fails=False
        for o in range(8):
            for q in range(o+1,8):
                D=o^q
                mono=len({px(s) for s in supp(W[o]@W[q].conj().T)})==1
                full=(not mono) and any(((u^v)&D)==D for u in aff({px(s) for s in supp(W[o])}) for v in aff({px(s) for s in supp(W[q])}))
                lmono=len({px(s) for s in S[(cls[o],cls[q])]})==1
                loc=(not lmono) and any(((px(P[o])^px(P[q])^u^v)&D)==D for u in aff({px(s) for s in S[(cls[o],cls[r])]}) for v in aff({px(s) for s in S[(cls[q],cls[r])]}))
                pairs+=1; agree+=(full==loc); fails|=full
        allfail&=fails
    boards_fail_all+=allfail
print('boards',len(files),'max classes',kmax,'pair tests',pairs,'agree',agree,'boards failing SH_grp^r for every r',boards_fail_all)
