"""Controls for tclose2: (1) with the failure condition replaced by 'any cross pair', the solver must find boards;
(2) the real two-class tuned boards tb_*.npz must be accepted by the pair-compat tables of their own support S."""
import tclose2 as T, numpy as np, glob, json, collections
from lib3 import PM, pauli_coeffs
Ss=T.supports()
# (1)
orig=T.solve.__code__
src=open('tclose2.py').read()
src2=src.replace("if b==1: f[i]=any((((P&7)^h)&D)==D for h in H)","if b==1: f[i]=True").split("if __name__")[0]
ns={}; exec(src2,ns)
import random; random.seed(0); samp=random.sample(Ss,300)
print('control1: boards with a cross pair found for',sum(ns['solve'](S) is not None for S in samp),'of 300 supports')
# (2)
acc=collections.Counter()
for f in sorted(glob.glob('tb_*.npz')):
    d=np.load(f); U=d['U']; P=d['P']; k=d['k']
    if len(set(k.tolist()))!=2: continue
    ks=sorted(set(k.tolist())); V={kk:PM[P[o]].conj().T@U[o] for o in range(8) for kk in [int(k[o])]}
    G=V[ks[1]]@V[ks[0]].conj().T; c=pauli_coeffs(G); S=[s for s in range(64) if abs(c[s])>1e-9]
    if len({s&7 for s in S})==1: acc['merged']+=1; continue
    # board in (P,b) form; left-translate S so that 0 in S: G = Q G0 with Q=S[0] -> P_o for b=1 becomes P_o^S[0]
    t=S[0]; S0=sorted(s^t for s in S)
    st=[(int(P[o]) ^ (t if k[o]==ks[1] else 0), int(k[o]==ks[1])) for o in range(8)]
    inlist=T.canon(S0) in set(Ss)
    Pa=st; ok=True
    for o in range(8):
        for q in range(o+1,8):
            D=o^q; X=Pa[o][0]^Pa[q][0]
            if Pa[o][1]==Pa[q][1]: ok&= not T.FORB[D][X]
            else: ok&= all(not T.FORB[D][X^s] for s in S0)
    acc[('accepted',ok,'S in enumerated list',inlist)]+=1
print('control2',dict(acc))
