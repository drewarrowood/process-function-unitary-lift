"""Round 20 (H.27.1): forward PF lifts = quantum boxes wired by a process function.  For each of the 8 maximal non-causal
refined PFs (Lugano sign variants, h20_fwd_enum.json) and each open-orbit representative facet, minimise the relative facet value of
p(i|o) = P(i | w(o)) over (a) local-deterministic boxes (= PFs; must be >= 0), (b) no-signalling boxes (LP)."""
import json
from scipy.optimize import linprog
from h20_common import *
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
lug=[p for p in maxi if all(max(x)==1 for x in p)]
print('maximal refined PFs with (2,2,2) blocks:',len(lug))
def wmap(parts): return [tuple(parts[k][others(k,o)] for k in range(3)) for o in range(8)]   # o -> setting triple x
def ns_constraints():
    # variables P[i,x] i,x in 0..7 (index 8*i+x); normalisation + no-signalling for each party
    Aeq=[];beq=[]
    for x in range(8):
        r=np.zeros(64); r[[8*i+x for i in range(8)]]=1; Aeq.append(r); beq.append(1)
    for k in range(3):
        for x in range(8):
            xb=list(B3[x]); xb[k]^=1; x2=B3.index(tuple(xb))
            for j in range(4):   # marginal outcome of the other two parties
                r=np.zeros(64)
                for i in range(8):
                    ib=B3[i]; oth=[ib[t] for t in range(3) if t!=k]
                    if 2*oth[0]+oth[1]==j: r[8*i+x]+=1; r[8*i+x2]-=1
                Aeq.append(r); beq.append(0)
    return np.array(Aeq),np.array(beq)
Aeq,beq=ns_constraints()
res_all={}
for orb in (OPEN if __name__=='__main__' else []):
    f=REP[orb]; Tm=Tn[f,:64].reshape(8,8)   # Tm[i,o]
    out=[]
    for parts in lug:
        wm=wmap(parts); c=np.zeros(64)
        for o in range(8):
            x=B3.index(wm[o])
            for i in range(8): c[8*i+x]+=Tm[i,o]
        # local deterministic: i_k = g_k(x_k)
        loc=min(sum(c[8*B3.index(tuple(g[k][B3[x][k]] for k in range(3)))+x] for x in range(8)) for g in it.product(list(it.product((0,1),repeat=2)),repeat=3))+Tn[f,64]
        r=linprog(c,A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*64,method='highs')
        out.append((round(loc,9),round(r.fun+Tn[f,64],9)))
    res_all[orb]=out
    print(f'orbit {orb} (facet {f}): (local min, NS min) per Lugano variant:',out,flush=True)
