"""H.17 structure model for boards with <=3 Pauli terms per U_o (generic parameters), msb convention (lib3).
U_o = P_o V_{k(o)}^{sigma(o)}:  class type 1: V=1;  type 2: V = al + i be A;  type 3: V = al + i(be A + ga B), A,B anticommuting
Hermitian Paulis;  sigma flips the signs of be (bit 0) and ga (bit 1).
Generic support of K_{oq} = U_o U_q^dag (Pauli strings mod phase, XOR encoding):
  same class:  P_o+P_q+S, S = {0} (same sigma), type 2: {0,A};  type 3: flip A {0,A,AB}, flip B {0,B,AB}, both {0,A,B}
  different classes: P_o+P_q+{0,A,B}+{0,A',B'}."""
import numpy as np, random, itertools as it
from lib3 import *
def gens(c): return [g for g in c[1:] if g is not None]
def S_same(c,ds):
    if c[0]==1 or ds==0: return (0,)
    if c[0]==2: return (0,c[1])
    a,b=c[1],c[2]; return {1:(0,a,a^b),2:(0,b,a^b),3:(0,a,b)}[ds]
def supp(st,sq,classes):
    (P,k,sg),(P2,k2,sg2)=st,sq
    if k==k2: S=S_same(classes[k],sg^sg2)
    else: S={x^y for x in [0]+gens(classes[k]) for y in [0]+gens(classes[k2])}
    return {P^P2^x for x in S}
def ok_pair(st,sq,classes,D): return not any(FORB[D][s] for s in supp(st,sq,classes))
NSIG={1:1,2:2,3:4}
ANTI=[(a,b) for a in range(1,64) for b in range(a+1,64) if anti(a,b)]
ORDER=[0,4,2,1,6,5,3,7]
class Done(Exception): pass
def rdfs(i,assign,classes,cnt,pnew,maxnodes=4000):
    cnt[0]+=1
    if cnt[0]>maxnodes: raise Done
    if i==8: raise Done(dict(assign),list(classes))
    o=ORDER[i]; prev=ORDER[:i]
    Pdom=[0] if i==0 else [P for P in range(64) if all(not FORB[o^q][P^assign[q][0]] for q in prev)]
    # generators allowed w.r.t. all single-party neighbours already placed (a K for |D|=1 must be trivial on that party)
    G=[s for s in range(1,64) if all(not FORB[o^q][s] for q in prev if bin(o^q).count('1')==1)]
    if i==0: newc=[(3,a,b) for a,b in random.sample(ANTI,40)]
    else:
        newc=[(1,None,None)]+[(2,a,None) for a in random.sample(G,min(len(G),10))]
        pairs=[(a,b) for a in G for b in G if a<b and anti(a,b)]
        newc+=[(3,a,b) for a,b in random.sample(pairs,min(len(pairs),25))]
    opts=[(P,('old',k,sg)) for P in Pdom for k,c in enumerate(classes) for sg in range(NSIG[c[0]])]
    opts+=[(P,('new',c)) for P in random.sample(Pdom,min(len(Pdom),6)) for c in newc]
    random.shuffle(opts); opts.sort(key=lambda x:(x[1][0]!='new') != (random.random()<pnew))
    for P,ch in opts:
        if ch[0]=='old': st=(P,ch[1],ch[2]); add=False
        else: classes.append(ch[1]); st=(P,len(classes)-1,0); add=True
        if all(ok_pair(st,assign[q],classes,o^q) for q in prev):
            assign[o]=st; rdfs(i+1,assign,classes,cnt,pnew,maxnodes); del assign[o]
        if add: classes.pop()
def random_structure(pnew=0.5,maxnodes=4000):
    try: rdfs(0,{},[],[0],pnew,maxnodes)
    except Done as e:
        if e.args: return e.args
    return None
def first_last(assign,classes):
    """operator-last direction j: all K across j-edges scalar; operator-first party k: no K term acts on k."""
    last=[all(supp(assign[o],assign[o^(1<<j)],classes)=={0} for o in range(8)) for j in range(3)]
    first=[all(((px(s)|pz(s))>>j)&1==0 for o in range(8) for q in range(8) if o!=q for s in supp(assign[o],assign[q],classes)) for j in range(3)]
    return any(last),any(first)
def build(assign,classes,par=None,rng=np.random):
    if par is None:
        par=[]
        for c in classes:
            th=rng.uniform(0.15,1.4); f=rng.uniform(0.15,1.4); par.append((th,f))
    U=[]
    for o in range(8):
        P,k,sg=assign[o]; c=classes[k]; th,f=par[k]
        if c[0]==1: V=np.eye(8,dtype=complex)
        elif c[0]==2: V=np.cos(th)*np.eye(8)+1j*(-1)**(sg&1)*np.sin(th)*HM[c[1]]
        else: V=np.cos(th)*np.eye(8)+1j*np.sin(th)*((-1)**(sg&1)*np.cos(f)*HM[c[1]]+(-1)**(sg>>1)*np.sin(f)*HM[c[2]])
        U.append(PM[P]@V)
    return np.array(U)
# ---- support-transport hypothesis (H.17.1) ----
def tclass(assign,classes,o):
    P,k,sg=assign[o]; c=classes[k]
    if c[0]==1 or all(px(g)==0 for g in gens(c)): return ('id',)
    return (k,sg)
def shadow(classes,tc):
    if tc==('id',): return (0,)
    c=classes[tc[0]]; return tuple(sorted({0}|{px(g) for g in gens(c)}))
def allowedX(x,D): return (x&D)!=D
def SH(assign,classes):
    tc={o:tclass(assign,classes,o) for o in range(8)}; bad=[]
    for o in range(8):
        for q in range(o+1,8):
            D=o^q; a=px(assign[o][0])^px(assign[q][0])
            if tc[o]==tc[q]:
                if not allowedX(a,D): bad.append((o,q,'same'))
                continue
            for t in shadow(classes,tc[o]):
                for t2 in shadow(classes,tc[q]):
                    if not allowedX(a^t^t2,D): bad.append((o,q,t,t2))
    return bad
