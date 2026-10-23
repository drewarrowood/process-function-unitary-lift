"""H.16 goal 4 [exhaustive, exact discrete]: structural enumeration of pure boards with Pauli support <=3
per outcome, in the generic-parameter model:
  U_o = P_o V_k^sigma,  V_k = alpha_k + i(beta_k A_k + gamma_k B_k), A_k,B_k anticommuting (3-term class),
  or alpha+i beta A (2-term), or 1 (1-term); sigma = sign flips from right Pauli factors; parameters generic.
Support of K_{o,q}=U_o U_q^dag (F2^6 strings, mod phase):
  same class: P_o+P_q+S(sigma^sigma');  S(0)={0}, S(1)={0,a,a+b}, S(2)={0,b,a+b}, S(3)={0,a,b}; 2-term S(1)={0,a}
  different classes: P_o+P_q+{0,a,b}+{0,a',b'}
Pauli rule (H.8.1): no support on strings nontrivial on every party of D(o,q).
WLOG (cube translation, global right Pauli, party perms x local Cliffords): vertex 0 is in a 3-term class
with canonical (a,b), P_0=0, sigma_0=0.  For each complete admissible structure we test operator-first /
operator-last parties (H.8.3, which force PF blends via H.6 / H.1); structures with neither are 'hard'."""
import itertools as it, sys, json, collections
def nt(s,t): return ((s>>t)&1) or ((s>>(3+t))&1)
def anti(u,v): return (bin((u&7)&(v>>3)).count('1')+bin((u>>3)&(v&7)).count('1'))%2
V=range(8); D={(o,q):[t for t in range(3) if (o^q)>>t&1] for o in V for q in V if o!=q}
FORB={k:[all(nt(s,t) for t in d) for s in range(64)] for k,d in D.items()}
def loc(s,t): return ((s>>t)&1)|(((s>>(3+t))&1)<<1)
def mk(l): return sum((l[t]&1)<<t | ((l[t]>>1)<<(3+t)) for t in range(3))
REPS=[]; seen=set()
for a in range(1,64):
  for b in range(a+1,64):
    if not anti(a,b) or (a,b) in seen: continue
    REPS.append((a,b))
    for pp in it.permutations(range(3)):
      for cl in it.product(list(it.permutations((1,2,3))),repeat=3):
        f=lambda s:mk([(0 if loc(s,pp[t])==0 else cl[t][loc(s,pp[t])-1]) for t in range(3)])
        seen.add(tuple(sorted((f(a),f(b)))))
def gens(c): return [x for x in c[1:] if x is not None]
def S_same(c,sg):
    if c[0]==1: return (0,)
    if c[0]==2: return (0,) if sg==0 else (0,c[1])
    a,b=c[1],c[2]; return [(0,),(0,a,a^b),(0,b,a^b),(0,a,b)][sg]
def supp(st,sq,classes):
    (P,k,sg),(P2,k2,sg2)=st,sq
    if k==k2: S=S_same(classes[k],sg^sg2)
    else: S={x^y for x in [0]+gens(classes[k]) for y in [0]+gens(classes[k2])}
    return {P^P2^x for x in S}
order=[0,1,2,4,3,5,6,7]
stats=collections.Counter(); hard=[]
def classify(assign,classes):
    last=[all(supp(assign[o],assign[o^(1<<j)],classes)=={0} for o in V) for j in range(3)]
    first=[all(not nt(s,k) for o in V for j in range(3) for s in supp(assign[o],assign[o^(1<<j)],classes)) for k in range(3)]
    return any(last),any(first)
def rec(i,assign,classes):
    if i==8:
        L,F=classify(assign,classes); stats[(L,F)]+=1
        if not L and not F and len(hard)<20000: hard.append(([assign[o] for o in V],list(classes)))
        return
    o=order[i]; prev=order[:i]
    if i==0: Pdom=[0]
    else: Pdom=[P for P in range(64) if all(not FORB[o,q][P^assign[q][0]] for q in prev)]
    G=[s for s in range(64) if all(not nt(s,D[o,q][0]) for q in prev if len(D[o,q])==1)]
    if i==0: newc=[(3,a,b) for a,b in REPS]
    else: newc=[(1,None,None)]+[(2,a,None) for a in G if a]+[(3,a,b) for a in G for b in G if 0<a<b and anti(a,b)]
    for P in Pdom:
        for k,c in enumerate(classes):
            for sg in range({1:1,2:2,3:4}[c[0]]):
                st=(P,k,sg)
                if all(not any(FORB[o,q][s] for s in supp(st,assign[q],classes)) for q in prev):
                    assign[o]=st; rec(i+1,assign,classes); del assign[o]
        for c in newc:
            classes.append(c); st=(P,len(classes)-1,0)
            if all(not any(FORB[o,q][s] for s in supp(st,assign[q],classes)) for q in prev):
                assign[o]=st; rec(i+1,assign,classes); del assign[o]
            classes.pop()
        if i==1: print('progress P',P,dict(stats),len(hard),flush=True)
rec(0,{},[])
print('REPS',REPS); print('stats (has_op_last, has_op_first): count',dict(stats)); print('hard',len(hard))
json.dump(hard,open('hard.json','w'))
