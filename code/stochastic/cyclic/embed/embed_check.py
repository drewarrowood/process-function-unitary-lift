"""H.15.6(c): exact signalling-structure check for the spacetime-embedding audit.
For the H.13.2 rational counterexample p (both sources) and the Lugano PF, compute in exact rational arithmetic:
 (1) party-to-party signalling X->Y (Y's input marginal depends on X's output for some fixed output of the third party),
     and set signalling X->{Y,Z}, {X,Y}->Z;
 (2) whether any party is 'first' (its input independent of all outputs) -- necessary for a fixed-order process;
 (3) the BCRWZ Thm-3 reduced test: for each fixed o_k, is the reduced bipartite process on the other two at most
     one-way signalling? (necessary and sufficient for a PF; mixtures of PFs may fail it, so it is diagnostic only).
VR (arXiv:2203.11245) Thm 3/4 need only 'not fixed order'; (1)-(2) certify that, so Thm 4 / Cor 1-2 apply to the
finite-dimensional processes here: any relativistically causal fixed-spacetime realisation non-localises in/outputs."""
import json, itertools as it
from fractions import Fraction as Fr
B3=list(it.product((0,1),repeat=3)); d=json.load(open('../switchboard/h13/min_cex.json')); m=d['m']
H=[[Fr((-1)**(sum(a*b for a,b in zip(x,y))%2)) for y in B3] for x in B3]
mm=lambda A,B:[[sum(A[i][l]*B[l][j] for l in range(8)) for j in range(8)] for i in range(8)]
U=[[[x/8 for x in r] for r in mm(mm(H,[[Fr((-1)**(m[o][x]//2)) if x==y else Fr(0) for y in range(8)] for x in range(8)]),H)] for o in range(8)]
def p_from(amp2): return {(B3[i],B3[o]):amp2(o,i) for o in range(8) for i in range(8)}   # p[(i,o)] = P(i|o)
phiA=[Fr(1,2)]*3+[0,0,Fr(-1,2),0,0]
pA=p_from(lambda o,i:sum(U[o][i][s]*phiA[s] for s in range(8))**2)
pB=p_from(lambda o,i:(U[o][i][0]+U[o][i][1]+U[o][i][2])**2/3)
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
pL={(i,o):Fr(int(i==lug(*o))) for i in B3 for o in B3}
N='ABC'
def marg(p,o,S): # distribution of inputs on parties S given full output o
    r={}
    for i in B3:
        k=tuple(i[t] for t in S); r[k]=r.get(k,0)+p[(i,o)]
    return r
def signals(p,X,Y):  # X (set) -> Y (set): exists fixed outputs of others s.t. marginal on Y changes with o_X
    rest=[t for t in range(3) if t not in X]
    for orest in it.product((0,1),repeat=len(rest)):
        ms=set()
        for ox in it.product((0,1),repeat=len(X)):
            o=[0]*3
            for t,v in zip(X,ox): o[t]=v
            for t,v in zip(rest,orest): o[t]=v
            ms.add(tuple(sorted(marg(p,tuple(o),Y).items())))
        if len(ms)>1: return True
    return False
def report(name,p):
    assert all(sum(p[(i,o)] for i in B3)==1 for o in B3)
    pair=[N[x]+'->'+N[y] for x in range(3) for y in range(3) if x!=y and signals(p,[x],[y])]
    sets=[N[x]+'->'+''.join(N[t] for t in range(3) if t!=x) for x in range(3) if signals(p,[x],[t for t in range(3) if t!=x])]
    sets+=[''.join(N[t] for t in range(3) if t!=y)+'->'+N[y] for y in range(3) if signals(p,[t for t in range(3) if t!=y],[y])]
    first=[N[k] for k in range(3) if not signals(p,[t for t in range(3) if t!=k],[k])]
    red=[]
    for k in range(3):
        x,y=[t for t in range(3) if t!=k]
        for ok in (0,1):
            def sig2(a,b):
                for ob in (0,1):
                    ms=set()
                    for oa in (0,1):
                        o=[0]*3; o[k]=ok; o[a]=oa; o[b]=ob
                        ms.add(tuple(sorted(marg(p,tuple(o),[b]).items())))
                    if len(ms)>1: return True
                return False
            red.append((N[k]+'='+str(ok), sig2(x,y) and sig2(y,x)))
    two=[r for r,t in red if t]
    orders=[]
    for pi in it.permutations(range(3)):   # classical fixed order pi: marginal on first j inputs indep. of outputs pi_j..pi_3
        ok=all(len({tuple(sorted(marg(p,o,list(pi[:j])).items())) for o in B3 if all(o[t]==base[t] for t in pi[:j-1])})==1
               for j in (1,2) for base in B3)
        if ok: orders.append(''.join(N[t] for t in pi))
    print(f'{name}:\n  pairwise signalling {pair}\n  set signalling {sets}\n  first parties {first or "none"}'
          f'\n  compatible fixed orders {orders or "none (not a fixed-order process)"}\n  reduced 2-way-signalling (BCRWZ Thm 3 fails) at {two or "none"}')
    return pair,first,two,orders
R={}
for nm,p in [('Lugano PF',pL),('H.13.2 p, phi=(|0>+|1>+|2>-|5>)/2',pA),('H.13.2 p, phi=(|0>+|1>+|2>)/sqrt3',pB)]:
    R[nm]=report(nm,p)
assert not R['Lugano PF'][2], 'PF must pass BCRWZ Thm 3'
assert all(not v[3] for v in R.values()), 'none may be fixed-order'
print('OK: none of the three is a fixed-order process; VR Thm 3 => cyclic signalling certified; VR Thm 4 / Cor 1-2 apply (finite dim).')

# (4) phi=(|0>+|1>+|2>-|5>)/2 has B first.  Is the A-C loop, conditioned on (i_B, o_B), itself a valid bipartite process?
# (If every conditional were valid it would be causally separable (classical bipartite), making p causal, hence in conv(PF),
#  contradicting H.13.2.  So some conditional must be invalid: validity of the A-C loop needs B's correlated input.)
fs=[(0,0),(1,1),(0,1),(1,0)]
pB_=lambda p,ib:sum(p[(i,(0,0,0))] for i in B3 if i[1]==ib)
bad=[]
for ib in (0,1):
    for ob in (0,1):
        w=pB_(pA,ib)
        if w==0: continue
        for fa,fc in it.product(range(4),repeat=2):
            tot=sum(pA[((ia,ib,ic),(fs[fa][ia],ob,fs[fc][ic]))] for ia in (0,1) for ic in (0,1))/w
            if tot!=1: bad.append((ib,ob,fa,fc,str(tot)))
print('(4) p(i_B)=',[str(pB_(pA,b)) for b in (0,1)],'; invalid conditional A-C loops (i_B,o_B,f_A,f_C,total):',len(bad), bad[:6])
assert bad, 'expected some invalid conditional'
