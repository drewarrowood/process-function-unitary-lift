import itertools,sys
from pysat.solvers import Cadical153
from pysat.card import CardEnc
K=int(sys.argv[1]); N=int(sys.argv[2]); X=int(sys.argv[3]); U=N+X
inS=lambda s: len(s)<=K
elems=[frozenset(c) for r in range(K+1) for c in itertools.combinations(range(N),r)]
def subsets(d):
    d=list(d); 
    for r in range(len(d)+1):
        for c in itertools.combinations(d,r): yield frozenset(c)
opts={}
for s in elems:
    o=[]
    # candidate d: subsets of U with size <= len(s)+K (box keeps support<=K)
    for r in range(1,2*K+1):
        for d in itertools.combinations(range(U),r):
            d=frozenset(d)
            if len(d-s)>K: continue
            if d==s: continue
            if max(d)>max(s,default=-1)+X: continue
            if all(inS(s^x) for x in subsets(d)): o.append(d)
    if s!=frozenset() or True:
        if frozenset() !=s: o.append(frozenset())  # z=0 allowed if s!=0
    opts[s]=o
var={}; n=0
for s in elems:
    for d in opts[s]: n+=1; var[(s,d)]=n
sol=Cadical153()
for s in elems:
    lits=[var[(s,d)] for d in opts[s]]
    sol.add_clause(lits)
for i,s in enumerate(elems):
    for t in elems[i+1:]:
        D=s^t
        for d in opts[s]:
            for e in opts[t]:
                if D <= (d^e): sol.add_clause([-var[(s,d)],-var[(t,e)]])
r=sol.solve(); print(K,N,U,'SAT' if r else 'UNSAT',n)
if r:
    m=set(x for x in sol.get_model() if x>0)
    for s in elems[:12]:
        print(sorted(s),[sorted(d) for d in opts[s] if var[(s,d)] in m][0])
