import itertools as it, collections, pickle
from tclose2 import classes
from tclose3 import patterns
from t3sym import Kof, reps, tuned
def qp(s,p): return ((s>>p)&1, (s>>(3+p))&1)
def pconst(S): return {p for p in range(3) if len({qp(s,p) for s in S})==1}
def sup(x,y):
    if not y: return [tuple(sorted((0,)+x))]
    if not x: return [tuple(sorted((0,)+y))]
    return patterns(x,y)
N={}   # N[(x,q)] = set of y != x adjacent-compatible along q
for x in classes:
    for y in classes:
        if y==x and x==(): continue
        for S in sup(x,y):
            if len(S)<2: continue
            for q in pconst(S): N.setdefault((x,q),set()).add(y)
rigid={x:[q for q in range(3) if not N.get((x,q))] for x in classes}
print('labels with >=1 rigid direction:',sum(1 for x in classes if rigid[x]),'of',len(classes)-1,'non-identity (identity rigid:',rigid[()],')')
deg=collections.Counter(len(N.get((x,q),())) for x in classes[1:] for q in range(3) if q not in rigid[x])
print('|N_q(x)| distribution over (non-identity x, non-rigid q):',sorted(deg.items())[:10],'... max',max(deg))
print('3-term orbit reps:',len(reps),'mean |N_q| over reps', sum(len(N.get((x,q),())) for x in reps for q in range(3))/len(reps)/3)
pickle.dump((N,rigid),open('/tmp/glue_adj.pkl','wb'))
# cross-check with the analytic proof of Lemma H: predicted rigid directions = qubits p on which the strings of supp V_x
# fall into >= 2 qubit-p sectors, every sector a single string, and #sectors * 1 > 3/2 ... i.e. (2-term: p in Q_x;
# 3-term: three distinct qubit-p parts among 1, A, B).
def predicted(x):
    st=(0,)+x
    out=[]
    for p in range(3):
        parts=[qp(s,p) for s in st]
        if len(st)==2 and len(set(parts))==2: out.append(p)
        if len(st)==3 and len(set(parts))==3: out.append(p)
    return out
sub=sum(1 for x in classes[1:] if set(predicted(x))<=set(rigid[x])); eq=sum(1 for x in classes[1:] if predicted(x)==rigid[x])
nonempty=sum(1 for x in classes[1:] if predicted(x))
print('analytic rigid set nonempty for',nonempty,'labels; contained in computed rigid set for',sub,'; equal for',eq,'of 1071')
