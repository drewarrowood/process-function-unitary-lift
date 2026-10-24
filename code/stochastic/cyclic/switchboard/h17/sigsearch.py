"""H.17: biased search for admissible <=3-term structures in which some pair fails the support-transport
hypothesis SH (only possible for same-class type-3 pairs with different sign patterns sigma)."""
import sys, json, time
import struct3 as S
from struct3 import *
seed=int(sys.argv[1]); N=int(sys.argv[2]); random.seed(seed); rng=np.random.default_rng(seed)
def rdfs(i,assign,classes,cnt,maxnodes=3000):
    cnt[0]+=1
    if cnt[0]>maxnodes: raise Done
    if i==8: raise Done(dict(assign),list(classes))
    o=ORDER[i]; prev=ORDER[:i]
    Pdom=[0] if i==0 else [P for P in range(64) if all(not FORB[o^q][P^assign[q][0]] for q in prev)]
    if i==0:
        a,b=random.choice(ANTI); classes.append((3,a,b)); assign[o]=(0,0,0); rdfs(1,assign,classes,cnt,maxnodes); return
    opts=[(P,sg) for P in Pdom for sg in range(4)]
    random.shuffle(opts); opts.sort(key=lambda x: (x[1]==0) != (random.random()<0.3))
    for P,sg in opts:
        st=(P,0,sg)
        if all(ok_pair(st,assign[q],classes,o^q) for q in prev):
            assign[o]=st; rdfs(i+1,assign,classes,cnt,maxnodes); del assign[o]
res=dict(complete=0,withsig=0,hard=0,shfail=0,best=-1.,ex=[])
T,canon=load_facets()
for n in range(N):
    try: rdfs(0,{},[],[0])
    except Done as e:
        if not e.args: continue
        A,C=e.args; res['complete']+=1
        if len({A[o][2] for o in A})<2: continue
        res['withsig']+=1
        L_,F_=first_last(A,C)
        if L_ or F_: continue
        res['hard']+=1
        bad=SH(A,C)
        if bad:
            res['shfail']+=1
            v=max(float(facet_viol(build(A,C,rng=rng),T).max()) for _ in range(5)); res['best']=max(res['best'],v)
            if len(res['ex'])<100: res['ex'].append([{str(o):A[o] for o in A},C,bad[:5],v])
    if n%200==0: print(n,json.dumps({k:v for k,v in res.items() if k!='ex'}),flush=True)
print('final',json.dumps({k:v for k,v in res.items() if k!='ex'}),flush=True)
json.dump(res,open('sig_%d.json'%seed,'w'))
