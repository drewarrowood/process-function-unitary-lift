"""H.16 goal 4 [numerical]: randomized DFS over the csp2.py structure model; for complete admissible
structures with a genuine 3-term class and NO operator-first/last party, build boards with random generic
parameters, verify unitarity + Pauli rule numerically, and scan all 29,344 hull facets (all source states)."""
import numpy as np, random, sys, json, gzip, itertools as it
sys.argv=[sys.argv[0]]+sys.argv[1:]
exec(open('csp2.py').read().split("order=[0,1,2,4,3,5,6,7]")[0])
order=[0,1,2,4,3,5,6,7]
def classify(assign,classes):
    last=[all(supp(assign[o],assign[o^(1<<j)],classes)=={0} for o in V) for j in range(3)]
    first=[all(not nt(s,k) for o in V for j in range(3) for s in supp(assign[o],assign[o^(1<<j)],classes)) for k in range(3)]
    return any(last),any(first)
seed=int(sys.argv[1]); random.seed(seed); rng=np.random.default_rng(seed)
X=np.array([[0,1],[1,0]]); Z=np.diag([1,-1])
def pm(s):
    M=np.array([[1]])
    for t in range(3): M=np.kron(M,np.linalg.matrix_power(X,(s>>t)&1)@np.linalg.matrix_power(Z,(s>>(3+t))&1))
    return M.astype(complex)
PM=np.array([pm(s) for s in range(64)])
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]; T=np.linalg.lstsq(np.c_[PF.reshape(744,-1),np.ones(744)],vals,rcond=None)[0].T/vals.max(0)[:,None]
def hullviol(U):
    P=np.einsum('ois,oit->iost',U.conj(),U).reshape(64,8,8)
    return (-np.linalg.eigvalsh(np.einsum('fr,rst->fst',T[:,:64],P)+T[:,64,None,None]*np.eye(8))[:,0]).max()
def ruleviol(U):
    bad=0
    for o in range(8):
        for q in range(o+1,8):
            c=np.einsum('sij,ij->s',PM.conj(),U[o]@U[q].conj().T)/8; bad+=sum(abs(c[s])**2 for s in range(64) if FORB[o,q][s])
    return bad
def build(assign,classes):
    par=[]
    for c in classes:
        th=rng.uniform(0.15,1.4); f=rng.uniform(0.15,1.4); par.append((np.cos(th),np.sin(th)*np.cos(f),np.sin(th)*np.sin(f)))
    U=[]
    for o in range(8):
        P,k,sg=assign[o]; c=classes[k]; al,be,ga=par[k]
        if c[0]==1: Vm=np.eye(8)
        elif c[0]==2:
            A=PM[c[1]]
            if np.allclose(A@A,-np.eye(8)): A=1j*A
            Vm=np.hypot(al,ga)*np.eye(8)+1j*(-1)**(sg&1)*be*A; Vm/=np.sqrt(np.hypot(al,ga)**2+be**2)
        elif False: Vm=np.hypot(al,ga)*np.eye(8)+1j*(-1)**(sg&1)*be*PM[c[1]]; Vm/=np.sqrt(np.hypot(al,ga)**2+be**2)
        else:
            A,B=PM[c[1]],PM[c[2]]
            if np.allclose(A@A,-np.eye(8)): A=1j*A
            if np.allclose(B@B,-np.eye(8)): B=1j*B
            Vm=al*np.eye(8)+1j*((-1)**(sg&1)*be*A+(-1)**(sg>>1)*ga*B)
        U.append(PM[P]@Vm)
    rev=[int(format(o,'03b')[::-1],2) for o in range(8)]   # csp vertex bit t = party t; facets use msb = party 0
    return np.array(U)[rev]
class Done(Exception): pass
def rdfs(i,assign,classes,cnt):
    cnt[0]+=1
    if cnt[0]>3000: raise Done
    if i==8: raise Done(([assign[o] for o in V],list(classes)))
    o=order[i]; prev=order[:i]
    Pdom=[0] if i==0 else [P for P in range(64) if all(not FORB[o,q][P^assign[q][0]] for q in prev)]
    G=[s for s in range(64) if all(not nt(s,D[o,q][0]) for q in prev if len(D[o,q])==1)]
    newc=[(3,a,b) for a,b in REPS] if i==0 else [(1,None,None)]+[(2,a,None) for a in G if a]+[(3,a,b) for a in G for b in G if 0<a<b and anti(a,b)]
    opts=[(P,('old',k,sg)) for P in Pdom for k,c in enumerate(classes) for sg in range({1:1,2:2,3:4}[c[0]])]
    opts+=[(P,('new',c)) for P in Pdom for c in random.sample(newc,min(len(newc),30))]
    random.shuffle(opts); opts.sort(key=lambda x:(x[1][0]!='new' or random.random()>BIAS[0]))
    for P,ch in opts:
        if ch[0]=='old': st=(P,ch[1],ch[2]); add=False
        else: classes.append(ch[1]); st=(P,len(classes)-1,0); add=True
        if all(not any(FORB[o,q][s] for s in supp(st,assign[q],classes)) for q in prev):
            assign[o]=st; rdfs(i+1,assign,classes,cnt); del assign[o]
        if add: classes.pop()
res=dict(complete=0,hard=0,best=0.0,maxrule=0.0,ex=[])
BIAS=[0.5]
for trial in range(int(sys.argv[2])):
    BIAS[0]=random.random()
    try: rdfs(0,{},[],[0])
    except Done as e:
        if not e.args: continue
        A,C=e.args[0]; res['complete']+=1
        if sum(c[0]==3 for c in C)==0: continue
        L_,F_=classify(dict(enumerate(A)),C)
        if L_ or F_: continue
        res['hard']+=1
        if len({(a[1],a[2]) for a in A})==1: res.setdefault('trivial_common_right',0); res['trivial_common_right']+=1; continue
        for _ in range(3):
            U=build(dict(enumerate(A)),C)
            un=max(np.abs(u@u.conj().T-np.eye(8)).max() for u in U); rv=ruleviol(np.array(U)[[int(format(o,'03b')[::-1],2) for o in range(8)]])
            res['maxrule']=max(res['maxrule'],rv,un)
            v=hullviol(U)
            if v>res['best']: res['best']=float(v)
        if len(res['ex'])<30: res['ex'].append([A,C])
    if trial%200==0: print(trial,json.dumps({k:v for k,v in res.items() if k!='ex'}),flush=True); json.dump(res,open('rsearch_%d.json'%seed,'w'))
print(json.dumps({k:v for k,v in res.items() if k!='ex'}),flush=True)
json.dump(res,open('rsearch_%d.json'%seed,'w'))
