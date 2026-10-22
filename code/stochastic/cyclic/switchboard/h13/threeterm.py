"""H.14 [numerical]: random/annealing search over general (non-X-type) 3-term boards
U_o = P_o (cos t_o + i sin t_o (cos f_o A_o + sin f_o B_o)), P_o,A_o,B_o Pauli strings, A_o,B_o anticommuting
(this is the general form of a unitary with Pauli support of size 3, up to phase; see H.14.1).
Discrete structure annealed to satisfy the Pauli rule H.8.1 identically (tested at random generic t,f);
admissible structures then scanned over (t,f) for hull-facet violations (all 29,344 facets, all source states)."""
import numpy as np, itertools as it, gzip, sys, json
rng=np.random.default_rng(int(sys.argv[1])); NIT=int(sys.argv[2])
B3=list(it.product((0,1),repeat=3)); X=np.array([[0,1],[1,0]]); Z=np.diag([1,-1])
def pm(a,b):
    M=np.array([[1]]);
    for x,z in zip(a,b): M=np.kron(M,np.linalg.matrix_power(X,x)@np.linalg.matrix_power(Z,z))
    return M.astype(complex)
PL=[(a,b) for a in B3 for b in B3]; PM=np.array([pm(a,b) for a,b in PL])            # [64,8,8]
anti=np.array([[sum(x*w+z*v for (x,z),(v,w) in zip(zip(*PL[i]),zip(*PL[j])))%2 for j in range(64)] for i in range(64)])
forb={}
for o in range(8):
    for q in range(8):
        if o!=q:
            D=[t for t in range(3) if B3[o][t]!=B3[q][t]]
            forb[o,q]=np.array([all(PL[s][0][t] or PL[s][1][t] for t in D) for s in range(64)])
def board(S,tf):
    return np.stack([PM[S[o,0]]@(np.cos(tf[o,0])*np.eye(8)+1j*np.sin(tf[o,0])*(np.cos(tf[o,1])*PM[S[o,1]]+np.sin(tf[o,1])*PM[S[o,2]])) for o in range(8)])
def viol(U):
    bad=0
    for (o,q),fm in forb.items():
        if o<q:
            c=np.einsum('sij,ij->s',PM.conj(),U[o]@U[q].conj().T)/8; bad+=np.sum(np.abs(c[fm])**2)
    return bad
def score(S):
    return sum(viol(board(S,rng.uniform(0.2,1.3,(8,2)))) for _ in range(2))
def rand_entry():
    a=rng.integers(1,64); b=rng.choice(np.nonzero(anti[a])[0]); return [rng.integers(64),a,b]
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]; T=np.linalg.lstsq(np.c_[PF.reshape(744,-1),np.ones(744)],vals,rcond=None)[0].T/vals.max(0)[:,None]
def hullviol(U):
    P=np.einsum('ois,oit->iost',U.conj(),U).reshape(64,8,8)
    return (-np.linalg.eigvalsh(np.einsum('fr,rst->fst',T[:,:64],P)+T[:,64,None,None]*np.eye(8))[:,0]).max()
found=[]; best=0
for run in range(NIT):
    S=np.array([rand_entry() for _ in range(8)]); s=score(S); temp=1.0
    for step in range(8000):
        S2=S.copy(); o=rng.integers(8)
        if rng.random()<0.5: S2[o,0]=rng.integers(64)
        else: S2[o]=rand_entry()
        s2=score(S2)
        if s2<=s or rng.random()<np.exp((s-s2)/temp): S,s=S2,s2
        temp*=0.9993
        if s<1e-20: break
    if s<1e-20:
        v=max(hullviol(board(S,rng.uniform(0.05,1.5,(8,2)))) for _ in range(15)); best=max(best,v)
        found.append(dict(S=S.tolist(),viol=float(v))); print(run,'admissible; max facet violation',v,flush=True)
    else: print(run,'stuck',s,flush=True)
json.dump(dict(found=found,best=best),open('threeterm_%s.json'%sys.argv[1],'w'))
