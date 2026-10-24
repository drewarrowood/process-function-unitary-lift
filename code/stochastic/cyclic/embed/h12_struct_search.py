"""Round 15, item 1 (achievable side): structured search for y_A on H.12 (H.22.1).
Each party and setting uses either a deterministic outcome (a,o), or a rank-1 projective qubit measurement along one of the 13 cube axes
(faces: Pauli X,Y,Z; edges: (X±Y)/√2 etc., which are the axes reached from Pauli axes by √X-type quarter-turns, cf. the √X-Lugano form H.21.2;
corners: (±X±Y±Z)/√3), with its two projectors assigned to two of the four outcomes (a,o).  160 options per (party, setting).
Discrete coordinate descent (objective is linear in each party's operators and separates over that party's settings), many random restarts,
then the continuous seesaw of h12_bound.py from the best distinct discrete optima.  [NUMERICAL]"""
import sys, numpy as np, itertools as it
seed=int(sys.argv[1]); nr=int(sys.argv[2]); npol=int(sys.argv[3]) if len(sys.argv)>3 else 30
sys.argv=['h12_bound.py',str(seed),'none']; exec(open('h12_bound.py').read())
y=Ys['y_A (H.15.7d, -0.7057)']
X=np.array([[0,1],[1,0]]); Yp=np.array([[0,-1j],[1j,0]]); Z=np.diag([1.,-1])
axes=[]
for n in it.product((-1,0,1),repeat=3):
    if n==(0,0,0): continue
    if n>tuple(-t for t in n): continue          # one of ±n
    v=np.array(n,float); v/=np.linalg.norm(v); axes.append(v)
assert len(axes)==13
OPTS=[]
for c in range(4):
    M=[np.zeros((2,2),complex) for _ in range(4)]; M[c]=np.eye(2); OPTS.append(M)
for v in axes:
    S=v[0]*X+v[1]*Yp+v[2]*Z; Pp=(np.eye(2)+S)/2; Pm=(np.eye(2)-S)/2
    for c1,c2 in it.permutations(range(4),2):
        M=[np.zeros((2,2),complex) for _ in range(4)]; M[c1]=Pp; M[c2]=Pm; OPTS.append(M)
NO=len(OPTS); OP=np.array(OPTS)          # NO x 4 x 2 x 2 ; outcome c = 2a+o
def inst(i0,i1): return [[[OPTS[i][2*a+o] for o in (0,1)] for a in (0,1)] for i in (i0,i1)]
def val_opts(G,x):   # value of every option for setting x of this party: sum_{a,o} Tr[E_{ao} G[x,a,o]]
    Gx=np.array([G[x,c>>1,c&1] for c in range(4)])           # 4x2x2
    return np.real(np.einsum('ncij,cji->n',OP,Gx))
res=[]
for rs in range(nr):
    ch=rng.integers(0,NO,(3,2)); E=[inst(*ch[k]) for k in range(3)]; prev=9
    for sweep in range(100):
        for k in range(3):
            G=Gk(E,y,k)
            for x in (0,1): ch[k,x]=int(np.argmin(val_opts(G,x)))
            E[k]=inst(*ch[k])
        v=(y*corr(E)).sum()
        if prev-v<1e-12: break
        prev=v
    res.append((round(v,9),tuple(map(tuple,ch))))
res.sort(); vals=[r[0] for r in res]
print(f'seed {seed}: {nr} discrete restarts; best discrete {vals[0]:.6f}; distinct values (lowest 10): {sorted(set(vals))[:10]}',flush=True)
seen=set(); best=9; bestE=None
for v,ch in res:
    if ch in seen: continue
    seen.add(ch)
    if len(seen)>npol: break
    E=[inst(*ch[k]) for k in range(3)]; prev=9
    for sweep in range(300):
        for k in range(3): E[k],w=best_party(Gk(E,y,k))
        if prev-w<1e-10: break
        prev=w
    w=(y*corr(E)).sum()
    if w<best: best=w; bestE=E
    print(f'  polish from discrete {v:.6f} -> seesaw {w:.6f} ({sweep} sweeps)',flush=True)
print(f'STRUCT BEST seed {seed}: {best:.6f}',flush=True)
np.save(f'/tmp/r15/struct_best_{seed}.npy',np.array([[[[bestE[k][x][a][o] for o in (0,1)] for a in (0,1)] for x in (0,1)] for k in range(3)]))
