"""Round 14, item 2 (achievable side): more seesaw restarts for y_A on H.12, random POVM starts and random rank-1 projective starts.
Uses the functions of h12_bound.py (exec'd with mode 'none').  [NUMERICAL]"""
import sys, numpy as np
seed=int(sys.argv[1]); nr=int(sys.argv[2])
sys.argv=['h12_bound.py',str(seed),'none']; exec(open('h12_bound.py').read())
y=Ys['y_A (H.15.7d, -0.7057)']
def rand_proj():
    E=[]
    for x in (0,1):
        q=np.linalg.qr(rng.normal(size=(2,2))+1j*rng.normal(size=(2,2)))[0]; Ps=[np.outer(q[:,j],q[:,j].conj()) for j in (0,1)]
        lab=rng.permutation(4)[:2]; Ms=[np.zeros((2,2),complex) for _ in range(4)]; Ms[lab[0]]=Ps[0]; Ms[lab[1]]=Ps[1]
        E.append([[Ms[0],Ms[1]],[Ms[2],Ms[3]]])
    return E
best=9
for rs in range(nr):
    E=[(rand_inst() if rs%2 else rand_proj()) for _ in range(3)]; prev=9
    for sweep in range(150):
        for k in range(3): E[k],v=best_party(Gk(E,y,k))
        if prev-v<1e-9: break
        prev=v
    val=(y*corr(E)).sum()
    if val<best: best=val; np.save(f'/tmp/r14/seesaw_best_{seed}.npy',np.array([[[[E[k][x][a][o] for o in (0,1)] for a in (0,1)] for x in (0,1)] for k in range(3)]))
    print(f'seed {seed} restart {rs} ({"povm" if rs%2 else "proj"}): {val:.6f}  best {best:.6f}',flush=True)
