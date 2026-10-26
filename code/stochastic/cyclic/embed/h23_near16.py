"""Round 23 (H.30.3): search near the -1/6 points of Valid.  For a facet f, take a vertex p* of Valid minimising f (relative
value -1/6 for the open orbits; H.17.5).  Start a classical-output pure process (COPP, H.29.1) exactly at p*: psi = |0>, and
U_o any unitary with U_o|0> = v_o, |v_o(i)|^2 = p*(i|o), random phases (so the start has the right statistics but is invalid).
Then minimise facet + mu*pen with slowly increasing mu (h22_copp_search.run), project onto pen = 0, and report the exact
minimum over psi.  usage: ORBS seed NSTART"""
import sys, time, numpy as np, torch
from scipy.optimize import linprog
import h22_copp_search as S
from h23_span_lp import Aeq
from h20_common import Tn, REP, canon
torch.set_num_threads(1)
ORBS=[int(a) for a in sys.argv[1].split(',')]; seed=int(sys.argv[2]); NS=int(sys.argv[3]); rng=np.random.default_rng(seed); t0=time.time()
def householder_to(v):
    e=np.zeros(8,complex); e[0]=1; ph=v[0]/abs(v[0]) if abs(v[0])>1e-12 else 1; w=v/ph
    u=e-w; n=np.linalg.norm(u)
    H=np.eye(8)-2*np.outer(u,u.conj())/n**2 if n>1e-12 else np.eye(8)
    return ph*H   # H e = w  (Householder reflection swaps e and w)
for orb in ORBS:
    f=REP[orb] if orb in REP else int(np.where(canon==orb)[0][0])
    lp=linprog(Tn[f,:64],A_eq=Aeq,b_eq=np.ones(64),bounds=[(0,None)]*64,method='highs-ds'); ps_=lp.x.reshape(8,8)   # [i,o]
    print(f'orbit {orb} facet {f}: Valid minimum {lp.fun+Tn[f,64]:.6f}',flush=True)
    Tf=torch.tensor(Tn[f,:64].reshape(8,8)); cf=float(Tn[f,64]); best=(9,9); hits=0
    for r in range(NS):
        U0=[]
        for o in range(8):
            v=np.sqrt(np.clip(ps_[:,o],0,None))*np.exp(1j*rng.uniform(0,2*np.pi,8)); v/=np.linalg.norm(v)
            Q=householder_to(v); R=np.linalg.qr(rng.normal(size=(7,7))+1j*rng.normal(size=(7,7)))[0]
            U0.append(Q@np.block([[np.eye(1),np.zeros((1,7))],[np.zeros((7,1)),R]]))
        S.U0=torch.tensor(np.array(U0)); x0=torch.tensor(rng.normal(size=(8,128))*1e-3); ps0=torch.zeros(16,dtype=torch.float64); ps0[0]=1
        try: v,pv,x,ps=S.run(Tf,cf,x0,ps0,mus=(1e-2,1e-1,1,10,100,1e3,1e4))
        except Exception as e: print('err',e); continue
        ok=pv<1e-12; hits+=ok and v<-1e-7
        if ok and v<best[0]: best=(v,pv)
        print(f'  start {r}: lam {v:.4e} pen {pv:.1e}  {time.time()-t0:.0f}s',flush=True)
    print(f'orbit {orb}: best valid lam {best[0]:.6e} (pen {best[1]:.1e}); valid starts below -1e-7: {hits}/{NS}; {time.time()-t0:.0f}s',flush=True)
