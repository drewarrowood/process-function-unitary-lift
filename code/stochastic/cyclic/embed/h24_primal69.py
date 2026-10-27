"""Round 24 (H.31.4): SDP2 primal for a facet (default: orbit 69 rep) on rule 4; report the spectrum of X (rank 1 would suggest a board),
then round the top eigenvector of X to a candidate board (u, psi from X; frames from the Z(i)) and evaluate the facet exactly in the
9-parameter model after local polish.  usage: orbit"""
import sys, numpy as np, time, torch
import h24_sdp2 as S, h24_conic as C
from h20_common import canon, Tn
from h24_lugsearch import lam
orb=int(sys.argv[1]); f=int(np.where(canon==orb)[0][0]); M=S.Model(4); t0=time.time()
T=Tn[f,:64].reshape(8,8); W=T@M.cnt; q=np.zeros(M.nv)
for i in range(8):
    for c in range(M.n): q[M.va[1+i][M.rep(c)]]+=W[i,c]
sol=C.solve_scs(q,M.Aeq,M.beq,M.blocks,M.nv,eps=1e-7)
x=sol['x']; print('SDP2',sol['info']['status'],sol['info']['pobj']+Tn[f,64],f'{time.time()-t0:.0f}s',flush=True)
np.save(f'/tmp/r24/primal{orb}.npy',x)
def mat(m):
    H=np.zeros((64,64),complex)
    for a in range(64):
        for b in range(64):
            c=M.idx[a,b]; rc=M.rep(c); sg=M.sgn(c); re=x[M.va[m][rc]]; im=x[M.vb[m][rc]] if sg!=0 else 0.0
            H[a,b]=re+1j*sg*im
    return H
X=mat(0); ev=np.linalg.eigvalsh(X)[::-1]; print('X eigenvalues (top 6)',np.round(ev[:6],5),'trace',ev.sum())
for i in range(8):
    e=np.linalg.eigvalsh(mat(1+i))[::-1]; print(' Z',i,'top 3',np.round(e[:3],5))
