"""Round 24 (H.31.1): the reduced class-lift relaxation R (h24_sdp2 without the X cone; X enters only linearly) for the
representative facets on Lugano rule 4, SCS eps 1e-9.  R is weaker than or equal to SDP2.  usage: orbits"""
import numpy as np, time, sys
import h24_sdp2 as S, h24_conic as C
from h20_common import canon, Tn
M=S.Model(4)
for orb in map(int,sys.argv[1].split(',')):
    f=int(np.where(canon==orb)[0][0]); t=time.time()
    T=Tn[f,:64].reshape(8,8); W=T@M.cnt; q=np.zeros(M.nv)
    for i in range(8):
        for c in range(M.n): q[M.va[1+i][M.rep(c)]]+=W[i,c]
    sol=C.solve_scs(q,M.Aeq,M.beq,M.blocks[1:],M.nv,eps=1e-9)
    print(orb, sol['info']['status'], sol['info']['pobj']+Tn[f,64], sol['info']['dobj']+Tn[f,64], f'{time.time()-t:.0f}s',flush=True)
    
