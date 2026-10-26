"""Round 20 (H.27.1): exact certificate over ALL 20 maximal refined PFs (settings alphabets of size 1..4 per party), not only the 8
Lugano-type ones, so the theorem does not rely on any causal-correlation argument.  Same method as h20_fwd_cert.py, with general
setting alphabets: P(i|x), x in prod_k [n_k], no-signalling equalities, exact affine facet function from the integer facet values on
the PFs D o w (D local deterministic), exact rational LP dual."""
import json
from fractions import Fraction as Fr
from scipy.optimize import linprog
from h20_common import *
from h20_fwd_cert import rref_solve, PFIDX
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
def setup(parts):
    nb=[max(p)+1 for p in parts]; X=list(it.product(*[range(n) for n in nb])); nx=len(X); nv=8*nx
    Aeq=[];beq=[]
    for xi in range(nx):
        r=[0]*nv
        for i in range(8): r[nx*i+xi]=1
        Aeq.append(r); beq.append(1)
    for k in range(3):
        for xi,x in enumerate(X):
            for xk2 in range(nb[k]):
                if xk2==x[k]: continue
                x2=list(x); x2[k]=xk2; xj=X.index(tuple(x2))
                for j in range(4):
                    r=[0]*nv
                    for i in range(8):
                        ib=B3[i]; oth=[ib[t] for t in range(3) if t!=k]
                        if 2*oth[0]+oth[1]==j: r[nx*i+xi]+=1; r[nx*i+xj]-=1
                    Aeq.append(r); beq.append(0)
    LOC=list(it.product(*[list(it.product((0,1),repeat=n)) for n in nb]))
    DV=[]
    for g in LOC:
        v=[0]*nv
        for xi,x in enumerate(X): v[nx*B3.index(tuple(g[k][x[k]] for k in range(3)))+xi]=1
        DV.append(v)
    xo=[X.index(tuple(parts[k][others(k,o)] for k in range(3))) for o in range(8)]
    return nb,X,nx,nv,Aeq,beq,LOC,DV,xo
def certify(f,parts,S):
    nb,X,nx,nv,Aeq,beq,LOC,DV,xo=S
    vals=[Fr(int(valsI[PFIDX[tuple(B3.index(tuple(g[k][X[xo[o]][k]] for k in range(3))) for o in range(8))],f])) for g in LOC]
    cz=rref_solve([d+[1] for d in DV],vals,[0]*(nv+1)); c=cz[:nv]; c0=cz[nv]
    assert all(sum(ci*di for ci,di in zip(c,d))+c0==v for d,v in zip(DV,vals))
    A=np.array(Aeq,float); cf=np.array([float(x) for x in c])
    r=linprog(cf,A_eq=A,b_eq=beq,bounds=[(0,None)]*nv,method='highs'); y0=r.eqlin.marginals; red=cf-A.T@y0
    Z=[j for j in range(nv) if red[j]<1e-7]
    y=rref_solve([[Aeq[i][j] for i in range(len(Aeq))] for j in Z],[c[j] for j in Z],[Fr(v).limit_denominator(10**6) for v in y0])
    rr=[c[j]-sum(Aeq[i][j]*y[i] for i in range(len(Aeq)) if Aeq[i][j]) for j in range(nv)]
    bound=sum(b*yy for b,yy in zip(beq,y))+c0
    assert all(isinstance(v,Fr) for v in rr+[bound])
    return min(rr)>=0, bound, min(vals), r.fun+float(c0)
allok=True
for parts in maxi:
    S=setup(parts); row=[]
    for orb in OPEN:
        ok,bound,locmin,flt=certify(REP[orb],parts,S); row.append(f'{orb}:{bound}'); allok&=ok and bound>=0 and bound==locmin
    print('blocks',S[0],'w =',parts,' exact NS bound per orbit =',' '.join(row),flush=True)
print('ALL 20 x 10 CERTIFIED (dual feasible, exact NS bound = min over local boxes >= 0):',allok)
