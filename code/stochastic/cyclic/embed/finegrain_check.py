"""H.15.7(B): is the correlation P(i|o) of the counterexamples (agents: setting = output o_k, outcome = input i_k,
a legal local operation 'measure input, emit o_k') a *causal correlation*?  Exact: enumerate all deterministic
causal (dynamically ordered) strategies, then LP (HiGHS) + exact rational certificate check of the dual (Farkas) if infeasible."""
import json, itertools as it, numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
B3=list(it.product((0,1),repeat=3))
d=json.load(open('../switchboard/h13/min_cex.json')); m=d['m']
H=[[Fr((-1)**(sum(a*b for a,b in zip(x,y))%2)) for y in B3] for x in B3]
mm=lambda A,B:[[sum(A[i][l]*B[l][j] for l in range(8)) for j in range(8)] for i in range(8)]
U=[[[x/8 for x in r] for r in mm(mm(H,[[Fr((-1)**(m[o][x]//2)) if x==y else Fr(0) for y in range(8)] for x in range(8)]),H)] for o in range(8)]
phiA=[Fr(1,2)]*3+[0,0,Fr(-1,2),0,0]
P={}
P['H.13.2 phi_A']=[[sum(U[o][i][s]*phiA[s] for s in range(8))**2 for i in range(8)] for o in range(8)]
P['H.13.2 phi_B']=[[(U[o][i][0]+U[o][i][1]+U[o][i][2])**2/3 for i in range(8)] for o in range(8)]
# H.12 (complex; float, NUMERICAL)
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
par=lambda x:bin(x).count('1')&1
U12=np.array([[[sum((-1)**par(z&(e^s))*1j**MT[o][z] for z in range(8))/8 for s in range(8)] for e in range(8)] for o in range(8)])
ph=np.zeros(8,complex); ph[3]=1/np.sqrt(2); ph[4]=np.exp(-1j*np.pi/4)/np.sqrt(2)
P['H.12 switchboard (float)']=[[abs((U12[o]@ph)[i])**2 for i in range(8)] for o in range(8)]
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
P['Lugano PF']=[[Fr(int(B3[i]==lug(*B3[o]))) for i in range(8)] for o in range(8)]
# deterministic causal strategies: first k1 (a_k1 = g(x_k1)); second k2 = h(x_k1) ; a_k2 = g2(x_k1,x_k2); last a_k3 = g3(x)
V=set()
for k1 in range(3):
    others=[t for t in range(3) if t!=k1]
    for g1 in it.product((0,1),repeat=2):
        for h in it.product(range(2),repeat=2):
            for g2 in it.product((0,1),repeat=4):
                for g3 in it.product((0,1),repeat=8):
                    out=[]
                    for xi,x in enumerate(B3):
                        a=[0,0,0]; a[k1]=g1[x[k1]]; k2=others[h[x[k1]]]; k3=others[1-h[x[k1]]]
                        a[k2]=g2[2*x[k1]+x[k2]]; a[k3]=g3[xi]; out.append(B3.index(tuple(a)))
                    V.add(tuple(out))
V=sorted(V); print('deterministic causal correlations:',len(V))
A=np.zeros((64,len(V)))
for j,v in enumerate(V):
    for x in range(8): A[8*x+v[x],j]=1
for name,p in P.items():
    b=np.array([float(p[x][a]) for x in range(8) for a in range(8)])
    r=linprog(np.zeros(len(V)),A_eq=A,b_eq=b,bounds=(0,None),method='highs')
    # robustness: max t s.t. t*p+(1-t)*uniform is causal
    print(f'{name}: causal correlation? {"YES (LP feasible)" if r.status==0 else "NO (LP infeasible)"}')
    if r.status!=0:   # Farkas certificate: find y with y.A>=0 on all vertices, y.b<0 ; verify exactly on rationals
        r2=linprog(np.r_[b,],A_ub=-A.T,b_ub=np.zeros(len(V)),bounds=(-1,1),method='highs')
        y=[Fr(v).limit_denominator(64) for v in r2.x]
        minV=min(sum(y[8*x+v[x]] for x in range(8)) for v in V)
        val=sum(y[8*x+a]*(p[x][a] if isinstance(p[x][a],Fr) else Fr(p[x][a]).limit_denominator(10**9)) for x in range(8) for a in range(8))
        print(f'   rational causal inequality: min over causal vertices = {minV}, value on p = {val} (float {float(val):.4f})',
              '-> EXACT violation' if minV>=0 and val<0 else '-> (rounded certificate not valid)')
