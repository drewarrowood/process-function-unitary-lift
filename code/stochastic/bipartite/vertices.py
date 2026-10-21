"""Bipartite classical processes p(a,b|x,y): a,b = inputs of A,B; x,y = outputs.
Validity: p>=0 and sum_{a,b} p(a,b|f(a),g(b)) = 1 for all f:A->X, g:B->Y.
Sample LP vertices with random objectives; check each is 0/1 (hence a process function).
Also check random interior points against conv(PF) by LP. Usage: python vertices.py dA dX dB dY N"""
import itertools, sys, numpy as np
from scipy.optimize import linprog
dA,dX,dB,dY,N = map(int, sys.argv[1:6]); rng=np.random.default_rng(0)
idx=lambda a,b,x,y: ((a*dB+b)*dX+x)*dY+y; n=dA*dB*dX*dY
rows=[]
for f in itertools.product(range(dX),repeat=dA):
  for g in itertools.product(range(dY),repeat=dB):
    r=np.zeros(n)
    for a in range(dA):
      for b in range(dB): r[idx(a,b,f[a],g[b])]=1
    rows.append(r)
Aeq=np.unique(np.array(rows),axis=0); beq=np.ones(len(Aeq))
# deterministic processes = functions (x,y)->(a,b); valid ones are PFs
PF=[]
for w in itertools.product(range(dA*dB),repeat=dX*dY):
  v=np.zeros(n)
  for k,ab in enumerate(w): v[idx(ab//dB,ab%dB,k//dY,k%dY)]=1
  if np.allclose(Aeq@v,1): PF.append(v)
PF=np.array(PF); print("PFs:",len(PF))
nondet=0; seen=set()
for t in range(N):
  res=linprog(rng.standard_normal(n),A_eq=Aeq,b_eq=beq,bounds=(0,None),method='highs-ds')
  v=res.x; seen.add(tuple(np.round(v,6)))
  if not np.allclose(v,np.round(v),atol=1e-7): nondet+=1; print("NONDETERMINISTIC vertex",v)
print("distinct vertices found:",len(seen),"non-deterministic:",nondet)
# hull check of random valid points (averages of 4 random LP vertices)
bad=0
for t in range(50):
  q=np.mean([linprog(rng.standard_normal(n),A_eq=Aeq,b_eq=beq,bounds=(0,None),method='highs-ds').x for _ in range(4)],axis=0); h=linprog(np.zeros(len(PF)),A_eq=np.vstack([PF.T,np.ones(len(PF))]),b_eq=np.append(q,1),bounds=(0,None))
  bad+= h.status!=0
print("interior points outside conv(PF):",bad)
