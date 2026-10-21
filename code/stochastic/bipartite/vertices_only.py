"""Vertex-only check for larger alphabets (no PF enumeration): sample LP vertices of the
bipartite validity polytope with random objectives and test each for 0/1 entries.
A 0/1 valid process is a process function. Usage: python vertices_only.py dA dX dB dY N"""
import itertools, sys, numpy as np
from scipy.optimize import linprog
dA,dX,dB,dY,N = map(int, sys.argv[1:6]); rng=np.random.default_rng(1)
idx=lambda a,b,x,y: ((a*dB+b)*dX+x)*dY+y; n=dA*dB*dX*dY
rows=[]
for f in itertools.product(range(dX),repeat=dA):
  for g in itertools.product(range(dY),repeat=dB):
    r=np.zeros(n)
    for a in range(dA):
      for b in range(dB): r[idx(a,b,f[a],g[b])]=1
    rows.append(r)
Aeq=np.unique(np.array(rows),axis=0); beq=np.ones(len(Aeq))
seen=set(); nd=0
for t in range(N):
  v=linprog(rng.standard_normal(n),A_eq=Aeq,b_eq=beq,bounds=(0,None),method='highs-ds').x
  seen.add(tuple(np.round(v,6))); nd+= not np.allclose(v,np.round(v),atol=1e-7)
print("distinct vertices:",len(seen),"non-deterministic:",nd)
