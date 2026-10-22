# Appendix H(A): structural classes of 3-party binary classical processes.
# p stored as M[i,o] (i = inputs (a,b,c), o = outputs (x,y,z)), like hull.py.
import numpy as np, itertools as it, json, sys
from scipy.optimize import linprog
B3=list(it.product((0,1),repeat=3)); idx={t:n for n,t in enumerate(B3)}
PFs=np.load('../pfs.npy') if False else None
import os
here=os.path.dirname(os.path.abspath(__file__))
PFs=np.load(os.path.join(here,'..','pfs.npy')) if os.path.exists(os.path.join(here,'..','pfs.npy')) else None
if PFs is None:
    sys.path.insert(0,os.path.join(here,'..')); os.chdir(os.path.join(here,'..')); import hull; PFs=hull.PFs; os.chdir(here)
fs=list(it.product((0,1),repeat=2))
def var(i,o): return idx[i]*8+idx[o]
# validity: sum_i p(i|f(i))=1 for all deterministic local f
Aeq=[];beq=[]
for f in it.product(fs,repeat=3):
    r=np.zeros(64)
    for i in B3: r[var(i,tuple(f[k][i[k]] for k in range(3)))]+=1
    Aeq.append(r);beq.append(1)
def first_marg(k):   # sum_{i: i_k=a} p(i|o) independent of o
    rows=[]
    for a in (0,1):
        for o in B3[1:]:
            r=np.zeros(64)
            for i in B3:
                if i[k]==a: r[var(i,o)]+=1; r[var(i,B3[0])]-=1
            rows.append(r)
    return rows
def first_valid(k):  # A first and conditional (unnormalised) bipartite process valid for each (a, o_k)
    rows=first_marg(k); o2=[j for j in range(3) if j!=k]
    for a in (0,1):
      for ok in (0,1):
        for g in it.product(fs,repeat=2):
          r=np.zeros(64)
          for i in B3:
            if i[k]!=a: continue
            o=[0,0,0]; o[k]=ok
            for t,j in enumerate(o2): o[j]=g[t][i[j]]
            r[var(i,tuple(o))]+=1
          # minus the same at reference g0 = constant 0 outputs, ok=0
          for i in B3:
            if i[k]!=a: continue
            r[var(i,(0,0,0))]-=1
          rows.append(r)
    return rows
def last(k):        # p independent of o_k
    rows=[]
    for i in B3:
        for o in B3:
            if o[k]==1:
                r=np.zeros(64); o0=list(o); o0[k]=0; r[var(i,o)]+=1; r[var(i,tuple(o0))]-=1; rows.append(r)
    return rows
Pf=PFs.reshape(len(PFs),-1)
def in_hull(v):
    n=len(Pf); A=np.vstack([Pf.T,np.ones(n)]); b=np.append(v,1)
    return linprog(np.zeros(n),A_eq=A,b_eq=b,bounds=(0,None),method='highs').status==0
def sample(extra,N,seed=0):
    rng=np.random.default_rng(seed); A=np.array(Aeq+extra); b=np.array(beq+[0]*len(extra),float)
    seen={};nondet=0;out=0
    for _ in range(N):
        r=linprog(rng.standard_normal(64),A_eq=A,b_eq=b,bounds=(0,1),method='highs-ds')
        v=np.round(r.x,9); key=tuple(v)
        if key in seen: continue
        det=np.all((np.abs(v)<1e-7)|(np.abs(v-1)<1e-7)); h=in_hull(v)
        seen[key]=1; nondet+=(not det); out+=(not h)
    return len(seen),nondet,out
def check(v,rows): return float(np.max(np.abs(np.array(rows)@v))) if rows else 0
if __name__=='__main__':
    reps=json.load(open(os.path.join(here,'..','reps.json')))
    C=np.zeros((8,8));Cb=np.zeros((8,8))
    for o in B3:
        i=(o[2],o[0],o[1]); C[idx[i],idx[o]]=1; Cb[idx[tuple(1-t for t in i)],idx[o]]=1
    E=((C+Cb)/2).ravel()
    pts=[('E_ex1',E)]+[('orbit%d'%n,np.array(r[0]).reshape(8,8).ravel()) for n,r in enumerate(reps)]
    res={}
    for name,v in pts:
        res[name]={'marg_first':[k for k in range(3) if check(v,first_marg(k))<1e-9],
                   'first_valid':[k for k in range(3) if check(v,first_valid(k))<1e-9],
                   'last':[k for k in range(3) if check(v,last(k))<1e-9],'in_hull':in_hull(v)}
        print(name,res[name],flush=True)
    stats={}
    for nm,ex in [('A_last',last(0)),('A_first_valid',first_valid(0)),('A_marg_first',first_marg(0))]:
        stats[nm]=sample(ex,int(sys.argv[1]) if len(sys.argv)>1 else 300); print(nm,'distinct vertices, nondet, outside hull:',stats[nm],flush=True)
    json.dump({'points':res,'sampling':stats},open(os.path.join(here,'classes.json'),'w'),indent=1)
