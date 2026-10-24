"""Realise every tclose3 candidate: solve for class parameters giving exactly the pattern S_ab (all coefficients nonzero),
build U_o = P_o V_k, check the Pauli rule (admissibility) and the facets (max over source states), and run the PF-blend LP
at random source states."""
import json, numpy as np, ast, collections
from scipy.optimize import least_squares
from lib3 import *
import importlib.util,sys
src=open('tbcheck.py').read().split('if __name__!=')[0]; ns={}; exec(src,ns); lp=ns['lp']; shgrp_r=ns['shgrp_r']
T,canon=load_facets(); rng=np.random.default_rng(3)
def mkV(g,v): return v[0]*np.eye(8)+1j*sum(v[m+1]*HM[g[m]] for m in range(len(g)))
def realise(ga,gb,S):
    na,nb=len(ga)+1,len(gb)+1
    for _ in range(200):
        x0=rng.normal(size=na+nb)
        def f(x):
            va=x[:na]/np.linalg.norm(x[:na]); vb=x[na:]/np.linalg.norm(x[na:])
            c=pauli_coeffs(mkV(gb,vb)@mkV(ga,va).conj().T)
            return np.r_[[c[s].real for s in range(64) if s not in S],[c[s].imag for s in range(64) if s not in S]]
        r=least_squares(f,x0,xtol=1e-15,ftol=1e-15,gtol=1e-15)
        va=r.x[:na]/np.linalg.norm(r.x[:na]); vb=r.x[na:]/np.linalg.norm(r.x[na:])
        if np.abs(f(r.x)).max()<1e-12 and min(np.abs(va).min(),np.abs(vb).min())>0.05:
            c=pauli_coeffs(mkV(gb,vb)@mkV(ga,va).conj().T)
            if all(abs(c[s])>1e-6 for s in S): return va,vb
    return None
rows=[l for l in open('tclose3.log') if l.startswith('CANDIDATE')]
stat=collections.Counter(); ex=[]
for l in rows:
    j=l.split(' ',1)[1]; i=j.index(') {'); job=ast.literal_eval(j[:i+1]); res=ast.literal_eval(j[i+2:])
    ga,gb,S=job; r=realise(ga,gb,set(S))
    if r is None: stat['not realisable']+=1; continue
    va,vb=r; V=[np.eye(8),mkV(ga,va),mkV(gb,vb)]
    U=np.array([PM[P]@V[k] for P,k in res['board']])
    rr=rule_residual(U); fv=float(facet_viol(U,T).max()); sg=shgrp_r(U)
    stat[('rule_ok',rr<1e-20,'facet_viol>1e-9',fv>1e-9,'SHgrp_r_numeric_bad>0',sg[0]>0)]+=1
    if len(ex)<5: ex.append(dict(job=job,board=res['board'],rule=rr,facet=fv,shgrp_r=sg))
print(dict(stat)); [print(e) for e in ex]
