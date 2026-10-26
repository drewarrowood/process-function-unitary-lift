"""Round 23 (H.30.1): is Valid ∩ S inside conv(PF)?  Float LP minimum over Valid ∩ S of every one of the 29,344 facets of the PF hull,
for families given as comp:i or rule:i.  usage: fam1,fam2,..."""
import sys, numpy as np
from scipy.optimize import linprog
from h23_span import *
from h23_span_lp import Aeq
from h20_common import Tn, canon
for fam in sys.argv[1].split(','):
    kind,ci=fam.split(':'); ci=int(ci)
    G=span_gens((lambda z,zp:opat_comp(ci,z,zp)) if kind=='comp' else (lambda z,zp:opat_rule(ci,z,zp))).astype(float)
    Q,sv,_=np.linalg.svd(G.T,full_matrices=False); d=int((sv>1e-9).sum()); Bs=Q[:,:d]
    vals=np.array([ (lambda lp: lp.fun+Tn[f,64] if lp.status==0 else np.nan)(linprog(Bs.T@Tn[f,:64],A_ub=-Bs,b_ub=np.zeros(64),A_eq=Aeq@Bs,b_eq=np.ones(64),bounds=[(None,None)]*d,method='highs')) for f in range(len(Tn))])
    bad=np.where(vals<-1e-9)[0]
    print(fam,'dim S',d,'facets with LP min < -1e-9:',len(bad),'min %.4g'%np.nanmin(vals),'orbits:',sorted(set(canon[bad].tolist()))[:40],flush=True)
