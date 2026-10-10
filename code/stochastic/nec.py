import json, numpy as np, fast3
R=json.load(open('reps.json')); out=[]
for i,(k,c) in enumerate(R):
    d,supp,r,m,Xs,Lam=fast3.prep(np.array(k).reshape(8,8))
    out.append(dict(i=i,count=c,rank=int(r),dimVW=int(m),nec_ok=bool(m>=r))); print(out[-1],flush=True)
json.dump(out,open('nec_results.json','w'))
