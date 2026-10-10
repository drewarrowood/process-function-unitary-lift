import json, numpy as np, sys
from fast2 import analyse
import fast2, numpy.linalg as la
R=json.load(open('reps.json')); out=open('reps_results.jsonl','a')
done=set()
try: done={json.loads(l)['i'] for l in open('reps_results.jsonl')}
except: pass
for i,(k,cnt) in enumerate(R):
    if i in done: continue
    E=np.array(k).reshape(8,8); res=analyse(E); res.update(i=i,count=cnt,vals=sorted(set(round(v,4) for v in k if v>1e-9)))
    out.write(json.dumps({a:(bool(b) if isinstance(b,np.bool_) else (int(b) if isinstance(b,np.integer) else b)) for a,b in res.items()})+'\n'); out.flush()
    print(res,flush=True)
