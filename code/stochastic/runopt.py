import json, numpy as np, opt
R=json.load(open('reps.json')); fn='opt_results.jsonl'
try: done={json.loads(l)['i'] for l in open(fn)}
except FileNotFoundError: done=set()
order=sorted(range(len(R)),key=lambda i:sum(v>1e-9 for v in R[i][0]))
for i in order:
    if i in done: continue
    k,cnt=R[i]; res=opt.search(np.array(k).reshape(8,8),restarts=2,maxiter=1500)
    res.update(i=i,count=cnt,vals=sorted(set(round(v,4) for v in k if v>1e-9)))
    open(fn,'a').write(json.dumps(res)+'\n'); print(res,flush=True)
