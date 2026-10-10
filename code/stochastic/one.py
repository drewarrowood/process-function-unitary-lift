import json, sys, time, numpy as np, opt
i=int(sys.argv[1]); R=json.load(open('reps.json')); k,cnt=R[i]; t=time.time()
res=opt.search(np.array(k).reshape(8,8),restarts=1,maxiter=int(sys.argv[2]))
res.update(i=i,count=cnt,secs=round(time.time()-t),maxiter=int(sys.argv[2]))
open('opt_results.jsonl','a').write(json.dumps(res)+'\n'); print(res,flush=True)
