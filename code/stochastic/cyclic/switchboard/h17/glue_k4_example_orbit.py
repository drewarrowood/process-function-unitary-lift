"""H.26.1a check: run glue_k4.work on EVERY member of the orbits of the worked examples g = 3424 and g = 37 (not just the
canonical representative), to illustrate that orbit members give the same answer (same job count, 0 candidates, 0 UNRESOLVED)."""
import json, time, glue_k4 as K
orbits={3424:[3424, 3430, 3598, 3604, 4576, 4582, 6205, 6211],
        37:[37, 42, 97, 218, 244, 295, 567, 575, 615, 791, 1207, 1225, 1272, 2936, 3091, 3130, 3408, 3606, 3621, 3629, 3669, 3845, 4518, 6402]}
it_=dict((gi,(gi,L,cid)) for gi,L,cid in K.items())
for g0,orb in orbits.items():
    t0=time.time(); res=[K.work(it_[g]) for g in orb]
    print(f'orbit of {g0}: members {len(orb)}; (g, jobs, cand, unres) =',[(r["g"],r["jobs"],len(r["cand"]),r["unres"]) for r in res],f'; {time.time()-t0:.0f} s',flush=True)
