"""SH_grp (H.17.8) on the saved tuned-cancellation nsearch2 boards (ns2_*.json 'ex': P, class k, generators g).
nsearch2 reuses a class only with the identical V, so same k <=> same V exactly; SH_grp depends only on
X-parts of P and of the class generators, so this check is exact for these boards."""
import json,glob,itertools as it
px=lambda s:s&7
def grp(g):
    H={0}
    for x in g: H|={h^px(x) for h in H}
    return H
tot=0;fail=0;shf=0;rows=[]
for f in sorted(glob.glob('ns2_*.json')):
    for e in json.load(open(f))['ex']:
        P,k,g=e['P'],e['k'],e['g']; H=[grp(x) for x in g]; bad=0
        for o in range(8):
            for q in range(o+1,8):
                if k[o]==k[q]: continue
                D=o^q; a=px(P[o])^px(P[q])
                if any(((a^t^u)&D)==D for t in H[k[o]] for u in H[k[q]]): bad+=1
        tot+=1; fail+=bad>0; shf+=e['shbad']>0
        rows.append((f,e['shbad'],bad,len(g),sorted(map(sorted,H))))
for r in rows: print(*r)
print('SUMMARY boards',tot,'SH_fail',shf,'SH_grp_fail',fail)
