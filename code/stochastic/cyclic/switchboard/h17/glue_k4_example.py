"""Worked example for H.26.1a: rerun the glue_k4 search on ONE canonical geometry, with full instrumentation.
Usage: python3 glue_k4_example.py [g=37]
Prints: the geometry (classes, labels as Pauli strings), its symmetry orbit among the 21,906 labelled geometries, every job
(support assignment) with the supports, and for each job what happens in the solver: quick exit, which root pairs are possible,
how many survive arc consistency, DFS nodes, leaves reached and why each leaf is rejected.  The instrumented solver below is a
line-by-line copy of glue_k4.solve with counters added; its verdict is asserted equal to glue_k4.solve's on every job.
Then the LOOSEN=1 control (leaf = 'hard admissible board', no root, no SH test) on the same jobs, and a recheck of the record
in glue_k4_done.jsonl.  Everything is exact integer/boolean arithmetic (numpy bool arrays, Python ints); no floating point."""
import sys, json, itertools as it, numpy as np, importlib, os
g=int(sys.argv[1]) if len(sys.argv)>1 else 37
os.environ.pop('LOOSEN',None)
import glue_k4 as K
from glue_k4 import assignments, FORB, XOR, aff, qp
from t3sym import G, cls_act, pbits
def pstr(s):
    x=s&7; z=s>>3; out=''
    for p in range(3):
        b=((x>>p)&1,(z>>p)&1); out+={(0,0):'I',(1,0):'X',(0,1):'Z',(1,1):'Y'}[b]
    return out
T=json.load(open('glue_k4_tuples.json'))
items=dict((gi,(L,cid)) for gi,L,cid in K.items())
L,cid=items[g]
print(f'geometry g = {g} (raw index into glue_k4_tuples.json): {T[g]}')
print('Pauli strings are written qubit A, B, C (= parties 0, 1, 2); s = x-bits + 8*z-bits.')
for c in range(4):
    vs=[v for v in range(8) if cid[v]==c]; lab=L[c]
    desc='identity class (label ())' if not lab else ('two-term class  alpha + i beta ' + pstr(lab[0])) if len(lab)==1 else ('three-term class alpha + i(beta '+pstr(lab[0])+' + gamma '+pstr(lab[1])+')')
    edge=vs[0]^vs[1]; print(f'  class {c}: vertices {vs} (o = {[format(v,"03b")[::-1] for v in vs]} as bits A B C), edge direction e_{edge.bit_length()-1}, label {lab} = {[pstr(s) for s in lab]}: {desc}')
# orbit of this geometry among all labelled geometries (same key as glue_k4_audit.py)
import ast
def lab_of(t):
    pr=ast.literal_eval(t['geo'][0]); c_={v:i for i,p in enumerate(pr) for v in p}
    order=[c_[0]]+[i for i in range(4) if i!=c_[0]]
    LL={order[j]:tuple(t['cls'][j]) for j in range(4)}
    return [(LL[c_[v]],c_[v]) for v in range(8)]
def orbit_key(lab):
    best=None
    for gg in G:
        pi=gg[0]; acted=[None]*8
        for v in range(8):
            l_,c_=lab[v]; acted[pbits(v,pi)]=(cls_act(gg,l_) if l_ else (),c_)
        for t in range(8):
            ren={}; tup=[]
            for w in range(8):
                l_,c_=acted[w^t]; ren.setdefault(c_,len(ren)); tup.append((l_,ren[c_]))
            tup=tuple(tup)
            if best is None or tup<best: best=tup
    return best
k0=orbit_key(lab_of(T[g])); orbit=[i for i,t in enumerate(T) if orbit_key(lab_of(t))==k0]
canon=set(json.load(open('glue_k4_canon.json')))
print(f'orbit under 8 translations x |G48| = {len(G)} symmetries: {len(orbit)} labelled geometries {orbit}; canonical representative(s) in glue_k4_canon.json: {[i for i in orbit if i in canon]}')
for i in orbit[:4]:
    if i!=g: print(f'  e.g. orbit member {i}: {T[i]}')
def solve_instr(cid,Sd,stats):
    SS={}
    for c in range(4):
        SS[(c,c)]=[0]
        for d in range(4):
            if c<d: SS[(c,d)]=SS[(d,c)]=sorted(Sd[(c,d)])
    AL={}
    for u in range(8):
        for w in range(8):
            if u==w: continue
            D=u^w; ok=np.ones((64,64),bool)
            for s in SS[(cid[u],cid[w])]: ok&=~FORB[D][XOR^s]
            AL[(u,w)]=ok
    mono={(c,d):len({s&7 for s in SS[(c,d)]})==1 for c in range(4) for d in range(4)}
    FA={}
    for r in range(4):
        Af={c:aff([s&7 for s in SS[(c,r)]]) for c in range(4)}
        for u in range(8):
            for w in range(u+1,8):
                c,d=cid[u],cid[w]; D=u^w
                FA[(r,u,w)]=np.array([(not mono[(c,d)]) and any(((a^x^y)&D)==D for x in Af[c] for y in Af[d]) for a in range(8)])
    def nonhard(P):
        for p in range(3):
            if all(((P[u]^P[u^(1<<p)]^s)&7)==0 for u in range(8) for s in SS[(cid[u],cid[u^(1<<p)])]): return ('W-level-last party',p)
            if all(qp(P[u]^P[w]^s,p)==(0,0) for u in range(8) for w in range(8) if u!=w for s in SS[(cid[u],cid[w])]): return ('operator-first party',p)
        return None
    def fails_all(P):
        nh=nonhard(P)
        if nh: stats['leaf_rejected_nonhard'].append(nh); return False
        for r in range(4):
            if not any(FA[(r,u,w)][(P[u]^P[w])&7] for u in range(8) for w in range(u+1,8)):
                stats['leaf_rejected_SH_holds_for_class'].append(r); return False
        return True
    r0=cid[0]
    dom={v:np.ones(64,bool) for v in range(8)}; dom[0]=np.zeros(64,bool); dom[0][0]=True; ch=True
    while ch:
        ch=False
        for v in range(8):
            for w in range(8):
                if v==w: continue
                nd=dom[v]&AL[(v,w)][:,dom[w]].any(1)
                if not nd.any(): stats['quick_exit']=f'vertex {v} has no admissible Pauli (arc consistency with vertex {w})'; return None
                if (nd!=dom[v]).any(): dom[v]=nd; ch=True
    stats['domain_sizes_after_plain_AC']=[int(dom[v].sum()) for v in range(8)]
    for u0,w0 in it.combinations(range(8),2):
        if not FA[(r0,u0,w0)].any(): stats['roots_impossible']+=1; continue
        stats['roots_possible'].append((u0,w0))
        C=dict(AL); fm=FA[(r0,u0,w0)][XOR&7]
        C[(u0,w0)]=AL[(u0,w0)]&fm; C[(w0,u0)]=C[(u0,w0)].T
        dom={v:np.ones(64,bool) for v in range(8)}; dom[0]=np.zeros(64,bool); dom[0][0]=True
        def ac(dom):
            ch=True
            while ch:
                ch=False
                for v in range(8):
                    for w in range(8):
                        if v==w: continue
                        nd=dom[v]&C[(v,w)][:,dom[w]].any(1)
                        if not nd.any(): return False
                        if (nd!=dom[v]).any(): dom[v]=nd; ch=True
            return True
        if not ac(dom): stats['roots_killed_by_AC'].append((u0,w0)); continue
        stats['roots_searched'].append((u0,w0)); P={}
        def dfs(dom):
            stats['dfs_nodes']+=1
            free=[v for v in range(8) if v not in P]
            if not free: stats['leaves']+=1; return fails_all(P)
            v=min(free,key=lambda v:dom[v].sum())
            for x in np.nonzero(dom[v])[0]:
                nd={w:dom[w].copy() for w in dom}; nd[v]=np.zeros(64,bool); nd[v][x]=True
                if not ac(nd): stats['ac_prunes']+=1; continue
                P[v]=int(x)
                if dfs(nd): return True
                del P[v]
            return False
        if dfs(dom): return dict(root=(u0,w0),P=P)
    return None
jobs=list(assignments(L,cid))
print(f'\njobs (support assignments surviving Lemmas A, B, C and the H.17.12(b) list): {len(jobs)}')
import collections
for j,Sd in enumerate(jobs):
    st=collections.defaultdict(list); st['dfs_nodes']=0; st['leaves']=0; st['ac_prunes']=0; st['roots_impossible']=0
    r=solve_instr(cid,Sd,st); r_ref=K.solve(cid,Sd); assert (r is None)==(r_ref is None) and r_ref!='UNRESOLVED'
    print(f'job {j}: supports S_cd of V_d V_c^dag (as Pauli strings):')
    for (c,d),S in sorted(Sd.items()): print(f'    S_{c}{d} = {{{", ".join(pstr(s) for s in sorted(S))}}}')
    if 'quick_exit' in st: print('    quick exit:',st['quick_exit'])
    else:
        print('    Pauli domains after plain arc consistency (P_0 = I fixed):',st['domain_sizes_after_plain_AC'])
        print(f'    root pairs (u,w) where SH_grp^r can fail for r = class of vertex 0: {len(st["roots_possible"])} of 28 ({st["roots_impossible"]} impossible from the supports alone)')
        print(f'    roots emptied by arc consistency: {len(st["roots_killed_by_AC"])}; roots searched by DFS: {len(st["roots_searched"])} {st["roots_searched"]}')
        print(f'    DFS nodes {st["dfs_nodes"]}, arc-consistency prunes {st["ac_prunes"]}, complete admissible boards (leaves) reached {st["leaves"]}')
        rej=collections.Counter(map(str,st['leaf_rejected_nonhard'])); rej2=collections.Counter(st['leaf_rejected_SH_holds_for_class'])
        print(f'    leaves rejected as non-hard (PF blend by H.1/H.6.2): {dict(rej)}; leaves rejected because SH_grp^r HOLDS for some class r (PF blend by H.17.11a): {dict(rej2)}')
    print('    verdict:', 'CANDIDATE' if r else 'no candidate (agrees with glue_k4.solve)')

# ---- Full enumeration of the job's admissible boards (only for small jobs): a brute-force cross-check of the DFS verdict ----
def all_boards(cid,Sd,cap=200000):
    SS={}
    for c in range(4):
        SS[(c,c)]=[0]
        for d in range(4):
            if c<d: SS[(c,d)]=SS[(d,c)]=sorted(Sd[(c,d)])
    AL={}
    for u in range(8):
        for w in range(8):
            if u==w: continue
            ok=np.ones((64,64),bool)
            for s in SS[(cid[u],cid[w])]: ok&=~FORB[u^w][XOR^s]
            AL[(u,w)]=ok
    out=[]; P={0:0}
    def rec(v):
        if len(out)>cap: return
        if v==8: out.append(dict(P)); return
        for x in range(64):
            if all(AL[(v,u)][x,P[u]] and AL[(u,v)][P[u],x] for u in P):
                P[v]=x; rec(v+1); del P[v]
    rec(1); return SS,out
def classify(cid,SS,P):
    mono={(c,d):len({s&7 for s in SS[(c,d)]})==1 for c in range(4) for d in range(4)}
    hard=True
    for p in range(3):
        if all(((P[u]^P[u^(1<<p)]^s)&7)==0 for u in range(8) for s in SS[(cid[u],cid[u^(1<<p)])]): hard=False
        if all(qp(P[u]^P[w]^s,p)==(0,0) for u in range(8) for w in range(8) if u!=w for s in SS[(cid[u],cid[w])]): hard=False
    fails={}
    for r in range(4):
        Af={c:aff([s&7 for s in SS[(c,r)]]) for c in range(4)}
        wit=[(u,w) for u in range(8) for w in range(u+1,8) if (not mono[(cid[u],cid[w])]) and any((((P[u]^P[w])&7^x^y)&(u^w))==(u^w) for x in Af[cid[u]] for y in Af[cid[w]])]
        fails[r]=wit
    return hard,fails
for j,Sd in enumerate(jobs):
    SS,B=all_boards(cid,Sd)
    if len(B)>200000: print(f'job {j}: more than 200000 admissible boards, brute force skipped'); continue
    nh=0; cnt=collections.Counter(); allfail=0; ex=None
    for P in B:
        hard,fails=classify(cid,SS,P)
        if not hard: continue
        nh+=1; key=tuple(r for r in range(4) if fails[r]); cnt[key]+=1
        if len(key)==4: allfail+=1
        if ex is None and fails[cid[0]]: ex=(P,fails)
    print(f'\nbrute force, job {j}: {len(B)} admissible boards with P_0 = I; {nh} hard; hard boards by the set of absorbed classes r for which SH_grp^r FAILS: {dict(cnt)}; failing for all four classes: {allfail}')
    if ex:
        P,fails=ex; print('  example hard board P_o =',{v:pstr(p) for v,p in sorted(P.items())})
        for r in range(4): print(f'    absorbed class {r}: SH_grp^r fails at {len(fails[r])} pairs {fails[r][:8]}{"..." if len(fails[r])>8 else ""}' if fails[r] else f'    absorbed class {r}: SH_grp^r HOLDS (no failing pair) -> PF blend by H.17.11a')
# LOOSEN control on the same jobs
os.environ['LOOSEN']='1'; K2=importlib.reload(K); n_hard=0
for Sd in jobs:
    r=K2.solve(cid,Sd)
    if r and r!='UNRESOLVED': n_hard+=1; ex=r
print(f'\nLOOSEN control (leaf = any hard admissible board, no root, no SH test): {n_hard} of {len(jobs)} jobs contain a hard admissible board',
      ('; example P_o = '+str({v:pstr(p) for v,p in sorted(ex['P'].items())})) if n_hard else '')
os.environ.pop('LOOSEN'); importlib.reload(K)
print(); rec=[json.loads(l) for l in open('glue_k4_done.jsonl') if json.loads(l)['g']==g]
print('record(s) in glue_k4_done.jsonl:',rec)
