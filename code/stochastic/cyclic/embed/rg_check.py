"""H.15.7(A'): brute-force checker of the Vanrietvelde-Ormrod-Kristjansson-Barrett validity rules (arXiv:2206.10042v3, Sec. 3:
Defs 3.1-3.7, Principles 1-2) for small routed graphs, applied to the Fourier-sector station candidate for the boards.
Graph: arrows {name:(src,dst,{value:dim})} (src/dst None = global in/out, trivial index); nodes {name:route}, route = set of
(in_tuple,out_tuple) over the node's in/out arrows in sorted order."""
import itertools as it, numpy as np, json
def analyse(arrows,routes,label):
    nodes=sorted(routes); ins={N:sorted(a for a,(s,d,_) in arrows.items() if d==N) for N in nodes}
    outs={N:sorted(a for a,(s,d,_) in arrows.items() if s==N) for N in nodes}
    def branches(R):   # Def 3.2: connected components of the bipartite relation; check branched
        I={i for i,_ in R}; br=[]
        for i in I:
            O=frozenset(o for j,o in R if j==i)
            for b in br:
                if b[1]&O:
                    assert b[1]==O,'route not branched'; b[0].add(i); break
            else: br.append([{i},O])
        return [(frozenset(a),b) for a,b in br]
    def univocal(ins,outs,routes):
        Br={N:branches(routes[N]) for N in nodes}; keys=[(N,j) for N in nodes for j in range(len(Br[N]))]
        names=sorted(arrows); cons=[]
        for vals in it.product(*[sorted(arrows[a][2]) for a in names]):
            v=dict(zip(names,vals)); asg={}
            for N in nodes:
                i=tuple(v[a] for a in ins[N]); o=tuple(v[a] for a in outs[N])
                if (i,o) not in routes[N]: break
                asg[N]=(next(j for j,(I,O) in enumerate(Br[N]) if i in I),o)
            else: cons.append((v,asg))
        cyl={}    # (Happens, choices on happening branches) cylinders in the space of bifurcation choices
        for v,asg in cons: cyl[frozenset((N,j,o) for N,(j,o) in asg.items())]=v
        C=list(cyl); size=lambda c:int(np.prod([len(Br[N][j][1]) for N,j in keys if (N,j) not in {(a,b) for a,b,_ in c}]))
        tot=int(np.prod([len(Br[N][j][1]) for N,j in keys]))
        def compat(c1,c2,skip=None):
            d1={(a,b):o for a,b,o in c1}; d2={(a,b):o for a,b,o in c2}
            return all(d1[k]==d2[k] for k in d1 if k in d2 and k!=skip)
        overl=any(compat(C[i],C[j]) for i in range(len(C)) for j in range(i))
        ok=(not overl) and sum(size(c) for c in C)==tot
        dep=set()   # functional dependence: choice at branch X -> Happens of branch Y
        hap=lambda c,Y: Y in {(a,b) for a,b,_ in c}
        if ok:
            for c1,c2 in it.combinations(C,2):
                for X in keys:
                    if compat(c1,c2,X):
                        for Y in keys:
                            if hap(c1,Y)!=hap(c2,Y): dep.add((X,Y))
        return ok,Br,keys,cons,dep
    okf,Br,keys,cons,depf=univocal(ins,outs,routes)
    rt={N:{(o,i) for i,o in routes[N]} for N in nodes}
    okb,_,_,_,depb=univocal(outs,ins,rt)
    print(f'[{label}] univocal: {okf}; adjoint univocal: {okb}; branches:',{N:len(Br[N]) for N in nodes})
    if not(okf and okb): return
    E=set()
    for a,(s,d,ix) in arrows.items():
        if s is None or d is None: continue
        for j in range(len(Br[s])):
            for k in range(len(Br[d])):
                vs={v[a] for v,asg in cons if asg[s][0]==j and asg[d][0]==k}
                if vs and not(len(vs)==1 and ix[next(iter(vs))]==1): E.add(((s,j),(d,k),'solid'))
    E|={(X,Y,'green') for X,Y in depf if X!=Y}|{(Y,X,'red') for X,Y in depb if X!=Y}
    adj={}
    for u,v,t in E: adj.setdefault(u,[]).append((v,t))
    def cycle(start):   # DFS for a simple cycle through start; report the first non-weak one
        st=[(start,[start],[])]
        while st:
            u,path,ty=st.pop()
            for v,t in adj.get(u,[]):
                if v==start and len(set(ty+[t]))>1 or v==start and t=='solid': return path,ty+[t]
                if v not in path and len(path)<8: st.append((v,path+[v],ty+[t]))
    bad=next((c for c in (cycle(n) for n in adj) if c),None)
    print(f'[{label}] branch-graph arrows: {len(E)}; weak loops principle: {bad is None}'+('' if bad is None else f'; non-weak loop: {" -> ".join(f"{N}^{j}" for N,j in bad[0])} -> back, arrow types {bad[1]}'))
    return bad
B3=list(it.product((0,1),repeat=3))
# ---- Fourier-sector station candidate (routes do not depend on the phases: same graph for Lugano, H.12, H.13.2, Z8) ----
ar={'P':('S','Phi',{z:1 for z in range(8)}),'M':('Phi','D',{z:1 for z in range(8)}),'F':('Phi',None,{0:8})}
for k in 'ABC': ar['I'+k]=('D',k,{0:2}); ar['O'+k]=(k,'Phi',{0:1,1:1})
R={'S':{((),(z,)) for z in range(8)},'D':{((z,),(0,0,0)) for z in range(8)},
   'Phi':{((o[0],o[1],o[2],z),(0,z)) for o in B3 for z in range(8)}}
for k in 'ABC': R[k]={((0,),(o,)) for o in (0,1)}
analyse(ar,R,'Fourier station: S -Hd.phi-> Phi(o-controlled phase on z) -Hd-> agents')
# calibration 1: a fixed-order circuit A -> B through a sectorised wire (valid)
analyse({'x':('A','B',{0:1,1:1}),'y':('B',None,{0:2}),'w':(None,'A',{0:2})},{'A':{((0,),(0,)),((0,),(1,))},'B':{((0,),(0,)),((1,),(0,))}},'calibration: A -> B (valid expected)')
# calibration 2: two agents in a loop, unindexed (invalid expected)
analyse({'x':('A','B',{0:2}),'y':('B','A',{0:2})},{'A':{((0,),(0,))},'B':{((0,),(0,))}},'calibration: A <-> B loop (invalid expected)')
# variant: o recorded on an internal indexed wire Phi -> Fo (so Phi's branches are labelled by (o,z))
ar2=dict(ar); ar2['F']=('Phi','Fo',{o:1 for o in range(8)}); ar2['G']=('Fo',None,{0:8})
R2=dict(R); R2['Phi']={((o[0],o[1],o[2],z),(B3.index(o),z)) for o in B3 for z in range(8)}; R2['Fo']={((o,),(0,)) for o in range(8)}
analyse(ar2,R2,'Fourier station, o-indexed record')
# fleshing out (exact, integers): with S = Hd.phi, Phi = sum_o |o><o| (x) diag((-1)^{m_o(z)/2}) (sector-preserving on z, so it
# follows the route), D = Hd, the composite is V_o = Hd D_o Hd = 8 U_o -- the H.13.2 unitary; check D_o diagonal & unimodular.
m=json.load(open('../switchboard/h13/min_cex.json'))['m']
print('fleshing out H.13.2: Phi follows the route (diagonal, entries +-1):',all(m[o][z]%2==0 for o in range(8) for z in range(8)))
