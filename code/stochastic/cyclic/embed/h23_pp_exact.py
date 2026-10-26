"""Round 23 (H.30.2): exact validity of the phase-process branches of H.29.3, by characters.
For phi = x . m(o,z) on a branch {x : M x = 0 mod 2 pi} (all branches torsion-free, h23_pp_enum2.log), and for each nonempty set S
of parties, c in {0,1}^{-S} and z, z' with z_{-S} = z'_{-S}, the COPP condition (H.29.1) reads
    sum_{o_S} (-1)^{|o_S|} exp(i x.(m(o,z') - m(o,z))) = 0  for all x on the branch,   o = (o_S, c).
The exponentials are characters of the torus ker M (mod 2 pi); two of them agree iff the difference of their integer vectors lies in
rowspace(M) (i.e. is orthogonal to ker M), and distinct characters are linearly independent.  So the condition holds on the whole
branch iff, for every class of equal characters, the signed count sum (-1)^{|o_S|} is 0.  Exact (integer kernel basis).
Also: the two cyclic branches are analysed exactly, and all their valid subtori are checked to lie in one of the 34 components."""
import itertools as it, numpy as np, sympy, json
from h22_phaseproc import MONO
from h20_common import B3
import h23_pp_enum2_rows as R
mono=np.array([[[int(all(B3[o][a] for a in m[0]) and all(B3[z][b] for b in m[1])) for m in MONO] for z in range(8)] for o in range(8)])
def kerZ(M):
    K=sympy.Matrix(M).nullspace(); out=[]
    for v in K:
        den=sympy.ilcm(*[sympy.fraction(t)[1] for t in v]); out.append([int(t*den) for t in v])
    return np.array(out,dtype=np.int64).T if out else np.zeros((12,0),dtype=np.int64)
def check(M):
    K=kerZ(M); bad=[]
    for S in [s for r in (1,2,3) for s in it.combinations(range(3),r)]:
        R_=[k for k in range(3) if k not in S]
        for c in it.product((0,1),repeat=len(R_)):
            os=[]
            for oS in it.product((0,1),repeat=len(S)):
                b=[0,0,0]
                for k,v in zip(S,oS): b[k]=v
                for k,v in zip(R_,c): b[k]=v
                os.append((4*b[0]+2*b[1]+b[2],(-1)**sum(oS)))
            for z in range(8):
                for zp in range(8):
                    if any(B3[z][k]!=B3[zp][k] for k in R_): continue
                    keys={}
                    for o,s in os:
                        key=tuple(((mono[o,zp]-mono[o,z])@K).tolist()); keys[key]=keys.get(key,0)+s
                    if any(v!=0 for v in keys.values()): bad.append((S,c,z,zp))
    return bad
if __name__=='__main__':
    br=R.branches(); C=json.load(open('h22_pp_components.json'))
    nok=0; fail=[]
    for M in br:
        b=check(M)
        if b: fail.append((M,b))
        else: nok+=1
    print(len(br),'branches;',nok,'exactly valid on the whole torus;',len(fail),'not',flush=True)
    comps_ok=all(not check(np.array(c['rows'])) for c in C); print('all 34 components exactly valid:',comps_ok)
    for M,b in fail:
        K=kerZ(M); free=[j for j in range(12) if K[j].any()]
        print('non-valid branch: free coordinates',free,'; failing conditions',len(b),'(sets S:',sorted({x[0] for x in b}),')')
        # valid subset: by the factorisation (1-e^{i alpha dz})(1-e^{i beta dz'})(1-e^{i gamma dz''}) one free coefficient must vanish
        for j in free:
            sub=[q for q in free if q!=j]
            Msub=np.vstack([M]+[np.eye(12,dtype=int)[j]])
            ok=not check(Msub)
            inside=[ci for ci,c in enumerate(C) if all(np.array(c['rows'])[:,q].sum()==0 or False for q in []) ]
            # containment: the subtorus {x: x_q = 0 for q not in sub} lies in component ci iff rows of ci vanish on coordinates sub
            cont=[ci for ci,c in enumerate(C) if not np.array(c['rows'])[:,sub].any()]
            print(f'  x_{j} = 0: exactly valid {ok}; contained in components {cont}')
