"""Round 20 (H.27.1): EXACT certificate that Lugano-wired no-signalling boxes satisfy every facet of the 10 open orbits.
For a representative facet f and a Lugano sign variant w, the facet value of p(i|o)=P(i|w(o)) is an affine function g of the NS box P.
(1) exact g: the unique affine function on the NS affine space with g(D) = valsI[PF(D o w), f] (an integer) on each of the 64 local
    deterministic boxes D (they affinely span the NS space; D o w is a process function);
(2) exact LP dual: y rational with reduced costs r = c - A^T y >= 0 (A = normalisation + no-signalling equalities), so that for every
    NS box g(P) = r.P + b.y + c0 >= b.y + c0; we verify b.y + c0 equals the minimum over local boxes (0 or a positive integer).
All arithmetic in Fraction after the float LP supplies the support and an initial dual."""
from fractions import Fraction as Fr
from scipy.optimize import linprog
from h20_common import *
from h20_fwd_ns import lug, wmap, Aeq, beq
PFIDX={tuple(int(np.argmax(PF[n][:,o])) for o in range(8)):n for n in range(744)}
def rref_solve(M,rhs,free_default):
    """Solve M z = rhs exactly (Fractions); free variables set to free_default[j]; raises if inconsistent."""
    m=len(M); n=len(M[0]); R=[[Fr(v) for v in M[r]]+[Fr(rhs[r])] for r in range(m)]; piv=[]; row=0
    for col in range(n):
        p=next((r for r in range(row,m) if R[r][col]!=0),None)
        if p is None: continue
        R[row],R[p]=R[p],R[row]; inv=1/R[row][col]; R[row]=[v*inv for v in R[row]]
        for r in range(m):
            if r!=row and R[r][col]!=0:
                fac=R[r][col]; R[r]=[a-fac*b for a,b in zip(R[r],R[row])]
        piv.append(col); row+=1
        if row==m: break
    for r in range(row,m):
        if R[r][n]!=0: raise ValueError('inconsistent')
    z=[Fr(v) for v in free_default]; pset=set(piv)
    for r,col in enumerate(piv):
        z[col]=R[r][n]-sum(R[r][j]*z[j] for j in range(n) if j not in pset and R[r][j]!=0)
    return z
LOC=[tuple(tuple(g) for g in gg) for gg in it.product(list(it.product((0,1),repeat=2)),repeat=3)]   # g[k][x_k] = i_k
def Dvec(g):
    v=[0]*64
    for x in range(8): v[8*B3.index(tuple(g[k][B3[x][k]] for k in range(3)))+x]=1
    return v
DV=[Dvec(g) for g in LOC]
Aq=[[Fr(int(a)) for a in row] for row in Aeq]; bq=[Fr(int(b)) for b in beq]
def certify(f,parts):
    wm=wmap(parts); xo=[B3.index(wm[o]) for o in range(8)]
    vals=[]
    for g in LOC:
        fun=tuple(B3.index(tuple(g[k][B3[xo[o]][k]] for k in range(3))) for o in range(8)); vals.append(Fr(int(valsI[PFIDX[fun],f])))
    # exact affine g: c.P + c0 with c.D + c0 = val for all 64 local boxes
    cz=rref_solve([d+[1] for d in DV],vals,[0]*65); c=cz[:64]; c0=cz[64]
    assert all(sum(ci*di for ci,di in zip(c,d))+c0==v for d,v in zip(DV,vals))
    cf=np.array([float(x) for x in c]); r=linprog(cf,A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*64,method='highs')
    y0=r.eqlin.marginals; red=cf-Aeq.T@y0; Z=[j for j in range(64) if red[j]<1e-7]
    y=rref_solve([[Aq[i][j] for i in range(len(Aq))] for j in Z],[c[j] for j in Z],[Fr(v).limit_denominator(10**6) for v in y0])
    rr=[c[j]-sum(Aq[i][j]*y[i] for i in range(len(Aq))) for j in range(64)]
    bound=sum(b*yy for b,yy in zip(bq,y))+c0
    assert all(isinstance(v,Fr) for v in rr+[bound]+c), "non-exact arithmetic"
    return min(rr)>=0, bound, min(vals)
if __name__=='__main__':
    allok=True
    for orb in OPEN:
        f=REP[orb]; row=[]
        for parts in lug:
            ok,bound,locmin=certify(f,parts); row.append((ok,str(bound),str(locmin))); allok&=ok and bound>=0 and bound==locmin
        print(f'orbit {orb} facet {f}: (dual feasible, exact NS lower bound, local min) per Lugano variant:',row,flush=True)
    print('ALL CERTIFIED (dual feasible, NS bound = local min >= 0):',allok)
