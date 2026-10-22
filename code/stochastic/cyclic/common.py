import itertools as it, numpy as np, scipy.optimize as so
B3=list(it.product((0,1),repeat=3)); IX={t:n for n,t in enumerate(B3)}
def bits(n): return B3[n]
def all_pfs():
    """744 binary 3-party process functions as 8x8 0/1 matrices P[i,o]."""
    out=[]; F=[list(it.product((0,1),repeat=4))]
    # w_k depends on the other two outputs (self-dependence excluded: PFs have no self-loop)
    fs=list(it.product((0,1),repeat=4))
    for f0 in fs:
        for f1 in fs:
            for f2 in fs:
                def w(o): return (f0[2*o[1]+o[2]],f1[2*o[0]+o[2]],f2[2*o[0]+o[1]])
                ok=True
                for g in it.product(range(4),repeat=3):  # local functions bit->bit
                    fp=0
                    for o in B3:
                        i=w(o)
                        if all([(0,0),(1,1),(0,1),(1,0)][g[k]][i[k]]==o[k] for k in range(3)): fp+=1
                    if fp!=1: ok=False;break
                if ok:
                    P=np.zeros((8,8))
                    for o in B3: P[IX[w(o)],IX[o]]=1
                    out.append(P)
    U=[];S=set()
    for P in out:
        k=P.tobytes()
        if k not in S: S.add(k);U.append(P)
    return U
def in_hull(p,pfs):
    """LP: min ||p - sum l_j P_j||_1 over convex l; returns distance (0 => in hull)."""
    n=len(pfs); A=np.array([P.ravel() for P in pfs]).T; m=A.shape[0]
    # vars: l (n), s+ (m), s- (m)
    c=np.r_[np.zeros(n),np.ones(2*m)]
    Aeq=np.block([[A,np.eye(m),-np.eye(m)],[np.ones((1,n)),np.zeros((1,2*m))]])
    beq=np.r_[p.ravel(),1]
    r=so.linprog(c,A_eq=Aeq,b_eq=beq,bounds=(0,None),method='highs'); return r.fun
def valid(p):
    """classical validity: p[i,o]>=0 and sum_i p(i|f(i))=1 for all 64 local function triples."""
    vals=[]
    for g in it.product(range(4),repeat=3):
        s=0
        for i in B3:
            o=tuple([(0,0),(1,1),(0,1),(1,0)][g[k]][i[k]] for k in range(3)); s+=p[IX[i],IX[o]]
        vals.append(s)
    return min(vals),max(vals),p.min()
def opfirst(V,dP):
    """V as array [i(8), f, o(8), s(dP)] (out x in). residual of 'no O -> I_k' for k=0,1,2."""
    res=[]
    dF=V.shape[1]
    T=V.reshape(2,2,2,dF,8,dP)
    for k in range(3):
        Tk=np.moveaxis(T,k,0).reshape(2,-1,8*dP)
        J=np.einsum('arn,brm->anbm',Tk,Tk.conj()).reshape(2,8,dP,2,8,dP)
        J=np.transpose(J,(0,2,1,3,5,4))  # a s o, b s' o'
        TrO=np.einsum('asobto->asbt',J)/8
        res.append(float(np.abs(J-np.einsum('asbt,or->asobtr',TrO,np.eye(8))).max()))
    return res
def influence(V,dP):
    """r[j][k]: residual of 'O_j does not influence I_k' through V (0 => no influence)."""
    dF=V.shape[1]; T=V.reshape(2,2,2,dF,2,2,2,dP); R=[[0]*3 for _ in range(3)]
    for k in range(3):
        Tk=np.moveaxis(T,k,0)                         # i_k, i_rest(2,2), F, o(2,2,2), s
        Tk=Tk.reshape(2,-1,2,2,2,dP)
        for j in range(3):
            A=np.moveaxis(Tk,2+j,2).reshape(2,Tk.shape[1],2,4*dP)   # i_k, rest, o_j, other-in
            J=np.einsum('arxn,brym->axnbym',A,A.conj())
            TrX=np.einsum('axnbxm->anbm',J)/2
            R[j][k]=float(np.abs(J-np.einsum('anbm,xy->axnbym',TrX,np.eye(2))).max())
    return R
