"""Round 24: minimal direct Clarabel interface (sparse), used by h24_sdp2.py.  Problem: min q.x  s.t.  Aeq x = beq,  sum_j x_j C^b_j + C^b_0 PSD for each block b."""
import numpy as np, scipy.sparse as sps, clarabel
def svec_index(n):
    iu=[]; 
    for j in range(n):
        for i in range(j+1): iu.append((i,j))
    pos={p:k for k,p in enumerate(iu)}; return iu,pos
def solve(q,Aeq,beq,blocks,nvar,verbose=False,tol=1e-9):
    """blocks: list of (n, rows, cols, vars, vals, const) meaning M = sum vals*E_{rows,cols} x_vars + const (dense n x n); entries listed for
    the UPPER triangle only (row <= col)."""
    As=[sps.csr_matrix(Aeq)]; bs=[np.asarray(beq,float)]; cones=[clarabel.ZeroConeT(Aeq.shape[0])]
    for (n,r,c,v,val,const) in blocks:
        iu,pos=svec_index(n); m=len(iu)
        sc=np.where(np.array(r)==np.array(c),1.0,np.sqrt(2))
        row=np.array([pos[(a,b)] for a,b in zip(r,c)])
        A=sps.csr_matrix((-np.array(val)*sc,(row,np.array(v))),shape=(m,nvar))
        b=np.array([const[i,j]*(1 if i==j else np.sqrt(2)) for (i,j) in iu]) if const is not None else np.zeros(m)
        As.append(A); bs.append(b); cones.append(clarabel.PSDTriangleConeT(n))
    A=sps.vstack(As).tocsc(); b=np.concatenate(bs)
    s=clarabel.DefaultSettings(); s.verbose=verbose; s.tol_gap_abs=tol; s.tol_gap_rel=tol; s.tol_feas=tol
    sol=clarabel.DefaultSolver(sps.csc_matrix((nvar,nvar)),np.asarray(q,float),A,b,cones,s).solve()
    return sol
if __name__=='__main__':
    # test: min x0 s.t. [[x0, 1],[1, x1]] PSD, x1 = 4  -> x0 = 1/4
    Aeq=sps.csr_matrix(np.array([[0.,1.]])); sol=solve([1,0],Aeq,[4],[(2,[0,0,1],[0,1,1],[0,0,1],[1,0,1],np.array([[0,1],[1,0.]]))],2)
    print(sol.x, sol.status)
def solve_scs(q,Aeq,beq,blocks,nvar,eps=1e-7,max_iters=200000,verbose=False):
    """same problem with SCS (low memory). SCS svec: lower triangle, column-wise, off-diagonals scaled by sqrt 2."""
    import scs
    As=[sps.csr_matrix(Aeq)]; bs=[np.asarray(beq,float)]; sizes=[]
    for (n,r,c,v,val,const) in blocks:
        il=[]
        for j in range(n):
            for i in range(j,n): il.append((i,j))
        pos={p:k for k,p in enumerate(il)}; m=len(il)
        rr=np.array(r); cc=np.array(c); lo=np.maximum(rr,cc); hi=np.minimum(rr,cc)   # (row>=col) after transpose of an upper entry
        sc=np.where(rr==cc,1.0,np.sqrt(2)); row=np.array([pos[(a,b)] for a,b in zip(lo,hi)])
        A=sps.csr_matrix((-np.array(val)*sc,(row,np.array(v))),shape=(m,nvar))
        b=np.zeros(m) if const is None else np.array([const[i,j]*(1 if i==j else np.sqrt(2)) for (i,j) in il])
        As.append(A); bs.append(b); sizes.append(n)
    A=sps.vstack(As).tocsc(); b=np.concatenate(bs)
    data=dict(A=A,b=b,c=np.asarray(q,float)); cone=dict(z=Aeq.shape[0],s=sizes)
    sol=scs.SCS(data,cone,eps_abs=eps,eps_rel=eps,max_iters=max_iters,verbose=verbose).solve()
    return sol
