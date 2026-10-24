"""H.15.7d(A) calibration: VOKB Fig. 27 (Lugano) routed graph, encoded for rg_check.analyse.  Shared indices of the figure
(l on X->A and A->F, etc.) are enforced through the routes.  Expected: bi-univocal, weak loops only (valid)."""
import itertools as it, sys
sys.argv=[sys.argv[0]]
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()): from rg_check import analyse
def lugano_graph():
    ag={'A':('l','i'),'B':('m','j'),'C':('n','k')}
    ar={}; R={}
    for N in 'ABC':
        ar['X'+N]=('X',N,{0:1,1:1})                       # result index (won?)
        ar[N+'X']=(N,'X',{(0,0):1,(1,0):1,(0,1):1})        # (vote, result) with vote.result = 0
        ar[N+'F']=(N,'F',{0:1,1:2})                        # result copy to F; won-sector carries the message
        R[N]={((0,),(0,(0,0))),((0,),(0,(1,0))),((1,),(1,(0,1)))}   # outputs sorted: NF, NX
    ar['XF']=('X','F',{v:1 for v in it.product((0,1),repeat=3)}); ar['G']=('F',None,{0:1})
    C=[]
    for i,j,k in it.product((0,1),repeat=3):
        l,m,n=(1-j)*k,(1-k)*i,(1-i)*j
        if i*l==0 and j*m==0 and k*n==0: C.append((i,j,k,l,m,n))
    # X: inputs sorted: AX,BX,CX ; outputs sorted: XA,XB,XC,XF
    R['X']={(((i,l),(j,m),(k,n)),(l,m,n,(i,j,k))) for i,j,k,l,m,n in C}
    # F: inputs sorted: AF,BF,CF,XF
    R['F']={((l,m,n,(i,j,k)),(0,)) for i,j,k,l,m,n in C}
    return ar,R,C
if __name__=='__main__':
    ar,R,C=lugano_graph(); print('global index constraint C:',len(C),'tuples', [c[:3] for c in C])
    bad=analyse(ar,R,'VOKB Fig. 27 Lugano')
