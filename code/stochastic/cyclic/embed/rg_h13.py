"""H.15.7d(A): (i) exact rotated form of H.13.2; (ii) routed-graph candidates for it, checked with rg_check.analyse.
(i) n_o(z) = m_o(z)/2 is linear in o over F2:  n_o(z) = o_A f_A(z) + o_B f_B(z) + o_C f_C(z) (mod 2) with
    f_A = z_B z_C,  f_B = z_A (1+z_C),  f_C = z_A + z_B + z_A z_B  (bits: z = (z_A,z_B,z_C), o = (o_A,o_B,o_C), B3 order).
    Hence, with Hadamards on every agent input AND output wire (and on past/future), V is the permutation
    W': |z>_P |w>_AO -> |z>_AI |w + f(z)>_F,  and each f_k does not depend on z_k.  Checked exactly below (integers)."""
import itertools as it, json, numpy as np, sys, io, contextlib
sys.argv=[sys.argv[0]]
with contextlib.redirect_stdout(io.StringIO()): from rg_check import analyse
B3=list(it.product((0,1),repeat=3)); par=lambda x:bin(x).count('1')&1
m=json.load(open('../switchboard/h13/min_cex.json'))['m']
f=lambda z:(z[1]*z[2], z[0]*(1-z[2]), (z[0]+z[1]+z[0]*z[1])%2)
ok=all(m[o][zi]//2==sum(a*b for a,b in zip(B3[o],f(B3[zi])))%2 for o in range(8) for zi in range(8))
print('n_o(z) = o.f(z) mod 2 for all 64 (o,z):',ok)
# exact check of the rotated form: Hd8 on AI, AO, P, F (integer matrices, scale 8^2)
H=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])   # = sqrt(8) Hd
V=np.zeros((64,64),int)   # rows (i,o_F), cols (o,s): V[(i,oF),(o,s)] = 8 U_o[i,s] delta(oF,o)
for o in range(8):
    U8=H@np.diag([(-1)**(m[o][z]//2) for z in range(8)])@H   # = 8 U_o
    for i in range(8):
        for s in range(8): V[8*i+o,8*o+s]=U8[i,s]
K=np.kron(H,H)          # Hadamard on both tensor factors (scale 8)
Wp=np.kron(H,H)@V@np.kron(H,H)   # (Hd on AI x F) V (Hd on AO x P), scale 8*8*8 = 512
Wexp=np.zeros((64,64),int)
for z in range(8):
    for w in range(8): Wexp[8*z+B3.index(tuple(a^b for a,b in zip(B3[w],f(B3[z])))),8*w+z]=512
print("exact: (Hd_AI x Hd_F) V (Hd_AO x Hd_P) = W' (permutation (z,w) -> (z, w+f(z))):",np.array_equal(Wp,Wexp))
print('f_k independent of z_k:',all(f(z)[k]==f(tuple(z[j]^(j==k) for j in range(3)))[k] for z in B3 for k in range(3)))
# (ii) candidates.  All sectors one-dimensional, per-agent computational indices.
# (a) single station X: inputs z (from source node S) and w_k; outputs z_k to agents and (w+f(z)) to F.
ar={'P':('S','X',{z:1 for z in B3}),'XF':('X','F',{w:1 for w in B3}),'G':('F',None,{0:1})}
R={'S':{((),(z,)) for z in B3},'F':{((w,),(0,)) for w in B3}}
for k in 'ABC': ar['X'+k]=('X',k,{0:1,1:1}); ar[k+'X']=(k,'X',{0:1,1:1}); R[k]={((a,),(b,)) for a in (0,1) for b in (0,1)}
R['X']={((w[0],w[1],w[2],z),(z[0],z[1],z[2],tuple(a^b for a,b in zip(w,f(z))))) for z in B3 for w in B3}
analyse(ar,R,"W' single station X: (z,w) -> (z, w+f(z))")
# (b) per-agent stations X_k (control z_j, j != k, passes through X_k on its way to agent j; target w_k): ring A<X_A<B,C ...
ar={'G':('F',None,{0:1})}; R={}
src={}  # z_j path: S -> X_k (k != j, in fixed order) -> agent j
order={'A':['XB','XC'],'B':['XA','XC'],'C':['XA','XB']}
R={k:{((a,),(b,)) for a in (0,1) for b in (0,1)} for k in 'ABC'}
ar['S_out']=None
del ar['S_out']
for j in 'ABC':
    path=['S']+order[j]+[j]
    for u,v in zip(path,path[1:]): ar[f'z{j}_{u}{v}']=(u,v,{0:1,1:1})
for k in 'ABC': ar[f'w{k}_in']=(k,'X'+k,{0:1,1:1}); ar[f'w{k}_out']=('X'+k,'F',{0:1,1:1})
def ins(N): return sorted(a for a,(s,d,_) in ar.items() if d==N)
def outs(N): return sorted(a for a,(s,d,_) in ar.items() if s==N)
R['S']={((),z) for z in B3}
R['F']={(w,(0,)) for w in B3}
for k,kk in zip('ABC',range(3)):
    I=ins('X'+k); O=outs('X'+k); rel=set()
    for vals in it.product((0,1),repeat=len(I)):
        v=dict(zip(I,vals)); z=[None]*3
        for a in I:
            if a.startswith('z'): z['ABC'.index(a[1])]=v[a]
        z[kk]=0   # f_k does not depend on z_k
        fk=f(tuple(z))[kk]; o={}
        for a in O:
            if a.startswith('z'): o[a]=next(v[b] for b in I if b.startswith('z'+a[1]))
            else: o[a]=v[f'w{k}_in']^fk
        rel.add((vals,tuple(o[a] for a in O)))
    R['X'+k]=rel
# S outputs sorted names -> tuple order must follow sorted(outs('S')): zA_SXB, zB_SXA, zC_SXA
R['S']={((),tuple(z[{'A':0,'B':1,'C':2}[a[1]]] for a in outs('S'))) for z in B3}
R['F']={(tuple(w[{'A':0,'B':1,'C':2}[a[1]]] for a in ins('F')),(0,)) for w in B3}
analyse(ar,R,"W' per-agent stations X_A, X_B, X_C (controls pass through, targets w_k)")
