"""Independent referee verification of Theorem H.12.1 (paper/lift.md). Written from the paper text only.
Conventions: 3-bit strings, party k (k=0,1,2) owns bit (2-k) (MSB = party 0), same for inputs i=e and outputs o.
V|o,s,t> = sum_e U_o[e,s] |e>_I |o>_F1 |e xor t>_F2 ; U_o = Hd diag(i^{m_o(z)}) Hd.
"""
import json, itertools, sys
import numpy as np
from fractions import Fraction as Fr
M_TAB = [[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],
         [0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
js = json.load(open('../c1/cex_phases.json'))       # units of pi/4
assert all(js[o][z] == 2*M_TAB[o][z] for o in range(8) for z in range(8)), 'phase table mismatch'
par = lambda x: bin(x).count('1') & 1
I4 = [(1,0),(0,1),(-1,0),(0,-1)]                    # i^m as (re,im)
# 8*U_o[e,s] = sum_z (-1)^{z.(e xor s)} i^{m(z)}  : Gaussian integers, exact
UR = np.zeros((8,8,8),dtype=np.int64); UI = np.zeros_like(UR)
for o in range(8):
    for e in range(8):
        for s in range(8):
            for z in range(8):
                sg = -1 if par(z & (e ^ s)) else 1
                UR[o,e,s] += sg*I4[M_TAB[o][z]][0]; UI[o,e,s] += sg*I4[M_TAB[o][z]][1]
Uc = UR + 1j*UI                                      # exact small ints in floats-free sense (ints < 2^53)
# (0) each U_o unitary exactly: (8U)(8U)^dag = 64 I
for o in range(8):
    G = np.rint(Uc[o] @ Uc[o].conj().T)
    assert np.array_equal(G, 64*np.eye(8)), o
print('[0] all U_o exactly unitary (Gaussian-integer arithmetic)')

# ---------- (2) exact purity criterion ----------
# For local unitaries A_k: I_k (x) a_k -> O_k (x) a_k the induced map is M = sum_{o,e} R_{o,e} (x) A_{o,e},
# A_{o,e} = (x)_k A^k_{o_k e_k},  R_{o,e}|s,t> = U_o[e,s] |o, t xor e>.
# M^dag M = sum_{o,e,e'} R_{oe}^dag R_{oe'} (x) (x)_k B^k_{o_k e_k e'_k},  B^k_{o e e'} = A^k_{oe}^dag A^k_{oe'},
# and unitarity of A^k gives exactly sum_o B^k_{o e e'} = delta_{ee'} 1.  Writing B^k = b0 (x) 1 + (N (x) L(a_k))
# with b0[o,e,e'] = [o=0][e=e'] and N = {v : sum_o v[o,e,e'] = 0} (dim 4), multilinearity shows:
#   T(b0,b0,b0) = 1  and  T(v1,v2,v3) = 0 whenever some v_k in N   ==>  M^dag M = 1 for ALL ancilla dims;
# M is square (64 d_a x 64 d_a) so M is unitary.  (Sufficient condition, checked exactly.)
b0 = np.zeros((2,2,2),dtype=np.int64); b0[0,0,0] = b0[0,1,1] = 1
Nb = []
for e in range(2):
    for ep in range(2):
        v = np.zeros((2,2,2),dtype=np.int64); v[0,e,ep] = 1; v[1,e,ep] = -1; Nb.append(v)
slot = [b0] + Nb
bits = lambda x: ((x>>2)&1, (x>>1)&1, x&1)
def T(v1,v2,v3):
    w = np.zeros((8,8,8),dtype=np.int64)            # w[o,e,e']
    for o,e,ep in itertools.product(range(8),repeat=3):
        bo,be,bp = bits(o),bits(e),bits(ep)
        w[o,e,ep] = v1[bo[0],be[0],bp[0]]*v2[bo[1],be[1],bp[1]]*v3[bo[2],be[2],bp[2]]
    # G[e,e',s,s'] = sum_o w * conj(8U[o,e,s]) 8U[o,e',s']  (exact ints)
    Gr = np.einsum('oab,oas,obt->abst', w, UR, UR) + np.einsum('oab,oas,obt->abst', w, UI, UI)
    Gi = np.einsum('oab,oas,obt->abst', w, UR, UI) - np.einsum('oab,oas,obt->abst', w, UI, UR)
    Q = np.zeros((8,8,8,8),dtype=np.int64); Qi = np.zeros_like(Q)   # Q[s,t,s',t'], nonzero iff t^e = t'^e'
    for e in range(8):
        for ep in range(8):
            for t in range(8):
                tp = t ^ e ^ ep
                Q[:,t,:,tp] += Gr[e,ep]; Qi[:,t,:,tp] += Gi[e,ep]
    return Q.reshape(64,64), Qi.reshape(64,64)
ok = True; cnt = 0
for a,b,c in itertools.product(range(5),repeat=3):
    Qr,Qi = T(slot[a],slot[b],slot[c]); cnt += 1
    target = 64*np.eye(64,dtype=np.int64) if (a,b,c)==(0,0,0) else np.zeros((64,64),dtype=np.int64)
    if not (np.array_equal(Qr,target) and not Qi.any()): ok = False; print('  FAIL at', a,b,c)
print('[2a] exact multi-affine purity criterion over %d slot combinations:'%cnt, 'PASS' if ok else 'FAIL')
PURE_EXACT = ok

# ---------- (2b) numerics: random local unitaries / isometries with ancillas ----------
rng = np.random.default_rng(12345)
U = Uc/8.0
def haar(n,m=None):
    m = m or n; Z = (rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))/np.sqrt(2)
    Qm,R = np.linalg.qr(Z); Qm = Qm*(np.diag(R)/abs(np.diag(R))); return Qm[:, :m]
def induced(As, din, dout):
    # As[k]: (2*dout_k) x (2*din_k) matrix, index (o_k, a'_k),(i_k, a_k)
    A = np.ones((1,1),dtype=complex)
    blocks = [Ak.reshape(2,dout[k],2,din[k]) for k,Ak in enumerate(As)]
    # A_{o,e} full ancilla operator
    Aoe = np.empty((8,8,np.prod(dout),np.prod(din)),dtype=complex)
    for o in range(8):
        for e in range(8):
            bo,be = bits(o),bits(e)
            Aoe[o,e] = np.kron(np.kron(blocks[0][bo[0],:,be[0],:],blocks[1][bo[1],:,be[1],:]),blocks[2][bo[2],:,be[2],:])
    Do,Di = np.prod(dout),np.prod(din)
    Mt = np.zeros((8,8,Do,8,8,Di),dtype=complex)   # [o,u,a',s,t,a]
    for e in range(8):
        for t in range(8):
            Mt[:,t^e,:,:,t,:] += np.einsum('os,oxy->oxsy', U[:,e,:], Aoe[:,e])
    return Mt.reshape(64*Do,64*Di)
worst = 0; worstR = 0; ntr = 0
for trial in range(1200):
    din = rng.integers(1,5,size=3)
    iso = trial % 3 == 2
    dout = din + (rng.integers(0,2,size=3) if iso else 0)
    As = [haar(2*dout[k])[:, :2*din[k]] for k in range(3)]
    Mm = induced(As, din, dout)
    worst = max(worst, abs(Mm.conj().T@Mm - np.eye(Mm.shape[1])).max())
    if not iso: worstR = max(worstR, abs(Mm@Mm.conj().T - np.eye(Mm.shape[0])).max())
    ntr += 1
print('[2b] %d random trials (1/3 isometries, ancilla dims 1..4/5): max|M^dag M-1|=%.2e, max|M M^dag-1| (unitary cases)=%.2e'%(ntr,worst,worstR))
# sanity: a generic NON-pure-looking perturbation should fail (control that the test is sensitive)
Ub = U.copy(); U = U.copy(); U[0] = U[0] @ np.diag(np.exp(1j*np.array([0,0,0,0,0,0,0,0.3])))
U[0] = U[0]  # still unitary board, but breaks the identities
As = [haar(2) for _ in range(3)]; ctrl = abs(induced(As,[1,1,1],[1,1,1]).conj().T@induced(As,[1,1,1],[1,1,1]) - np.eye(64)).max()
U = Ub
print('     control (board 000 perturbed): max|M^dag M-1| = %.2e (should be >0)'%ctrl)

# ---------- (3) exact classical process p ----------
# p(i|o) = |<i|U_o phi>|^2, phi = (|011> + zeta8^{-1}|100>)/sqrt2.  Write 8U = integer pair.  With w = conj(8U[i,3]) 8U[i,4]:
# 64 p = (|8U3|^2+|8U4|^2)/2 + (Re w + Im w)/sqrt2  ->  p = A + B sqrt2, A,B rational.
P = {}
for o in range(8):
    for i in range(8):
        a3 = complex(Uc[o,i,3]); a4 = complex(Uc[o,i,4])
        n = int(round(abs(a3)**2 + abs(a4)**2)); w = a3.conjugate()*a4
        P[(i,o)] = (Fr(n,128), Fr(int(round(w.real))+int(round(w.imag)),128))
def sgnq(x):   # sign of A + B sqrt2
    A,B = x
    if A >= 0 and B >= 0: return (A>0 or B>0)*1
    if A <= 0 and B <= 0: return -1*(A<0 or B<0)
    return (1 if A>0 else -1) if A*A > 2*B*B else ((-1 if A>0 else 1) if A*A < 2*B*B else 0)
add = lambda x,y: (x[0]+y[0], x[1]+y[1])
assert all(sgnq(P[k]) >= 0 for k in P)
cols = all(sum(P[(i,o)][0] for i in range(8))==1 and sum(P[(i,o)][1] for i in range(8))==0 for o in range(8))
# numeric cross check of p vs complex arithmetic with true phi
phi = np.zeros(8,complex); phi[3] = 1/np.sqrt(2); phi[4] = np.exp(-1j*np.pi/4)/np.sqrt(2)
pn = np.array([[abs((U[o]@phi)[i])**2 for o in range(8)] for i in range(8)])
pe = np.array([[float(P[(i,o)][0])+float(P[(i,o)][1])*2**.5 for o in range(8)] for i in range(8)])
print('[3a] p >= 0 exactly; columns sum to 1 exactly:', cols, '; exact-vs-float max diff %.1e'%abs(pn-pe).max())
fs = [(0,0),(1,1),(0,1),(1,0)]   # local maps x -> f(x): const0,const1,id,not
def fapply(F,i):
    b = bits(i); return sum(fs[F[k]][b[k]] << (2-k) for k in range(3))
allone = True
for F in itertools.product(range(4),repeat=3):
    tot = (Fr(0),Fr(0))
    for i in range(8): tot = add(tot, P[(i,fapply(F,i))])
    allone &= (tot == (Fr(1),Fr(0)))
print('[3b] all 64 deterministic local interventions give total probability exactly 1:', allone,
      '(total prob is multi-affine in the 3 local stochastic maps, so this covers all local stochastic interventions)')
# also via the full quantum circuit: party unitaries |i,x> -> |f(i) xor x, i> (ancilla = copy), source phi(x)|0>, measure I in comp. basis
maxd = 0
for F in itertools.product(range(4),repeat=3):
    As = []
    for k in range(3):
        A = np.zeros((4,4))
        for i_ in range(2):
            for x in range(2): A[((fs[F[k]][i_]^x)*2 + i_), i_*2 + x] = 1   # out (o,a'), in (i,a)
        As.append(A)
    Mm = induced(As,[2,2,2],[2,2,2])
    # input: phi_s (x) |0>_t (x) |000>_anc ; recover distribution of recorded i (anc') : prob over i
    vin = np.kron(np.kron(phi, np.eye(8)[0]), np.eye(8)[0]); vout = (Mm@vin).reshape(8,8,8)
    pi = (abs(vout)**2).sum(axis=(0,1))
    # anc' holds i bits; compare with p(i|f(i))
    maxd = max(maxd, max(abs(pi[i] - pe[i, fapply(F,i)]) for i in range(8)))
print('[5] full circuit (V + copying party unitaries, source phi(x)|0>) reproduces p(i|f(i)): max diff %.1e'%maxd)

# ---------- (4) process functions from scratch ----------
W = np.array(list(itertools.product(range(8),repeat=8)),dtype=np.uint8)   # w[o] for o=0..7 ; 16.7M
good = np.ones(len(W),bool)
for F in itertools.product(range(4),repeat=3):
    idx = np.array([fapply(F,i) for i in range(8)])
    nfix = (W[:,idx] == np.arange(8,dtype=np.uint8)).sum(axis=1)
    good &= (nfix == 1)
PFs = W[good]; del W
print('[4a] process functions (unique fixed point for all 64 local deterministic maps), brute force over 8^8:', len(PFs))
PFv = np.zeros((len(PFs),64),dtype=np.int64)       # coordinate r = i*8+o, value [w(o)=i]
for n,w in enumerate(PFs):
    for o in range(8): PFv[n, int(w[o])*8+o] = 1
pvec = [P[(r//8, r%8)] for r in range(64)]
g = [int(x) for x in "0 0 0 0 0 0 0 0 1 -1 0 0 0 0 0 0 1 0 -1 0 0 0 0 0 1 0 0 0 0 0 0 0 1 0 0 0 -1 0 0 0 2 0 0 0 -1 0 0 0 1 0 0 0 0 0 -1 0 2 0 0 0 0 0 0 0 0".split()]
gv, g0 = g[:64], g[64]
vals = PFv @ np.array(gv) + g0
gp = (Fr(g0),Fr(0))
for r in range(64): gp = add(gp,(gv[r]*pvec[r][0], gv[r]*pvec[r][1]))
print('[4b] paper inequality (from exact_cex.log): min over my PFs = %d, tight on %d; g.p+g0 = %s + %s*sqrt2, sign %d'%(vals.min(),(vals==0).sum(),gp[0],gp[1],sgnq(gp)))
# (4c) my own LP: separation. min g.p+g0 s.t. g.PF+g0>=0, -1<=g<=1 ; then rationalise and verify exactly
from scipy.optimize import linprog
pf = np.array(pe).reshape(-1)
c = np.r_[pf,1.0]; Aub = -np.c_[PFv,np.ones(len(PFv))]; bub = np.zeros(len(PFv))
res = linprog(c,A_ub=Aub,b_ub=bub,bounds=[(-1,1)]*64+[(-64,64)],method='highs')
print('     separation LP optimum (float) =', res.fun)
best = None
for scale in [1,2,4,8,16,32,64,128,256,1024]:
    gi = np.rint(res.x*scale).astype(np.int64)
    v = PFv@gi[:64] + gi[64]
    if v.min() < 0: continue
    s = (Fr(int(gi[64])),Fr(0))
    for r in range(64): s = add(s,(int(gi[r])*pvec[r][0], int(gi[r])*pvec[r][1]))
    if sgnq(s) < 0: best = (scale,s); break
print('[4c] own rational separating inequality, exactly verified on all PFs and p:', best)
# membership LP (float, feasibility of p = sum lambda PF)
res2 = linprog(np.zeros(len(PFv)), A_eq=np.r_[PFv.T, np.ones((1,len(PFv)))], b_eq=np.r_[pf,1], bounds=(0,None), method='highs')
print('     membership LP status:', res2.status, res2.message)
