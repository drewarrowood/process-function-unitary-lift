"""H.18: explicit realisation of H.13.2 on time-delocalised subsystems (TDS), checked numerically to machine precision.
(1) The Lugano purification L: |s>_P|o>_AO -> |s+lug(o)>_AI|o>_F, lug(a,b,c)=((1-b)c,(1-c)a,(1-a)b), is exactly the
    Baumeler-Wolf unitary extension U_BW of the Araujo-Feix process used by Wechs-Branciard-Oreshkov (WBO, arXiv:2201.11832,
    Eq. (5)/(55)): lug = (not b and c, not c and a, not a and b).
(2) WBO's temporal circuit (their Fig. 5, Suppl. Note 4A, Eqs. (51)-(54)) is implemented gate by gate on a 6-qubit register
    and compared with the cyclic composition of L with random agent unitaries U_A,U_B,U_C (qubit + qubit ancilla each).
(3) Time reversal: Cyc(L^T; W) = Cyc(L; W^T)^T, so the transposed gate sequence (reverse order, each gate transposed;
    controlled-U^T -> controlled-U, U_C sigma U_C^dag -> W_C^dag sigma W_C) is a temporal circuit realising L^T.
(4) H.13.2: V_13.2 = (Hd X^fo)_AI (Hd X^fi)_F L^T (Hd)_AO (X^fo Hd)_P (H.15.7e), so Cyc(V_13.2; W) equals
    local(F) Cyc(L^T; W~) local(P) with W~_X = Hd W_X (Hd X^fo_X): the reversed WBO circuit with frame-rotated agent
    operations realises H.13.2 on time-delocalised subsystems.  All checks: max abs deviation over random draws."""
import itertools as it, json, numpy as np
rng=np.random.default_rng(7)
B3=list(it.product((0,1),repeat=3)); ix=B3.index
lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b); xo=lambda u,v:tuple(p^q for p,q in zip(u,v))
def haar(n):
    z=(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))/np.sqrt(2); q,r=np.linalg.qr(z); return q*(np.diag(r)/abs(np.diag(r)))
# processes as 64x64 matrices: rows (agent-ins a,b,c ; future 3 bits), cols (agent-outs a,b,c ; past 3 bits); index 8*x+y
L=np.zeros((64,64))
for s in B3:
    for o in B3: L[8*ix(xo(s,lug(*o)))+ix(o),8*ix(o)+ix(s)]=1
WAF=lambda a,b,c:(int((not b) and c),int((not c) and a),int((not a) and b))
print('(1) lug == Araujo-Feix/Baumeler-Wolf function (not b&c, not c&a, not a&b):',all(lug(*o)==WAF(*o) for o in B3))
def T(M): # 64x64 (in3,fut3 ; out3,past3) -> 12-index tensor [i_a,i_b,i_c,f1,f2,f3, o_a,o_b,o_c,p1,p2,p3]
    return M.reshape((2,)*12)
def cyc(M,UA,UB,UC):
    """cyclic composition: agent X applies U_X: (X_in, X'_in) -> (X_out, X'_out) (4x4, index 2*sys+anc).
    returns G: (past3, a',b',c' in) -> (future3, a',b',c' out) as 64x64, index 8*(p or f)+ (a'b'c')."""
    t=T(M); u=[U.reshape(2,2,2,2) for U in (UA,UB,UC)]   # u[out,anc_out,in,anc_in]
    G=np.einsum('abcFGHxyzPQR,xAaD,yBbE,zCcK->FGHABCPQRDEK',t,*u,optimize=True)
    return G.reshape(64,64)
# ---------- WBO temporal circuit on register (r0..r5) = (p1,p2,p3,a',b',c'); qubit r0 is most significant
def op(fun,n=6):   # basis map -> matrix; fun(bits)-> list of (bits',amp)
    M=np.zeros((2**n,2**n),complex)
    for x in it.product((0,1),repeat=n):
        for y,a in fun(x): M[int(''.join(map(str,y)),2),int(''.join(map(str,x)),2)]+=a
    return M
def wbo_gates(UA,UB,UC):
    u={k:U.reshape(2,2,2,2) for k,U in (('A',UA),('B',UB),('C',UC))}
    def apply(Uk,x,i,j):   # agent op on register slots (i = system, j = ancilla)
        out=[]
        for s,t in it.product((0,1),repeat=2):
            a=u[Uk][s,t,x[i],x[j]]
            if abs(a)>0: y=list(x); y[i],y[j]=s,t; out.append((tuple(y),a))
        return out
    def w1(x):  # (p1,p2,p3,.,.,c'_in) -> (T1,E1,Q,.,.,gamma): U_C on (p3,c'); Q=c_O; order chosen by c_O
        out=[]
        for y,a in apply('C',x,2,5):
            c=y[2]; T1,E1=(x[0],x[1]) if c==0 else (x[1],x[0]); out.append(((T1,E1,c,x[3],x[4],y[5]),a))
        return out
    def s1(x): return apply('A',x,0,3) if x[2]==0 else apply('B',x,0,4)
    def w2(x):  # (T1',E1,Q) -> (T2,E2,Q): Q=0: T2=E1+T1'; Q=1: T2=E1+not T1'; E2=T1'
        t,e,q=x[0],x[1],x[2]; T2=e^t if q==0 else e^(1-t); return [((T2,t,q,x[3],x[4],x[5]),1)]
    def s2(x): return apply('B',x,0,4) if x[2]==0 else apply('A',x,0,3)
    UCm=UC; SX=np.kron(np.array([[0,1],[1,0]]),np.eye(2)); R=UCm@SX@UCm.conj().T   # U_C (sigma_x on C_I) U_C^dag on (C_O,C'_O)
    Rt=R.reshape(2,2,2,2)
    def w3(x):  # (T2',E2,Q,.,.,gamma) -> (F1,F2,F3,.,.,c'_out)
        q=x[2]; a,b=(x[1],x[0]) if q==0 else (x[0],x[1])
        if not (a==0 and b==1): return [((a,b,q,x[3],x[4],x[5]),1)]
        return [((0,1,s,x[3],x[4],t),Rt[s,t,q,x[5]]) for s,t in it.product((0,1),repeat=2) if abs(Rt[s,t,q,x[5]])>0]
    return [op(g) for g in (w1,s1,w2,s2,w3)]
def chain(gs):
    M=np.eye(64)
    for g in gs: M=g@M
    return M
# register index = 32p1+16p2+8p3+4a'+2b'+c' ; cyc index = 8*(p)+a'b'c'  -> identical layout
dev1=dev2=dev3=0; uni=0
m=json.load(open('../switchboard/h13/min_cex.json'))['m']
par=lambda x:bin(x).count('1')&1
Hd8=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/np.sqrt(8)
V=np.zeros((64,64))
for o in range(8):
    U8=Hd8@np.diag([(-1)**(m[o][z]//2) for z in range(8)])@Hd8
    for i in range(8):
        for s in range(8): V[8*i+o,8*o+s]=U8[i,s]       # rows (AI, F=o), cols (AO, P)
LT=np.zeros((64,64))
for p in B3:
    for q in B3: LT[8*ix(p)+ix(xo(q,lug(*p))),8*ix(q)+ix(p)]=1
h=np.array([[1,1],[1,-1]])/np.sqrt(2); X=np.array([[0,1],[1,0]]); I2=np.eye(2)
fo,fi=(0,1,0),(0,0,1)
Xm=lambda t:np.kron(np.kron(np.linalg.matrix_power(X,t[0]),np.linalg.matrix_power(X,t[1])),np.linalg.matrix_power(X,t[2]))
H3=np.kron(np.kron(h,h),h)
print('(4a) V_13.2 = (Hd X^fo)_AI (Hd X^fi)_F L^T (Hd)_AO (X^fo Hd)_P :',np.allclose(V,np.kron(H3@Xm(fo),H3@Xm(fi))@LT@np.kron(H3,Xm(fo)@H3)))
def tr_agent(U): return U.reshape(2,2,2,2).transpose(2,3,0,1).reshape(4,4)   # (out,anc_out;in,anc_in) -> transpose
for trial in range(20):
    UA,UB,UC=haar(4),haar(4),haar(4)
    G=cyc(L,UA,UB,UC); Tm=chain(wbo_gates(UA,UB,UC))
    uni=max(uni,abs(G.conj().T@G-np.eye(64)).max()); dev1=max(dev1,abs(G-Tm).max())
    WA,WB,WC=haar(4),haar(4),haar(4)
    GT=cyc(LT,WA,WB,WC)
    gs=wbo_gates(tr_agent(WA),tr_agent(WB),tr_agent(WC))
    Trev=chain([g.T for g in gs[::-1]])                 # reversed, transposed gate sequence
    dev2=max(dev2,abs(GT-Trev).max())
    # H.13.2: agent sees, inside L^T, W~ = (Hd)_out W (Hd X^fo_X)_in per party, ancillas untouched
    Wt=[np.kron(h,I2)@W@np.kron(h@np.linalg.matrix_power(X,f),I2) for W,f in zip((WA,WB,WC),fo)]
    G13=cyc(V,WA,WB,WC)
    Pm=np.kron(Xm(fo)@H3,np.eye(8)); Fm=np.kron(H3@Xm(fi),np.eye(8))
    gs=wbo_gates(*[tr_agent(W) for W in Wt]); Trev13=Fm@chain([g.T for g in gs[::-1]])@Pm
    dev3=max(dev3,abs(G13-Trev13).max())
print('(2) WBO temporal circuit == cyclic composition L*U_A*U_B*U_C, 20 Haar draws: max dev %.2e (G unitary dev %.2e)'%(dev1,uni))
print('(3) reversed+transposed WBO circuit == cyclic composition L^T*W, 20 draws: max dev %.2e'%dev2)
print('(4b) frame-rotated reversed WBO circuit == cyclic composition V_13.2*W, 20 draws: max dev %.2e'%dev3)
# gate census of the reversed circuit: which agent instances occur, conditioned how
print('reversed circuit for L^T / H.13.2, time order: w3^T [W_C^dag sigma W_C on (C-wires) iff (a,b)=(0,1)],'
      ' slot2^T [W_B if Q=0 else W_A], w2^T, slot1^T [W_A if Q=0 else W_B], w1^T [W_C, Q=c read out]')
# classical instruments of H.15.7b (measure the input, emit the setting) dilate to SWAP: (X_in, s) -> (X_out=s, record=X_in)
SW=np.array([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]],float)
W=[SW,SW,SW]; Wt=[np.kron(h,I2)@w@np.kron(h@np.linalg.matrix_power(X,f),I2) for w,f in zip(W,fo)]
gs=wbo_gates(*[tr_agent(w) for w in Wt]); Trev13=Fm@chain([g.T for g in gs[::-1]])@Pm
G13=cyc(V,*W); print('(5) agents = SWAP dilations of the classical instruments: reversed-WBO circuit == V_13.2 composition, max dev %.2e'%abs(G13-Trev13).max())
# induced P(i|o) from the circuit with source |0> on P: record register (anc out) = agent inputs i, setting (anc in) = o
P=np.zeros((8,8))
for o in range(8):
    psi=np.zeros(64,complex); psi[o]=1                 # past p=000, ancilla-in = settings o (index 8*p + o)
    out=Trev13@psi; pr=(abs(out)**2).reshape(8,8).sum(0); P[:,o]=pr
Pv=np.zeros((8,8))
for o in range(8):
    psi=np.zeros(64,complex); psi[o]=1; out=G13@psi; Pv[:,o]=(abs(out)**2).reshape(8,8).sum(0)
print('    P(i|o) from the time-local circuit equals the cyclic-composition statistics: max dev %.2e; columns sum to 1: %s'%(abs(P-Pv).max(),np.allclose(P.sum(0),1)))
