"""H.15.9(A,B): structure of the H.12 board.  Labels per item in the printout.
Systems of a pure lift-form process vector |w>: P (8-dim), AO_A, AO_B, AO_C, AI_A, AI_B, AI_C (qubits), F (8-dim); w[s,o,i,f] = V[(i,f),(s,o)],
V = sum_o U_o (x) |o><o| (F records o).  Local-unitary (LU) invariants: spectra of rho_S for subsets S of the 8 systems (P, F whole).
Allowed equivalences: LU on each of the 8 systems and a permutation of the parties.  Time reversal (Guerin-Brukner) = complex conjugation
plus P<->F, AI_k<->AO_k, so its spectra are the relabelled spectra.
(A) compare H.12 with the purifications L_g of all 744 PFs and with their time reverses L_g^T (this includes Lugano, Lugano^T, H.13.2 ~ L_f^T).
(B) classical restrictions of H.12's time reverse V^T in computational / Hadamard frames, max over sources of facet violation of conv(PF)."""
import numpy as np, itertools as it, gzip
F='../../physics/facets/'
B3=list(it.product((0,1),repeat=3)); ix=B3.index; par=lambda x:bin(x).count('1')&1
Hd=np.array([[(-1)**par(x&y) for y in range(8)] for x in range(8)])/8**.5
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
U12=np.array([Hd@np.diag([1j**MT[o][z] for z in range(8)])@Hd for o in range(8)])
PF=np.load('../pfs744.npy'); gs=[tuple(int(np.argmax(PF[n][:,o])) for o in range(8)) for n in range(744)]
def board_w(U):  # U[o] : P->AI ; returns w with axes (P, AO_A,AO_B,AO_C, AI_A,AI_B,AI_C, F)
    w=np.zeros((8,8,8,8),complex)
    for o in range(8): w[:,o,:,o]=U[o].T     # w[s,o,i,f]=delta_fo U_o[i,s]
    return (w/8).reshape(8,2,2,2,2,2,2,8)
def pf_U(g): return np.array([np.array([[float(i==(s^g[o])) for s in range(8)] for i in range(8)]) for o in range(8)])
def rev(w): return np.conj(w).transpose(7,4,5,6,1,2,3,0)    # P'=F, AO'_k=AI_k, AI'_k=AO_k, F'=P
SUBS_ALL=[S for r in range(1,5) for S in it.combinations(range(8),r)]
SUBS=[S for r in range(1,3) for S in it.combinations(range(8),r)]   # cheap filter: all 1- and 2-system spectra
def sig(w,SUBS=SUBS):
    d=[8,2,2,2,2,2,2,8]; out={}
    for S in SUBS:
        T=[j for j in range(8) if j not in S]; m=np.transpose(w,list(S)+T).reshape(int(np.prod([d[j] for j in S])),-1)
        ev=np.linalg.eigvalsh(m@m.conj().T)[::-1]; out[S]=tuple(np.round(ev[ev>1e-9],6))
    return out
def perm_sys(pi):   # party permutation on system indices
    mp={0:0,7:7}
    for k in range(3): mp[1+k]=1+pi[k]; mp[4+k]=4+pi[k]
    return mp
def equiv(s1,s2,SUBS=SUBS):
    for pi in it.permutations(range(3)):
        mp=perm_sys(pi)
        if all(s1[S]==s2[tuple(sorted(mp[j] for j in S))] for S in SUBS if S in s1): return pi
    return None
w12=board_w(U12); s12=sig(w12)
assert abs(np.vdot(w12,w12)-1)<1e-12
print('(A) H.12 reduced spectra, a few: AI_A:',s12[(4,)],' AO_A:',s12[(1,)],' {AI_A,AO_A}:',s12[(1,4)],' P:',s12[(0,)][:4],'...',len(s12[(0,)]))
nmatch_f=[];nmatch_r=[]; dist=[]
for n,g in enumerate(gs):
    wg=board_w(pf_U(g)); sg=sig(wg); sr=sig(rev(wg))
    if equiv(s12,sg) is not None: nmatch_f.append(n)
    if equiv(s12,sr) is not None: nmatch_r.append(n)
print('(A) PF purifications L_g passing the 1-2-system spectral filter vs H.12:',nmatch_f,' time reverses L_g^T:',nmatch_r,'  [of 744 each]')
# which invariant separates H.12 from Lugano^T most simply
lug=lambda o:((1-o[1])*o[2],(1-o[2])*o[0],(1-o[0])*o[1])
gl=tuple(ix(lug(B3[o])) for o in range(8)); sL=sig(board_w(pf_U(gl))); sLr=sig(rev(board_w(pf_U(gl))))
for name,s in (('Lugano L',sL),('Lugano^T',sLr)):
    diff=[S for S in SUBS if len(S)<=2 and s12[S]!=s[S]]
    print(f'   H.12 vs {name}: differing 1-2 system spectra e.g.',[(S,s12[S],s[S]) for S in diff[:2]])
# sanity: H.13.2 must match its Lugano^T
m=__import__('json').load(open('../switchboard/h13/min_cex.json'))['m']
U13=np.array([Hd@np.diag([(-1)**(m[o][x]//2) for x in range(8)])@Hd for o in range(8)])
print('   sanity: H.13.2 LU-equivalent to Lugano^T by these invariants:',equiv(sig(board_w(U13)),sLr) is not None)
print('   H.12 equivalent to its own time reverse by these invariants:',equiv(s12,sig(rev(w12))) is not None)
# (B) classical restrictions of reversed H.12 and conv(PF) facets
Zc=np.load(F+'Z.npy').astype(float); L=gzip.open(F+'pf.out.gz','rt').read().split('\n')
k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
vals=Zc@Hm[:,:37].T+Hm[:,37]; A=np.c_[PF.reshape(744,-1),np.ones(744)]; T=np.linalg.lstsq(A,vals,rcond=None)[0].T; Tn=T/vals.max(0)[:,None]
def facet_viol(P):   # P[(i*8+o)] hermitian 8x8 form in the source
    Fm=np.einsum('fr,rst->fst',Tn[:,:64],P)+Tn[:,64,None,None]*np.eye(8); return (-np.linalg.eigvalsh(Fm)[:,0]).max()   # >0 iff some source gives p outside conv(PF)
def rev_forms(U,Ain,Bout):   # reversed board: past f, agents output beta_q=Bout[:,q], measure input in basis Ain[:,i]
    P=np.zeros((64,8,8),complex)
    for i in range(8):
        for q in range(8):
            C=np.array([Ain[f,i].conj()*(Bout[:,q]@U[f]) for f in range(8)]).T   # C[s,f]
            P[i*8+q]=C.conj().T@C
    return P
def fwd_forms(U,Ain,Bout):   # forward board: source s, agents output beta, measure in Ain
    P=np.zeros((64,8,8),complex)
    for i in range(8):
        for q in range(8):
            C=sum(Bout[o,q]*np.outer(np.eye(8)[o],Ain[:,i].conj()@U[o]) for o in range(8))  # F record o (coherent)
            P[i*8+q]=C.conj().T@C
    return P
I8=np.eye(8)
for name,U in (('H.12',U12),('H.13.2',U13),('Lugano',pf_U(gl))):
    for fr,(Ai,Bo) in {'comp/comp':(I8,I8),'Had/Had':(Hd,Hd),'comp-in/Had-out':(I8,Hd),'Had-in/comp-out':(Hd,I8)}.items():
        Pr=rev_forms(U,Ai,Bo); assert np.allclose(Pr.reshape(8,8,8,8).sum(0),np.eye(8)[None])
        Pf=fwd_forms(U,Ai,Bo); assert np.allclose(Pf.reshape(8,8,8,8).sum(0),np.eye(8)[None])
        print(f'(B) {name:7s} {fr:16s} max facet violation over sources: time reverse {facet_viol(Pr):+.6f}   forward {facet_viol(Pf):+.6f}')
