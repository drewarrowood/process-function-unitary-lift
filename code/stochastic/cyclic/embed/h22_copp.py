"""Round 22 (H.29): pure processes whose future records the agents' outputs ("classical-output pure processes", COPP).
V |s>_P |o>_AO = (U_o |s>)_AI |o>_F,  U_o unitary on the three agent input qubits (8x8), o in {0,1}^3.
Statistics (agents measure AI in the computational basis; frames are absorbed in U_o):  p(i|o) = |<i| U_o psi>|^2.
Validity (derived in H.29.1): with F traced, W = sum_o |o><o|_AO (x) |v_o><v_o|, so a process is valid iff
   sum_o U_o^dag (x)_k M^k_{o_k} U_o = 1   for all binary POVMs (M^k_0, M^k_1) of each party,
which, writing M^k_{c_k} = 1 - X_k, M^k_{1-c_k} = X_k and using multilinearity, is equivalent to: for every nonempty set S of
parties and every c in {0,1}^{-S},
   sum_{o_S} (-1)^{|o_S|} U_{(o_S,c)}^dag (X_S (x) 1_{-S}) U_{(o_S,c)} = 0   for all operators X_S on the S qubits.
pen(U) = sum of squared Frobenius norms of these linear maps (zero iff valid)."""
import itertools as it, numpy as np, torch
torch.set_default_dtype(torch.float64)
SUBS=[S for r in (1,2,3) for S in it.combinations(range(3),r)]
def oidx(bits): return 4*bits[0]+2*bits[1]+bits[2]
def pen(U):   # U: tensor [8 (o), 8, 8]
    tot=0.
    Ut=U.reshape(8,2,2,2,8)
    for S in SUBS:
        R=[k for k in range(3) if k not in S]
        perm=[0]+[1+k for k in S]+[1+k for k in R]+[4]
        Up=Ut.permute(perm).reshape(8,2**len(S),2**len(R),8)
        for c in it.product((0,1),repeat=len(R)):
            T=0
            for oS in it.product((0,1),repeat=len(S)):
                b=[0,0,0]
                for k,v in zip(S,oS): b[k]=v
                for k,v in zip(R,c): b[k]=v
                u=Up[oidx(b)]; sg=(-1)**sum(oS)
                T=T+sg*torch.einsum('sxb,txc->bcst',u.conj(),u)
            tot=tot+(T.abs()**2).sum()
    return tot
def resid(U):  # the residual maps as one real vector (pen = |resid|^2)
    out=[]; Ut=U.reshape(8,2,2,2,8)
    for S in SUBS:
        R=[k for k in range(3) if k not in S]
        Up=Ut.permute([0]+[1+k for k in S]+[1+k for k in R]+[4]).reshape(8,2**len(S),2**len(R),8)
        for c in it.product((0,1),repeat=len(R)):
            T=0
            for oS in it.product((0,1),repeat=len(S)):
                b=[0,0,0]
                for k,v in zip(S,oS): b[k]=v
                for k,v in zip(R,c): b[k]=v
                u=Up[oidx(b)]; T=T+(-1)**sum(oS)*torch.einsum('sxb,txc->bcst',u.conj(),u)
            out+= [T.real.reshape(-1),T.imag.reshape(-1)]
    return torch.cat(out)
def V_of(U):  # 64x64 in the h16 layout: rows (iA iB iC, f), cols (oA oB oC, s)
    V=torch.zeros(8,8,8,8,dtype=torch.complex128)
    for o in range(8): V[:,o,o,:]=U[o]
    return V.reshape(64,64)
def stats(U,psi):  # p[i,o]
    a=torch.einsum('ois,s->io',U,psi); return (a.abs()**2)/torch.vdot(psi,psi).real
def facet_M(U,Tf,cf):  # quadratic form of the facet in psi: sum_{i,o} T[i,o] U_o^dag |i><i| U_o + c
    return torch.einsum('io,oia,oib->ab',Tf.to(torch.complex128),U.conj(),U)+cf*torch.eye(8)
