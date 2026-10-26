"""Round 21 (H.28.2): which diagonal-phase boards V|t,f> = e^{i Phi(t,f)}|f>_AI|t>_F are valid?
(a) penalty of Phi = sum_k theta_k(t_k, f_{-k}) with ARBITRARY theta (not through a refined PF);  (b) Hessian of the Araujo penalty
at Phi = 0 (64x64): its null space = first-order valid directions; compared with span{ functions of (t_k, f_{-k}) } and with the
span of refined-PF phase functions."""
import sys, json, itertools as it, numpy as np, torch
sys.argv=[sys.argv[0],'0','0']
from h16_gen_search import penalty
from h20_common import B3, others
torch.set_default_dtype(torch.float64)
eye8=torch.eye(8,dtype=torch.complex128)
def V0(Phi): return torch.einsum('tf,if,st->istf',torch.exp(1j*Phi.reshape(8,8)).to(torch.complex128),eye8,eye8).reshape(64,64)
rng=np.random.default_rng(0)
def fam(theta):   # theta[k][t_k][j], j = f_{-k} index
    Phi=np.zeros((8,8))
    for t in range(8):
        for f in range(8): Phi[t,f]=sum(theta[k][B3[t][k]][others(k,f)] for k in range(3))
    return Phi
print('(a) arbitrary theta_k(t_k,f_-k), 5 random draws: penalties',[round(float(penalty(V0(torch.tensor(fam(rng.uniform(0,2*np.pi,(3,2,4))))))),4) for _ in range(5)])
for k0 in range(3):
    th=np.zeros((3,2,4)); th[k0]=rng.uniform(0,2*np.pi,(2,4)); print('    only party',k0,'nonzero:',float(penalty(V0(torch.tensor(fam(th))))))
H=torch.autograd.functional.hessian(lambda x: penalty(V0(x)), torch.zeros(64))
ev,U=np.linalg.eigh(H.numpy()); null=U[:,np.abs(ev)<1e-8]; print('(b) Hessian at 0: null space dim',null.shape[1],' (nonzero eigenvalues:',int((np.abs(ev)>=1e-8).sum()),')')
# span of functions of (t_k, f_{-k})
B=[]
for k in range(3):
    for tk in range(2):
        for j in range(4):
            th=np.zeros((3,2,4)); th[k][tk][j]=1; B.append(fam(th).reshape(-1))
B=np.array(B).T; rB=np.linalg.matrix_rank(B); print('    span{theta_k(t_k,f_-k)}: dim',rB)
P=null@null.T; print('    is that span inside the null space? residual %.2e'%np.abs(B-P@B).max())
E=json.load(open('h20_fwd_enum.json')); maxi=[tuple(map(tuple,p)) for p in E['maximal']]
R=[]
for parts in maxi:
    for k in range(3):
        for tk in range(2):
            for x in range(max(parts[k])+1):
                th=np.zeros((3,2,4)); th[k][tk]=[1.0 if parts[k][j]==x else 0 for j in range(4)]; R.append(fam(th).reshape(-1))
R=np.array(R).T; print('    span of all refined-PF phase functions: dim',np.linalg.matrix_rank(R),'; null-space dim',null.shape[1])
# is the null space = span B?
print('    null space inside span{theta_k(t_k,f_-k)}? residual %.2e'%np.abs(null-B@np.linalg.lstsq(B,null,rcond=None)[0]).max())
