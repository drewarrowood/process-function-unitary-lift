"""Round 24 (H.31.3): independent checker B for h24_cert_o<orbit>.json.
Recomputes from scratch (no h24_sdp2 / h24_cert code): the rule-4 phase-board exponents, the classes (z,z',e), the frame spans,
checks that the certificate's facet functional reproduces the facet on all 744 PFs, and checks
 (i)  every H_i = P_i G_i P_i^T is PSD: G_i's real embedding is positive definite, by strict sign alternation of its exact
      characteristic polynomial (all roots real and positive);
 (ii) for every class c and every frame-span generator r: r . (W[:,c] - conj h_c - mu [c diagonal-zero]) = 0 exactly;
 (iii) mu + g0 >= 0;
 (iv) sanity (numerical): on random rule-4 phase boards with random frames and sources, facet value = sum_i <H_i, Z(i)> + mu + g0.
usage: orbit [json]"""
import sys, json, itertools as it, numpy as np
from fractions import Fraction as Fr
import flint
sys.set_int_max_str_digits(0)
fq=lambda x: flint.fmpq(int(Fr(x).numerator),int(Fr(x).denominator))
orb=int(sys.argv[1]); d=json.load(open(sys.argv[2] if len(sys.argv)>2 else f'h24_cert_o{orb}.json')); f=d['facet']
bits=lambda n:((n>>2)&1,(n>>1)&1,n&1)
from h20_common import PF, valsI
from h23_span import MAXI
blk=MAXI[4]
def xk(k,z):
    b=bits(z); r=[b[j] for j in range(3) if j!=k]; return blk[k][2*r[0]+r[1]]
assert all(len(set(blk[k]))==2 for k in range(3)), 'rule 4 should have block counts (2,2,2)'
# functional: the certificate's representative g must reproduce the facet value on all 744 PFs exactly (then it is the facet
# functional on aff(PF) = aff(Valid), which contains every phase board); independently, the PF rows have rank 38 (flint rref)
Xr=[[int(PF[n][i][o]) for i in range(8) for o in range(8)]+[1] for n in range(744)]; v=[int(valsI[n,f]) for n in range(744)]
_,rk=flint.fmpq_mat(Xr).rref(); assert rk==38
sol=[Fr(x) for x in d['g']]
assert all(sum(sol[j]*Xr[n][j] for j in range(65) if Xr[n][j])==v[n] for n in range(744)), 'g is not the facet functional'
print('g reproduces the facet on all 744 PFs; PF affine rank',rk)
g=[[sol[8*i+o] for o in range(8)] for i in range(8)]; g0=sol[64]
mu=Fr(d['mu']); print('mu+g0 =',mu+g0, '(iii)', mu+g0>=0)
# classes
key={}
def cls(o,z,op,zp):
    e=tuple(bits(o)[k]*xk(k,z)-bits(op)[k]*xk(k,zp) for k in range(3)); return key.setdefault((z,zp,e),len(key))
ID=[[cls(a>>3,a&7,b>>3,b&7) for b in range(64)] for a in range(64)]
def span(z,zp):
    fs=[[(1,1),(1,-1)] if bits(z)[k]==bits(zp)[k] else [(1,-1)] for k in range(3)]
    return [[p[bits(i)[0]]*q[bits(i)[1]]*s[bits(i)[2]] for i in range(8)] for p,q,s in it.product(*fs)]
# H_i exact
H=[]; okpd=True
for i in range(8):
    P=[[Fr(x) for x in row] for row in d['P'][i]]; GA=[[Fr(x) for x in row] for row in d['GA'][i]]; GB=[[Fr(x) for x in row] for row in d['GB'][i]]
    r=len(GA); E=flint.fmpq_mat([[fq(GA[s][t]) for t in range(r)]+[fq(-GB[s][t]) for t in range(r)] for s in range(r)]+[[fq(GB[s][t]) for t in range(r)]+[fq(GA[s][t]) for t in range(r)] for s in range(r)])
    assert all(E[a,b]==E[b,a] for a in range(2*r) for b in range(2*r))
    cp=E.charpoly().coeffs()   # low -> high; PD iff coefficients strictly alternate in sign
    m=len(cp)-1; pd=all(cp[k]!=0 and ((cp[k]>0)==((m-k)%2==0)) for k in range(m+1)); okpd&=pd
    Pm=flint.fmpq_mat([[fq(x) for x in row] for row in P]); Ar=flint.fmpq_mat([[fq(x) for x in row] for row in GA]); Br=flint.fmpq_mat([[fq(x) for x in row] for row in GB])
    HA=Pm*Ar*Pm.transpose(); HB=Pm*Br*Pm.transpose()      # H = HA + i HB  (P real)
    H.append((HA,HB))
print('(i) all G_i positive definite (charpoly sign test):',okpd)
n=len(key); hre=[[Fr(0)]*n for _ in range(8)]; him=[[Fr(0)]*n for _ in range(8)]
for i in range(8):
    HA,HB=H[i]
    for a in range(64):
        for b in range(64):
            c=ID[a][b]; x=HA[a,b]; y=HB[a,b]
            if x!=0: hre[i][c]+=Fr(int(x.p),int(x.q))
            if y!=0: him[i][c]+=Fr(int(y.p),int(y.q))
Wc=[[sum(g[i][a>>3] for a in range(64) for b in range(64) if (a>>3)==(b>>3) and ID[a][b]==c) for c in range(n)] for i in range(8)]
inv={c:k for k,c in key.items()}; bad=0
for c in range(n):
    z,zp,e=inv[c]; dz=(z==zp and e==(0,0,0))
    for r_ in span(z,zp):
        re=sum(r_[i]*(Wc[i][c]-hre[i][c]-(mu if dz else 0)) for i in range(8)); im=sum(r_[i]*him[i][c] for i in range(8))   # conj h: -i Im h
        if re!=0 or im!=0: bad+=1
print('(ii) class conditions violated:',bad,'of classes',n)
# (iv) numerical sanity on random boards
rng=np.random.default_rng(7); Hc=[np.array([[float(HA[a,b]) for b in range(64)] for a in range(64)])+1j*np.array([[float(HB[a,b]) for b in range(64)] for a in range(64)]) for HA,HB in H]
gn=np.array([[float(x) for x in row] for row in g]); err=0
for trial in range(20):
    u=np.exp(1j*rng.uniform(0,2*np.pi,3)); psi=rng.normal(size=8)+1j*rng.normal(size=8); psi/=np.linalg.norm(psi)
    Us=[np.linalg.qr(rng.normal(size=(2,2))+1j*rng.normal(size=(2,2)))[0] for _ in range(3)]
    fr=np.array([np.prod([Us[k][bits(z)[k],bits(i)[k]] for k in range(3)]) for i in range(8) for z in range(8)]).reshape(8,8)  # fr[i,z] = <z|f_i>
    vo=np.array([[np.prod([u[k]**(bits(o)[k]*xk(k,z)) for k in range(3)])*psi[z] for z in range(8)] for o in range(8)])
    p=np.abs(fr.conj()@vo.T)**2   # p[i,o]
    val=(gn*p).sum()+float(g0)
    V=vo.reshape(64); q=0
    for i in range(8):
        w=np.tile(fr[i].conj(),8)*V; Z=np.outer(w,w.conj())   # Z(i)[(o,z),(o',z')]
        q+=np.real(np.sum(Hc[i].conj()*Z))
    err=max(err,abs(val-(q+float(mu)+float(g0))))
print('(iv) max |value - (sum<H,Z> + mu + g0)| over 20 random boards:',err)
ok=okpd and bad==0 and mu+g0>=0 and err<1e-8
print(f'CHECKER B orbit {orb} facet {f}: certificate {"VALID" if ok else "INVALID"}; proves facet >= {mu+g0} on all PF phase boards on rule 4')
