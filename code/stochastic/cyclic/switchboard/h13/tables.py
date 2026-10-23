"""Appendix J tables [numerical selection, exact where stated]: per facet orbit of conv(PF):
orbit size, sparse integer representative inequality, Z4 exact max (exactmax logs), Z8 numerical max,
Z8 exact certificates. Writes tables.md."""
import numpy as np, gzip, ast, re, json
from scipy.optimize import linprog
F='../../../physics/facets/'
PF=np.load('../../pfs744.npy').astype(float); Zc=np.load(F+'Z.npy').astype(float)
L=gzip.open(F+'pf.out.gz','rt').read().split('\n'); k=next(j for j,l in enumerate(L) if l.strip().endswith('support hyperplanes:'))
Hm=np.array([list(map(int,L[k+1+f].split())) for f in range(int(L[k].split()[0]))],float)
canon=np.load('xviol.npz')['canon'].astype(int); v4=np.load('xviol.npz')['viol'].max(0); v8=np.load('xviol_z8.npz')['viol'].max(0)
B=[(a,b,c) for a in (0,1) for b in (0,1) for c in (0,1)]; bs=lambda t:''.join(map(str,t))
ex={}
for fn in ['exactmax_part1.log','exactmax_part2.log']:
    for l in open(fn):
        m=re.match(r'(\d+) (\{.*\})',l.strip())
        if m: ex[int(m[1])]=ast.literal_eval(m[2])
cert={int(m[1]):l.strip() for l in open('cert_z8.log') for m in [re.search(r'orbit (\d+) facet',l)] if m}
Pf=PF.reshape(744,-1); out=['| orbit | size | representative facet (index) : integer inequality, value >= 0 on every PF |','|---|---|---|']
tab=['| orbit | Z4 exact max: min-eigenvalue polynomial, root (facet range r) | rel. Z4 | rel. Z8 (numerical) | status |','|---|---|---|---|---|']
for o in range(canon.max()+1):
    fs=np.nonzero(canon==o)[0]; f=fs.min(); vals=Zc@Hm[f,:37]+Hm[f,37]
    A=np.c_[Pf,-Pf,np.ones(744),-np.ones(744)]
    r=linprog(np.r_[np.ones(128),0,0],A_eq=A,b_eq=vals,bounds=[(0,None)]*130,method='highs')
    g=r.x[:64]-r.x[64:128]; t=r.x[128]-r.x[129]
    nz=np.abs(g)>1e-7; sc=1/np.abs(g[nz]).min()
    for m in range(1,25):
        G=g*sc*m; T=t*sc*m
        if np.abs(G-np.round(G)).max()<1e-6 and abs(T-round(T))<1e-6: break
    G=np.round(G).astype(int).reshape(8,8); T=int(round(T))
    assert np.abs(Pf@G.ravel()+T - vals*sc*m).max()<1e-6
    terms=[('%+d'%G[i,j]).replace('+1','+').replace('-1','-')+'p(%s|%s)'%(bs(B[i]),bs(B[j])) for i in range(8) for j in range(8) if G[i,j]]
    s=' '.join(terms)+(' %+d'%T if T else '')
    out.append('| %d | %d | (%d) %s >= 0 |'%(o,len(fs),f,s.lstrip('+').replace('+','+ ').replace('-','- ').replace('- ','-',0)))
    st='never violated by Z4/Z8 X-type boards [numerical]' if v8[o]<=1e-6 else ('Z8 exact certificate (Q(zeta8))' if o in cert else ('violated, Z4' if v4[o]>1e-6 else 'violated, Z8 only'))
    e=ex.get(o); es='%s (r=%s)'%(e['lam_min'].replace('**','^').replace('*',''),e['range']) if e else '-'
    tab.append('| %d | %s | %s | %.4g | %s |'%(o,es,'%.4g'%e['relviol'] if e else ('%.3g'%(v4[o] if v4[o]>1e-6 else 0)),(v8[o] if v8[o]>1e-6 else 0),st))
open('tables.md','w').write('\n'.join(out)+'\n\n'+'\n'.join(tab)+'\n')
print(sum(v8<=1e-6),'never', len(cert),'cert')
