"""Round 33 (H.38): zero-set facial reduction for the t0 = 0 SOS of h33_sos.py.
Homogenised basis vector V_b(t1,t2,u): y1^i y2^j u^m scaled by cos(t1/2)^d1 cos(t2/2)^d2, i.e. s1^i c1^(d1-i) s2^j c2^(d2-j) u^m.
Zero families of H (homogenised; h33_face.py checks H = 0 on samples):
  F1 {u2=1, y2=0}; F2 {u0=u2=1}; F3 {u1=u2=1}; Y0 {y1=y2=0}; YE {y1=0, a0=a1=pi, y2=1};
  I1 {y1=inf} x ({y2=0} | {u1=1} | {u0u2=1}); I2 {y2=inf} x ({y1=0} | {u2=1} | {u0u2=1}).
Kernel K_b = span of Re/Im V_b(z) over samples; compared with the numerical kernel of the SCS Gram (h33_sos.py).  usage: orbit"""
import sys
orb=sys.argv[1]; sys.argv=['h33_sos.py',orb,'1']
exec(open('h33_sos.py').read().split("if __name__=='__main__':")[0])
Hs=sp.expand(sum(c*y[1]**k[0]*y[2]**k[1]*u[0]**k[2]*u[1]**k[3]*u[2]**k[4] for k,c in H.items()))
ss=sp.symbols('s1 c1 s2 c2',real=True)
Hh=sp.expand(Hs.subs({y[1]:ss[0]/ss[1],y[2]:ss[2]/ss[3]})*ss[1]**(2*d1)*ss[3]**(2*d2))
fH=sp.lambdify([*u,*ss],Hh,'numpy')
rng=np.random.default_rng(int(sys.argv[2]) if len(sys.argv)>2 else 0)
def pt(fam):
    a=rng.uniform(-np.pi,np.pi,3); t=rng.uniform(-np.pi,np.pi,2)
    if fam=='F1': a[2]=0; t[1]=0
    if fam=='F2': a[0]=a[2]=0
    if fam=='F3': a[1]=a[2]=0
    if fam=='Y0': t[:]=0
    if fam=='Yp':
        t[0]=0; U0,U1=np.exp(1j*a[0]),np.exp(1j*a[1]); a[2]=np.angle((U0+U1-2)/(U0*U1-1))   # u2 = (u0+u1-2)/(u0u1-1)
    if fam=='YE': t[0]=0; a[0]=a[1]=np.pi; t[1]=np.pi/2
    if fam[0]=='I':
        k=int(fam[1])-1; t[k]=np.pi; w=fam[3:]
        if w=='y0': t[1-k]=0
        if w=='u1': a[1]=0
        if w=='u2': a[2]=0
        if w=='u02': a[2]=-a[0]
    return a,t
fams=['F1','F2','F3','Y0','YE','I1:y0','I1:u1','I1:u02','I2:y0','I2:u2','I2:u02']
def V(b,a,t):
    s1,c1,s2,c2=np.sin(t[0]/2),np.cos(t[0]/2),np.sin(t[1]/2),np.cos(t[1]/2)
    return np.array([s1**i*c1**(d1-i)*s2**j*c2**(d2-j)*np.exp(1j*np.dot(m,a)) for i,j,m in b])
for fam in fams:
    a_,t_=pt(fam); val=fH(*np.exp(1j*a_),np.sin(t_[0]/2),np.cos(t_[0]/2),np.sin(t_[1]/2),np.cos(t_[1]/2))
    print(orb,fam,'H(sample) =',np.round(complex(val),12),flush=True)
Ks={}
for kb,b in basis.items():
    rows=[]
    for fam in fams:
        for r in range(150):
            a_,t_=pt(fam); v=V(b,a_,t_); rows+= [v.real,v.imag]
    Mz=np.array(rows); sv=np.linalg.svd(Mz,compute_uv=False); rk=(sv>1e-8*sv[0]).sum()
    print(orb,kb,'zero-set kernel rank',rk,'sv around gap',sv[max(rk-2,0):rk+2],flush=True)
    Ks[kb]=Mz
pickle.dump(Ks,open(f'/tmp/h33_face_{orb}.pkl','wb'))
