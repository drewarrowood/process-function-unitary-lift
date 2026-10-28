"""Round 33 (H.38): exact proof that B0 = M0[Q,Q] (sheet t0 = 0) is positive semidefinite, and positive definite off {y1 = 0}.
det B0 = (1+y1^2)^2 (row0 + y1^2 row2 + y1^4 row4) / 81 (as trig polynomials in a0, a1; Y = y2^2), with
  row0 = 4 (1+Y)^2 (1 + (K+1) Y + Y^2),  K = cos a0 + cos a1 - cos(a0+a1) >= -3,  so row0 >= 4 (1+Y)^2 (1-Y)^2 >= 0;
  row2 = 8 + (20+12K-8 s0 s1) Y + (40+8K) Y^2 + (32+4 s0 s1) Y^3 + 8 Y^4  >=  p(Y) = 8 - 24Y + 16Y^2 + 28Y^3 + 8Y^4 > 0 (Y >= 0);
  row4 = 4 (1+Y)^4.
All identities are verified symbolically below; positivity of p on [0, inf) by exact real-root isolation.  usage: orbit"""
import sys, pickle, sympy as sp, numpy as np
orb=int(sys.argv[1]); a=pickle.load(open(f'h33_exact_o{orb}.pkl','rb'))
y=sp.symbols('y0:3',real=True); u=sp.symbols('u0:3'); Y=sp.Symbol('Y')
c0=(u[0]+1/u[0])/2; c1=(u[1]+1/u[1])/2; c01=(u[0]*u[1]+1/(u[0]*u[1]))/2
s0s1=c0*c1-c01                                    # sin a0 sin a1 = cos a0 cos a1 - cos(a0+a1)
K=c0+c1-c01
row0=4*(1+Y)**2*(1+(K+1)*Y+Y**2)
row2=8+(20+12*K-8*s0s1)*Y+(40+8*K)*Y**2+(32+4*s0s1)*Y**3+8*Y**4
row4=4*(1+Y)**4
claim=(1+y[1]**2)**2*(row0+y[1]**2*row2+y[1]**4*row4).subs(Y,y[2]**2)/81
diff=sp.simplify(sp.together(sp.expand(a['dB0']-claim)))
print(orb,'det B0 - claimed decomposition =',diff)
p=8-24*Y+16*Y**2+28*Y**3+8*Y**4
print(orb,'p real roots:',sp.Poly(p,Y).real_roots(),' p(0) =',p.subs(Y,0))
# row2 - p = (12K+36 - 8 s0s1 - 8 ... ) check sign: row2 - p = (12(K+3) + 8(1 - s0s1)) Y + 8(K+3) Y^2 + 4(1+s0s1) Y^3
print(orb,'row2 - p - [12(K+3)+8(1-s0s1)]Y - 8(K+3)Y^2 - 4(1+s0s1)Y^3 =',sp.simplify(sp.expand(row2-p-(12*(K+3)+8*(1-s0s1))*Y-8*(K+3)*Y**2-4*(1+s0s1)*Y**3)))
print(orb,'K+3 = (1+cos a0)+(1+cos a1)+(1-cos(a0+a1)) >= 0; 1 +- s0s1 >= 0.  Hence det B0 >= 0, with det B0 > 0 when y1 != 0.')
# B0 PD at one point of each component y1>0, y1<0 (det B0 > 0 on each connected component => B0 > 0 there)
B0=a['B0']
for y1v in (1,-1):
    Bn=np.array(B0.subs({u[0]:1,u[1]:1,u[2]:1,y[1]:y1v,y[2]:0}).evalf(),dtype=complex)
    print(orb,f'eig B0 at a=0,y1={y1v},y2=0:',np.round(np.linalg.eigvalsh(Bn),6))
