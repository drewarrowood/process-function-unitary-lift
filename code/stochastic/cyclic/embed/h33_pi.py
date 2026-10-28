"""Round 33 (H.38): exact sign of the transverse coefficient on the sheet t0 = pi (both orbits).
G_pi = det A2 * w^dag B0 w - (C w)^dag adj(A2) (C w), w = (1,0,y1,0) spanning ker B2.  Claim:
  G_pi = 2 (1+y1^2)^4 (1+y2^2)^4 Q / 243,
  Q = y1^4 |1-u1|^2 + y1^2 y2^2 |1-u2|^2 + 8 y1^2 s1 s12 c2 + |1-u1 u2|^2
    = 4 (s1 y1^2 + s12 c2)^2 + 4 s12^2 s2^2 + 4 y1^2 y2^2 s2^2  >= 0,
with s1 = sin(a1/2), s12 = sin((a1+a2)/2), c2 = cos(a2/2), s2 = sin(a2/2).  usage: orbit"""
import sys, pickle, sympy as sp
orb=int(sys.argv[1]); a=pickle.load(open(f'h33_exact_o{orb}.pkl','rb'))
y=sp.symbols('y0:3',real=True); u=sp.symbols('u0:3'); v=sp.symbols('v1:3')   # v_k = exp(i a_k / 2)
Gpi=sp.together(a['Gpi'])
sn=lambda z:(z-1/z)/(2*sp.I); cs=lambda z:(z+1/z)/2
s1,s12,c2,s2=sn(v[0]),sn(v[0]*v[1]),cs(v[1]),sn(v[1])
Q=4*(s1*y[1]**2+s12*c2)**2+4*s12**2*s2**2+4*y[1]**2*y[2]**2*s2**2
claim=2*(1+y[1]**2)**4*(1+y[2]**2)**4*Q/243
d=sp.expand(sp.numer(sp.together(Gpi.subs({u[1]:v[0]**2,u[2]:v[1]**2},simultaneous=True)-claim)))
print(orb,'numerator of G_pi - 2(1+y1^2)^4(1+y2^2)^4 Q/243 (Laurent in v_k = e^{i a_k/2}) =',d)
Qu=sp.expand(y[1]**4*(2-u[1]-1/u[1])+y[1]**2*y[2]**2*(2-u[2]-1/u[2])+(2-u[1]*u[2]-1/(u[1]*u[2])))
e=sp.expand(sp.numer(sp.together((Q-8*y[1]**2*s1*s12*c2).subs({},)-Qu.subs({u[1]:v[0]**2,u[2]:v[1]**2}))))
print(orb,'Q - [y1^4|1-u1|^2 + y1^2y2^2|1-u2|^2 + 8y1^2 s1 s12 c2 + |1-u1u2|^2] =',e)
print(orb,'zeros of Q: s2 = 0 and s12 = 0 and s1 y1 = 0, i.e. {a1 = a2 = 0} u {y1 = 0, a1 + a2 = 0} (mod 2 pi)')
print(orb,'det A2 =',sp.factor(a['dA2']))
