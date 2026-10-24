"""H.15.7e(A): exact fleshing-out of VOKB's Lugano routed circuit (Fig. 30, eqs. (20)-(21)) by classical link-product evaluation.
All node maps are permutations of basis states (one-dimensional sectors, except the 'won' sector of A->F, which holds Aout),
so the composite on a basis input (past qubits p, agent outputs a) is the sum over consistent internal assignments.
Node A (likewise B, C): CNOT l -> p_A gives Ain = p_A + l;  V (eq. 20): l=0: (vote i = Aout, l=0) to X, l=0 to F;
l=1: (i=0, l=1) to X, (l=1, z=Aout) to F.  Node X (eq. 21): on the constraint set C, outputs l,m,n and ijk.  F: record.
Check: for every (p,a) there is exactly ONE consistent assignment, Ain = p + lug(a), and the F record determines a
(so a final unitary U maps it to |a>): the composite is the Lugano purification L.  Its transpose (every node transposed, arrows
reversed) is therefore L^T, which with the local unitaries of rg_h13_lugano.py is the H.13.2 purification."""
import itertools as it
B3=list(it.product((0,1),repeat=3)); lug=lambda a,b,c:((1-b)*c,(1-c)*a,(1-a)*b)
C={(i,j,k,(1-j)*k,(1-k)*i,(1-i)*j) for i,j,k in B3}; C={c for c in C if c[0]*c[3]==0 and c[1]*c[4]==0 and c[2]*c[5]==0}
ok=True; recs={}
for p in B3:
    for a in B3:
        sols=[]
        for r in B3:                      # r = (l,m,n) on X -> agents
            votes=[a[k] if r[k]==0 else 0 for k in range(3)]
            if tuple(votes)+r not in C: continue
            Ain=tuple(p[k]^r[k] for k in range(3))
            rec=(tuple(votes),tuple((r[k],a[k] if r[k] else None) for k in range(3)))
            sols.append((Ain,rec))
        if len(sols)!=1 or sols[0][0]!=tuple(x^y for x,y in zip(p,lug(*a))): ok=False
        recs.setdefault(sols[0][1] if sols else None,set()).add(a)
inj=all(len({a for a in v})==1 for v in recs.values()) and len(recs)==8
print('every (p,a): exactly one consistent assignment and Ain = p + lug(a):',ok)
print('F record determines a (8 distinct records, U embeds them into |a>):',inj)
print('=> fleshing-out of Fig. 27/30 is the Lugano purification L [exact]; its transpose is L^T')
