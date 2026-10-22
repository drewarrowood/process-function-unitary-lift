"""Exact check (rational arithmetic, python-flint) that, for every nonempty D in {A,B,C}, the linear functionals
of Lemma H.7.1 on K in C^{8x8} and the 'forbidden Pauli coefficient' functionals have the same kernel.
Both families have integer coefficients, so equality of row spaces over Q decides it."""
import itertools as it, flint
B3=list(it.product((0,1),repeat=3)); IX={t:n for n,t in enumerate(B3)}
def h71(D):
    rows=[]
    for d in B3:
        S=[k for k in D if d[k]==0]; rest=[k for k in range(3) if k not in S]
        for er in it.product((0,1),repeat=len(rest)):
            r=[0]*64
            for es in it.product((0,1),repeat=len(S)):
                e=[0]*3
                for k,v in zip(rest,er): e[k]=v
                for k,v in zip(S,es): e[k]=v
                e2=tuple(a^b for a,b in zip(e,d)); r[8*IX[tuple(e)]+IX[e2]]+=(-1)**sum(es)
            rows.append(r)
    return rows
def pauli(D):
    # <X^a Z^b, K> = sum_e K[e, e+a] (-1)^{b.(e+a)}  (entry <e|X^aZ^b|e'> nonzero iff e'=e+a; real integer form)
    rows=[]
    for a in B3:
        for b in B3:
            if all(a[k] or b[k] for k in D):
                r=[0]*64
                for e in B3:
                    e2=tuple(x^y for x,y in zip(e,a)); r[8*IX[e]+IX[e2]]+=(-1)**sum(b[k]*e2[k] for k in range(3))
                rows.append(r)
    return rows
ok=True
for n in (1,2,3):
    for D in it.combinations(range(3),n):
        A=flint.fmpq_mat(h71(D)); P=flint.fmpq_mat(pauli(D)); J=flint.fmpq_mat(h71(D)+pauli(D))
        ra,rp,rj=A.rank(),P.rank(),J.rank(); ok&=(ra==rp==rj)
        print('D',D,'rank H.7.1',ra,'rank Pauli',rp,'rank joint',rj,'allowed dim',64-rp)
print('EQUIVALENT' if ok else 'MISMATCH')
