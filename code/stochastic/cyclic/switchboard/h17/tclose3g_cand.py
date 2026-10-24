"""Triple-consistency filter for tclose3g candidates and unresolved jobs [PROVED necessary condition]:
V_cV_a^dag = (V_cV_b^dag)(V_bV_a^dag), so supp G_ac is contained in the sumset S_bc + S_ab (Pauli strings multiply by XOR up to phase),
and likewise for the other two orderings.  This is invariant under the job translations.  A job that violates it has no unitary realisation."""
import gzip, json, collections
def sums(A,B): return {a^b for a in A for b in B}
def consistent(j):
    ab,ac,bc=map(set,j)
    return ac<=sums(ab,bc) and ab<=sums(ac,bc) and bc<=sums(ab,ac)
st=collections.Counter(); keep=[]
for l in gzip.open('tclose3g_done.txt.gz','rt'):
    ai,d=l.split('\t'); ai=int(ai); d=json.loads(d)
    for j,r in d['cand']:
        ok=consistent(j); st['cand '+('CONSISTENT' if ok else 'inconsistent')]+=1
        if ok: keep.append((ai,j,r)); print('CONSISTENT CANDIDATE',ai,j,r)
    for j in d['unresolved']:
        st['unresolved '+('consistent' if consistent(j) else 'inconsistent')]+=1
print(dict(st))
