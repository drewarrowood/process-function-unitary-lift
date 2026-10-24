"""Round 16 (H.23.1b): XOR boards i = s xor f(o), f_k a function of o_{-k} (16^3 tables): count the valid ones (exactly one fixed point under every deterministic intervention), the non-causal ones, and those with no constant f_k."""
import itertools as it
B3=list(it.product((0,1),repeat=3))
G=[(0,0),(0,1),(1,0),(1,1)]  # g(i)= table
res=[]
for tabs in it.product(range(16),repeat=3):
    def f(o):
        out=[]
        for k in range(3):
            oth=[o[j] for j in range(3) if j!=k]; out.append((tabs[k]>>(2*oth[0]+oth[1]))&1)
        return tuple(out)
    ok=True
    for g in it.product(G,repeat=3):
        n=sum(1 for o in B3 if tuple(g[k][f(o)[k]] for k in range(3))==o)
        if n!=1: ok=False;break
    if ok: res.append(tabs)
print(len(res))
# causal? check whether some party's input is constant (first party)
def noncausal(t):
    # causal order exists iff recursively some party's f is constant
    import itertools
    tabs=list(t)
    for perm in itertools.permutations(range(3)):
        # f_perm0 const; f_perm1 depends only on perm0
        a,b,c=perm
        def dep(k,j):  # does f_k depend on o_j
            oth=[x for x in range(3) if x!=k]; pos=oth.index(j)
            for v in range(4):
                w=v^(1<<(1-pos))
                if ((tabs[k]>>v)&1)!=((tabs[k]>>w)&1): return True
            return False
        if not dep(a,b) and not dep(a,c) and not dep(b,c): return False
    return True
nc=[t for t in res if noncausal(t)]
print(len(nc)); print(nc[:40])
nc=[t for t in res if all(x not in (0,15) for x in t)]
print('no constant:',len(nc)); print(nc)
