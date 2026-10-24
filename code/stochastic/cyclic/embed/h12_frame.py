"""H.15.8: is the H.12 board a phased permutation in the Hadamard frame (like H.13.2 = phase lift of a PF)?
In the frame of H.15.7d, U_o = Hd diag(i^{m_o(z)}) Hd becomes |z>|w> -> |z> (Hd-transform over o of i^{m_o(z)} (-1)^{o.w}).
This is a basis state (up to phase) for every z iff o -> i^{m_o(z) - m_0(z)} is a character (-1)^{o.c(z)}.  Exact integer test."""
MT=[[0,3,0,0,2,0,3,0],[0,3,2,2,2,0,3,0],[0,3,0,0,2,1,3,1],[0,3,2,2,2,1,3,1],[0,1,2,2,2,2,1,2],[0,1,0,0,2,2,1,2],[0,1,2,2,2,3,1,3],[0,1,0,0,2,3,1,3]]
par=lambda x:bin(x).count('1')&1
bad=[]
for z in range(8):
    col=[MT[o][z] for o in range(8)]
    ok=[c for c in range(8) if all((col[o]-col[0]-2*par(o&c))%4==0 for o in range(8))]
    print('z =',format(z,'03b'),'exponents over o:',col,'-> character' if ok else '-> NOT a character'); bad+=[] if ok else [z]
print('H.12 is a phased permutation in the Hadamard frame:',not bad,'; failing z:',[format(z,'03b') for z in bad])
