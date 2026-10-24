"""Re-check the 144 first-pass tclose3 candidates with the translation-normalised groups of H.17.11(a) (leaf test only changed;
the root condition is unchanged, so non-candidates stay non-candidates)."""
import ast, tclose3 as T
from multiprocessing import Pool
rows=[l for l in open('tclose3_pass1.log') if l.startswith('CANDIDATE')]
jobs=[]
for l in rows:
    j=l.split(' ',1)[1]; i=j.index(') {'); jobs.append(ast.literal_eval(j[:i+1]))
with Pool(8) as p: res=p.map(T.solve,jobs)
for j,r in zip(jobs,res):
    if r: print('STILL',j,r)
print('SUMMARY rechecked',len(jobs),'still candidates',sum(r not in (None,'UNRESOLVED') for r in res),'unresolved',sum(r=='UNRESOLVED' for r in res))
