# negative control for h12_exact_sympy.py part (5): flip one phase exponent; the exact test must FAIL
exec(open('h12_exact_sympy.py').read().split("assert all((u*u.H)")[0].replace("m=[[0,3,0,0,2,0,3,0]","m=[[1,3,0,0,2,0,3,0]"))
src=open('h12_exact_sympy.py').read(); part5=src[src.index("def rat_unitary"):].replace("[1,1,1,2,2]","[1]").replace("assert ok1 and ok2","print('negative control (expected False):',ok1,ok2)")
exec(part5.replace("print('ALL EXACT CHECKS PASSED')",""))
