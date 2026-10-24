import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
# cube coords for bit strings abc (A,B,C)
def pos(s):
    a,b,c=map(int,s)
    return np.array([b*1.0 + 0.45*c, a*1.0 + 0.35*c])
verts=[format(i,'03b') for i in range(8)]
edges=[(u,v) for u in verts for v in verts if u<v and sum(x!=y for x,y in zip(u,v))==1]
def cube(ax,title,arrows,start,note):
    for u,v in edges:
        p,q=pos(u),pos(v); ax.plot([p[0],q[0]],[p[1],q[1]],color='#cccccc',lw=1,zorder=1)
    for s in verts:
        p=pos(s); hit=s in [t for t,_ in arrows]
        ax.scatter(*p,s=650,color=('#1f77b4' if s==start else ('#ffd27f' if hit else 'white')),edgecolor='k',zorder=3)
        ax.text(p[0],p[1],s,ha='center',va='center',fontsize=8,zorder=4,color=('white' if s==start else 'k'))
    p0=pos(start)
    for t,amp in arrows:
        q=pos(t)
        if t==start:
            ax.annotate('',xy=(p0[0]-0.13,p0[1]+0.2),xytext=(p0[0]+0.13,p0[1]+0.2),
                arrowprops=dict(arrowstyle='->',connectionstyle='arc3,rad=-1.2',color='#d62728' if amp<0 else '#2ca02c',lw=2))
            ax.text(p0[0]-0.32,p0[1]+0.12,f'{amp:+.1f}'.replace('0.5','½').replace('1.0','1'),ha='center',fontsize=11,color='#d62728' if amp<0 else '#2ca02c')
        else:
            d=q-p0; ax.annotate('',xy=q-0.14*d/np.linalg.norm(d),xytext=p0+0.14*d/np.linalg.norm(d),
                arrowprops=dict(arrowstyle='->',color='#d62728' if amp<0 else '#2ca02c',lw=2),zorder=2)
            m=p0+0.6*d; ax.text(m[0]+0.05,m[1]+0.06,f'{amp:+.1f}'.replace('0.5','½').replace('1.0','1'),fontsize=11,color='#d62728' if amp<0 else '#2ca02c')
    ax.set_title(title,fontsize=12); ax.text(0.5,-0.08,note,transform=ax.transAxes,ha='center',va='top',fontsize=9.5,wrap=True)
    ax.set_xlim(-0.4,1.85); ax.set_ylim(-0.4,1.85); ax.set_aspect('equal'); ax.axis('off')
fig,axs=plt.subplots(1,2,figsize=(11,5.6))
cube(axs[0],'One term: a deterministic loop\n(process function, e.g. flip B)',[('010',1.0)],'000',
     'Loop state 000 goes to exactly one state.\nOne history; nothing to interfere.')
cube(axs[1],'Four terms: H.13.2 when outputs are o = 001\n$U = \\frac{1}{2}(-1 + X_A + X_B + X_AX_B)$',
     [('000',-0.5),('100',0.5),('010',0.5),('110',0.5)],'000',
     'Loop state 000 splits into four flip patterns at once,\neach with amplitude ±½ (probability ¼). The minus sign lets\nbranches cancel when several paths meet.')
fig.text(0.5,0.01,'Cube corners = the three loop bits (A,B,C). Green = +, red = −. Exact terms computed from the H.13.2 table in lift.md.',ha='center',fontsize=9,color='#555')
plt.tight_layout(rect=(0,0.04,1,0.95)); import pathlib; plt.savefig(pathlib.Path(__file__).resolve().parent/'fourterms.png',dpi=150)
