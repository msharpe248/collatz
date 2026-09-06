#!/usr/bin/env python3
"""Construct late zero-base-parameter bridges using an exact cycle invariant.

Requires both BASE orbits to reach the trivial cycle. This does not assume
convergence of their quotient lifts. Every lifted bridge remains conditional on
a smaller transfer. Negative invariant gaps reject this restricted late-bridge
mechanism only, not bridges earlier in the orbits.
"""
import json
from affine_bridge_search import step


def charge(x,p,t):
    if x not in (1,2):
        raise ValueError('charge is defined here only on the trivial cycle')
    return 2*p-t+(x==1)


def construct(u, cap=10000):
    if u<1 or cap<1:
        raise ValueError('positive parameter and step cap required')
    x,y,p,q,t=3*u+2,27*u+20,1,3,0
    def advance(x,y,p,q,t):
        return step(x),step(y),p+x%2,q+y%2,t+1
    while x not in (1,2) or y not in (1,2):
        if t>=cap:
            return dict(kind='base_orbit_cap',parameter=u,depth=t)
        x,y,p,q,t=advance(x,y,p,q,t)
    delta=charge(y,q,t)-charge(x,p,t)
    if delta<0:
        return dict(kind='negative_cycle_gap',parameter=u,gap=delta,depth=t)
    bridges=[]
    for _ in range(delta):
        # Waiting on the cycle preserves charge and eventually makes the
        # lifted parameter slope <= the original parameter slope.
        while x!=2 or 3**(p-1)>2**t:
            if t>=cap:
                return dict(kind='construction_cap',parameter=u,depth=t)
            x,y,p,q,t=advance(x,y,p,q,t)
        old=charge(x,p,t)
        bridges.append(dict(time=t,parameter=0,exponent=p-1))
        x,p=20,p+2
        # T^7(20)=2 with two odd steps: total p increment four and
        # clock increment seven, hence charge increases by one.
        for _ in range(7):
            if t>=cap:
                return dict(kind='construction_cap',parameter=u,depth=t)
            x,y,p,q,t=advance(x,y,p,q,t)
        assert charge(x,p,t)==old+1
    assert (x,p)==(y,q)
    return dict(kind='certificate',parameter=u,depth=t,bridges=bridges,
                endpoint=y,exponent=q,initial_gap=delta)


def census(limit=1000):
    rows=[construct(u) for u in range(1,limit+1)]
    counts={kind:sum(r['kind']==kind for r in rows) for kind in sorted({r['kind'] for r in rows})}
    certificates=[r for r in rows if r['kind']=='certificate']
    return dict(scope='base parameters 1..limit; conditional lifted certificates, no global coverage',
                kernel_certified_census=False,limit=limit,counts=counts,
                max_bridges=max(len(r['bridges']) for r in certificates),
                max_depth=max(r['depth'] for r in certificates),rows=rows)


if __name__=='__main__':
    print(json.dumps(census(),indent=2))
