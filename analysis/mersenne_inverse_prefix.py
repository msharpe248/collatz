#!/usr/bin/env python3
"""Exact prefix formulas for the three-step inverse template's Mersenne inputs.

These arithmetic formulas are not yet Lean declarations. They characterize
only the interval t<=k, not eventual convergence or all inverse templates.
"""
import json
from source_witness_search import trajectory
from two_early_bridges import search,replay


def predicted(k,t):
    if not 0<=t<=k:raise ValueError('require 0<=t<=k')
    if t==0:source,js=27*2**k-14,0
    else:
        m,r=divmod(t-1,3)
        js=2*m+(r!=0)
        source=27*3**js*2**(k-t)-(7,10,5)[r]
    m,r=divmod(t,3)
    jt=2*m+(r!=0)
    target=27*3**jt*2**(k-t)-(7,10,5)[r]
    return source,js,target,jt


def check(k):
    a=trajectory(27*2**k-14,k)
    b=trajectory(27*2**k-7,k)
    for t in range(k+1):
        x,j,y,l=predicted(k,t)
        assert (x,j)==a[t][:2] and (y,l)==b[t][:2]
        assert 3**(j+2)>2**t # necessary slope condition for an extra bridge fails
        assert x!=y or j!=l # uniform same-count merge fails


def report():
    for k in range(101):check(k)
    rows=[]
    for k in range(4,65,6):
        c=search((2**k-7)//9,depth=300,max_extra=1)
        if c['kind']=='certificate':
            assert c['depth']>k
            for Q in (0,1,7):replay(c,Q)
        rows.append(dict(exponent=k,kind=c['kind'],depth=c['depth'],
                         extra_bridges=len(c.get('extra',[]))))
    return dict(scope='prefix formulas tested k=0..100; finite one-extra-bridge probes',
                kernel_certified=False,probes=rows)

if __name__=='__main__':print(json.dumps(report(),indent=2))
