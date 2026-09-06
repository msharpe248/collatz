#!/usr/bin/env python3
"""Signed orbit excursions repair either cycle-charge mismatch.

Construction assumes only verified convergence of the finite BASE pair. The
quotient lifts remain conditional on smaller affine-transfer instances. It
therefore does not establish global Collatz coverage.
"""
import json
from affine_bridge_search import step
from source_witness_search import trajectory


def construct(u,cap=10000):
    if u<=15:
        raise ValueError('this construction needs u>15')
    x,y,p,q,t=3*u+2,27*u+20,1,3,0
    ops=[]
    def record_forward(length):
        if length:
            if ops and ops[-1]['kind']=='forward':ops[-1]['length']+=length
            else:ops.append(dict(kind='forward',length=length))
    while x not in (1,2) or y not in (1,2):
        if t>=cap:return dict(kind='base_cap',parameter=u)
        p,q=p+x%2,q+y%2
        x,y,t=step(x),step(y),t+1
    record_forward(t)
    entry=t
    delta=2*q+(y==1)-2*p-(x==1)
    initial_delta=delta
    high=t
    def advance(x,p,t,length):
        record_forward(length)
        for _ in range(length):p,x,t=p+x%2,step(x),t+1
        return x,p,t
    negatives=0
    while delta<0:
        # Stay beyond both original cycle entries even after reversing 65
        # steps; retain enough powers of 3 and a decreasing parameter slope.
        while x!=2 or t<entry+65 or p<39 or 3**(p-39)>2**(t-65):
            if t>=cap:return dict(kind='construction_cap',parameter=u)
            x,p,t=advance(x,p,t,1)
        high=max(high,t)
        ops.append(dict(kind='inverse_47',length=65))
        x,p,t=47,p-38,t-65
        ops.append(dict(kind='bridge',parameter=15))
        x,p=425,p+2
        x,p,t=advance(x,p,t,38)
        assert x==2
        delta+=7;negatives+=1
    for _ in range(delta):
        while x!=2 or 3**(p-1)>2**t:
            if t>=cap:return dict(kind='construction_cap',parameter=u)
            x,p,t=advance(x,p,t,1)
        if t+7>cap:return dict(kind='construction_cap',parameter=u)
        ops.append(dict(kind='bridge',parameter=0))
        x,p=20,p+2
        x,p,t=advance(x,p,t,7)
        high=max(high,t)
    # Final binary modulus must accommodate every earlier forward prefix,
    # including prefixes followed by backwards movement.
    x,p,t=advance(x,p,t,max(0,high-t))
    target,j,_=trajectory(27*u+20,t)[-1]
    assert (x,p)==(target,j+3)
    return dict(kind='certificate',parameter=u,depth=t,operations=ops,
                endpoint=x,exponent=p,initial_gap=initial_delta,
                negative_excursions=negatives)


def replay(c,Q):
    D,u=c['depth'],c['parameter']
    U=u+2**D*Q
    x,t=3*U+2,0
    for op in c['operations']:
        if op['kind']=='forward':
            x,_,_=trajectory(x,op['length'])[-1]
            t+=op['length']
            assert t<=D
        elif op['kind']=='inverse_47':
            assert x>=2 and (x-2)%3**38==0
            predecessor=47+2**65*((x-2)//3**38)
            assert trajectory(predecessor,65)[-1][0]==x
            x,t=predecessor,t-65
            assert t>=0
        else:
            assert x%3==2
            v=(x-2)//3
            assert op['parameter']<=v<U
            x=27*v+20
    assert t==D
    assert x==trajectory(27*U+20,D)[-1][0]
    assert x==c['endpoint']+3**c['exponent']*Q


if __name__=='__main__':
    rows=[construct(u) for u in range(16,1001)]
    counts={kind:sum(c['kind']==kind for c in rows) for kind in sorted({c['kind'] for c in rows})}
    print(json.dumps(dict(scope='finite base census; smaller-transfer premises remain',
                         kernel_certified_census=False,
                         counts=counts,max_depth=max(c.get('depth',0) for c in rows),
                         examples=[c for c in rows if c['parameter'] in (16,20,23,1000)]),indent=2))
