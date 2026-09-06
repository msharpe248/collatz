#!/usr/bin/env python3
"""Add a forward smaller-transfer bridge after the three-step inverse template.

Records symbolic slopes on u=9w+6+9*2^D*Q. All recursive premises stay
explicit; a successful finite sample is not global coverage.
"""
import json
from affine_bridge_search import step
from source_witness_search import trajectory


def search(w,depth=60,max_extra=1,state_cap=10000):
    u=9*w+6
    states={(243*w+175,5):()}
    y,q=243*w+182,5
    for t in range(depth+1):
        queue=list(states)
        for x,p in queue:
            path=states[x,p]
            if (len(path)<max_extra and x%3==2 and (x-2)//3<u
                    and 3**(p-3)<=2**t):
                key=(9*x+2,p+2)
                candidate=path+((t,(x-2)//3,p-1),)
                if key not in states or len(candidate)<len(states[key]):
                    states[key]=candidate;queue.append(key)
                    if len(states)>state_cap:return dict(kind='state_cap',w=w,depth=t)
        if (y,q) in states:
            return dict(kind='certificate',w=w,depth=t,
                        extra=[dict(time=s,parameter=v,exponent=e) for s,v,e in states[y,q]],
                        endpoint=y,exponent=q)
        next_states={}
        for (x,p),path in states.items():
            key=(step(x),p+x%2)
            if key not in next_states or len(path)<len(next_states[key]):
                next_states[key]=path
        states=next_states
        q,y=q+y%2,step(y)
    return dict(kind='depth_limit',w=w,depth=depth)


def replay(c,Q):
    w,D=c['w'],c['depth']
    W=w+2**D*Q
    u,v=9*W+6,8*W+5
    assert v<u
    assert trajectory(3*v+2,3)[-1][0]==3*u+2
    x=trajectory(27*v+20,3)[-1][0]
    t=0
    for op in c['extra']:
        x=trajectory(x,op['time']-t)[-1][0]
        v=op['parameter']+3**op['exponent']*2**(D-op['time'])*Q
        assert 0<=v<u and x==3*v+2
        x=27*v+20;t=op['time']
    x=trajectory(x,D-t)[-1][0]
    assert x==trajectory(27*u+20,D)[-1][0]
    assert x==c['endpoint']+3**c['exponent']*Q


if __name__=='__main__':
    rows=[search(w) for w in range(256)]
    counts={kind:sum(c['kind']==kind for c in rows) for kind in sorted({c['kind'] for c in rows})}
    print(json.dumps(dict(scope='finite sample; smaller-transfer premises explicit',
                         kernel_certified_census=False,counts=counts,
                         example=search(1)),indent=2))
