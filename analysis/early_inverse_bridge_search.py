#!/usr/bin/env python3
"""Uniform early inverse bridges on u=3w+2, without target-cycle assumptions.

T(6w+5)=9w+8 and T(54w+47)=81w+71. Transfer at v=2w+1
therefore supplies convergence of 81w+71. A same-count merge with 81w+74
supplies transfer at u=3w+2. Search whole binary w-cylinders exactly.
"""
import json
from affine_bridge_search import step


def search(depth=12, *, multiplier=81, small=71, large=74):
    rows=[(0,small,large,0,0)]
    covered=0
    levels=[];certs=[]
    for t in range(1,depth+1):
        new=[];hits=0
        for r,x,y,j,k in rows:
            for bit in (0,1):
                xx,yy=x+multiplier*3**j*bit,y+multiplier*3**k*bit
                jj,kk=j+xx%2,k+yy%2
                xx,yy=step(xx),step(yy)
                rr=r+2**(t-1)*bit
                if xx==yy and jj==kk:
                    hits+=1
                    certs.append(dict(w=rr,depth=t,endpoint=xx,odds=jj))
                else:new.append((rr,xx,yy,jj,kk))
        rows=new;covered=2*covered+hits
        assert covered+len(rows)==2**t
        levels.append(dict(depth=t,covered=covered,unresolved=len(rows),new_rules=hits))
    return dict(scope='all quotients of certified w-cylinders; smaller-transfer premise retained',
                kernel_certified_census=False,levels=levels,certificates=certs)


if __name__=='__main__':print(json.dumps(search(),indent=2))
