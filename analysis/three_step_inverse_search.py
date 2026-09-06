#!/usr/bin/env python3
"""Early inverse template u=9w+6 -> v=8w+5.

T^3(24w+17)=27w+20, while T^3(216w+155)=243w+175.
The target is 243w+182. Same-clock/same-count merges give uniform rules.
No target convergence is assumed to discover a rule; coverage stays open.
"""
import json
from early_inverse_bridge_search import search
from affine_bridge_search import step


def classify_base_pair(w,cap=10000):
    x,y,j,k=243*w+175,243*w+182,0,0
    for t in range(cap+1):
        if x==y and j==k:
            return dict(kind='merge',depth=t)
        if x in (1,2) and y in (1,2):
            return dict(kind='terminal_without_merge',depth=t,
                        small=x,large=y,small_odds=j,large_odds=k)
        if t==cap:return dict(kind='cap',depth=t)
        j,k=j+x%2,k+y%2
        x,y=step(x),step(y)


def report(depth=12):
    data=search(depth,multiplier=243,small=175,large=182)
    data['template']='u=9w+6; v=8w+5; three inverse ordinary steps'
    data['mersenne_examples']=[dict(exponent=k,w=(2**k-7)//9,
                                    result=classify_base_pair((2**k-7)//9))
                               for k in (4,10,16,22)]
    return data


if __name__=='__main__':print(json.dumps(report(),indent=2))
