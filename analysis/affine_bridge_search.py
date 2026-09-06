#!/usr/bin/env python3
"""Symbolic smaller-transfer bridges on binary parameter cylinders.

At clock t a marked source is x + 3**p * 2**(D-t) * Q. A bridge
replaces it by nine times itself plus two, using transfer at the parameter
(source-2)/3. Every such parameter must be strictly below u+2**D*Q for
all Q>=0. Certificates are conditional on those smaller transfer instances.
No global coverage or termination claim is made.
"""
import argparse
from collections import Counter
import json


def step(n):
    return (3*n+1)//2 if n % 2 else n//2


def classify_pair(u, cap=10000):
    """Original two criteria; joint cycle proves failure at all later times."""
    if u < 0 or cap < 1:
        raise ValueError('nonnegative parameter and positive cap required')
    x, y, j, k = 3*u+2, 27*u+20, 0, 0
    for t in range(1, cap+1):
        j, k = j+x % 2, k+y % 2
        x, y = step(x), step(y)
        if x == y and j == k+2:
            kind = 'merge'
        elif (y == 9*x+2 and j == k and x % 3 == 2
              and (x-2)//3 < u and 3**j <= 2**t):
            kind = 'return'
        elif x <= 2 and y <= 2:
            # Equal cycle states retain their odd-count difference. Unequal
            # cycle states never meet. Neither admits y=9*x+2.
            kind = 'terminal_without_certificate'
        else:
            continue
        return dict(kind=kind, time=t)
    return dict(kind='cap', time=cap)


def search(u, depth=30, max_bridges=2, state_cap=10000):
    if u < 0 or depth < 1 or max_bridges < 0 or state_cap < 1:
        raise ValueError('invalid search limits')
    states = {(3*u+2, 1): ()}
    y, q = 27*u+20, 3
    peak = 1
    for t in range(depth+1):
        # Closure at this clock; fewer bridges dominates more bridges for
        # the same symbolic state. Every bridge strictly increases p.
        queue = list(states)
        cursor = 0
        while cursor < len(queue):
            x, p = queue[cursor]
            cursor += 1
            path = states[x, p]
            if (len(path) < max_bridges and x % 3 == 2
                    and (x-2)//3 < u and 3**(p-1) <= 2**t):
                key = (9*x+2, p+2)
                new_path = path + ((t, (x-2)//3, p-1),)
                if key not in states or len(new_path) < len(states[key]):
                    states[key] = new_path
                    queue.append(key)
                    if len(states) > state_cap:
                        return dict(kind='state_cap', parameter=u, depth=t)
        peak = max(peak, len(states))
        if (y, q) in states:
            return dict(kind='certificate', parameter=u, depth=t,
                        bridges=[dict(time=s, parameter=v, exponent=e)
                                 for s, v, e in states[y, q]],
                        endpoint=y, exponent=q, peak_states=peak)
        if t == depth:
            break
        new = {}
        for (x, p), path in states.items():
            key = step(x), p+x % 2
            if key not in new or len(path) < len(new[key]):
                new[key] = path
        states = new
        q, y = q+y % 2, step(y)
    return dict(kind='depth_limit', parameter=u, depth=depth, peak_states=peak)


def census(limit=1000, depth=30, max_bridges=2):
    rows = []
    for u in range(limit+1):
        rows.append(dict(original=classify_pair(u),
                         expanded=search(u, depth, max_bridges)))
    return dict(scope='finite census; certificates conditional on smaller transfers',
                kernel_certified_census=False, limit=limit, depth=depth,
                max_bridges=max_bridges,
                original_counts=dict(Counter(r['original']['kind'] for r in rows)),
                expanded_counts=dict(Counter(r['expanded']['kind'] for r in rows)),
                rescued_terminal=sum(r['original']['kind']=='terminal_without_certificate'
                                     and r['expanded']['kind']=='certificate' for r in rows),
                rows=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=1000)
    parser.add_argument('--depth', type=int, default=30)
    parser.add_argument('--max-bridges', type=int, default=2)
    args = parser.parse_args()
    print(json.dumps(census(args.limit, args.depth, args.max_bridges), indent=2))
