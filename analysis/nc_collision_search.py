#!/usr/bin/env python3
"""Exact bounded test of equal-count collision-free NC parity prefixes.

This is a conjecture test, not a proof of injectivity at arbitrary depth.
Only surviving prefixes are stored. A conservative state cap stops before
allocating a next layer whose worst-case size exceeds the requested cap.
"""
import argparse
import json


def children(rows, depth):
    scale = 2**(depth-1)
    for r, j, e in rows:
        for b in (0, 1):
            k = j+b
            if 2**depth > 3**k:
                continue
            lift = (e % 2) ^ b
            n = r+scale*lift
            y = e+3**j*lift
            y = (3*y+1)//2 if b else y//2
            yield n, k, y


def search(max_depth=26, max_states=3_000_000):
    rows = [(0, 0, 0)]
    levels = []
    result = dict(requested_depth=max_depth, max_states=max_states,
                  completed_depth=0, status='completed', levels=levels,
                  scope='finite prefix test; no arbitrary-depth theorem',
                  kernel_certified=False)
    for t in range(1, max_depth+1):
        if 2*len(rows) > max_states:
            result['status'] = 'state_limit'
            result['unsearched_next_depth'] = t
            return result
        nxt, seen, collision = [], {}, None
        for n, j, e in children(rows, t):
            key = (j, e)
            if key in seen and collision is None:
                collision = dict(seed=n, other_seed=seen[key], odd_count=j, endpoint=e)
            seen[key] = n
            nxt.append((n, j, e))
        rows = nxt
        levels.append(dict(depth=t, noncontracting_prefixes=len(rows), collision=collision))
        result['completed_depth'] = t
        if collision is not None:
            result['status'] = 'counterexample'
            return result
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-depth', type=int, default=26)
    parser.add_argument('--max-states', type=int, default=3_000_000)
    args = parser.parse_args()
    if args.max_depth < 0 or args.max_states < 1:
        parser.error('depth must be nonnegative and state cap positive')
    print(json.dumps(search(args.max_depth, args.max_states), indent=2))
