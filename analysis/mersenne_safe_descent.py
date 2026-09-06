#!/usr/bin/env python3
"""Finite exit descents to the cutoff justified by BoundedTransfer.lean."""
import json


def cutoff(u):
    if u < 1:
        raise ValueError('require positive transfer parameter')
    b, power = 0, 1
    while 3*power <= 36*u:
        b, power = b+1, 3*power
    assert power <= 36*u < 3*power
    return b


def probe(h, cap=20000):
    if h < 0 or cap < 0:
        raise ValueError('require nonnegative h and cap')
    u = 16*64**h-1
    b = cutoff(u)
    x, j = 729*81**h-10, 0
    for t in range(cap+1):
        if x < 2**b:
            return dict(h=h, kind='descent', cutoff_exponent=b, exit_depth=t, odd_steps=j)
        if x%2:
            x, j = (3*x+1)//2, j+1
        else:
            x //= 2
    return dict(h=h, kind='depth_limit', cutoff_exponent=b, exit_depth=cap)


def report():
    rows = [probe(h) for h in range(513)]
    return dict(scope='finite witnesses for a Lean-proved conditional criterion; not global coverage',
                kernel_certified_witnesses=False, max_h=512, cap=20000,
                descents=sum(r['kind']=='descent' for r in rows),
                depth_limits=sum(r['kind']=='depth_limit' for r in rows), probes=rows)


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
