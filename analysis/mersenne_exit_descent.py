#!/usr/bin/env python3
"""Finite target descents below the original Mersenne parameter.

These are ordinary-orbit witnesses, not proofs of the affine-transfer
premises or of uniform convergence. Exact arithmetic only.
"""
import argparse
import json


def probe(h, cap=20000):
    if h < 0 or cap < 0:
        raise ValueError('require nonnegative h and cap')
    bound = 16 * 64 ** h - 1
    initial = 729 * 81 ** h - 10
    # T^d(initial) >= initial/2^d: strict descent requires 2^d > initial/bound.
    minimum_depth = (initial // bound).bit_length()
    x, odds = initial, 0
    for depth in range(cap + 1):
        if x < bound:
            return dict(h=h, kind='descent', depth=depth, odd_steps=odds,
                        necessary_minimum_depth=minimum_depth)
        if x % 2:
            x = (3*x+1)//2
            odds += 1
        else:
            x //= 2
    return dict(h=h, kind='depth_limit', depth=cap,
                necessary_minimum_depth=minimum_depth)


def report(max_h=512, cap=20000):
    if max_h < 0:
        raise ValueError('require nonnegative maximum h')
    rows = [probe(h, cap) for h in range(max_h+1)]
    return dict(scope='finite ordinary descents only; no uniform bound or transfer closure',
                kernel_certified=False, max_h=max_h, cap=cap,
                descents=sum(r['kind']=='descent' for r in rows),
                depth_limits=sum(r['kind']=='depth_limit' for r in rows),
                probes=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-h', type=int, default=512)
    parser.add_argument('--cap', type=int, default=20000)
    args = parser.parse_args()
    print(json.dumps(report(args.max_h, args.cap), indent=2))
