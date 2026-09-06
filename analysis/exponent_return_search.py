#!/usr/bin/env python3
"""Uniform same-clock exponent reductions for 3^k+1.

A certificate needs equal endpoints and j_lower=j_upper+d. Then the
constant affine corrections agree, and all exponents congruent modulo a
period of 3 modulo 2^t inherit the equality. This is a search, not coverage.
"""
import argparse
import json

from source_witness_search import trajectory


def period(depth):
    # A valid period, not necessarily minimal for depth one.
    return 2**max(1,depth-2)


def census(depth=12, max_drop=8):
    modulus = period(depth)
    certs = []
    missing = []
    for residue in range(modulus):
        # Pick an exponent above every tested decrement in this residue.
        k = residue+modulus*((max_drop+1+modulus-1)//modulus)
        upper = trajectory(3**k+1,depth)
        lower = {d:trajectory(3**(k-d)+1,depth) for d in range(1,max_drop+1)}
        hit = None
        for t in range(1,depth+1):
            x,j,c = upper[t]
            for d in range(1,max_drop+1):
                y,l,e = lower[d][t]
                if x==y and l==j+d:
                    assert 3**j+c == 3**l+e
                    hit = dict(residue=residue,modulus=modulus,depth=t,drop=d,
                               representative=k,upper_odds=j,lower_odds=l,
                               upper_correction=c,lower_correction=e)
                    break
            if hit:
                break
        if hit:
            certs.append(hit)
        else:
            missing.append(residue)
    return dict(scope='uniform exponent congruence rules when k>drop; no global coverage',
                kernel_certified_census=False,depth=depth,max_drop=max_drop,
                modulus=modulus,covered=len(certs),unresolved=len(missing),
                certificates=certs,unresolved_residues=missing)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth',type=int,default=12)
    parser.add_argument('--max-drop',type=int,default=8)
    args=parser.parse_args()
    if not 1<=args.depth<=14 or not 1<=args.max_drop<=32:
        parser.error('require depth 1..14 and maximum drop 1..32')
    print(json.dumps(census(args.depth,args.max_drop),indent=2))
