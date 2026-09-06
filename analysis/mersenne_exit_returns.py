#!/usr/bin/env python3
"""Uniform pair returns for F(e): R(3^e-7) -> R(3^(e+1)-10).

Both sides must merge with their smaller-exponent counterpart. Clocks
may differ between sides; each equality is checked as an affine identity.
Only positive drops divisible by four preserve the Mersenne exit family.
"""
import argparse
import json
from mersenne_exit_search import signature


def path(residue, coefficient, constant, depth):
    x = coefficient * residue + constant
    a, b = coefficient, constant
    out = [(a, b)]
    for t in range(1, depth + 1):
        if x % 2:
            a, b = 3 * a, 3 * b + 2 ** (t - 1)
            x = (3 * x + 1) // 2
        else:
            x //= 2
        out.append((a, b))
    return out


def match(upper, lower, drop):
    return next((t for t, ((a, b), (c, d)) in enumerate(zip(upper, lower))
                 if (a * 3 ** drop, b) == (c, d)), None)


def census(depth=20, max_drop=16):
    if not 4 <= depth <= 20 or max_drop < 4 or max_drop % 4:
        raise ValueError('require depth 4..20 and a positive multiple-of-four maximum drop')
    modulus = 2 ** (depth - 2)
    records = []
    target_residues = source_residues = 0
    for e in range(1, modulus, 4):
        r = pow(3, e, 2 ** depth)
        upper_a, upper_b = path(r, 1, -7, depth), path(r, 3, -10, depth)
        any_source = any_target = False
        found = None
        for drop in range(4, max_drop + 1, 4):
            s = pow(3, (e - drop) % modulus, 2 ** depth)
            ta = match(upper_a, path(s, 1, -7, depth), drop)
            tb = match(upper_b, path(s, 3, -10, depth), drop)
            any_source |= ta is not None
            any_target |= tb is not None
            if found is None and ta is not None and tb is not None:
                found = dict(exponent_residue=e, exponent_modulus=modulus,
                             drop=drop, source_depth=ta, target_depth=tb,
                             direct_merge_within_bound=signature(r, depth) is not None)
        source_residues += any_source
        target_residues += any_target
        if found:
            records.append(found)
    return dict(scope='conditional F(e-drop) implies F(e), only when e-drop>=5; no global coverage',
                kernel_certified=False, depth=depth, max_drop=max_drop,
                eligible=modulus // 4, source_return_residues=source_residues,
                target_return_residues=target_residues, pair_return_residues=len(records),
                additional_to_direct_merges=sum(not r['direct_merge_within_bound'] for r in records),
                certificates=records)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=20)
    parser.add_argument('--max-drop', type=int, default=16)
    args = parser.parse_args()
    print(json.dumps(census(args.depth, args.max_drop), indent=2))
