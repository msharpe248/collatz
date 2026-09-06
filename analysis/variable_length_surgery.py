#!/usr/bin/env python3
"""Bounded exact variable-length merging search on canonical NC prefixes.

Only forward/backward lengths through depth are searched. No assertion of
universal coverage or failure at unsearched lengths is made.
"""
import argparse
import json

from variable_count_surgery import canonical_levels
from word_surgery import orbit


def scan(depth=18, include_certificates=False):
    indices = [(0, {(0, 0): 0}, {(0, 0): 0})]
    rows = [(0, 0, 0, True)]
    for s, rows in canonical_levels(depth):
        all_min, nc_min = {}, {}
        for r, k, e, nc in rows:
            key = (k, e)
            all_min[key] = min(r, all_min.get(key, r))
            if nc:
                nc_min[key] = min(r, nc_min.get(key, r))
        indices.append((s, all_min, nc_min))
    counts = dict(noncontracting_prefixes=0, equal_count_covered=0,
                  variable_length_additions=0, additions_preserving_noncontraction=0,
                  positive_forward_time_certificates=0, no_bounded_certificate=0)
    examples, missing, certificates, all_missing = [], [], [], []
    for n, j, e, nc in sorted(rows):
        if not nc or n == 0:
            continue
        counts['noncontracting_prefixes'] += 1
        # Independent replay of every selected forward-prefix hypothesis.
        assert all(2**i <= 3**orbit(n, i)[1] for i in range(depth+1))
        if indices[-1][1][j, e] < n:
            counts['equal_count_covered'] += 1
            continue
        y, jt = n, 0
        general = strong = None
        for t in range(depth+1):
            for s, all_min, nc_min in indices:
                for k in range(s+1):
                    q, f = divmod(y, 3**k)
                    for restricted, table in ((False, all_min), (True, nc_min)):
                        r = table.get((k, f))
                        if r is None:
                            continue
                        x = r + 2**s*q
                        if not 0 < x < n:
                            continue
                        cert = dict(seed=n, predecessor=x, forward_time=t,
                                    inverse_time=s, endpoint=y,
                                    forward_odds=jt, inverse_odds=k)
                        if general is None:
                            general = cert
                        if restricted and 2**s*3**jt <= 2**t*3**k:
                            strong = cert
                            break
                    if strong:
                        break
                if strong:
                    break
            if strong:
                break
            jt += y % 2
            y = (3*y+1)//2 if y % 2 else y//2
        if general:
            counts['variable_length_additions'] += 1
            c = strong or general
            x, s, t = c['predecessor'], c['inverse_time'], c['forward_time']
            assert orbit(x, s) == (c['endpoint'], c['inverse_odds'])
            assert orbit(n, t) == (c['endpoint'], c['forward_odds'])
            assert all(orbit(n, i)[0] >= n for i in range(t+1))
            if strong:
                counts['additions_preserving_noncontraction'] += 1
                if include_certificates:
                    certificates.append(strong)
                counts['positive_forward_time_certificates'] += t > 0
                assert all(2**i <= 3**orbit(x, i)[1] for i in range(s+1))
                assert 2**s*3**c['forward_odds'] <= 2**t*3**c['inverse_odds']
            if len(examples) < 16:
                examples.append(c)
        else:
            counts['no_bounded_certificate'] += 1
            if include_certificates:
                all_missing.append(n)
            if len(missing) < 20:
                missing.append(n)
    result = dict(depth=depth, seed_interval=[1, 2**depth-1],
                scope='finite seeds and bounded lengths; not universal coverage',
                kernel_certified=False, counts=counts,
                examples=examples, smallest_uncovered=missing)
    if include_certificates:
        result['certificates'] = certificates
        result['uncertified_seeds'] = all_missing
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=18)
    args = parser.parse_args()
    if not 1 <= args.depth <= 20:
        parser.error('depth must be between 1 and 20')
    print(json.dumps(scan(args.depth), indent=2))
