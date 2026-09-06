#!/usr/bin/env python3
"""Exact binary-cylinder certificates for the affine transfer problem.

Merge certificates prove transfer directly. Return certificates reduce its
parameter. Coverage counts are finite Python evidence, not universal coverage.
"""
import argparse
import json


def search(depth=18):
    rows = [(0, 2, 20, 0, 0)]
    merge_count = return_count = 0
    levels, certificates = [], []
    for t in range(1, depth+1):
        new = []
        hits = {'merge': 0, 'return': 0}
        for r, x, y, j, k in rows:
            for b in (0, 1):
                xx, yy = x+3**(j+1)*b, y+3**(k+3)*b
                jj, kk = j+xx % 2, k+yy % 2
                xx = (3*xx+1)//2 if xx % 2 else xx//2
                yy = (3*yy+1)//2 if yy % 2 else yy//2
                rr = r+2**(t-1)*b
                kind, v = None, None
                if xx == yy and jj == kk+2:
                    kind = 'merge'
                elif yy == 9*xx+2 and jj == kk and xx % 3 == 2:
                    v = (xx-2)//3
                    if v < rr and 3**jj <= 2**t:
                        kind = 'return'
                if kind:
                    hits[kind] += 1
                    certificates.append(dict(kind=kind, parameter=rr, depth=t,
                                             small_endpoint=xx, large_endpoint=yy,
                                             small_odds=jj, large_odds=kk,
                                             next_parameter=v))
                else:
                    new.append((rr, xx, yy, jj, kk))
        rows = new
        merge_count = 2*merge_count+hits['merge']
        return_count = 2*return_count+hits['return']
        assert len(rows)+merge_count+return_count == 2**t
        levels.append(dict(depth=t, new_merge=hits['merge'], new_return=hits['return'],
                           merge_covered=merge_count, return_covered=return_count,
                           unresolved=len(rows)))
    return dict(scope='all quotients on certified binary cylinders; no global coverage',
                kernel_certified_census=False, levels=levels, certificates=certificates)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=18)
    args = parser.parse_args()
    if not 1 <= args.depth <= 22:
        parser.error('depth must be between 1 and 22')
    print(json.dumps(search(args.depth), indent=2))
