#!/usr/bin/env python3
"""Test whether varying odd counts adds same-time merging coverage.

The finite residue test accounts for every nonnegative cylinder quotient,
not just a sample of lifts. See variable_count_surgery.md for its derivation.
This is an exact Python experiment, not a kernel-certified theorem.
"""
import argparse
import json


def canonical_levels(max_depth):
    # (canonical seed, odd count, endpoint, all prefix coefficients >= 1)
    rows = [(0, 0, 0, True)]
    for t in range(1, max_depth + 1):
        scale = 2 ** (t - 1)
        nxt = []
        for r, j, e, nc in rows:
            for b in (0, 1):
                lift = (e % 2) ^ b
                nr = r + scale * lift
                ne = e + 3**j * lift
                nj = j + b
                ne = (3 * ne + 1) // 2 if b else ne // 2
                nxt.append((nr, nj, ne, nc and 2**t <= 3**nj))
        rows = nxt
        yield t, rows


def compare_counts(max_depth):
    results = []
    for t, rows in canonical_levels(max_depth):
        minima = {}
        higher_images = [set() for _ in range(t + 1)]
        for r, j, e, _ in rows:
            assert 0 <= r < 2**t and 0 <= e < 3**j
            minima[j, e] = min(r, minima.get((j, e), r))
            for k in range(j):
                higher_images[k].add(e % 3**k)
        survivors = [(r, j, e) for r, j, e, nc in rows
                     if nc and minima[j, e] == r]
        lower = [(r, j, e) for r, j, e in survivors
                 if any(0 < minima.get((k, e), r) < r for k in range(j))]
        higher = [(r, j, e) for r, j, e in survivors
                  if e in higher_images[j]]
        results.append(dict(depth=t, words=len(rows),
                            noncontracting_prefixes=sum(nc for _, _, _, nc in rows),
                            not_covered_by_equal_count=len(survivors),
                            added_by_lower_count_at_quotient_zero=len(lower),
                            added_by_higher_count_for_some_lifts=len(higher),
                            first_lower_example=lower[:1],
                            first_higher_example=higher[:1]))
    return results


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-depth', type=int, default=18)
    args = parser.parse_args()
    if not 0 <= args.max_depth <= 22:
        parser.error('max-depth must be between 0 and 22')
    print(json.dumps(dict(scope='finite depth; all nonnegative cylinder quotients',
                          kernel_certified=False,
                          results=compare_counts(args.max_depth)), indent=2))
