#!/usr/bin/env python3
"""Exact finite census of equal-time, equal-count smaller merging cylinders.

All words through the requested depth are enumerated, without sampling.
Coverage counts are finite evidence, not a universal Collatz theorem.
"""
import argparse
import json


def orbit(n, t):
    j = 0
    for _ in range(t):
        b = n % 2
        j += b
        n = (3 * n + 1) // 2 if b else n // 2
    return n, j


def census(max_depth):
    # Each row is canonical seed, odd count, correction, prefix noncontraction.
    rows = [(0, 0, 0, True)]
    results = []
    for t in range(max_depth):
        scale = 2**t
        nxt = []
        for r, j, d, nc in rows:
            end = (3**j * r + d) // scale
            for b in (0, 1):
                nr = r + scale * ((end % 2) ^ b)
                nj = j + b
                nd = (3 if b else 1) * d + scale * b
                nxt.append((nr, nj, nd, nc and 2 * scale <= 3**nj))
        rows = nxt
        depth = t + 1
        minima = {}
        for r, j, d, _ in rows:
            num = 3**j * r + d
            assert num % (2 * scale) == 0
            end = num // (2 * scale)
            # Canonical endpoint bound also holds in the Lean library.
            assert 0 <= end < 3**j
            key = (j, end)
            minima[key] = min(r, minima.get(key, r))
        covered = nc_total = nc_covered = 0
        for r, j, d, nc in rows:
            end = (3**j * r + d) // (2 * scale)
            x = minima[j, end]
            smaller = x < r
            if smaller:
                assert 0 < x
                # Independent orbit replay verifies every reported certificate.
                assert orbit(x, depth) == orbit(r, depth) == (end, j)
            covered += smaller
            nc_total += nc
            nc_covered += nc and smaller
        results.append(dict(depth=depth, words=len(rows), covered=covered,
                            noncontracting_prefixes=nc_total,
                            covered_noncontracting_prefixes=nc_covered))
    return results


def boundary_check():
    assert orbit(27, 70) == (1, 41)
    for x in range(1, 27):
        assert all(orbit(x, t) != orbit(27, t) for t in range(71))
        end, j = orbit(x, 70)
        assert end in (1, 2) and j <= 35
    # The all-time conclusion uses the cycle argument in WordSurgery.lean.
    return dict(seed=27, finite_time_bound=70, smaller_seeds_checked=26,
                endpoint=1, odd_count=41, smaller_odd_count_upper_bound=35)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-depth', type=int, default=18)
    args = parser.parse_args()
    if not 0 <= args.max_depth <= 22:
        parser.error('max-depth must be between 0 and 22 (exponential enumeration)')
    print(json.dumps(dict(scope='finite exhaustive cylinder census; not convergence',
                          census=census(args.max_depth),
                          boundary_check=boundary_check()), indent=2))
