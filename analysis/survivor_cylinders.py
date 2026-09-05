#!/usr/bin/env python3
"""Exact height-limited survivor intervals, matching Collatz.Cylinder.

This enumerates finite heights only. Plateau measurements are observations,
not a universal bound on stopping times or proof of eventual exhaustion.
"""
import argparse
import json


def terras(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def quotient_interval(depth, residue, height):
    """All q >= 0 with 1 <= r+2^depth q <= H surviving depth steps.

    Intersect exact affine inequalities. Return inclusive (lo,hi), or None.
    """
    if depth < 0 or height < 0 or not 0 <= residue < 1 << depth:
        raise ValueError("invalid depth, residue or height")
    modulus = 1 << depth
    lo = max(0, -((residue - 1) // modulus))
    hi = (height - residue) // modulus
    endpoint, odd = residue, 0
    for i in range(depth + 1):
        coefficient = 3 ** odd * (1 << (depth - i))
        slope, rhs = coefficient - modulus, residue - endpoint
        if slope > 0:
            lo = max(lo, -((-rhs) // slope))
        elif slope < 0:
            hi = min(hi, rhs // slope)
        elif rhs > 0:
            return None
        if lo > hi:
            return None
        odd += endpoint % 2
        endpoint = terras(endpoint)
    return lo, hi


def survivor_intervals(depth, height):
    for residue in range(1 << depth):
        interval = quotient_interval(depth, residue, height)
        if interval is not None:
            yield residue, interval


def first_descent(seed, limit):
    value = seed
    for step in range(1, limit + 1):
        value = terras(value)
        if value < seed:
            return step
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=int, default=4096)
    parser.add_argument("--depth", type=int, default=12)
    parser.add_argument("--follow", type=int, default=1000)
    args = parser.parse_args()
    if args.height < 1 or args.depth < 0 or args.follow < args.depth:
        parser.error("require height >= 1, depth >= 0, follow >= depth")
    count, intervals, unresolved, records = 0, 0, [], []
    for residue, (lo, hi) in survivor_intervals(args.depth, args.height):
        intervals += 1
        count += hi - lo + 1
        for q in range(lo, hi + 1):
            seed = residue + (1 << args.depth) * q
            if seed == 1:
                continue  # 1 has no strict descent; it is the known cycle.
            stopping = first_descent(seed, args.follow)
            if stopping is None:
                unresolved.append(seed)
            else:
                records.append((stopping - args.depth, seed, stopping))
    print(json.dumps({
        "height": args.height, "depth": args.depth,
        "nonempty_cylinders": intervals, "survivor_count_including_one": count,
        "follow_limit": args.follow, "unresolved_seeds_above_one": unresolved,
        "largest_extra_depths": sorted(records, reverse=True)[:10],
    }, indent=2))


if __name__ == "__main__":
    main()
