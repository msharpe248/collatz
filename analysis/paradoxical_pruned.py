#!/usr/bin/env python3
"""Exact fixed-length prefix pruning with a proved suffix envelope.

Python implementation is tested, not Lean-extracted. An exhausted work limit
is explicitly incomplete. No result concerns all lengths.
"""
import argparse
from bisect import bisect_left
from functools import cache
import json
from pathlib import Path
from paradoxical_cylinders import step, orbit, quotient_interval


@cache
def jump_table():
    """Exact eight-step affine maps on all 256 residue classes."""
    rows = []
    for r in range(256):
        values = orbit(r, 8)
        odd = sum(n % 2 for n in values[:-1])
        rows.append((values[-1], 3**odd, odd))
    return rows


def advance(n, length):
    """Endpoint and odd count via exact residue lifts, with no rounding."""
    table = jump_table()
    odd = 0
    for _ in range(length//8):
        endpoint, coefficient, count = table[n & 255]
        n = endpoint+coefficient*(n >> 8)
        odd += count
    for _ in range(length % 8):
        odd += n % 2
        n = step(n)
    return n, odd


def completion_parameters(length, depth, odd, powers, max_odd=None):
    """Largest admissible suffix odd count; the envelope is monotone in it."""
    if max_odd is None:
        max_odd = bisect_left(powers, 1 << length) - 1
    k = min(length-depth, max_odd-odd)
    if k < 0:
        return None
    return (powers[k], (1 << (length-k))*(powers[k]-(1 << k)),
            (1 << length)-powers[odd+k])


def completion_possible(length, depth, residue, odd, correction, powers):
    modulus = 1 << depth
    minimum = residue + modulus*max(0, (3-residue+modulus-1)//modulus)
    params = completion_parameters(length, depth, odd, powers)
    return params is not None and params[0]*correction+params[1] >= params[2]*minimum


def search(length, work_limit=2_000_000, direct_limit=16, progress=None):
    if length < 1 or work_limit < 1 or direct_limit < 0:
        raise ValueError("positive length/work limit and nonnegative direct limit required")
    powers = [3**j for j in range(length+1)]
    max_odd = bisect_left(powers, 1 << length)-1
    envelopes = [[completion_parameters(length, depth, odd, powers, max_odd)
                  for odd in range(depth+1)] for depth in range(length+1)]
    stack = [(0, 0, 0, 0, 0)]  # depth, residue, endpoint, odd count, correction
    visited = pruned = leaves = checked_seeds = resolved_cylinders = 0
    segments = []
    while stack and visited < work_limit:
        depth, r, endpoint, odd, correction = stack.pop()
        visited += 1
        if progress is not None and visited % 1_000_000 == 0:
            progress({"length": length, "visited_nodes": visited,
                      "checked_seeds": checked_seeds, "pending_nodes": len(stack),
                      "segments_so_far": len(segments)})
        assert (1 << depth)*endpoint == powers[odd]*r+correction
        modulus = 1 << depth
        minimum = r + modulus*max(0, (3-r+modulus-1)//modulus)
        params = envelopes[depth][odd]
        if params is None or params[0]*correction+params[1] < params[2]*minimum:
            pruned += 1
            continue
        # Every paradoxical completion obeys this finite seed bound, not just
        # its smallest representative. Resolve a short quotient interval by
        # direct trajectories instead of expanding its entire parity tree.
        seed_upper = (params[0]*correction+params[1])//params[2]
        qlo = (minimum-r)//modulus
        qhi = (seed_upper-r)//modulus
        if depth < length and qhi-qlo+1 <= direct_limit:
            resolved_cylinders += 1
            for q in range(qlo, qhi+1):
                checked_seeds += 1
                n = r+modulus*q
                final, extra_odd = advance(endpoint+powers[odd]*q, length-depth)
                actual_odd = odd+extra_odd
                if final >= n and powers[actual_odd] < 1 << length:
                    values = orbit(n, length)
                    assert values[-1] == final
                    assert sum(x % 2 for x in values[:-1]) == actual_odd
                    segments.append({"length": length, "seed": n, "endpoint": values[-1],
                                     "odd_steps": actual_odd, "quotient": n//(1 << length),
                                     "first_descent_within_segment": next(
                                         (t for t, x in enumerate(values) if x < n), None)})
            continue
        if depth == length:
            leaves += 1
            interval = quotient_interval(depth, r, endpoint, odd)
            if interval is None:
                continue
            lo, hi = interval
            for q in range(lo, hi+1):
                n = r+(1 << depth)*q
                values = orbit(n, length)
                assert values[-1] >= n and powers[sum(x%2 for x in values[:-1])] < 1 << length
                assert values[-1] == endpoint+powers[odd]*q
                segments.append({"length": length, "seed": n, "endpoint": values[-1],
                                 "odd_steps": odd, "quotient": q,
                                 "first_descent_within_segment": next(
                                     (t for t, x in enumerate(values) if x < n), None)})
            continue
        for lift in (1, 0):
            value = endpoint+lift*powers[odd]
            bit = value % 2
            child_correction = 3*correction+(1 << depth) if bit else correction
            stack.append((depth+1, r+lift*(1 << depth), step(value), odd+bit, child_correction))
    segments.sort(key=lambda row: row["seed"])
    return {"length": length, "status": "complete" if not stack else "incomplete_work_limit",
            "visited_nodes": visited, "pruned_nodes": pruned, "surviving_leaves": leaves,
            "resolved_cylinders": resolved_cylinders, "checked_seeds": checked_seeds,
            "full_residue_count": 1 << length, "pending_nodes": len(stack),
            "segments": segments}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lengths", nargs="+", type=int, default=[8, 20, 27, 32, 40, 65])
    parser.add_argument("--work-limit", type=int, default=2_000_000)
    parser.add_argument("--direct-limit", type=int, default=16)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("paradoxical_pruned_results.json"))
    args = parser.parse_args()
    results = []
    for length in args.lengths:
        row = search(length, args.work_limit, args.direct_limit,
                     progress=lambda p: print(json.dumps({"progress": p}), flush=True))
        results.append(row)
        print(json.dumps({**{k: v for k, v in row.items() if k != "segments"},
                          "segment_count": len(row["segments"])}), flush=True)
    args.output.write_text(json.dumps({"method": "maximal admissible odd-count envelope and finite seed-interval resolution",
        "scope": "fixed lengths; Python computation with Lean-proved pruning inequality; no seed cutoff",
        "work_limit_per_length": args.work_limit, "direct_limit": args.direct_limit,
        "results": results}, indent=2)+"\n")


if __name__ == "__main__":
    main()
