#!/usr/bin/env python3
"""Exact fixed-length prefix pruning with a proved suffix envelope.

Python implementation is tested, not Lean-extracted. An exhausted work limit
is explicitly incomplete. No result concerns all lengths.
"""
import argparse
import json
from pathlib import Path
from paradoxical_cylinders import step, orbit, quotient_interval


def completion_possible(length, depth, residue, odd, correction, powers):
    modulus = 1 << depth
    minimum = residue + modulus*max(0, (3-residue+modulus-1)//modulus)
    full_modulus = 1 << length
    for k in range(length-depth+1):
        coefficient = powers[odd+k]
        if coefficient >= full_modulus:
            break
        upper = powers[k]*correction + (1 << (length-k))*(powers[k]-(1 << k))
        if upper >= (full_modulus-coefficient)*minimum:
            return True
    return False


def search(length, work_limit=2_000_000):
    if length < 1 or work_limit < 1:
        raise ValueError("positive length and work limit required")
    powers = [3**j for j in range(length+1)]
    stack = [(0, 0, 0, 0, 0)]  # depth, residue, endpoint, odd count, correction
    visited = pruned = leaves = 0
    segments = []
    while stack and visited < work_limit:
        depth, r, endpoint, odd, correction = stack.pop()
        visited += 1
        assert (1 << depth)*endpoint == powers[odd]*r+correction
        if not completion_possible(length, depth, r, odd, correction, powers):
            pruned += 1
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
            "full_residue_count": 1 << length, "pending_nodes": len(stack),
            "segments": segments}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lengths", nargs="+", type=int, default=[8, 20, 27, 32, 40, 65])
    parser.add_argument("--work-limit", type=int, default=2_000_000)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("paradoxical_pruned_results.json"))
    args = parser.parse_args()
    results = []
    for length in args.lengths:
        row = search(length, args.work_limit)
        results.append(row)
        print(json.dumps({**{k: v for k, v in row.items() if k != "segments"},
                          "segment_count": len(row["segments"])}), flush=True)
    args.output.write_text(json.dumps({"method": "prefix correction envelope for each admissible suffix odd count",
        "scope": "fixed lengths; Python computation with Lean-proved pruning inequality; no seed cutoff",
        "work_limit_per_length": args.work_limit, "results": results}, indent=2)+"\n")


if __name__ == "__main__":
    main()
