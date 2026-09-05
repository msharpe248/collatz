#!/usr/bin/env python3
"""Exhaust every seed at each fixed length via exact residue cylinders.

Matches Collatz.paradoxical_quotient_interval. This Python enumerator is
cross-checked, not extracted from Lean. No claim across unbounded lengths.
"""
import argparse
import json
from pathlib import Path


def step(n):
    return n // 2 if n % 2 == 0 else (3*n+1) // 2


def orbit(seed, depth):
    values = [seed]
    for _ in range(depth):
        values.append(step(values[-1]))
    return values


def quotient_interval(depth, residue, endpoint, odd, minimum=3):
    modulus = 1 << depth
    coefficient = 3**odd
    if coefficient >= modulus or endpoint < residue:
        return None
    lo = max(0, (minimum-residue+modulus-1)//modulus)
    hi = (endpoint-residue)//(modulus-coefficient)
    return (lo, hi) if lo <= hi else None


def layers(max_depth):
    # Index r stores (T^depth(r), oddSteps depth r).
    states = [(0, 0)]
    for depth in range(1, max_depth+1):
        modulus = 1 << (depth-1)
        next_states = [None] * (2*modulus)
        powers = [3**j for j in range(depth)]
        for r, (endpoint, odd) in enumerate(states):
            for lift in (0, 1):
                value = endpoint + lift*powers[odd]
                next_states[r+lift*modulus] = (step(value), odd+value%2)
        states = next_states
        yield depth, states


def census(max_depth):
    summaries, segments = [], []
    for depth, states in layers(max_depth):
        found, cylinders, max_quotient = [], 0, 0
        for r, (endpoint, odd) in enumerate(states):
            interval = quotient_interval(depth, r, endpoint, odd)
            if interval is None:
                continue
            cylinders += 1
            lo, hi = interval
            max_quotient = max(max_quotient, hi)
            for q in range(lo, hi+1):
                seed = r + (1 << depth)*q
                values = orbit(seed, depth)
                actual_odd = sum(n % 2 for n in values[:-1])
                assert values[-1] == endpoint+3**odd*q
                assert actual_odd == odd
                assert 3**odd < 1 << depth and values[-1] >= seed
                first_descent = next((t for t, n in enumerate(values) if n < seed), None)
                found.append({"length": depth, "seed": seed, "endpoint": values[-1],
                              "odd_steps": odd, "quotient": q,
                              "first_descent_within_segment": first_descent})
        found.sort(key=lambda row: row["seed"])
        summaries.append({"length": depth, "residues_exhausted": len(states),
                          "nonempty_cylinders": cylinders, "segments": len(found),
                          "max_seed": max((r["seed"] for r in found), default=None),
                          "max_quotient": max_quotient,
                          "no_prior_descent": sum(r["first_descent_within_segment"] is None
                                                  for r in found)})
        segments.extend(found)
    return {"method": "exact contracting residue cylinders; all seeds >= 3 at each checked length",
            "max_length": max_depth, "seed_height_cutoff": None,
            "verification": "Python enumeration with direct orbit replay; underlying cylinder equivalence proved in Lean",
            "scope": "finite lengths only; no proof of global paradoxical finiteness or Collatz",
            "total_segments": len(segments), "lengths": summaries, "segments": segments}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-length", type=int, default=20)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("paradoxical_census.json"))
    args = parser.parse_args()
    if not 1 <= args.max_length <= 24:
        parser.error("choose a length between 1 and 24 (exponential residue enumeration)")
    data = census(args.max_length)
    args.output.write_text(json.dumps(data, indent=2)+"\n")
    print(json.dumps({k: v for k, v in data.items() if k != "segments"}, indent=2))


if __name__ == "__main__":
    main()
