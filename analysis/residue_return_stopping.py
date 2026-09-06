#!/usr/bin/env python3
"""Exact exploratory scan of coefficient stopping at residue-two visits.

This is a finite Python experiment, not a universal convergence certificate.
Each seed is processed until its first sampled contraction or a stated cap.
"""
import argparse
import json


def first_sampled_contraction(seed, step_limit):
    value, odd_steps, visits = seed, 0, 0
    for time in range(1, step_limit + 1):
        odd_steps += value % 2
        value = (3 * value + 1) // 2 if value % 2 else value // 2
        if value % 9 == 2:
            visits += 1
            if 3**odd_steps < 2**time:
                return dict(seed=seed, endpoint=value, time=time,
                            odd_steps=odd_steps, visits=visits,
                            descends=value < seed)
    return None


def scan(seed_limit, step_limit):
    checked = 0
    censored, counterexamples = [], []
    longest = None
    for seed in range(11, seed_limit + 1, 9):
        result = first_sampled_contraction(seed, step_limit)
        if result is None:
            censored.append(seed)
            continue
        checked += 1
        if not result['descends']:
            counterexamples.append(result)
        if longest is None or result['time'] > longest['time']:
            longest = result
    return dict(scope='finite Python experiment; not a universal theorem',
                seed_limit_inclusive=seed_limit, step_limit=step_limit,
                tested_seeds=checked + len(censored), completed_seeds=checked,
                censored_seeds=censored, counterexamples=counterexamples,
                longest_first_sampled_contraction=longest)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed-limit', type=int, default=9_000_001)
    parser.add_argument('--step-limit', type=int, default=3000)
    args = parser.parse_args()
    if args.seed_limit < 11 or args.step_limit < 1:
        parser.error('seed limit must be at least 11 and step limit positive')
    print(json.dumps(scan(args.seed_limit, args.step_limit), indent=2))
