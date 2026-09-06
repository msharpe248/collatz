#!/usr/bin/env python3
"""Finite residue certificate for an arbitrary-horizon fixed-table obstruction.

The mathematical deduction is in paper/merge_rule_obstruction.tex. Lean
checks the two rule-classification theorems; the arbitrary-horizon deduction
is a written proof, not yet a Lean theorem. No obstruction to other rules
or to seed-dependent forward horizons is asserted.
"""
import argparse
import json
from pathlib import Path

from merge_chain_search import RuleIndex

BINARY = 2**18
TERNARY = 3**11
MODULUS = BINARY*TERNARY


def residue_classes():
    result = []
    for k in range(12):
        ternary = (pow(3, k, TERNARY)*pow(pow(2, k, TERNARY), -1, TERNARY)-1) % TERNARY
        q = (ternary-(BINARY-1))*pow(BINARY, -1, TERNARY) % TERNARY
        result.append(BINARY-1+BINARY*q)
    return result


def verify_table(rules):
    classes = residue_classes()
    assert rules[0] == dict(seed=2, predecessor=1, seed_step=3,
                           predecessor_step=2, forward_time=0, inverse_time=1,
                           forward_odds=0, inverse_odds=1)
    for r in rules:
        assert MODULUS % r['seed_step'] == 0
    for k, c in enumerate(classes):
        hits = [i for i, r in enumerate(rules)
                if c % r['seed_step'] == r['seed'] % r['seed_step']]
        assert hits == ([] if k == 0 else [0])
        assert c % BINARY == BINARY-1
    return classes


def witness(horizon, quotient=0):
    if horizon < 0 or quotient < 0:
        raise ValueError('horizon and quotient must be nonnegative')
    binary = 2**(horizon+18)
    q = (-(binary-1)*pow(binary, -1, TERNARY)) % TERNARY
    return binary-1+binary*q+binary*TERNARY*quotient


def replay(rules, horizon, quotient=0):
    classes = verify_table(rules)
    index = RuleIndex(rules)
    n = witness(horizon, quotient)
    assert n % TERNARY == 0
    assert (n+1) % 2**(horizon+18) == 0
    previous, y = None, n
    for k in range(horizon+1):
        assert y % MODULUS == classes[min(k, 11)]
        edges = list(index.edges(y))
        if k == 0:
            assert edges == []
        else:
            assert len(edges) == 1
            x, rho, rule_id = edges[0]
            assert rule_id == 0 and 2*rho == 3 and x == previous
        assert y % 2 == 1
        previous, y = y, (3*y+1)//2
    return dict(horizon=horizon, quotient=quotient, seed=n,
                terminal_shifted_seed=previous,
                scope='replayed instance of the written arbitrary-horizon construction')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--horizon', type=int, default=64)
    parser.add_argument('--quotient', type=int, default=0)
    args = parser.parse_args()
    rules = json.loads(Path(__file__).with_name('merge_progressions_results.json').read_text())['rules']
    print(json.dumps(dict(modulus=MODULUS, classes=verify_table(rules),
                         example=replay(rules, args.horizon, args.quotient)), indent=2))
