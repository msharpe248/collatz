#!/usr/bin/env python3
"""Search certified rules after an orbit shift, retaining coefficient deficits.

Finite search evidence only. A witness excludes a least positive NeverContracts
seed conditionally; neither global rule coverage nor Collatz is asserted.
"""
import argparse
from fractions import Fraction
import heapq
import json
from pathlib import Path

from variable_count_surgery import canonical_levels


class RuleIndex:
    def __init__(self, rules):
        self.rules = rules
        self.index = {}
        for i, r in enumerate(rules):
            A = r['seed_step']
            self.index.setdefault(A, {}).setdefault(r['seed'] % A, []).append(i)

    def edges(self, n):
        for A, residues in self.index.items():
            for i in residues.get(n % A, []):
                r = self.rules[i]
                if n >= r['seed']:
                    q = (n-r['seed'])//A
                    x = r['predecessor']+r['predecessor_step']*q
                    assert 0 < x < n
                    yield x, Fraction(A, r['predecessor_step']), i


def descend(index, start, deficit, threshold, max_states=10000):
    """Exact best-deficit DAG search; descending seeds give topological order.

    C_i(start) >= 1/deficit is the conditional input. An edge of boost rho
    gives C_i(x) >= 1/max(1, deficit/rho). Only the best deficit at each seed
    is needed. A cap is reported separately from exhausting reachable nodes.
    """
    best = {start: (Fraction(deficit), [])}
    queue = [-start]
    expanded = 0
    while queue:
        if expanded >= max_states:
            return dict(status='state_limit', expanded=expanded)
        n = -heapq.heappop(queue)
        D, path = best[n]
        expanded += 1
        if n < threshold and D <= 1:
            return dict(status='certificate', predecessor=n, path=path,
                        expanded=expanded)
        for x, rho, rule_id in index.edges(n):
            newD = max(Fraction(1), D/rho)
            if x not in best:
                heapq.heappush(queue, -x)
            if x not in best or newD < best[x][0]:
                best[x] = (newD, path+[rule_id])
    return dict(status='exhausted', expanded=expanded)


def search_seed(index, n, horizon=64, max_states=10000):
    y, C = n, Fraction(1)
    capped = []
    for k in range(horizon+1):
        if C < 1:
            return dict(status='coefficient_contracted', time=k, capped_shifts=capped)
        found = descend(index, y, C, n, max_states)
        if found['status'] == 'certificate':
            return dict(seed=n, shift=k, shifted_seed=y,
                        initial_deficit=str(C), capped_shifts=capped, **found)
        if found['status'] == 'state_limit':
            capped.append(k)
        odd = y % 2
        C *= Fraction(3 if odd else 1, 2)
        y = (3*y+1)//2 if odd else y//2
    return dict(status='horizon_reached', capped_shifts=capped)


def single_rule_witness(index, n, horizon):
    y, C = n, Fraction(1)
    for _ in range(horizon+1):
        if C < 1:
            break
        if any(x < n and rho >= C for x, rho, _ in index.edges(y)):
            return True
        odd = y % 2
        C *= Fraction(3 if odd else 1, 2)
        y = (3*y+1)//2 if odd else y//2
    return False


def unresolved_seeds(depth, index):
    rows = [(0, 0, 0, True)]
    for _, rows in canonical_levels(depth):
        pass
    minima = {}
    for n, j, e, _ in rows:
        minima[j, e] = min(n, minima.get((j, e), n))
    return [n for n, j, e, nc in rows if n > 0 and nc
            and minima[j, e] == n and not list(index.edges(n))]


def run(depth=18, horizon=64, max_states=10000):
    rules = json.loads(Path(__file__).with_name('merge_progressions_results.json').read_text())['rules']
    index = RuleIndex(rules)
    seeds = sorted(unresolved_seeds(depth, index))
    counts, examples, unresolved = {}, [], []
    capped_count = 0
    for n in seeds:
        result = search_seed(index, n, horizon, max_states)
        status = result['status']
        counts[status] = counts.get(status, 0)+1
        capped_count += bool(result.get('capped_shifts'))
        if status == 'certificate':
            examples.append(result)
        else:
            unresolved.append(n)
    return dict(depth=depth, horizon=horizon, max_states_per_shift=max_states,
                input_seeds=len(seeds), counts=counts, seeds_with_capped_shifts=capped_count,
                certified_without_single_rule_witness=sum(
                    not single_rule_witness(index, c['seed'], horizon) for c in examples),
                scope='finite canonical seeds; conditional least-NC exclusions; no global coverage',
                kernel_certified=False, certificates=examples,
                unresolved_seeds=unresolved)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=18)
    parser.add_argument('--horizon', type=int, default=64)
    parser.add_argument('--max-states', type=int, default=10000)
    args = parser.parse_args()
    print(json.dumps(run(args.depth, args.horizon, args.max_states), indent=2))
