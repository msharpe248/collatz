#!/usr/bin/env python3
"""Classical Garner/LaDue exit dichotomy inside the fixed-table obstruction.

This constructs examples for both exit branches; it makes no global coverage
claim. The generic endpoint identities are proved in Collatz.OddRunMerges.
"""
import json
from pathlib import Path

from merge_chain_search import RuleIndex
from merge_rule_obstruction import TERNARY
from word_surgery import orbit


def seed(a, quotient=0, double_even=True):
    if a < 1 or quotient < 0:
        raise ValueError('positive run length and nonnegative quotient required')
    # Force n divisible by 3^11, exact v2(n+1)=a, and either exit branch.
    m3 = pow(2**a, -1, TERNARY)
    m4 = ((1 if double_even else 3)*pow(pow(3, a, 4), -1, 4)) % 4
    m = m3+TERNARY*((m4-m3)*pow(TERNARY, -1, 4) % 4)+4*TERNARY*quotient
    return 2**a*m-1, m


def check(index, a, quotient=0, double_even=True):
    n, m = seed(a, quotient, double_even)
    assert m % 2 == 1 and n % TERNARY == 0
    assert (3**a*m) % 4 == (1 if double_even else 3)
    y = n
    for k in range(max(0, a-18)+1):
        edges = list(index.edges(y))
        if a >= 18:
            if k == 0:
                assert edges == []
            else:
                assert len(edges) == 1 and edges[0][0] == previous and edges[0][2] == 0
        previous, y = y, (3*y+1)//2
    x, _ = orbit(n, a+2)
    z, _ = orbit(n-1, a+2)
    assert x == (z if double_even else 9*z+2)
    return dict(run_length=a, quotient=quotient, seed=n, odd_part=m,
                table_obstruction_horizon=a-18 if a >= 18 else None,
                branch='double_even_merge' if double_even else 'single_even_pair',
                endpoint=x, predecessor_endpoint=z, meeting_test_time=a+2)


if __name__ == '__main__':
    rules = json.loads(Path(__file__).with_name('merge_progressions_results.json').read_text())['rules']
    ix = RuleIndex(rules)
    print(json.dumps(dict(scope='constructed examples; no global coverage or novelty claim',
                         examples=[check(ix, a, double_even=b)
                                   for a in (18, 19, 32, 64) for b in (True, False)]), indent=2))
