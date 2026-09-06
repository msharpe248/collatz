#!/usr/bin/env python3
"""Generate a finite NC correction envelope; Lean checks its inequalities."""
import argparse
import json
from pathlib import Path


def envelope(horizon):
    rows = [[0]*(horizon+1)]
    for t in range(1, horizon+1):
        row = [0]*(horizon+1)
        for j in range(t+1):
            if 2**t <= 3**j:
                row[j] = max(rows[-1][j],
                             3*rows[-1][j-1]+2**(t-1) if j else 0)
        rows.append(row)
    return rows


def lean_table(rows):
    return ('private def table : Array (Array ℕ) := #[\n'
            + ',\n'.join('  #['+', '.join(map(str, row))+']' for row in rows)
            + ']\n\n')


def verify(rows):
    H = len(rows)-1
    assert rows[0][0] == 0
    for t in range(H):
        for j in range(t+1):
            if 2**(t+1) <= 3**j:
                assert rows[t][j] <= rows[t+1][j]
            if 2**(t+1) <= 3**(j+1):
                assert 3*rows[t][j]+2**t <= rows[t+1][j+1]
    return [(t, j) for t in range(H+1) for j in range(t+1)
            if 2**t <= 3**j and rows[t][j]+2**j >= 5*3**j]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-lean-table', action='store_true')
    args = parser.parse_args()
    rows = envelope(31)
    assert verify(rows) == []
    if args.write_lean_table:
        target = Path(__file__).resolve().parents[1]/'lean/Collatz/NCPrefixInjective.lean'
        text = target.read_text()
        a = text.index('private def table :')
        b = text.index('private def bound', a)
        target.write_text(text[:a]+lean_table(rows)+text[b:])
    print(json.dumps(dict(horizon=31, table_dimensions=[32, 32],
                          first_failed_checks_at_32=verify(envelope(32)),
                          scope='envelope validation; failure does not refute injectivity'), indent=2))
