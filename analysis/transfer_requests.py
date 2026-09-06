#!/usr/bin/env python3
"""Exact finite requests of the classical odd-run transfer proof.

The request schema is Lean-proved. Enumeration and optimized cutoff
values below are Python calculations, not imported Lean certificates.
"""
import json


def requests(limit):
    if limit < 0:
        raise ValueError('require nonnegative seed bound')
    found = {}
    a = 2
    while 2**a <= limit:
        residue = 1 if a%2 else 3
        for m in range(residue, limit//2**a+1, 4):
            v = (3**a*m-27)//36
            n = 2**a*m-1
            assert v >= 0 and 36*v+27 == 3**a*m
            found[v] = min(found.get(v, n), n)
        a += 1
    return found


def minimum_seed(v):
    if v < 0:
        raise ValueError('require nonnegative transfer parameter')
    m, a = 4*v+3, 2
    while m%3 == 0:
        m //= 3
        a += 1
    assert 36*v+27 == 3**a*m
    return 2**a*m-1


def missing_request_cutoff(u):
    """Smallest seed whose odd-run proof can request an unavailable v>=u.

    For each a take the least admissible m, then minimize over a. All
    larger a have seed >=2**a-1, so the stopping condition is exhaustive.
    """
    if u < 1:
        raise ValueError('require a positive available-parameter cutoff')
    best = 16*u+11  # a=2,m=4u+3 requests v=u
    witness = None
    a = 2
    while 2**a-1 <= best:
        p = 3**a
        m = (36*u+27+p-1)//p
        m += ((1 if a%2 else 3)-m)%4
        n = 2**a*m-1
        if n <= best:
            best = n
            witness = dict(a=a, m=m, parameter=(p*m-27)//36)
        a += 1
    return dict(parameter_cutoff=u, seed_cutoff=best, witness=witness)


def report():
    rows = []
    for b in (8, 12, 16):
        needed = requests(2**b)
        rows.append(dict(b=b, distinct_requests=len(needed),
                         interval_instances=max(0, (3**b-27)//36+1),
                         largest_request=max(needed),
                         requests_above_seed_bound=sum(v >= 2**b for v in needed)))
    return dict(scope='finite request enumeration and optimized cutoffs; no global convergence',
                kernel_certified_computations=False, census=rows,
                cutoffs=[missing_request_cutoff(u) for u in (1, 2, 15, 60, 61, 100, 1000, 2**64-1)])


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
