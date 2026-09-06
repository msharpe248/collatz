#!/usr/bin/env python3
"""Search uniform merges after the Mersenne inverse prefix.

For k=6h+4 the reduced endpoints at clock k are X-7 and 3X-10,
where X=3**(4h+5). Only exact symbolic merges are certificates.
No global coverage or Lean certification is asserted.
"""
import argparse
import json


def signature(residue, depth):
    """Numerators a*X+b for both trajectories, denominator 2**depth.

    Residue arithmetic determines parities; symbolic coefficients prevent
    accidental equality at one representative from becoming a certificate.
    """
    x, y = residue - 7, 3 * residue - 10
    a, b, c, d = 1, -7, 3, -10
    for t in range(1, depth + 1):
        if x % 2:
            a, b = 3 * a, 3 * b + 2 ** (t - 1)
            x = (3 * x + 1) // 2
        else:
            x //= 2
        if y % 2:
            c, d = 3 * c, 3 * d + 2 ** (t - 1)
            y = (3 * y + 1) // 2
        else:
            y //= 2
        if (a, b) == (c, d):
            return dict(depth=t, coefficient=a, correction=b)
    return None


def census(depth=16):
    if not 4 <= depth <= 20:
        raise ValueError('require depth 4..20')
    modulus = 2 ** (depth - 2)
    counts = {}
    rules = {}
    for exponent in range(1, modulus, 4):
        residue = pow(3, exponent, 2 ** depth)
        hit = signature(residue, depth)
        if hit is None:
            continue
        t = hit['depth']
        counts[t] = counts.get(t, 0) + 1
        rule_modulus = 2 ** max(2, t - 2)
        key = (t, exponent % rule_modulus)
        if key not in rules:
            e = exponent % rule_modulus
            # e=4h+5, k=6h+4; choose the least admissible exponent.
            first_e = e if e >= 5 else e + rule_modulus
            first_k = 6 * ((first_e - 5) // 4) + 4
            rules[key] = dict(**hit, exponent_residue=e,
                              exponent_modulus=rule_modulus,
                              power_residue=pow(3, e, 2 ** t),
                              mersenne_k_residue=first_k,
                              mersenne_k_modulus=6 * (rule_modulus // 4))
    covered = sum(counts.values())
    return dict(scope='uniform direct exit merges only; unresolved is not impossible',
                kernel_certified=False, depth=depth, exponent_modulus=modulus,
                eligible=modulus // 4, covered=covered,
                unresolved=modulus // 4 - covered,
                covered_by_first_depth=counts,
                rules=sorted(rules.values(), key=lambda r: (r['depth'], r['exponent_residue'])))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=16)
    args = parser.parse_args()
    print(json.dumps(census(args.depth), indent=2))
