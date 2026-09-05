#!/usr/bin/env python3
"""Explore constant-weight substitutions with an exact Padé/height screen.

Output entries are candidates, not new irrationality theorems. The script
checks finite coefficients and a strict integer growth comparison. A Lean
proof still needs infinite coefficient identities, rational-value transport,
nonvanishing and the full height ledger including finite factors.
"""
import argparse
from itertools import product
import json

from pade_rung1 import pade
from sturmian_prefix_power import affine_prefixes


def fixed_prefix(zero, one, length):
    if len(zero) != len(one) or not one or one[0] != 1:
        raise ValueError("require equal length and a prolongable one image")
    word = [1]
    while len(word) < length:
        word = [bit for symbol in word for bit in (one if symbol else zero)]
    return word[:length]


def check_equation(word, zero, one):
    """Coefficients of F = A/(1-z^L) + B F(z^L)."""
    L = len(zero)
    B = [b - a for a, b in zip(zero, one)]
    for n, value in enumerate(word):
        expected = zero[n % L] + B[n % L] * word[n // L]
        if value != expected:
            return False
    return True


def candidates(length=3, max_degree=6, prefix_length=512):
    if length < 2 or max_degree < 1 or prefix_length < 2 * max_degree + 4:
        raise ValueError("invalid search sizes")
    words = list(product((0, 1), repeat=length))
    for zero in words:
        if zero[0] != 0:
            continue  # B(0)=1 keeps the transport denominator odd.
        weight = sum(zero)
        if (1 << length) >= 3 ** weight:
            continue
        for one in words:
            if one[0] != 1 or sum(one) != weight:
                continue
            word = fixed_prefix(zero, one, prefix_length)
            assert check_equation(word, zero, one)
            B = [b - a for a, b in zip(zero, one)]
            bdegree = max(i for i, value in enumerate(B) if value)
            _, d0 = affine_prefixes(zero)
            _, d1 = affine_prefixes(one)
            certificates = []
            for degree in range(1, max_degree + 1):
                p0, p1, order, leading = pade(word, degree)
                if not leading or order == len(word):
                    continue
                # Dominant exponents after multiplying by L-1:
                # L*order > weight*log2(3)*(degree+(L+bdegree)/(L-1)).
                left = 1 << (length * order * (length - 1))
                right = 3 ** (weight * (degree * (length - 1) + length + bdegree))
                if left > right:
                    certificates.append({
                        "degree": degree, "p0": p0, "p1": p1,
                        "observed_order": order, "leading_coefficient": leading,
                        "growth_left": left, "growth_right": right,
                    })
            yield {
                "zero_image": list(zero), "one_image": list(one),
                "length": length, "weight": weight,
                "A_coefficients": list(zero), "B_coefficients": B,
                "correction_zero": d0[-1], "correction_one": d1[-1],
                "coefficients_checked": prefix_length,
                "status": "finite exact search; infinite Lean certificate not yet supplied",
                "pade_candidates": certificates,
            }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--length", type=int, default=3)
    parser.add_argument("--degree", type=int, default=6)
    args = parser.parse_args()
    print(json.dumps(list(candidates(args.length, args.degree)), indent=2))


if __name__ == "__main__":
    main()
