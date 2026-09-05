#!/usr/bin/env python3
"""Exact initial-height certificates from repeated parity blocks.

For a hypothetical unbounded orbit with the supplied word as a prefix,
Collatz.prefix_power_initial_bound proves

  2^(M+s) <= (2^l + 3^o) * (3^j_s * n + d_s) + 3^o * 2^(l+s).

The correction d_s is essential. Each repetition gives an exact height H
such that no seed 1 <= n <= H of an unbounded orbit can have this prefix.
The displayed bit score is only log2(H+1), for plotting.

Finite continued fractions generate rational words with exact arithmetic.
They are finite experiments, not certificates that an irrational-slope word
has the same prefix at arbitrary depth. No finite run proves all-seeds or
all-intercepts exclusion.
"""
import argparse
import math
from fractions import Fraction


def sturmian(alpha, rho, length):
    """Exact for Fraction inputs; reject floats to avoid floor errors."""
    if isinstance(alpha, float) or isinstance(rho, float):
        raise TypeError("Use Fraction inputs to make floor comparisons exact")
    alpha, rho = Fraction(alpha), Fraction(rho)
    if not 0 <= alpha <= 1:
        raise ValueError("slope must lie in [0, 1]")
    return [((i + 1) * alpha + rho).__floor__() -
            (i * alpha + rho).__floor__() for i in range(length)]


def cf_to_fraction(coefficients):
    if not coefficients:
        raise ValueError("empty continued fraction")
    x = Fraction(coefficients[-1])
    for a in reversed(coefficients[:-1]):
        x = a + 1 / x
    return x


def affine_prefixes(word):
    """Odd counts J and exact corrections D for every prefix."""
    J, D = [0], [0]
    for i, b in enumerate(word):
        if b not in (0, 1):
            raise ValueError("word must be binary")
        J.append(J[-1] + b)
        D.append((3 if b else 1) * D[-1] + b * (1 << i))
    return J, D


def excluded_height(J, D, s, period, length):
    """Exact H assuming repetition and an unbounded orbit.

    The caller must verify the repetition. H=0 excludes no positive seed.
    """
    if not 0 <= s or not 1 <= period <= length or s + length >= len(J):
        raise ValueError("invalid repetition window")
    odd = J[s + period] - J[s]
    factor = (1 << period) + 3 ** odd
    coefficient = factor * 3 ** J[s]
    constant = factor * D[s] + 3 ** odd * (1 << (period + s))
    return max(0, ((1 << (length + s)) - 1 - constant) // coefficient)


def best_margin(word, smax, lmax):
    """Return (excluded height, start, period, length) certificates.

    A block reaching the word's end is still a valid finite repetition;
    no unobserved extension is assumed.
    """
    J, D = affine_prefixes(word)
    out = []
    for s in range(min(smax, len(word))):
        for period in range(1, min(lmax, len(word) - s + 1)):
            length = period
            while s + length < len(word) and word[s + length] == word[s + length - period]:
                length += 1
            height = excluded_height(J, D, s, period, length)
            if height:
                out.append((height, s, period, length))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--length", type=int, default=20000)
    parser.add_argument("--starts", type=int, default=256)
    parser.add_argument("--periods", type=int, default=512)
    args = parser.parse_args()
    if min(args.length, args.starts, args.periods) < 1:
        parser.error("all limits must be positive")
    slopes = {
        "golden (subcritical control)": [0] + [1] * 40,
        "golden tail [0;1,1,2,1,...]": [0, 1, 1, 2] + [1] * 40,
        "golden tail [0;1,1,1,3,1,...]": [0, 1, 1, 1, 3] + [1] * 40,
        "golden tail [0;1,1,1,2,1,...]": [0, 1, 1, 1, 2] + [1] * 40,
        "silver [0;1,2,2,...]": [0, 1] + [2] * 40,
        "periodic tail [0;1,1,3,1,3,...]": [0, 1] + [1, 3] * 20,
    }
    for name, cf in slopes.items():
        alpha = cf_to_fraction(cf)
        print(f"\n{name}: rational approximation {float(alpha):.9f}")
        for rho in map(Fraction, ("0", "1/4", "1/2", "7071/10000", "9/10")):
            word = sturmian(alpha, rho, args.length)
            result = sorted(best_margin(word, args.starts, args.periods), reverse=True)
            top = [(round(math.log2(h + 1), 2), s, p, m) for h, s, p, m in result[:3]]
            print(f"  rho={str(rho):>10}: (excluded-height bits, s, period, length) {top}")


if __name__ == "__main__":
    main()
