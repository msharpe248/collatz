"""
The inverse-itinerary telescope.

The parity-vector bijection (Parity.lean), taken to the limit, says the
map {2-adic integers} -> {infinite parity words} is a bijection: every
infinite word w in {0,1}^N is the Terras parity itinerary of exactly one
x in Z_2, computable mod 2^k from the first k letters by running the two
inverse branches backward:

    w_t = 0  (even step):  x = 2y
    w_t = 1  (odd step):   x = (2y - 1)/3      (3 is invertible in Z_2)

The composed backward map after k steps is x = (2^k * unit) * seed + B,
so x mod 2^k is independent of the seed: k letters give x mod 2^k exactly.

This inverts the search for divergent orbits: instead of iterating
integers forward and watching parities, PRESCRIBE any supercritical
itinerary (periodic, Sturmian, substitutive, ...) and ask whether its
unique 2-adic realization could be a positive integer — i.e. whether its
digits are eventually all 0 (or all 1 for a negative integer). Periodic
words realize exactly the rational cycle spectrum of rational_cycles.py
(cross-checked below); aperiodic supercritical words are the candidate
divergent itineraries, and the digit tails diagnose them instantly.
"""

import math
from fractions import Fraction

LOG23 = math.log2(3)
CRIT = 1 / LOG23   # critical odd density = log2/log3 = 0.6309...

def inverse_itinerary(word, k):
    """x mod 2^k realizing the parity prefix word[0..k-1] (len(word)>=k)."""
    M = 1 << k
    inv3 = pow(3, -1, M)
    x = 0
    for t in range(k - 1, -1, -1):
        if word[t] == 0:
            x = (2 * x) % M
        else:
            x = ((2 * x - 1) * inv3) % M
    return x

def digit_tail_report(x, k, head=64):
    """Are the digits beyond `head` eventually constant (integer-like)?"""
    bits = [(x >> i) & 1 for i in range(k)]
    tail = bits[head:]
    runs_end = 1
    for b in reversed(tail[:-1]):
        if b == tail[-1]:
            runs_end += 1
        else:
            break
    longest = best = 1
    for i in range(1, len(tail)):
        best = best + 1 if tail[i] == tail[i - 1] else 1
        longest = max(longest, best)
    return sum(tail), len(tail), runs_end, longest

def sturmian(alpha, n):
    return [int((t + 1) * alpha) - int(t * alpha) for t in range(n)]

def main():
    K = 512
    print("== cross-check: periodic words recover the rational cycle spectrum ==")
    for word, expect in [((1,), Fraction(-1)), ((1, 1, 0), Fraction(-5)),
                         ((1, 1, 1, 0), Fraction(-19, 11)),
                         ((1, 1, 1, 1, 0), Fraction(-65, 49))]:
        w = (word * (K // len(word) + 1))[:K]
        x = inverse_itinerary(w, K)
        a, q = expect.numerator, expect.denominator
        ok = x == (a * pow(q, -1, 1 << K)) % (1 << K)
        print(f"  word {word} -> x = {expect}  verified mod 2^{K}: {ok}")

    print("\n== candidate divergent itineraries: is the realization an integer? ==")
    print("(positive integer <=> digits eventually all 0; negative <=> all 1)")
    print(f"{'itinerary':<38} {'density':>7} {'tail ones':>10} {'end-run':>8} {'max-run':>8}")
    cases = [
        ("Sturmian, slope log2/log3 (critical)", sturmian(CRIT, K)),
        ("Sturmian, slope 0.64", sturmian(0.64, K)),
        ("Sturmian, slope 2/3", sturmian(2 / 3 + 1e-12, K)),
        ("Sturmian, slope 0.75", sturmian(0.75, K)),
        ("blocks 1^7 0^4 with Sturmian phase", None),
    ]
    w = []
    s = sturmian(CRIT, K)
    for t in range(K):           # structured aperiodic block word
        w.append(1 if (t % 11) < 7 or s[t % len(s)] and (t % 11) == 7 else 0)
    cases[-1] = ("blocks 1^7 0^4, perturbed", w)
    for name, word in cases:
        x = inverse_itinerary(word, K)
        ones, total, endrun, maxrun = digit_tail_report(x, K)
        dens = sum(word) / len(word)
        print(f"{name:<38} {dens:7.4f} {ones:>6}/{total:<3} {endrun:>8} {maxrun:>8}")
    print(f"\n(random-digit expectation: tail ones ~ {(K-64)//2}, max-run ~ "
          f"{math.log2(K-64):.0f}; an integer needs end-run = {K-64})")

if __name__ == "__main__":
    main()
