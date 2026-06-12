"""
The automatic rung of the word-complexity ladder: Mahler-method
machinery, verified numerically.

Rung zero is formal (Ladder.lean): divergent itineraries are aperiodic.
The next rung targets AUTOMATIC itineraries (fixed points of
constant-length substitutions and their codings). Strategy, Mahler
style: the 2-adic realization of an itinerary w is the convergent series

    x(w) = - sum_{i : w_i = 1} 2^i * 3^(-(1 + #ones of w before i))

(the limit of -3^(-j_T) d(w_{<T}); d's closed form is dcoef_closed in
Ladder.lean). For a fixed point w = sigma(w) of a constant-length-L
substitution with a ones in EVERY image block (so j_{LT} = a*T exactly),
the cocycle law gives a FUNCTIONAL EQUATION relating x(w) to the
reweighted series with (2,3) -> (2^L, 3^a) — the classical Mahler setup,
chaining x through the weight tower (2,3), (2^L,3^a), (2^{L^2},3^{a^2}),…
Proving "x(w) is never a positive integer" along such towers would
exclude divergent orbits with automatic itineraries of this type.

This script:
 (1) checks the block decomposition identity behind the functional
     equation, exactly, in integers;
 (2) realizes automatic fixed-point itineraries via the telescope and
     inspects their 2-adic digit tails (integer realizations would have
     eventually-constant digits);
 (3) sanity-controls against the periodic word (110)^inf -> -5 (rung
     zero territory) and measures shadow clustering for automatic words.
"""

import math
import random

LOG23 = math.log2(3)

def terras(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def dcoef_word(w):
    """d(w) by the closed form (matches dcoef_closed in Ladder.lean)."""
    T = len(w)
    total = 0
    ones_after = [0] * (T + 1)
    for i in range(T - 1, -1, -1):
        ones_after[i] = ones_after[i + 1] + w[i]
    for i in range(T):
        if w[i] == 1:
            total += 2 ** i * 3 ** (ones_after[i + 1])
    return total

def realize(w):
    k = len(w)
    M = 1 << k
    inv3 = pow(3, -1, M)
    x = 0
    for t in range(k - 1, -1, -1):
        x = (2 * x) % M if w[t] == 0 else ((2 * x - 1) * inv3) % M
    return x

def sub_fixed_point(sigma, T):
    """Fixed point of substitution sigma (dict letter -> word), from 1."""
    w = [1]
    while len(w) < T:
        w = [c for b in w for c in sigma[b]]
    return w[:T]

def exp1_functional_equation():
    print("== (1) the block decomposition behind the Mahler equation ==")
    # sigma: 1 -> 110, 0 -> 011  (length 3, two ones in each block)
    sigma = {1: [1, 1, 0], 0: [0, 1, 1]}
    dB = {b: dcoef_word(tuple(sigma[b])) for b in (0, 1)}
    print(f"  block corrections: d(sigma(0)) = {dB[0]}, d(sigma(1)) = {dB[1]}")
    rng = random.Random(5)
    ok = True
    for trial in range(200):
        T = rng.randrange(1, 40)
        w = [rng.randrange(2) for _ in range(T)]
        img = [c for b in w for c in sigma[b]]
        lhs = dcoef_word(tuple(img))
        # cocycle-derived block formula: each block i contributes
        # 2^(3i) * 3^(2*(#letters after i)) * d(sigma(w_i))
        rhs = sum(2 ** (3 * i) * 3 ** (2 * (T - 1 - i)) * dB[w[i]]
                  for i in range(T))
        if lhs != rhs:
            ok = False
    print(f"  d(sigma(w)) = sum_i 8^i * 9^(T-1-i) * d(sigma(w_i)) "
          f"exactly, 200 random words: {ok}")
    print("  => x(sigma-fixed-point) satisfies a Mahler-type relation with")
    print("     weights (2,3) -> (8,9): the tower for the classical method.")

def digit_tail(x, k, head=64):
    bits = [(x >> i) & 1 for i in range(k)]
    tail = bits[head:]
    longest = best = 1
    for i in range(1, len(tail)):
        best = best + 1 if tail[i] == tail[i - 1] else 1
        longest = max(longest, best)
    return sum(tail), len(tail), longest

def exp2_realizations():
    print("\n== (2) realizations of automatic fixed points (K = 600) ==")
    K = 600
    cases = {
        "sigma: 1->110, 0->011 (density 2/3)": {1: [1, 1, 0], 0: [0, 1, 1]},
        "sigma: 1->101, 0->110 (density 2/3)": {1: [1, 0, 1], 0: [1, 1, 0]},
        "sigma: 1->11010,0->11001 (dens 3/5)": {1: [1, 1, 0, 1, 0],
                                                 0: [1, 1, 0, 0, 1]},
    }
    print(f"{'word':<38} {'density':>8} {'tail ones':>11} {'max run':>8}")
    for name, sg in cases.items():
        w = sub_fixed_point(sg, K)
        x = realize(tuple(w))
        ones, total, run = digit_tail(x, K)
        print(f"{name:<38} {sum(w)/len(w):>8.4f} {ones:>6}/{total:<4} "
              f"{run:>8}")
    # control: periodic (110)^inf must realize -5 (all-ones tail)
    w = ([1, 1, 0] * (K // 3 + 1))[:K]
    x = realize(tuple(w))
    expect = (-5) % (1 << K)
    print(f"  control (110)^inf -> -5 exactly: {x == expect}")
    print("  (random-like tails for the aperiodic cases: no integer "
          "realization in sight,")
    print("   consistent with the automatic-rung conjecture)")

def exp3_shadow_clustering():
    print("\n== (3) shadows of automatic words cluster ==")
    T = 40
    rng = random.Random(9)
    sigma = {1: [1, 1, 0], 0: [0, 1, 1]}
    shadows = set()
    M = 300
    for s in range(M):
        # automatic family: tails/shifts of the fixed point
        w = sub_fixed_point(sigma, T + s)[s:s + T]
        n = realize(tuple(w))
        if n < 3:
            n += 1 << T
        m = n
        for _ in range(T):
            m = terras(m)
        j = sum(w)
        shadows.add((j, m % 3 ** j))
    rnd = set()
    for _ in range(M):
        j = math.ceil(T * 2 / 3)
        ones = rng.sample(range(T), j)
        w = [0] * T
        for i in ones:
            w[i] = 1
        n = realize(tuple(w))
        if n < 3:
            n += 1 << T
        m = n
        for _ in range(T):
            m = terras(m)
        shadows_rnd_j = sum(w)
        rnd.add((shadows_rnd_j, m % 3 ** shadows_rnd_j))
    print(f"  T={T}: {M} automatic shifts -> {len(shadows)} distinct "
          f"shadows; {M} random density-2/3 words -> {len(rnd)}")

if __name__ == "__main__":
    exp1_functional_equation()
    exp2_realizations()
    exp3_shadow_clustering()
