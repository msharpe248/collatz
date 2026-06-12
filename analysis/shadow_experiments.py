"""
Phase-3 experiments for the 3-adic shadow program (see Shadow.lean for
the formal layer: shadow_modEq, dcoef_add, shadow_compression).

Measures three things the theorems don't yet capture:
  (1) the TRUE shadow entropy: collisions of the word -> shadow map make
      the reachable 3-adic set thinner than the binomial-tail bound;
  (2) cross-scale structure: how prefix shadows correlate with full
      shadows (the cocycle d(w1 w2) = 3^j2 d(w1) + 2^|w1| d(w2) couples
      scales — is the joint distribution a product, or thinner?);
  (3) structured words: do near-critical Sturmian words produce shadows
      with extra structure (clustering/thinness) versus generic
      supercritical words?
"""

import math
import random
from itertools import combinations
from math import comb

LOG23 = math.log2(3)

def terras(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def realize(w):
    """The unique residue mod 2^|w| whose parity word is w (Parity.lean)."""
    k = len(w)
    M = 1 << k
    inv3 = pow(3, -1, M)
    x = 0
    for t in range(k - 1, -1, -1):
        x = (2 * x) % M if w[t] == 0 else ((2 * x - 1) * inv3) % M
    return x

def shadow_of_word(w):
    """(j, n_T mod 3^j) for the word w — independent of the realizing n."""
    n = realize(w)
    if n < 3:
        n += 1 << len(w)
    m = n
    for _ in range(len(w)):
        m = terras(m)
    j = sum(w)
    return j, m % 3 ** j

def words_with_j(T, j):
    for ones in combinations(range(T), j):
        w = [0] * T
        for i in ones:
            w[i] = 1
        yield tuple(w)

def exp1_true_entropy():
    print("== (1) true shadow entropy vs the binomial bound ==")
    print(f"{'T':>4} {'j':>4} {'words C(T,j)':>14} {'distinct shadows':>17} "
          f"{'log2/T words':>13} {'log2/T shadows':>15}")
    for T in (12, 15, 18, 21):
        j = math.ceil(T * 1 / LOG23)
        shadows = set()
        cnt = 0
        for w in words_with_j(T, j):
            shadows.add(shadow_of_word(w))
            cnt += 1
        print(f"{T:>4} {j:>4} {cnt:>14} {len(shadows):>17} "
              f"{math.log2(cnt)/T:>13.4f} {math.log2(len(shadows))/T:>15.4f}")
    print("(ambient rate = j*log2(3)/T ≈ 1.0; bound rate = H(j/T) ≈ 0.95)")

def exp2_cross_scale():
    print("\n== (2) cross-scale: prefix shadow vs full shadow ==")
    T = 9   # window halves of a 2T = 18 window
    j = math.ceil(2 * T / LOG23)
    pairs = set()
    pre = set()
    full = set()
    cnt = 0
    for w in words_with_j(2 * T, j):
        w1, w2 = w[:T], w[T:]
        s1 = shadow_of_word(w1)
        s = shadow_of_word(w)
        pairs.add((s1, s))
        pre.add(s1)
        full.add(s)
        cnt += 1
    print(f"  2T={2*T}, j={j}: words={cnt}, prefix shadows={len(pre)}, "
          f"full shadows={len(full)}")
    print(f"  joint (prefix, full) pairs: {len(pairs)} vs product bound "
          f"{len(pre)*len(full)} (ratio {len(pairs)/(len(pre)*len(full)):.3f})")
    print("  (a ratio well below 1 = scales are correlated: consistency is")
    print("   an active constraint, not a formality)")

def exp3_sturmian():
    print("\n== (3) structured words: Sturmian vs random supercritical ==")
    T = 40
    rng = random.Random(11)
    # Sturmian family: mechanical words at slopes just above critical
    stur = set()
    M = 400
    for i in range(M):
        alpha = 1 / LOG23 + 0.002 + 0.03 * i / M
        phase = rng.random()
        w = tuple(int((t + 1) * alpha + phase) - int(t * alpha + phase)
                  for t in range(T))
        stur.add((sum(w), shadow_of_word(w)[1]))
    # random words at matched densities
    rnd = set()
    for _ in range(M):
        j = math.ceil(T * (1 / LOG23 + 0.002 + 0.03 * rng.random()))
        ones = rng.sample(range(T), j)
        w = [0] * T
        for i in ones:
            w[i] = 1
        rnd.add((sum(w), shadow_of_word(tuple(w))[1]))
    print(f"  T={T}, {M} words each: Sturmian -> {len(stur)} distinct "
          f"shadows; random -> {len(rnd)} distinct")
    print("  (fewer distinct Sturmian shadows = structured words cluster")
    print("   in the 3-adic world; parity = no extra structure)")

if __name__ == "__main__":
    exp1_true_entropy()
    exp2_cross_scale()
    exp3_sturmian()
