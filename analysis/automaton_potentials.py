"""
Digit-automaton potentials: a certificate family that EVADES the no-go theorem.

NoGo.lean kills every potential V(n) = n * W(n) with W bounded (finite-memory
observers). But a multiplicative weight read off ALL binary digits of n --
the simplest being W(n) = c^popcount(n) -- is NOT bounded: it ranges over
n^(log2 c) scales. The no-go theorem does not apply.

Why this family is promising: the no-go adversary n = 2^L - 1 has iterates
T^j(n) = 3^j * 2^(L-j) - 1, in binary (3^j - 1 bits)(1^(L-j)), with popcount
~ L - j/2 falling linearly. So V(n) = n * c^ones(n) CONTRACTS along the
Mersenne orbit as (3/2)^j * c^(-j/2) -- shrinking for c > 9/4 -- on exactly
the orbit that destroys every finite-state certificate.

This script measures, for the potential V(n) = n * c^ones(n):
  worst-case over n of   min_{1<=t<=B} V(T^t n) / V(n)
using random sampling plus adversarial hill-climbing over bit strings.
A certificate needs this < 1. Whatever family blocks it is the next
theorem (the analogue of how certificate_search.py motivated NoGo.lean).
"""

import random

def terras(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def ones(n: int) -> int:
    return bin(n).count("1")

def logV_ratio_window(n: int, B: int, log2c: float) -> float:
    """min over 1<=t<=B of log2(V(T^t n)/V(n)) for V(n)=n*c^ones(n)."""
    import math
    base = math.log2(n) + log2c * ones(n)
    best = float("inf")
    m = n
    for _ in range(B):
        m = terras(m)
        cur = math.log2(m) + log2c * ones(m) - base
        best = min(best, cur)
    return best

def mersenne_check(log2c: float, B: int, Ls=(50, 100, 200, 400)) -> float:
    return max(logV_ratio_window(2**L - 1, B, log2c) for L in Ls)

def hill_climb(log2c: float, B: int, bits: int, iters: int, rng) -> tuple:
    """Adversarially search for n maximizing the windowed ratio."""
    n = rng.getrandbits(bits) | (1 << bits) | 1  # odd, full length
    best = logV_ratio_window(n, B, log2c)
    best_n = n
    for _ in range(iters):
        m = best_n ^ (1 << rng.randrange(bits))  # flip a random bit
        m |= 1  # keep odd (even n trivially contract by halving)
        if m < 3:
            continue
        v = logV_ratio_window(m, B, log2c)
        if v > best:
            best, best_n = v, m
    return best, best_n

def structured_adversaries(bits: int):
    """Families with extremal bit statistics."""
    L = bits
    yield 2**L - 1                                # all ones (kills NoGo certs)
    yield 2**L + 1                                # sparse
    yield (4**(L // 2) - 1) // 3                  # 010101...01
    yield int("10" * (L // 2), 2) | 1             # 1010...11
    yield (2**L - 1) ^ (2**(L // 2))              # ones with one hole
    yield (2**(L // 2) - 1) << (L // 2) | 1       # ones then zeros then 1
    for k in (3, 5, 7):                           # blocks of ones
        block = (1 << k) - 1
        v = 0
        while v.bit_length() < L:
            v = (v << (k + 1)) | block
        yield v | 1

def main():
    import math
    rng = random.Random(2026)
    print(f"{'log2(c)':>8} {'B':>4} {'mersenne':>9} {'random':>8} {'struct':>8} {'hill':>8}  verdict")
    for log2c in (0.0, 0.5, 1.17, 1.5, 2.0):   # c = 1, 1.41, 2.25, 2.83, 4
        for B in (20, 60):
            mer = mersenne_check(log2c, B)
            rnd = max(logV_ratio_window((rng.getrandbits(96) << 1) | 1, B, log2c)
                      for _ in range(3000))
            stru = max(logV_ratio_window(n, B, log2c)
                       for n in structured_adversaries(120))
            hc, hc_n = max((hill_climb(log2c, B, 120, 4000, rng) for _ in range(4)),
                           key=lambda p: p[0])
            worst = max(mer, rnd, stru, hc)
            verdict = "CONTRACTS (so far)" if worst < 0 else "blocked"
            print(f"{log2c:8.2f} {B:4d} {mer:9.3f} {rnd:8.3f} {stru:8.3f} {hc:8.3f}  {verdict}")
            if worst >= 0 and hc >= worst:
                print(f"         blocker n = {hc_n:#x}")
                print(f"         binary: {bin(hc_n)[2:]}")

if __name__ == "__main__":
    main()
