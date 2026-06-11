"""
Positive-drift rational cycles of the Terras map — the complete adversary
spectrum for digit-weight certificates.

Every rational a/q with q odd is a 2-adic integer, and T (the Terras map)
preserves the denominator: T(a/q) = (a/2)/q or ((3a+q)/2)/q. Integers
n ≡ a/q (mod 2^L) shadow its orbit for ~L steps. So every T-cycle of
rationals with positive drift (3^j > 2^P over the cycle) is an adversary
family for ANY potential certificate: shadowing integers rise along it for
arbitrarily long stretches. The classical no-go adversary (NoGo.lean) is
the q=1 fixed point x=-1; here we enumerate the rest of the spectrum.

For a 1-state digit weight (V(n) = n * prod_bits w(b)), the weight change
per shadow step is exactly -g(parity of x_t): the constraint each cycle
imposes involves only its PARITY density j/P (supercritical by drift>0)
and its drift. The second half of the script sweeps the full 2-parameter
family V(n) = n * 2^(g1*ones(n) + g0*zeros(n)) adversarially: the
experimental feasibility map for 1-state certificates.
"""

from fractions import Fraction
import math
import random

LOG23 = math.log2(3)

def terras_frac(x: Fraction):
    if x.numerator % 2 == 0:
        return x / 2, 0
    return (3 * x + 1) / 2, 1

def find_cycles(qmax=99, arange=6, max_steps=400):
    """Enumerate T-cycles on rationals a/q, q odd <= qmax, |a| <= arange*q."""
    cycles = {}
    for q in range(1, qmax + 1, 2):
        for a0 in range(-arange * q, arange * q + 1):
            x = Fraction(a0, q)
            seen = {}
            traj = []
            for i in range(max_steps):
                if x in seen:
                    cyc = tuple(traj[seen[x]:])
                    key = min(cyc)
                    cycles[key] = cyc
                    break
                seen[x] = i
                traj.append(x)
                x, _ = terras_frac(x)
                if abs(x.numerator) > 10**6:
                    break
    return list(cycles.values())

def cycle_stats(cyc):
    P = len(cyc)
    j = sum(1 for x in cyc if x.numerator % 2 == 1)
    drift2 = (j * LOG23 - P) / P
    return P, j, drift2

def main_cycles():
    cycles = find_cycles()
    rows = []
    for cyc in cycles:
        P, j, drift2 = cycle_stats(cyc)
        rows.append((drift2, P, j, cyc[0]))
    rows.sort(reverse=True)
    print("All distinct T-cycles found (q ≤ 99), sorted by drift:")
    print(f"{'drift(log2)':>11} {'P':>4} {'j':>4} {'density':>8}  min element")
    pos = 0
    for drift2, P, j, x in rows:
        tag = " <-- POSITIVE DRIFT (adversary)" if drift2 > 0 else ""
        if drift2 > 0:
            pos += 1
        print(f"{drift2:11.4f} {P:4d} {j:4d} {j/P:8.4f}  {x}{tag}")
    print(f"\n{pos} positive-drift cycles -> certificate constraints.")
    print("Constraint per cycle (1-state weight g0,g1, junk-model):")
    print("  (j/P)*g1 + (1-j/P)*g0  >=  drift * (1 + (g0+g1)/2)")

# ---------------- adversarial sweep of the 2-parameter family --------------

def terras(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def logV(n, g0, g1):
    ones = bin(n).count("1")
    zeros = n.bit_length() - ones
    return math.log2(n) + g1 * ones + g0 * zeros

def window_ratio(n, B, g0, g1):
    base = logV(n, g0, g1)
    best = float("inf")
    m = n
    for _ in range(B):
        m = terras(m)
        best = min(best, logV(m, g0, g1) - base)
    return best

def hill(g0, g1, B, bits, iters, rng):
    n = rng.getrandbits(bits) | (1 << bits) | 1
    best, bn = window_ratio(n, B, g0, g1), n
    for _ in range(iters):
        m = (bn ^ (1 << rng.randrange(bits))) | 1
        if m < 3:
            continue
        v = window_ratio(m, B, g0, g1)
        if v > best:
            best, bn = v, m
    return best

def main_sweep():
    rng = random.Random(2026)
    B, bits = 40, 120
    print("\nAdversarial sweep of V(n) = n * 2^(g1*ones + g0*zeros), window B=40")
    print("(needs worst < 0 to be a certificate; Mersenne column = 2^L-1 check)")
    print(f"{'g0':>6} {'g1':>6} {'mersenne':>9} {'hill':>8}  verdict")
    for g0 in (-0.4, -0.2, 0.0, 0.2):
        for g1 in (0.7, 0.9, 1.17, 1.5):
            mer = max(window_ratio(2**L - 1, B, g0, g1) for L in (60, 120, 240))
            hc = max(hill(g0, g1, B, bits, 3000, rng) for _ in range(3))
            worst = max(mer, hc)
            print(f"{g0:6.2f} {g1:6.2f} {mer:9.3f} {hc:8.3f}  "
                  f"{'contracts(sofar)' if worst < 0 else 'BLOCKED'}")

if __name__ == "__main__":
    main_cycles()
    main_sweep()
