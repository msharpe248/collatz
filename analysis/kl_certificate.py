"""
Exact rational certification of new Krasikov-Lagarias exponents.

kl_exponent.py finds (by power iteration) float vectors c with
F_lambda(c) >= c, i.e. feasible solutions of the KL linear program
L_k^NT(lambda). This script converts such a solution into an EXACT,
independently checkable certificate:

  * gamma = p/q rational, lambda = 2^(p/q);
  * rational lower bounds for the three coefficients
        l^-2      = (1/2^2p)^(1/q)
        l^(a-2)   = (3^p/2^2p)^(1/q)      [a = log2 3]
        l^(a-1)   = (3^p/2^p)^(1/q)
    each verified by a pure integer power comparison u^q * den <= v^q * num
    (rounding coefficients DOWN only weakens the right sides, so any
    vector passing the rounded system passes the true system);
  * an integer vector C (the float certificate scaled by 2^48, floored,
    clamped to >= 2^48 so c = C/2^48 >= 1), verified against every
    constraint of L_k^NT(2^(p/q)) in exact integer arithmetic.

A passing run, combined with Krasikov-Lagarias Theorems 2.2 and 6.1
(Acta Arith. 109 (2003) 237-258), proves:

    for every a !≡ 0 (mod 3):  pi_a(x) >= x^(p/q)  for all x >= x0(a),

where pi_a(x) counts n <= x whose 3x+1 forward orbit contains a.
"""

import sys
from fractions import Fraction
import numpy as np

ALPHA = float(np.log2(3.0))
SCALE = 1 << 48

def rational_root_lower_bound(num, den, q, bits=64):
    """Largest-ish u/2^bits with (u/2^bits)^q <= num/den, verified exactly.
    Guess computed in log space (num, den may exceed float range)."""
    import math
    log2_guess = (math.log2(num) - math.log2(den)) / q
    u = int(2.0 ** (log2_guess + bits))
    v = 1 << bits
    while u ** q * den > v ** q * num:      # ensure soundness
        u -= 1
    while (u + 1) ** q * den <= v ** q * num:   # tighten
        u += 1
    assert u ** q * den <= v ** q * num
    return u, v

def build_maps_int(k):
    P = 3 ** k
    N = 3 ** (k - 1)
    S = 3 ** (k - 2)
    i = np.arange(N, dtype=np.int64)
    m = 3 * i + 2
    i4 = ((4 * m) % P - 2) // 3
    r9 = m % 9
    A = np.where(r9 == 2)[0]
    C = np.where(r9 == 8)[0]
    jA = (((4 * m[A] - 2) % P) // 3 - 2) // 3
    jC = (((2 * m[C] - 1) % P) // 3 - 2) // 3
    return N, S, i4, r9, A, C, jA, jC

def refine_at(k, lam, c0, iters=3000, demand=1.0 + 1e-9):
    """Re-run power iteration at the exact target lambda to (re)certify."""
    import kl_exponent as KL
    maps = KL.build_maps(k)
    ok, c, r = KL.feasible(k, maps, lam, iters=iters, c0=c0)
    return ok, c, r

def certify(k, p, q):
    gamma = Fraction(p, q)
    lam = 2.0 ** (p / q)
    print(f"k={k}: certifying gamma = {p}/{q} = {float(gamma):.7f} "
          f"(lambda = 2^gamma = {lam:.7f})")
    # float certificate adapted to this exact lambda
    c0 = np.load(f"/tmp/kl_cert_k{k}.npy")
    ok, c, r = refine_at(k, lam, c0)
    print(f"  float pre-check: min F(c)/c = {r:.9f} ({'ok' if ok else 'FAIL'})")
    if not ok:
        return False
    # exact rational coefficient lower bounds
    u2, v2 = rational_root_lower_bound(1, 2 ** (2 * p), q)          # l^-2
    uA, vA = rational_root_lower_bound(3 ** p, 2 ** (2 * p), q)     # l^(a-2)
    uC, vC = rational_root_lower_bound(3 ** p, 2 ** p, q)           # l^(a-1)
    print(f"  coefficient lower bounds verified by integer power comparison "
          f"(q-th powers, q={q})")
    # integer certificate vector (floored; clamped so c = C/2^48 >= 1)
    c = c / c.min()
    Cv = [max(int(x), SCALE) for x in (c * SCALE)]
    N, S, i4, r9, A, C3, jA, jC = build_maps_int(k)
    i4 = i4.tolist(); r9l = r9.tolist()
    Aset = set(A.tolist()); Cset = set(C3.tolist())
    jAl = dict(zip(A.tolist(), jA.tolist()))
    jCl = dict(zip(C3.tolist(), jC.tolist()))
    # verify every constraint exactly:
    #  (L2): Cm * v2 <= u2 * C4m
    #  (L1): Cm * v2*vA <= u2*vA * C4m + uA*v2 * Cmin
    #  (L3): Cm * v2*vC <= u2*vC * C4m + uC*v2 * Cmin
    bad = 0
    v2vA, u2vA, uAv2 = v2 * vA, u2 * vA, uA * v2
    v2vC, u2vC, uCv2 = v2 * vC, u2 * vC, uC * v2
    for i in range(N):
        Cm, C4 = Cv[i], Cv[i4[i]]
        r = r9l[i]
        if r == 5:
            okc = Cm * v2 <= u2 * C4
        elif r == 2:
            j = jAl[i]
            Cmin = min(Cv[j], Cv[j + S], Cv[j + 2 * S])
            okc = Cm * v2vA <= u2vA * C4 + uAv2 * Cmin
        else:
            j = jCl[i]
            Cmin = min(Cv[j], Cv[j + S], Cv[j + 2 * S])
            okc = Cm * v2vC <= u2vC * C4 + uCv2 * Cmin
        if not okc:
            bad += 1
    cmax = max(Cv) / SCALE
    print(f"  exact integer verification: {N - bad}/{N} constraints hold"
          f"{'' if bad == 0 else f'  ({bad} VIOLATIONS)'}")
    print(f"  c in [1, {cmax:.2f}] (C^max), all c >= 1: ok")
    if bad == 0:
        print(f"  CERTIFIED: L_{k}^NT(2^({p}/{q})) is feasible.")
        print(f"  By Krasikov-Lagarias Thm 2.2 + 6.1: pi_a(x) >= x^({p}/{q}) "
              f"= x^{float(gamma):.5f} for all a !≡ 0 mod 3, x >= x0(a).")
    return bad == 0

if __name__ == "__main__":
    k, p, q = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    sys.path.insert(0, "analysis")
    ok = certify(k, p, q)
    sys.exit(0 if ok else 1)
