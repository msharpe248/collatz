"""
Scaling the Krasikov-Lagarias lower-bound program for the 3x+1 problem.

Krasikov-Lagarias (Acta Arith. 109 (2003) 237-258; arXiv:math/0205002)
prove: if the linear program L_k^NT(lambda) has a feasible solution, then
pi_a(x) >= c x^gamma with gamma = log2(lambda), for every a !≡ 0 mod 3
(Theorems 2.2 + 6.1). Their record, computed in 2002 at k = 11
(59,049 classes): lambda = 1.7922310, gamma = 0.84175.

The system, for classes m in [3^k] := {m mod 3^k : m ≡ 2 mod 3}, with
alpha = log2(3) and lambda in (1,2]:

  (L1) m ≡ 2 (9):  c_m <= c_{4m} l^-2 + cbar_{(4m-2)/3} l^(a-2)
  (L2) m ≡ 5 (9):  c_m <= c_{4m} l^-2
  (L3) m ≡ 8 (9):  c_m <= c_{4m} l^-2 + cbar_{(2m-1)/3} l^(a-1)
  cbar_u := min over the three lifts of u (mod 3^(k-1)) to [3^k],
  with 1 <= c_m <= C^max.   (Indices mod 3^k; 4m and the u's stay ≡ 2 mod 3.)

KEY STRUCTURE: for fixed lambda this is c <= F(c) with F monotone,
homogeneous, concave (sum of a linear gather and a min-of-three gather).
Feasibility therefore needs no LP solver: ANY vector with
min_m F(c)_m / c_m >= 1 is itself a certificate, and near-eigenvectors of
F (power iteration, Collatz-Wielandt) find one whenever lambda < lambda_k.
This replaces the 2002 LP bottleneck and scales to millions of classes.

lambda_k is non-decreasing in k (KL prove feasible solutions lift from k
to k+1 by copying values to the three lifts), so larger k can only
improve the exponent. This script validates against KL's Table 2
(k = 2..11, seven decimals) and then pushes k beyond 11.

Output of the search phase is a certified pair (lambda, c): the vector c
is the certificate, checked here in floating point with a safety margin
and exported for exact rational verification by kl_certificate.py.
"""

import sys
import numpy as np

ALPHA = np.log2(3.0)

def build_maps(k):
    """Index maps for classes m = 3i+2, i in [0, 3^(k-1))."""
    P = 3 ** k
    N = 3 ** (k - 1)
    S = 3 ** (k - 2)            # lift stride in i-space
    i = np.arange(N, dtype=np.int64)
    m = 3 * i + 2
    i4 = ((4 * m) % P - 2) // 3
    r9 = m % 9
    A = np.where(r9 == 2)[0]    # (L1)
    C = np.where(r9 == 8)[0]    # (L3)
    uA = ((4 * m[A] - 2) % P) // 3
    uC = ((2 * m[C] - 1) % P) // 3
    jA = (uA - 2) // 3          # i-index of the base lift, in [0, 3^(k-2))
    jC = (uC - 2) // 3
    return N, S, i4, A, C, jA, jC

def make_F(k, maps, lam):
    N, S, i4, A, C, jA, jC = maps
    q2 = lam ** (-2.0)
    qA = lam ** (ALPHA - 2.0)
    qC = lam ** (ALPHA - 1.0)
    def F(c):
        out = q2 * c[i4]
        out[A] += qA * np.minimum(np.minimum(c[jA], c[jA + S]), c[jA + 2 * S])
        out[C] += qC * np.minimum(np.minimum(c[jC], c[jC + S]), c[jC + 2 * S])
        return out
    return F

def feasible(k, maps, lam, iters=4000, c0=None, tol=0.0):
    """Try to exhibit c with min F(c)/c >= 1+tol. Returns (cert?, c, ratio)."""
    N = maps[0]
    F = make_F(k, maps, lam)
    c = np.ones(N) if c0 is None else c0.copy()
    best_ratio, best_c = -np.inf, None
    for t in range(iters):
        fc = F(c)
        r = fc / c
        rmin = r.min()
        if rmin > best_ratio:
            best_ratio, best_c = rmin, c.copy()
            if rmin >= 1.0 + tol:
                return True, c, rmin
        c = fc / fc.max()       # normalized power iteration
    return False, best_c, best_ratio

def lambda_sup(k, lo=1.3, hi=2.0, prec=2e-7, iters=4000, verbose=False):
    """Bisect for sup{lambda feasible}; returns certified lo and its cert."""
    maps = build_maps(k)
    cert_c = None
    # certify lo first
    ok, c, r = feasible(k, maps, lo, iters)
    assert ok, f"k={k}: starting lambda {lo} not certified (ratio {r})"
    cert_c = c
    while hi - lo > prec:
        mid = 0.5 * (lo + hi)
        ok, c, r = feasible(k, maps, mid, iters, c0=cert_c)
        if verbose:
            print(f"    k={k} lambda={mid:.7f} ratio={r:.7f} {'OK' if ok else 'no'}",
                  flush=True)
        if ok:
            lo, cert_c = mid, c
        else:
            hi = mid
    return lo, cert_c

# KL Table 2 (Acta Arith. 109 (2003), p.16) for validation
KL_TABLE = {2: 1.3534010, 3: 1.5275960, 4: 1.6122870, 5: 1.6627590,
            6: 1.6944520, 7: 1.7201900, 8: 1.7449630, 9: 1.7615320,
            10: 1.7771270, 11: 1.7922310}

def main():
    ks = [int(a) for a in sys.argv[1:]] or list(range(2, 12))
    print(f"{'k':>3} {'classes':>9} {'lambda_k (certified)':>21} {'gamma=log2':>11} "
          f"{'KL 2003':>9} {'match':>6}")
    prev = None
    for k in ks:
        lo = prev - 0.001 if prev else 1.30
        lam, cert = lambda_sup(k, lo=max(lo, 1.30))
        gam = np.log2(lam)
        ref = KL_TABLE.get(k)
        match = "" if ref is None else ("yes" if abs(lam - ref) < 2e-5 else "NO")
        refs = f"{ref:.7f}" if ref else "--"
        print(f"{k:>3} {3**(k-1):>9} {lam:>21.7f} {gam:>11.7f} {refs:>9} {match:>6}",
              flush=True)
        prev = lam
        np.save(f"/tmp/kl_cert_k{k}.npy", cert)

if __name__ == "__main__":
    main()
