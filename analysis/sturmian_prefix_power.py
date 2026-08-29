#!/usr/bin/env python3
"""
Sturmian itineraries vs the prefix-power criterion (2026-08-28, /adhd run 2).

Criterion (Lean: Collatz/PrefixPower.lean, `prefix_power_bound`): if the
itinerary of n is l-periodic on its first M letters and T^l(n) != n, then
    2^M <= 2^l n + 3^o (n + 2^l),   o = #ones in the first l letters,
i.e.  M - l - o*log2(3) - 1 <= log2(n+1)  (up to O(1)).

For a divergent orbit this holds at every tail position s with n -> n_s,
and log2(n_s) <= log2(n) + (j_s log2 3 - s)  (exact orbit identity).

Question: for a Sturmian word of slope alpha (ones-density) ABOVE the
critical line, does the "margin"
    m(s, l, M) := (M - l) - o*log2(3) - (j_s*log2 3 - s)
exceed every fixed bound infinitely often (over positions s and periods
l with M-letter periodicity at s)?  If yes, NO integer has that word (or
any of its shifts) as itinerary: the word is excluded at every intercept.

We test characteristic words c_alpha and a grid of intercepts rho, slopes
with golden-type tails just above 0.6309, and report the running max of
the margin as a function of prefix length.  A positive, growing margin
= exclusion; a margin stuck below a constant = the criterion fails there.
"""
import math
from fractions import Fraction

LOG23 = math.log2(3)
CRIT = math.log(2) / math.log(3)

def sturmian(alpha, rho, T):
    """Mechanical word s_n = floor((n+1)alpha + rho) - floor(n alpha + rho)."""
    return [int(math.floor((n + 1) * alpha + rho) - math.floor(n * alpha + rho)) for n in range(T)]

def cf_to_real(a):
    x = 0.0
    for q in reversed(a[1:]):
        x = 1.0 / (q + x)
    return a[0] + x

def best_margin(w, smax, lmax):
    """For each start s <= smax and period l <= lmax, find max M with
    w[s:s+M] l-periodic; return list of (margin, s, l, M)."""
    T = len(w)
    out = []
    # prefix ones counts
    J = [0]
    for x in w:
        J.append(J[-1] + x)
    for s in range(0, smax):
        shift_cost = J[s] * LOG23 - s   # log2(n_s / n) upper bound
        for l in range(1, lmax):
            # extend periodicity
            M = l
            while s + M < T and w[s + M] == w[s + M - l]:
                M += 1
            if s + M >= T:
                break  # ran out of word; unreliable
            o = J[s + l] - J[s]
            margin = (M - l) - o * LOG23 - shift_cost - 1
            out.append((margin, s, l, M))
    return out

def main():
    T = 200000
    slopes = {
        "golden tail [0;1,1,1,...] = 1/phi = 0.618 (SUBcritical control)": [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        "[0;1,1,2,1,1,1,...] golden tail, 0.6667": [0, 1, 1, 2] + [1] * 30,
        "[0;1,1,1,3,1,1,...] golden tail, 0.6316 (just above crit)": [0, 1, 1, 1, 3] + [1] * 30,
        "[0;1,1,1,2,1,1,...] golden tail, 0.6364": [0, 1, 1, 1, 2] + [1] * 30,
        "[0;1,2,2,2,...] silver, 0.7071": [0, 1] + [2] * 30,
        "[0;1,1,3,1,3,1,3,...] 0.680": [0, 1] + [1, 3] * 15,
    }
    for name, cf in slopes.items():
        alpha = cf_to_real(cf)
        print(f"\n=== slope {name}: alpha = {alpha:.5f}  (critical {CRIT:.5f}; supercritical: {alpha > CRIT})")
        for rho in [0.0, 0.25, 0.5, 0.7071, 0.9]:
            w = sturmian(alpha, rho, T)
            res = best_margin(w, smax=3000, lmax=4000)
            res.sort(reverse=True)
            top = res[:3]
            # running max over prefix length s+M to see growth
            pts = sorted(res, key=lambda r: r[1] + r[3])
            run, curve = -1e9, []
            for mg, s, l, M in pts:
                if mg > run:
                    run = mg
                    curve.append((s + M, round(mg, 1)))
            print(f"  rho={rho:<6} best margins (margin, s, l, M): {[(round(a,1),b,c,d) for a,b,c,d in top]}")
            print(f"           running max vs prefix length: {curve[-6:]}")

if __name__ == "__main__":
    main()
