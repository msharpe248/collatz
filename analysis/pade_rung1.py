#!/usr/bin/env python3
"""
Padé + Mahler-iteration test for rung 1 (2026-08-28, /adhd session).

Claim under test: irrationality of F_2(8/9) follows from a DEGREE-1
Padé form E(z) = p0(z) + p1(z) F(z), deg p_i <= m, ord_z E = N >= 2m+1,
iterated along alpha_k = (8/9)^{3^k} — the 0.946 truncation barrier of
RUNG1_ATTACK.md §4(b) being an artifact of using partial sums.

Ledger.  If F_2(8/9) = r in Q, then F_2(alpha_k) = r_k in Q by running the
functional equation F(z) = A(z) + B(z) F(z^3), A = (z+z^2)/(1-z^3),
B = 1-z^2, backwards.  Then E_k := E(alpha_k) = p0(alpha_k)+p1(alpha_k) r_k
is a NONZERO rational with
   v_2(E_k) = N*3^{k+1} + v_2(c)          (c = leading coeff of E/z^N,
                                            valid once |alpha_k|_2 < |c|_2)
   den(E_k) | 9^{m 3^k} * den(r_k),   den(r_k) ~ 9^{(5/2) 3^k},  odd.
Product formula: a nonzero rational with odd denominator D and 2-adic
valuation v has |numerator| >= 2^v, so 2^v <= D * |E_k|_inf.  Contradiction
for large k iff  3 N log2 > (m + 5/2) log 9,  i.e. N=2m+1, m >= 2.

This script (1) builds the Padé certificate exactly, (2) verifies the
valuation law against the TRUE 2-adic value (computed mod 2^M from the
series), (3) measures den(r_k) growth for the hypothetical rational r,
(4) prints the ledger margin per k.
"""
from fractions import Fraction as Fr
import math, sys

# ---------- the word and its generating function ----------
def sub_fixed_point(T):
    w = [1]
    while len(w) < T:
        w = [b for a in w for b in ((1,1,0) if a == 1 else (0,1,1))]
    return w[:T]

def check_functional_equation(w, deg=600):
    # F(z) - (1-z^2)F(z^3) == (z+z^2)/(1-z^3)  <=> coefficients of
    # (1-z^3)(F - (1-z^2)F(z^3)) equal those of z+z^2
    G = [0]*(deg+1)
    for i in range(deg+1):
        G[i] += w[i]
        if i % 3 == 0:
            G[i] -= w[i//3]
        if i >= 2 and (i-2) % 3 == 0:
            G[i] += w[(i-2)//3]
    H = [G[i] - (G[i-3] if i >= 3 else 0) for i in range(deg+1)]
    target = [0,1,1] + [0]*(deg-2)
    assert H == target, "functional equation FAILS"

# ---------- Padé certificate ----------
def pade(w, m):
    """Find p0,p1 in Z[z], deg<=m, with ord(p0 + p1 F) >= 2m+1. Returns
    (p0, p1, N, c) with N the exact order and c the leading coeff."""
    N0 = 2*m + 1
    # unknowns: p0_0..p0_m, p1_0..p1_m ; equations: coeff z^j, j < N0
    rows = []
    for j in range(N0):
        row = [0]*(2*m+2)
        if j <= m:
            row[j] = 1
        for i in range(m+1):
            if j - i >= 0:
                row[m+1+i] = w[j-i]
        rows.append(row)
    v = nullvec(rows)
    den = 1
    for x in v:
        den = math.lcm(den, x.denominator)
    v = [int(x*den) for x in v]
    g = 0
    for x in v: g = math.gcd(g, x)
    v = [x//g for x in v]
    p0, p1 = v[:m+1], v[m+1:]
    # exact order and leading coefficient
    def coeff(j):
        s = p0[j] if j <= m else 0
        for i in range(m+1):
            if j-i >= 0: s += p1[i]*w[j-i]
        return s
    j = 0
    while coeff(j) == 0:
        j += 1
        assert j < len(w) - m
    return p0, p1, j, coeff(j)

def nullvec(rows):
    """One nonzero rational vector in the nullspace of rows (exact)."""
    A = [[Fr(x) for x in r] for r in rows]
    n = len(A[0]); piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]
        A[r] = [x / A[r][c] for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f*b for a, b in zip(A[i], A[r])]
        piv.append(c); r += 1
        if r == len(A): break
    free = next(c for c in range(n) if c not in piv)
    v = [Fr(0)]*n; v[free] = Fr(1)
    for i, c in enumerate(piv):
        v[c] = -A[i][free]
    return v

def v2(x):
    x = Fr(x)
    n, d = x.numerator, x.denominator
    if n == 0: return math.inf
    v = 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v

# ---------- true 2-adic value of F at alpha_k, mod 2^M ----------
def F2_mod(w, alpha, M):
    """sum w_i alpha^i in Z_2 mod 2^M, alpha = a/b, b odd, |a|_2<1."""
    a, b = alpha.numerator, alpha.denominator
    mod = 1 << M
    binv = pow(b, -1, mod)
    s, term = 0, 1  # term = alpha^i mod 2^M
    for i, wi in enumerate(w):
        if term == 0: break
        if wi: s = (s + term) % mod
        term = (term * a % mod) * binv % mod
    return s

def evalpoly(p, z):
    return sum(Fr(c) * z**i for i, c in enumerate(p))

def main():
    T = 20000
    w = sub_fixed_point(T)
    check_functional_equation(w)
    print("functional equation verified to degree 600")
    alpha0 = Fr(8, 9)
    A = lambda z: (z + z*z) / (1 - z**3)
    B = lambda z: 1 - z*z

    for m in [2, 3, 4, 6]:
        p0, p1, N, c = pade(w, m)
        print(f"\n=== m={m}: N={N}, c={c}, v2(c)={v2(c)}")
        print("    p0 =", p0)
        print("    p1 =", p1)
        gain = 3*N*math.log(2); cost = (m + 2.5)*math.log(9)
        print(f"    ledger per 3^k: gain 3N log2 = {gain:.3f}  vs  cost (m+5/2) log9 = {cost:.3f}"
              f"  -> {'WINS' if gain > cost else 'loses'}")

        # (2) valuation law against the true 2-adic value
        # E(alpha_k) = p0(alpha_k) + p1(alpha_k) F_2(alpha_k); predicted v2 = N*3^(k+1)+v2(c)
        for k in range(0, 4):
            ak = alpha0 ** (3**k)
            M = N * 3**(k+1) + 40
            F2 = F2_mod(w, ak, M)
            mod = 1 << M
            # E mod 2^M, working with odd-denominator rationals
            def tomod(x):
                return x.numerator % mod * pow(x.denominator, -1, mod) % mod
            E = (tomod(evalpoly(p0, ak)) + tomod(evalpoly(p1, ak)) * F2) % mod
            vE = 0
            while E % 2 == 0 and vE < M: E //= 2; vE += 1
            pred = N * 3**(k+1) + v2(c)
            print(f"    k={k}: v2(E(alpha_k)) = {vE}  (predicted {pred}, |alpha_k|_2 = 2^-{3**(k+1)})")

        # (3)+(4) the height ledger for a hypothetical rational value.
        # r = F_2(8/9) = 9(n+10)/5 if x(w) = n.  Take n = 1 as a stand-in;
        # only den and size growth matter (they are n-independent in rate).
        r = Fr(9*(1+10), 5)
        rk, ak = r, alpha0
        print("    height ledger (r_k from the backward tower, n=1 stand-in):")
        for k in range(0, 6):
            Ek_den_bound = 9**(m * 3**k) * rk.denominator
            Ek_abs = abs(evalpoly(p0, ak)) + abs(evalpoly(p1, ak)) * abs(rk)
            lhs = N * 3**(k+1) + v2(c)               # v2 forced on numerator
            rhs = math.log2(Ek_den_bound) + math.log2(float(Ek_abs) + 1e-300)
            print(f"      k={k}: log2 den(r_k)={math.log2(rk.denominator):9.1f} "
                  f"(~(5/2)3^k log2 9 = {2.5*3**k*math.log2(9):8.1f}), |r_k|={float(rk):.4g}; "
                  f"need 2^v <= D|E|: v={lhs} vs log2(D|E|)={rhs:.1f} -> "
                  f"{'CONTRADICTION' if lhs > rhs else 'ok'}")
            # backward step: F(a) = A(a) + B(a) F(a^3)  =>  F(a^3) = (F(a)-A(a))/B(a)
            rk = (rk - A(ak)) / B(ak)
            ak = ak ** 3

if __name__ == "__main__":
    main()
