#!/usr/bin/env python3
"""
Grid-form Krasikov–Lagarias certificates for machine verification.

The Lean framework (Krasikov50.lean, generic in k) proves, for the
1/50-grid cap sequence cap(t) = 2^(t/50)·r[t%50], the difference
inequalities

  m ≡ 5 (9):  phi(4m, t)                                 ≤ phi(m, t+100)
  m ≡ 2 (9):  phi(4m, t) + min-lifts phi((4m-2)/3, t+79)  ≤ phi(m, t+100)
  m ≡ 8 (9):  phi(4m, t) + min-lifts phi((2m-1)/3, t+129) ≤ phi(m, t+100)

(the last with the corrected offset 129 = 100 + 29, 29 < 50·log2(3/2)).
With growth rate mu = p/q per grid step (lambda = mu^50, gamma = 50 log2 mu),
a certificate is an integer vector c ≥ 1 with, for every class m ≡ 2 (3)
of modulus 3^k:

  (5)  c_m p^100            ≤ c_{4m} q^100
  (2)  c_m p^100            ≤ c_{4m} q^100 + cbar p^79 q^21
  (8)  c_m p^100 q^29       ≤ c_{4m} q^129 + cbar p^129

This is KL's LP with the exponents alpha-2 = -0.415, alpha-1 = 0.585
replaced by -21/50, +29/50.  We find c by power iteration on the monotone
map F (as in kl_exponent.py), round to integers, and CHECK EXACTLY.

Usage: kl_grid_certificate.py k p q [scale_bits]
Outputs analysis/certs/klgrid_k{k}_{p}_{q}.json + .cert (packed shards)
"""
import sys, json, math, random
import numpy as np

def build_maps(k):
    P = 3 ** k; N = 3 ** (k - 1); S = 3 ** (k - 2)
    i = np.arange(N, dtype=np.int64); m = 3 * i + 2
    i4 = ((4 * m) % P - 2) // 3
    r9 = m % 9
    A = np.where(r9 == 2)[0]; C = np.where(r9 == 8)[0]
    uA = ((4 * m[A] - 2) % P) // 3
    uC = ((2 * m[C] - 1) % P) // 3
    jA = (uA - 2) // 3; jC = (uC - 2) // 3
    return P, N, S, i4, A, C, jA, jC

def make_F(maps, mu):
    P, N, S, i4, A, C, jA, jC = maps
    q2 = mu ** (-100.0); qA = mu ** (-21.0); qC = mu ** (29.0)
    def F(c):
        out = q2 * c[i4]
        out[A] += qA * np.minimum(np.minimum(c[jA], c[jA + S]), c[jA + 2 * S])
        out[C] += qC * np.minimum(np.minimum(c[jC], c[jC + S]), c[jC + 2 * S])
        return out
    return F

def power_iterate(maps, mu, iters, c0=None):
    N = maps[1]; F = make_F(maps, mu)
    c = np.ones(N) if c0 is None else c0.copy()
    best = (-1.0, None)
    for t in range(iters):
        fc = F(c); r = (fc / c).min()
        if r > best[0]: best = (r, c.copy())
        c = fc / fc.max()
        c = np.maximum(c, 1e-300)
    return best

def exact_check(k, p, q, C):
    P, N, S, i4, A, C_, jA, jC = build_maps(k)
    p100 = p ** 100; q100 = q ** 100; p79q21 = p ** 79 * q ** 21
    q29 = q ** 29; q129 = q ** 129; p129 = p ** 129
    Cl = [int(x) for x in C]
    bad = 0
    for i in range(N):
        m = 3 * i + 2
        c4 = Cl[int(i4[i])]
        r = m % 9
        if r == 5:
            ok = Cl[i] * p100 <= c4 * q100
        elif r == 2:
            u = ((4 * m - 2) % P) // 3; j = (u - 2) // 3
            cb = min(Cl[j], Cl[j + S], Cl[j + 2 * S])
            ok = Cl[i] * p100 <= c4 * q100 + cb * p79q21
        else:
            u = ((2 * m - 1) % P) // 3; j = (u - 2) // 3
            cb = min(Cl[j], Cl[j + S], Cl[j + 2 * S])
            ok = Cl[i] * p100 * q29 <= c4 * q129 + cb * p129
        if not ok: bad += 1
    return bad

def terras(n): return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

def witnesses(k):
    """For each class m ≡ 2 (3) mod 3^k: a = m + 3^k·w reaching 8 in s steps
    (small w, short s)."""
    P = 3 ** k; N = 3 ** (k - 1)
    W = []; Sst = []
    for i in range(N):
        m = 3 * i + 2
        best = None
        for w in range(0, 400):
            a = m + P * w
            if a < 3: continue
            x = a; s = 0
            while x != 8 and s < 3000 and x > 2:
                x = terras(x); s += 1
            if x == 8 and (best is None or s < best[1]):
                best = (w, s)
                if s < 60: break
        assert best is not None, m
        W.append(best[0]); Sst.append(best[1])
    return W, Sst

def pack(vals, bits):
    c = 0
    for v in reversed(vals):
        assert 0 <= v < (1 << bits)
        c = (c << bits) | v
    return c

def main():
    k = int(sys.argv[1]); p = int(sys.argv[2]); q = int(sys.argv[3])
    scale_bits = int(sys.argv[4]) if len(sys.argv) > 4 else 24
    mu = p / q
    print(f"k={k} mu={p}/{q}={mu:.8f} lambda=mu^50={mu**50:.6f} gamma={50*math.log2(mu):.6f}")
    maps = build_maps(k); N = maps[1]
    ratio, c = power_iterate(maps, mu, iters=3000)
    print(f"power iteration: min F(c)/c = {ratio:.8f}")
    if ratio < 1.0:
        print("NOT FEASIBLE at this mu (need ratio ≥ 1); lower p/q"); sys.exit(2)
    # integer certificate: scale, floor, clamp ≥ 1
    c = c / c.max()
    C = np.floor(c * (1 << scale_bits)).astype(object)
    C = [max(int(x), 1) for x in C]
    bad = exact_check(k, p, q, C)
    print(f"exact integer check: {bad} violations of {N}")
    if bad: sys.exit(3)
    Cmax = max(C)
    print(f"Cmax = {Cmax} (bits {Cmax.bit_length()})")
    W, Sst = witnesses(k)
    print(f"witnesses: max w = {max(W)}, max steps = {max(Sst)}")
    S = 2187
    nsh = (N + S - 1) // S
    entry_bits = 32
    shards = [pack(C[j*S:(j+1)*S], entry_bits) for j in range(nsh)]
    wshards = [pack(W[j*S:(j+1)*S], 16) for j in range(nsh)]
    sshards = [pack(Sst[j*S:(j+1)*S], 16) for j in range(nsh)]
    out = {"k": k, "p": p, "q": q, "N": N, "S": S, "nsh": nsh, "entry_bits": entry_bits,
           "Cmax": Cmax, "c_root8": C[2], "shards": [str(x) for x in shards],
           "wshards": [str(x) for x in wshards], "sshards": [str(x) for x in sshards]}
    import os
    os.makedirs("analysis/certs", exist_ok=True)
    fn = f"analysis/certs/klgrid_k{k}_{p}_{q}.json"
    json.dump(out, open(fn, "w"))
    print("wrote", fn)

if __name__ == "__main__":
    sys.set_int_max_str_digits(0)
    main()
