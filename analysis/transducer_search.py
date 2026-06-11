"""
Multi-state transducer certificates: CEGIS search over 2-state weighted
digit automata.

Certificate family: A = (Q, delta, g) reading the bits of n LSB-first;
log2 V(n) = log2 n + sum g(q_i, b_i). Since log V is LINEAR in the weight
vector g, fitting g against a finite adversary pool is a piecewise-linear
min-max problem (subgradient descent); the adversary then attacks the
fitted certificate with:
  - the Mersenne family 2^L - 1 (the NoGo adversary),
  - 2-adic shadows of the positive-drift rational cycles
    (-1, -65/49, -19/11, -5, -17 from rational_cycles.py),
  - exact MINIMAL-WEIGHT strings of the automaton (dynamic programming)
    = the optimal injection seeds: lowest possible potential, which the
    dynamics then refills,
  - random + hill-climbing over bit flips.
Violators join the pool (CEGIS). Verdict per transition structure: does
any weighting survive?

1-state result (rational_cycles.py): dead across the plane. This script
asks whether one extra bit of digit memory changes anything.
"""

import math
import random
from itertools import product

LOG23 = math.log2(3)
B_WINDOW = 30          # certificate window
BITS = 96              # adversary bit length
GBOUND = 3.0           # |g| <= GBOUND per transition (log2 units)
EPS = 0.05             # required contraction margin

def terras(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2

# ---------------- automaton machinery ----------------

def counts(n, d):
    """Visit counts per transition (q,b), reading bits of n LSB-first."""
    c = [0, 0, 0, 0]   # index 2q+b
    q = 0
    while n:
        b = n & 1
        c[2 * q + b] += 1
        q = d[2 * q + b]
        n >>= 1
    return c

def logV(n, d, g):
    c = counts(n, d)
    return math.log2(n) + sum(ci * gi for ci, gi in zip(c, g))

def window_profile(n, d, B):
    """[(dlog2, dcounts) for t=1..B] — ratio_t(g) = dlog2 + dcounts . g"""
    c0, l0 = counts(n, d), math.log2(n)
    out = []
    m = n
    for _ in range(B):
        m = terras(m)
        ct = counts(m, d)
        out.append((math.log2(m) - l0, [a - b for a, b in zip(ct, c0)]))
    return out

def ratio(profile, g):
    return min(dl + sum(dc[i] * g[i] for i in range(4)) for dl, dc in profile)

# ---------------- validity floor: V must grow with n ----------------
# A descent certificate needs V >= n^delta (else contraction of V says
# nothing about descent — inverted potentials track growth instead).
# Sufficient: every cycle of the weight graph has mean weight >= -(1-delta).

FLOOR = 0.9   # mean cycle weight >= -FLOOR  (delta = 0.1)

def graph_cycles(d):
    """Simple cycles of the 2-state labeled digraph, as edge-index lists."""
    cyc = []
    for q in (0, 1):
        for b in (0, 1):
            if d[2 * q + b] == q:
                cyc.append([2 * q + b])
    for b1 in (0, 1):
        for b2 in (0, 1):
            if d[b1] == 1 and d[2 + b2] == 0:
                cyc.append([b1, 2 + b2])
    return cyc

# ---------------- weight fitting (subgradient on max-min) ----------------

def fit(profiles, d, steps=2500, seed=0):
    """Minimize H(g) = max(worst adversary ratio, worst floor violation)."""
    rng = random.Random(seed)
    cycles = graph_cycles(d)
    g = [rng.uniform(-1, 1) for _ in range(4)]
    best_g, best_f = g[:], float("inf")
    for it in range(steps):
        worst_val, grad = -float("inf"), None
        for prof in profiles:
            val, act = min(
                ((dl + sum(dc[i] * g[i] for i in range(4)), dc) for dl, dc in prof),
                key=lambda p: p[0])
            if val > worst_val:
                worst_val, grad = val, act
        for cyc in cycles:   # floor violation as competing max-term
            mean = sum(g[e] for e in cyc) / len(cyc)
            viol = -mean - FLOOR
            if viol > worst_val:
                gvec = [0.0] * 4
                for e in cyc:
                    gvec[e] = -1.0 / len(cyc)
                worst_val, grad = viol, gvec
        if worst_val < best_f:
            best_f, best_g = worst_val, g[:]
        lr = 0.5 / math.sqrt(1 + it)
        g = [max(-GBOUND, min(GBOUND, g[i] - lr * grad[i])) for i in range(4)]
    return best_g, best_f

def floor_ok(d, g):
    return all(sum(g[e] for e in c) / len(c) >= -FLOOR - 1e-9
               for c in graph_cycles(d))

# ---------------- adversaries ----------------

CYCLES = [(-1, 1), (-65, 49), (-19, 11), (-5, 1), (-17, 1)]

def shadow(a, q, L):
    return (a * pow(q, -1, 2 ** L)) % (2 ** L) or 1

def min_weight_string(d, g, L):
    """DP: the L-bit odd number of minimal automaton weight (injection seed)."""
    dp = {0: (0.0, 0, 1)}          # state -> (cost, bits-so-far, next position placeholder)
    # position 0: force bit 1 (odd)
    dp = {d[1]: (g[1], 1)}
    for pos in range(1, L - 1):
        ndp = {}
        for q, (cost, val) in dp.items():
            for b in (0, 1):
                nq, nc = d[2 * q + b], cost + g[2 * q + b]
                nv = val | (b << pos)
                if nq not in ndp or nc < ndp[nq][0]:
                    ndp[nq] = (nc, nv)
        dp = ndp
    # final position: force bit 1 (full length)
    best = None
    for q, (cost, val) in dp.items():
        nc = cost + g[2 * q + 1]
        nv = val | (1 << (L - 1))
        if best is None or nc < best[0]:
            best = (nc, nv)
    return best[1]

def attack_seeds(d, g, bits, rng, nrand):
    """Structured + random adversary seeds. INCLUDES EVEN NUMBERS:
    certificates must hold at even anchors, and shift-injections
    2^j·(2^k - 1) expose any LSB-anchored state (one halving re-aligns
    the read head and releases the stored weight at once)."""
    seeds = [2 ** (bits - 1) - 1, 2 ** bits - 1]
    seeds += [shadow(a, q, bits) for a, q in CYCLES]
    seeds += [min_weight_string(d, g, bits)]
    for j in (1, 2, 4, 8):                      # shift injections
        seeds += [(2 ** (bits - j) - 1) << j]
        seeds += [shadow(a, q, bits - j) << j for a, q in CYCLES[:2]]
    seeds += [(rng.getrandbits(bits) | (1 << (bits - 1))) for _ in range(nrand)]
    return [s for s in seeds if s >= 2]

def attack(d, g, rng, iters=1500, restarts=2):
    """Best violator found: max over seeds/hill of windowed ratio."""
    def score(n):
        return ratio(window_profile(n, d, B_WINDOW), g)
    seeds = attack_seeds(d, g, BITS, rng, 30)
    best_n = max(seeds, key=score)
    best = score(best_n)
    for _ in range(restarts):
        n, v = best_n, best
        for _ in range(iters):
            m = n ^ (1 << rng.randrange(BITS))   # any bit, parity included
            if m < 2:
                continue
            vm = score(m)
            if vm > v:
                n, v = m, vm
        if v > best:
            best, best_n = v, n
    return best, best_n

# ---------------- CEGIS per structure ----------------

def cegis(d, rng, rounds=6):
    pool = [2 ** L - 1 for L in (BITS // 2, BITS)]
    pool += [shadow(a, q, BITS) for a, q in CYCLES]
    pool += [(2 ** (BITS - j) - 1) << j for j in (1, 4)]   # shift injections
    pool += [(rng.getrandbits(BITS) | (1 << (BITS - 1))) for _ in range(10)]
    pool = [n for n in pool if n >= 2]
    history = []
    for rd in range(rounds):
        profiles = [window_profile(n, d, B_WINDOW) for n in pool]
        g, f_pool = fit(profiles, d, seed=rd)
        f_attack, adv = attack(d, g, rng)
        history.append((f_pool, f_attack))
        if f_pool <= -EPS and f_attack <= -EPS and floor_ok(d, g):
            return "CANDIDATE", g, history, adv
        pool.append(adv)
    return "dead", g, history, adv

def deep_verify(d, g, rng):
    """Heavy multi-length attack on a surviving candidate."""
    worst, worst_n, worst_bits = -float("inf"), None, None
    for bits in (64, 96, 160, 240):
        def score(n):
            return ratio(window_profile(n, d, B_WINDOW), g)
        seeds = attack_seeds(d, g, bits, rng, 60)
        n0 = max(seeds, key=score)
        for restart in range(5):
            n, v = n0, score(n0)
            for _ in range(6000):
                m = n ^ (1 << rng.randrange(bits))
                if m < 2:
                    continue
                vm = score(m)
                if vm > v:
                    n, v = m, vm
            if v > worst:
                worst, worst_n, worst_bits = v, n, bits
    return worst, worst_n, worst_bits

def main():
    rng = random.Random(2026)
    print(f"CEGIS over 2-state weighted digit automata "
          f"(B={B_WINDOW}, bits={BITS}, |g|<={GBOUND})")
    print(f"{'structure d':>14} {'verdict':>10} {'pool-fit':>9} {'attack':>8}  trajectory (pool-fit/attack per round)")
    candidates = []
    # d encoded as (d00,d01,d10,d11): next state for (q,b)
    for d in product((0, 1), repeat=4):
        verdict, g, hist, adv = cegis(list(d), rng)
        f_pool, f_attack = hist[-1]
        traj = " ".join(f"{a:+.1f}/{b:+.1f}" for a, b in hist)
        print(f"{str(d):>14} {verdict:>10} {f_pool:9.2f} {f_attack:8.2f}  {traj}")
        if verdict == "CANDIDATE":
            candidates.append((d, g, adv))
    if not candidates:
        print("\nVERDICT: every 2-state structure is dead — CEGIS converges to")
        print("violators for all weightings (with the validity floor enforced).")
        print("One bit of digit memory does not evade the injection/global-")
        print("rewrite obstructions.")
    else:
        print("\nCANDIDATES — deep verification (heavy attack, 4 bit-lengths):")
        survivors = 0
        for d, g, adv in candidates:
            worst, wn, wb = deep_verify(list(d), g, rng)
            status = "SURVIVES (!)" if worst <= -EPS else "killed"
            print(f"  d={d} g={[round(x,3) for x in g]}: "
                  f"deep-attack max ratio {worst:+.3f} at {wb} bits -> {status}")
            if worst <= -EPS:
                survivors += 1
            else:
                print(f"    violator (hex): {wn:#x}")
        if survivors == 0:
            print("\nVERDICT: all candidates die under deep attack — every valid")
            print("2-state digit-weight certificate is refuted.")

if __name__ == "__main__":
    main()
