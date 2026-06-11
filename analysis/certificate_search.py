"""
Search for a finite-state descent certificate for the Collatz conjecture,
and demonstrate why none exists.

The idea
--------
A "certificate" is a potential function V(n) = log n + phi(n mod 2^a 3^b)
that strictly decreases on every step of the Terras map

    T(n) = n/2          if n even
    T(n) = (3n+1)/2     if n odd.

If such a phi exists for ANY modulus, the Collatz conjecture follows
(every large n descends, and the base case is verified far beyond the
resulting threshold). The existence of phi is a finite, decidable
question: it is a linear program over the transition graph of residue
states, feasible iff the graph has no cycle of positive mean weight
(LP duality / Karp's algorithm).

The result
----------
The LP is infeasible at every modulus, and the blocking object is always
the same: the state n = -1 (mod 2^a), a self-loop of weight +log(3/2).
This is the shadow of the 2-adic fixed point T(-1) = -1, and it is
realized by genuine integers: n = 2^L - 1 satisfies

    T^j(2^L - 1) = 3^j * 2^(L-j) - 1     for j <= L,

rising by a factor (3/2)^L before anything else can happen. Hence no
finite-modulus (in fact no finite-memory) certificate can exist. The
formal proof is in lean/Collatz/NoGo.lean.

State-transition model
----------------------
State = (n mod 2^a, n mod 3^b). One bit of 2-adic precision is lost per
halving, so each state has TWO possible 2-adic successors (both kept:
the graph over-approximates, which is sound for worst-case
certificates). The 3-adic part is exact since 2 is invertible mod 3^b.
"""

from math import log


def build_graph(a: int, b: int):
    """Transition graph over Z/2^a x Z/3^b with log-size edge weights."""
    M2, M3 = 2 ** a, 3 ** b
    inv2 = pow(2, -1, M3) if b > 0 else 0
    LN2, LN32 = log(2), log(3 / 2)
    edges = [[] for _ in range(M2 * M3)]
    for s in range(M2 * M3):
        r2, r3 = s % M2, s // M2
        if r2 % 2 == 0:
            base2 = r2 // 2
            s3 = (r3 * inv2) % M3 if b else 0
            w = -LN2
        else:
            base2 = ((3 * r2 + 1) % M2) // 2
            s3 = (((3 * r3 + 1) % M3) * inv2) % M3 if b else 0
            w = LN32
        for lift in (base2, base2 + M2 // 2):
            edges[s].append((lift % M2 + M2 * s3, w))
    return edges


def max_mean_cycle(edges) -> float:
    """Karp's algorithm: maximum mean cycle weight of the graph."""
    M = len(edges)
    NEG = float("-inf")
    dp = [[NEG] * M for _ in range(M + 1)]
    dp[0] = [0.0] * M
    for k in range(1, M + 1):
        row, prev = dp[k], dp[k - 1]
        for u in range(M):
            du = prev[u]
            if du == NEG:
                continue
            for v, w in edges[u]:
                if du + w > row[v]:
                    row[v] = du + w
    best = NEG
    for v in range(M):
        if dp[M][v] == NEG:
            continue
        m = min(
            (dp[M][v] - dp[k][v]) / (M - k)
            for k in range(M)
            if dp[k][v] > NEG
        )
        best = max(best, m)
    return best


def demonstrate_blocking_orbit(L: int = 40) -> None:
    """Integers n = 2^L - 1 realize the positive-drift cycle for L steps."""
    n = 2 ** L - 1
    x, rises = n, 0
    while x % 2 == 1 and (3 * x + 1) // 2 > x:
        x = (3 * x + 1) // 2
        rises += 1
    assert rises == L and x == 3 ** L - 1
    print(f"n = 2^{L}-1 rises for {rises} consecutive T-steps to 3^{L}-1 "
          f"(factor ~(3/2)^{L} = {x / n:.3g}x)")


def main() -> None:
    print(__doc__)
    print(f"{'(a, b)':>8} {'states':>7} {'max mean cycle':>15}   verdict")
    for a, b in [(4, 0), (6, 1), (6, 2), (5, 3), (8, 1)]:
        edges = build_graph(a, b)
        mmc = max_mean_cycle(edges)
        verdict = "CERTIFICATE EXISTS" if mmc < 0 else "infeasible"
        print(f"{f'({a}, {b})':>8} {len(edges):>7} {mmc:>+15.6f}   {verdict}")
    print(f"\nlog(3/2) = {log(3/2):+.6f}: the blocker is always the "
          f"n = -1 (mod 2^a) self-loop.\n")
    demonstrate_blocking_orbit()


if __name__ == "__main__":
    main()
