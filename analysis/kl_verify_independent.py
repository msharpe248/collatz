"""
INDEPENDENT verifier for Krasikov-Lagarias certificate artifacts.

Usage: kl_verify_independent.py /tmp/kl_cert_k17_179_200.le64

Re-implements the verification of kl_certificate.py from scratch as
referee-proofing. Deliberate independence from the search/export code:

  * Python STANDARD LIBRARY ONLY (array, json, math, hashlib) — no
    numpy, no imports from the other kl_* modules;
  * the constraint system is re-derived here directly from
    Krasikov-Lagarias, Acta Arith. 109 (2003), display (2.8)-(2.14)
    [arXiv:math/0205002, Section 2], with the congruence bookkeeping
    re-done from first principles and asserted along the way;
  * coefficient lower bounds use a DIFFERENT scheme: denominator 10^21
    (vs 2^64 in the original) and a downward-adjustment loop verified
    by the integer power comparison  u^q * den <= v^q * num;
  * constraints are checked per-class in a plain loop over class
    representatives m (no vectorization, no index gymnastics shared
    with the original).

What is verified, for the artifact's (k, p, q) and lambda = 2^(p/q):

  (a) every entry C_m >= 2^scale (i.e. c_m = C_m/2^scale >= 1), and
      the vector is finite with C^max = max c;
  (b) for every m in [3^k] = {m mod 3^k : m = 2 mod 3}:
        m = 2 (mod 9):  c_m <= l^-2 c_{4m} + l^(a-2) cbar_{(4m-2)/3}
        m = 5 (mod 9):  c_m <= l^-2 c_{4m}
        m = 8 (mod 9):  c_m <= l^-2 c_{4m} + l^(a-1) cbar_{(2m-1)/3}
      where cbar_u = min over the three lifts u + j*3^(k-1), j = 0,1,2,
      all indices mod 3^k, a = log2(3) — with each coefficient REPLACED
      BY A CERTIFIED RATIONAL LOWER BOUND (sound direction: smaller
      right-hand sides only);
  (c) the case split mod 9 is exhaustive over m = 2 (mod 3), and all
      referenced classes remain = 2 (mod 3)  (asserted, not assumed).

A pass proves L_k^NT(2^(p/q)) feasible; by KL Thm 2.2 + 6.1 this gives
pi_a(x) >= x^(p/q) for every a !≡ 0 (mod 3) and x >= x0(a).
"""

import json
import math
import sys
from array import array

def root_lower_bound(num, den, q, V=10 ** 21):
    """Largest u/V with (u/V)^q <= num/den, by binary search on the
    certified integer predicate u^q * den <= V^q * num."""
    rhs = V ** q * num
    ok = lambda u: u ** q * den <= rhs
    lo, hi = 0, 2 * V          # num/den < 2^q in all our uses
    while hi - lo > 1:          # invariant: ok(lo), not ok(hi)
        mid = (lo + hi) // 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    assert ok(lo) and lo > 0
    return lo, V

def verify(path):
    meta = json.load(open(path.replace(".le64", ".json")))
    k, p, q, sb = meta["k"], meta["p"], meta["q"], meta["scale_bits"]
    P = 3 ** k          # modulus
    H = 3 ** (k - 1)    # number of classes / lift stride
    C = array("q")
    with open(path, "rb") as f:
        C.fromfile(f, meta["count"])
    assert len(C) == H, "artifact length != 3^(k-1)"

    # independent sanity of the artifact
    import hashlib
    h = hashlib.sha256(C.tobytes()).hexdigest()
    assert h == meta["sha256"], "sha256 mismatch"
    ONE = 1 << sb
    cmin = min(C)
    assert cmin >= ONE, "some c_m < 1"

    # certified rational lower bounds for the three coefficients
    u2, V2 = root_lower_bound(1, 2 ** (2 * p), q)        # lambda^-2
    uA, VA = root_lower_bound(3 ** p, 2 ** (2 * p), q)   # lambda^(alpha-2)
    uB, VB = root_lower_bound(3 ** p, 2 ** p, q)         # lambda^(alpha-1)

    # cross-multiplied integer constants (denominators identical = V)
    assert V2 == VA == VB
    V = V2
    L1_lhs, L1_t1, L1_t2 = V, u2, uA       # c_m*V <= u2*c4 + uA*cbar
    L3_lhs, L3_t1, L3_t2 = V, u2, uB

    def cls(m):
        """storage slot of class m (m = 2 mod 3), derived: m = 3*slot+2."""
        assert m % 3 == 2
        return (m - 2) // 3

    bad = 0
    checked = [0, 0, 0]
    for m in range(2, P, 3):                # all m = 2 (mod 3) in [0, P)
        cm = C[cls(m)]
        m4 = (4 * m) % P
        c4 = C[cls(m4)]                     # asserts m4 = 2 mod 3
        r = m % 9
        if r == 5:
            ok = cm * V <= u2 * c4
            checked[1] += 1
        else:
            if r == 2:
                w = (4 * m - 2) % P
                t2 = L1_t2
                checked[0] += 1
            else:
                assert r == 8, "case split mod 9 not exhaustive"
                w = (2 * m - 1) % P
                t2 = L3_t2
                checked[2] += 1
            assert w % 3 == 0
            uu = w // 3                     # class mod 3^(k-1), lift base
            cbar = min(C[cls(uu)], C[cls(uu + H)], C[cls(uu + 2 * H)])
            ok = cm * V <= u2 * c4 + t2 * cbar
        if not ok:
            bad += 1
    total = sum(checked)
    assert total == H
    print(f"k={k} gamma={p}/{q}: {total - bad}/{total} constraints verified "
          f"(cases mod 9 = {checked}), C^max = {max(C) / ONE:.2f}")
    if bad == 0:
        print(f"INDEPENDENT VERIFICATION PASSED: L_{k}^NT(2^({p}/{q})) "
              f"feasible => pi_a(x) >= x^({p}/{q}).")
    else:
        print(f"FAILED: {bad} violations.")
    return bad == 0

if __name__ == "__main__":
    sys.exit(0 if verify(sys.argv[1]) else 1)
