"""
Single-target feasibility shot for the KL system at large k.

Usage:  kl_oneshot.py k gamma [warmstart_k]

Tests lambda = 2^gamma at level k, warm-starting from the saved
certificate of level warmstart_k (default k-1) via the Krasikov-Lagarias
lift (copy values to the three lifts of each class). Saves the
certificate to /tmp/kl_cert_k{k}.npy on success. Used for k = 16, 17
where full bisection is unnecessary: one certified target suffices,
since any certificate is final (kl_certificate.py makes it exact).
"""

import sys
import numpy as np
import kl_exponent as KL

def main():
    k = int(sys.argv[1])
    gamma = float(sys.argv[2])
    wk = int(sys.argv[3]) if len(sys.argv) > 3 else k - 1
    lam = 2.0 ** gamma
    maps = KL.build_maps(k)
    c0 = np.load(f"/tmp/kl_cert_k{wk}.npy")
    reps = 3 ** (k - wk)
    c0 = np.tile(c0, reps)
    ok, c, r = KL.feasible(k, maps, lam, iters=8000, c0=c0)
    print(f"k={k} lambda=2^{gamma}: ratio={r:.9f} "
          f"{'CERTIFIED' if ok else 'not certified'}")
    if ok:
        np.save(f"/tmp/kl_cert_k{k}.npy", c)

if __name__ == "__main__":
    sys.path.insert(0, "analysis")
    main()
