"""
Export a canonical integer certificate artifact for independent verification.

Usage: kl_export_certificate.py k p q

Reproduces exactly the integer vector that kl_certificate.py verifies
(load float cert -> re-certify at lambda = 2^(p/q) -> normalize to
min = 1 -> scale by 2^48, floor, clamp at 2^48) and writes it to

    /tmp/kl_cert_k{k}_{p}_{q}.le64     (raw little-endian int64)
    /tmp/kl_cert_k{k}_{p}_{q}.json     (k, p, q, scale_bits, count, sha256)

The .le64 file IS the certificate: a self-contained list of integers.
Verifiers (the original kl_certificate.py logic and the independent
stdlib-only kl_verify_independent.py) check it against the
Krasikov-Lagarias constraint system in exact arithmetic.
"""

import hashlib
import json
import sys

import numpy as np
import kl_exponent as KL

SCALE_BITS = 48

def export(k, p, q):
    lam = 2.0 ** (p / q)
    c0 = np.load(f"/tmp/kl_cert_k{k}.npy")
    maps = KL.build_maps(k)
    ok, c, r = KL.feasible(k, maps, lam, iters=3000, c0=c0)
    assert ok, f"float certificate not reproducible at 2^({p}/{q}): ratio {r}"
    c = c / c.min()
    Cv = [max(int(x), 1 << SCALE_BITS) for x in (c * (1 << SCALE_BITS))]
    raw = b"".join(int(x).to_bytes(8, "little", signed=False) for x in Cv)
    base = f"/tmp/kl_cert_k{k}_{p}_{q}"
    with open(base + ".le64", "wb") as f:
        f.write(raw)
    meta = {"k": k, "p": p, "q": q, "scale_bits": SCALE_BITS,
            "count": len(Cv), "sha256": hashlib.sha256(raw).hexdigest()}
    with open(base + ".json", "w") as f:
        json.dump(meta, f, indent=1)
    print(f"exported {base}.le64  ({len(Cv)} entries, "
          f"sha256 {meta['sha256'][:16]}...)")

if __name__ == "__main__":
    sys.path.insert(0, "analysis")
    export(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
