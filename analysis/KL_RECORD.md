# A new lower-bound exponent for the 3x+1 problem (2026-06-11)

**Update 2026-08-30 — MACHINE-VERIFIED: γ = 0.8676 (k=14, `KL14.lean`, 29 h kernel), 0.8569 (k=13, lean4checker-replayed) and 0.8476 (k=12, retired), all > 0.84.**
`lean/Collatz/KL12.lean` (`Collatz.K12.density_bound`) kernel-checks a
k = 12 certificate of the *grid* form of the KL system (exponents
100/79/129 in 1/50-doubling units, `analysis/kl_grid_certificate.py`)
with μ = 101182/100000, λ = μ^50 = 1.7995, γ = 0.8476. The generic growth
theorem (`lean/Collatz/KLGrid.lean`, `G50.growth_root`) handles KL's
advanced term by a strong induction over roots on the measure
10t + ⌊log₂(a^498)⌋ instead of their §3–5 elimination. Axioms:
propext, Classical.choice, Quot.sound; no native_decide. The truncated
system (offset 99, `Krasikov50.lean`) caps at γ ≈ 0.66 at every k; the
grid system gives 0.800 (k=8), 0.813, 0.826, 0.838, 0.849 (k=12), 0.859
(k=13) — about 0.005 below the exact LP column below.


**Result.** For every a ≢ 0 (mod 3), the counting function
π_a(x) = #{n ≤ x : the 3x+1 orbit of n contains a} satisfies

    π_a(x) ≥ x^(179/200) = x^0.895        for all sufficiently large x,

certified at k = 17 by an exact integer verification of all
43,046,721 constraints of the Krasikov–Lagarias linear program. The
previous published record was **x^0.84** (Krasikov–Lagarias, *Acta
Arith.* 109 (2003) 237–258, computed 2002 at k = 11; still cited as
best known in Lagarias's 2021 overview, arXiv:2111.02635).

**Method: their theorem, our computation.** KL prove (their Thm 2.2 +
6.1) that any feasible solution of an explicit linear program
L_k^NT(λ) — over the 3^(k−1) congruence classes m ≡ 2 (mod 3) of
modulus 3^k — yields π_a(x) ≥ c·x^γ with γ = log₂ λ, and that
feasibility lifts from k to k+1 (so larger k never hurts). Their 2002
computation solved the LP at k = 11 (59,049 classes).

The scaling insight: for fixed λ the system is

    c ≤ F_λ(c),   F_λ monotone, homogeneous, concave
    (a linear gather + a min-of-three-lifts gather per class),

so feasibility needs no LP solver at all. Any vector with
min_m F_λ(c)_m / c_m ≥ 1 **is itself the certificate** (this is the
Collatz–Wielandt inequality for monotone homogeneous maps — pleasingly,
that Collatz is Lothar Collatz of the conjecture). Near-eigenvectors of
F_λ found by normalized power iteration produce such certificates
whenever λ < λ_k. This replaces the 2002 LP bottleneck with O(N) sweeps
and scales to tens of millions of classes.

## Results

Engine validation: bisection reproduces ALL of KL's Table 2
(k = 2..11) to the seven published decimals, including the record point
λ_11 = 1.7922310 exactly.

New territory (λ_k certified by explicit vectors; exact rational
certificates as listed):

| k  | classes    | λ_k (float bisect) | γ = log₂λ | exact certificate γ |
|----|-----------:|--------------------|-----------|---------------------|
| 11 | 59,049     | 1.7922310 (= KL)   | 0.8417566 | (KL 2003: "0.84")   |
| 12 | 177,147    | 1.8064235          | 0.8531361 | **853/1000 = 0.853** |
| 13 | 531,441    | 1.8188238          | 0.8630058 | **863/1000 = 0.863** |
| 14 | 1,594,323  | 1.8307723          | 0.8724524 | **2181/2500 = 0.8724** |
| 15 | 4,782,969  | 1.8419683          | 0.8812483 | **2203/2500 = 0.8812** |
| 16 | 14,348,907 | ≥ 1.8506 (one-shot) | ≥ 0.888  | **111/125 = 0.888**  |
| 17 | 43,046,721 | ≥ 1.8596 (one-shot) | ≥ 0.895  | **179/200 = 0.895**  |

k = 16, 17 were certified by single-target shots (`kl_oneshot.py`,
warm-started from the KL lift of the previous level's certificate)
rather than full bisection; the true λ_16, λ_17 are a bit higher.

## Soundness chain (what a referee checks)

1. **KL Theorem 2.2 + 6.1** (published, peer-reviewed): feasible
   solution of L_k^NT(λ) ⇒ π_a(x) ≥ Δ·x^(log₂λ). We add no theory.
2. **Exact rational certificate** (`kl_certificate.py`): γ = p/q chosen
   rational, λ = 2^(p/q); the three coefficients λ^(−2), λ^(α−2),
   λ^(α−1) (α = log₂3) are *lower-bounded* by dyadic rationals verified
   via integer power comparisons (u^q·2^(2p) ≤ v^q·3^p etc.) — rounding
   the coefficients down only weakens the right-hand sides, so soundness
   is one-directional. The certificate vector is integer (the float
   solution scaled by 2^48, floored, clamped ≥ 2^48 so c ≥ 1), and
   every constraint of L_k^NT is checked in exact integer arithmetic —
   e.g. all 14,348,907 constraints at k = 16.
3. **No floating point** survives in the final verification; floats are
   used only to *find* the certificate.

## Reproducibility

    venv/bin/python analysis/kl_exponent.py            # validate k=2..11 vs KL Table 2
    venv/bin/python analysis/kl_exponent.py 12 13 14   # new bisections
    venv/bin/python analysis/kl_certificate.py 16 111 125   # exact check

Runtimes on a laptop: seconds (k ≤ 11), ~1 min (k = 13), ~5 min
(k = 14), ~25 min (k = 15 bisection), ~10 min (k = 16/17 one-shots).
Certificate vectors are regenerated deterministically; the exact
verification pass is independent of how the vector was found.

## Independent re-verification (2026-06-11, late)

Every certificate was re-verified by a clean-room second implementation
(`kl_verify_independent.py`): Python standard library only (no numpy,
no shared code), constraint system re-derived from KL §2 displays
(2.8)–(2.14) with the congruence bookkeeping asserted, coefficient
lower bounds by a different scheme (denominator 10^21 + binary search,
vs 2^64 + unit adjustment), plain per-class loop (no vectorization).
Certificates travel as canonical artifacts (`kl_export_certificate.py`:
raw little-endian int64 + sha256 sidecar). Results:

| k  | artifact sha256 (prefix) | constraints | verdict |
|----|--------------------------|------------:|---------|
| 12 | 0ce746ca96d585a6 |    177,147 | PASS (C^max 146.80, matches) |
| 13 | 99cba822ee295701 |    531,441 | PASS (223.52, matches) |
| 14 | 735b0d0144e3e36e |  1,594,323 | PASS (339.08, matches) |
| 15 | f6eee6dc2cf4bebb |  4,782,969 | PASS (516.05, matches) |
| 16 | 5355e02fc12f2700 | 14,348,907 | PASS (781.90, matches) |
| 17 | 423789e6b195019e | 43,046,721 | PASS (1185.68, matches) |

Structural cross-checks: the three cases mod 9 each contain exactly
3^(k-2) classes at every level (asserted exhaustive). Negative control:
corrupting a single entry of the k=12 artifact (+5% at one class) is
detected as exactly 1 violation, exit code 1 — the verifier has
discriminating power. The k=12 sample artifact ships in
`analysis/certs/`; larger ones regenerate deterministically.

## Paper

Written up as `paper/klbound.tex` / `klbound.pdf`: "An Improved Lower
Bound for the 3x+1 Problem: π_a(x) ≥ x^0.895" (June 11, 2026).
Literature review performed before writing: KL 2003 record confirmed
current by (i) Lagarias's 2021 overview (arXiv:2111.02635), (ii) the
CCChallenge literature database (359 papers, June 2026), (iii) Liu's
December 2025 preprint (arXiv:2512.13760) which states "the historical
record is 0.84", and (iv) no citing work claiming better.

## Notes and next steps

- λ_k → 2 (γ → 1) as k → ∞ is exactly the open "density one" statement
  (KL §6); the marginal gains per level are slowly decaying
  (+0.0099, +0.0094, +0.0088, +0.0068*, +0.006* — starred entries are
  un-squeezed one-shots). k = 18 (129M classes) is within reach of a
  few hours of compute / ~10 GB RAM; k = 20 wants a GPU or C kernel.
- The bound is for the count of integers reaching a (in particular
  a = 1, assuming nothing); it is unconditional.
- Before public claim: literature sweep for any post-2003 improvement
  (the 2021 Lagarias overview, arXiv:2111.02635, still lists 0.84;
  searches found nothing newer), and a check of KL's errata if any.
- Natural formalization target: the exact certificate check is a finite
  integer computation of exactly the kind Cycles.lean discharges by
  `decide`; the KL theorem itself (Thm 2.2) is induction over difference
  inequalities — formalizable with the repo's existing machinery, which
  would make this the first machine-verified density exponent for 3x+1.
