# Reciprocal orbit sums and bounded correction

Updated 2026-09-05. Formal source: `lean/Collatz/Reciprocal.lean`.

For a positive seed N, let n_t be its shortcut Collatz orbit, c_t its
normalized affine correction (`idealC t N`), and S_L = sum_{t<L} 1/n_t.
Lean now proves the exact equivalence

    Supercritical N ↔ Summable (orbitReciprocal N).

`Supercritical` means that c_t is bounded above. It does not include a
strict density-gap assumption. This is a characterization, not an exclusion.

## Finite proof mechanism

The existing affine identity yields 2^t/3^j_t = (N+c_t)/n_t.
On an odd step the correction increment is (N+c_t)/(3n_t); on an even
step it is zero and the reciprocal orbit value doubles. Consequently:

    N*S_L ≤ 6*c_L + N*(1/n_L - 1/N)
    N+c_L ≤ N*exp(S_L).

The first inequality follows by summing a one-step inequality whose endpoint
terms telescope. The second follows by multiplying the bounds
N+c_(t+1) ≤ (N+c_t)*(1+1/n_t) and using 1+x ≤ exp(x).

If c_t ≤ B, the first inequality bounds S_L by 6B/N+1. If the reciprocal
series sums to S, the second bounds every c_L by N*exp(S). Nonnegative-series
convergence proves both directions. The constants are not claimed optimal.

The module also proves `supercritical_orbit_tendsto_atTop`: bounded correction
forces the orbit eventually above every finite bound, since summable terms
tend to zero. A positive periodic orbit therefore cannot have bounded
correction. The last implication is explained in the paper, not separately
named in Lean.

## Research implication and limits

This replaces the earlier merely sufficient geometric hypothesis with an
exact criterion. No favorable growth condition has been established for any
escaping natural Collatz orbit. Mere escape does not generally imply reciprocal
summability: the abstract sequence t+1 illustrates that logical gap, without
being a Collatz example.

The next distinct target is to constrain escaping integer orbits with
divergent reciprocal series. Establishing summability for every escaping orbit
would cover that gap but would still leave bounded-correction orbit exclusion.
Nontrivial cycles remain a separate problem. Finite numerical prefixes cannot
certify convergence or divergence of the infinite series.

## Validation

`lake build Collatz.Reciprocal` succeeds. `analysis/audit_theorems.py --build`
selectively rebuilt its target modules and audited 48 declarations. The new
finite bounds, equivalence, and escape theorem use only standard foundations
(`propext`, `Classical.choice`, `Quot.sound`). No `sorry`, new axiom, or
`native_decide` occurs in the new module. This is not a rebuild or independent
kernel replay of every nested library. No literature-priority claim is made.

Technical paper: `paper/reciprocal.tex` and `.pdf`.
Friendly guide: `paper/reciprocal_guide.tex` and `.pdf`.
