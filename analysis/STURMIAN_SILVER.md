# Unconditional exclusion at slope 1/√2

Date: 2026-09-04. This is a new proved result in this repository, not a
claim of priority in the mathematical literature or a proof of Collatz.

Publication files: [technical paper](../paper/silver.pdf),
[friendly guide](../paper/silver_guide.pdf), and their matching `.tex` sources.
The paper also records the supporting block-swap, survivor-cylinder, corrected
height-bound, and bounded-correction results.

## The theorem

For every natural number `N` and every real intercept `ρ`, its Terras
parity itinerary is not the mechanical word

`w_t = floor((t+1)α+ρ) - floor(tα+ρ)`, where `α = sqrt(2)/2`.

The exclusion also holds after any finite orbit prefix. The slope is
strictly above `log 2 / log 3`; this is not a subcritical drift exclusion.
All natural starting values and real intercepts are quantified in Lean.

- `Collatz.Silver.no_itinerary`
- `Collatz.Silver.no_eventual_itinerary`
- Source: [SturmianSilver.lean](../lean/Collatz/SturmianSilver.lean)

The proof discharges every separation, visit-coverage, and size hypothesis
of the existing Sturmian level theorem. It uses no cited mathematical
axioms and no `sorry` or `native_decide`. The theorem-level audit is in
[theorem_audit.json](theorem_audit.json), reproducible with
`python3 analysis/audit_theorems.py --build`.

## 1. Pell data supply a bracketing pair

Set `(q₀,p₀)=(3,2)` and

`q_(k+1)=3q_k+4p_k`, `p_(k+1)=2q_k+3p_k`.

The invariant is `q²−2p²=1`, with `3≤q`, `1≤p`, `q≤2p`, and `p≤q`.
The sequence is unbounded: the formal proof already establishes `k+3≤q_k`.
For `α=√2/2`, put `δ=qα−p`. Then

`δ(qα+p)=1/2`, so `0<δ<1`.

The upper neighbor is `(Q,P)=(q+2p,q+p)`. It satisfies

`Qα=P−ε`, `ε=(2α−1)δ>0`, and `Pq−pQ=1`.

A general elementary lemma proves that a determinant-one pair bracketing
α yields

`|mα−r| ≥ δ` whenever `0<m<Q` and `r` is an integer.

Proof: express `(m,r)=A(q,p)+B(Q,P)` with integer coefficients from the
determinant. Its error is `Aδ−Bε`. If `A≤0`, the height restriction forces
`A≤−1` and `B≥1`, making the error at most `−δ`. If `A>0`, it forces
`A≥1` and `B≤0`, making the error at least `δ`. This gives the required
separation without an imported continued-fraction theorem.

## 2. Use a larger grid instead of the three-distance theorem

The previous planned proof used a grid of size `q+Q`. This proof uses the
slightly larger `G=q_(k+1)=2Q+q`, whose lower numerator is `p_(k+1)`.
Its error is `e=(3−4α)δ≥0`, and its Bezout certificate is

`−Q*p_(k+1)+P*G=1`.

The width condition is `1+G*e≤G*δ`. Subtracting 1 from `G(δ−e)` gives

`δ[(10α−6)q+(16α−10)p] ≥ 0`,

using `α>2/3`. This identity follows from the Pell invariant.

The general grid lemma is elementary: for arbitrary intercept ρ choose
the integer `z=ceil(G(1−δ−ρ))`. Bezout supplies `0≤n<G` with
`n*p_(k+1)=z+hG`. The quantity `y=nα+ρ−h` satisfies

`Gy=z+Gρ+n*e`.

The ceiling bounds and `1+G*e≤G*δ` imply `1−δ≤y<1`, hence
`fract(nα+ρ)=y` belongs to the visit interval. Replacing ρ by `aα+ρ`
gives a visit in every window `[a,a+G)`. In particular, half-open endpoint
conventions and every real intercept are handled in the proof.

## 3. The size margin survives the larger grid

Write `a=3^α`. Exact rational bounds establish `2≤a<20/9`, hence
`a²≤8` and `a⁶<128`. The endpoint reduction means only `s=G` needs to be
checked in the level theorem.

Let `d=Q−2q≥0`. Then

`G=2Q+q≤7q`, `q+G=6q+2d`, and `Q+G=7q+3d`.

Multiplying the endpoint inequality by 8 reduces it to

`24*a^(q+G)*(3N+3G+1) < 2^(Q+G)`.

The left side is at most

`24*(3N+21q+1)*(a⁶)^q*8^d`,

whereas the right side is `128^q*8^d`. It therefore suffices that

`24*(3N+21q+1)*(a⁶/128)^q < 1`.

This holds eventually because `0≤a⁶/128<1` and a geometric decay
dominates a linear factor. Mathlib's proved limit theorem supplies this
last step. Since `q_k` is unbounded, a suitable level exists for every N.
The level theorem then excludes the itinerary, independently of ρ.

## Reusable components

- [SturmianEndpoint.lean](../lean/Collatz/SturmianEndpoint.lean): endpoint
  reduction above the critical line.
- [SturmianApprox.lean](../lean/Collatz/SturmianApprox.lean): separation
  from a determinant-one pair; uniform visits from an explicit Bezout
  grid, approximation error and width inequality.
- [SturmianSilver.lean](../lean/Collatz/SturmianSilver.lean): Pell data,
  arithmetic inequalities, asymptotic size estimate and final exclusion.

These interfaces may support other quadratic slopes without developing
the full continued-fraction library first. They do not yet provide such
a family theorem. Ordinary-integer itinerary coverage and exclusion of
all nontrivial cycles remain independent open problems.
