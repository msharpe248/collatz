# Distinct orbit values give a sixth-root correction bound

Updated 2026-09-05. Source: `lean/Collatz/CorrectionGrowth.lean`.

For a positive shortcut Collatz seed N, write n_t for the orbit, j_T for
the number of odd steps, and c_T for `idealC T N`. Lean proves:

    (N+c_T)^6 ≤ N^6 * (j_T+1).

The finite theorem `idealC_sixth_bound_of_prefix` assumes only that
n_0,...,n_(T-1) are distinct and avoid one. It imposes no assumption on
later values, including the endpoint n_T. The theorem
`unbounded_idealC_sixth_bound` derives these hypotheses from unboundedness
and applies at every time. No reciprocal summability or strict density
gap is assumed.

## Proof

The correction cocycle gives the exact product

    N+c_T = N * product_{t<T, n_t odd} (1+1/(3*n_t)).

For x>1, clearing positive denominators proves

    (1+1/(3*x))^6 ≤ (x+1)/(x-1),

because the cross-product difference is
243*x^5 + 675*x^4 + 405*x^3 + 117*x^2 + 17*x + 1 ≥ 0.

Write every odd value greater than one as n_t=2*k_t+1. The k_t are distinct
positive integers. A finite set S of positive integers satisfies

    product_{k in S} (k+1)/k ≤ card(S)+1.

To prove this, remove its largest member m. If card(S)=q, then q≤m;
induction bounds the remaining product by q, so the full product is at
most q*(m+1)/m≤q+1. Combining the two product bounds proves the theorem.

An unbounded deterministic orbit cannot repeat a value: any return gives
a bounded periodic tail. It cannot reach one, which returns after two
shortcut steps. These facts are also proved in the module.

## Integer drift consequences

Using the exact affine identity, Lean proves

    (2^T*n_T)^6 ≤ (3^j_T*N)^6*(j_T+1).

At a non-descent time n_T≥N, cancellation gives

    (2^T)^6 ≤ (3^j_T)^6*(j_T+1).

Both are natural-number inequalities. Their logarithmic interpretation is
j_T≥T*log(2)/log(3)−log(j_T+1)/(6*log(3)). The logarithmic version and the
equivalent root form c_T≤N*((j_T+1)^(1/6)−1) are explained in the paper,
not separately named as Lean declarations.

## Significance and boundary

The bound covers every hypothetical unbounded positive orbit, including
the escaping orbits with divergent reciprocal series left open by the
previous characterization. Correction growth is quantitatively constrained
even in that case. But an O(T^(1/6)) upper bound is not a constant bound;
it does not prove reciprocal summability or exclude unbounded orbits.
Nontrivial cycles remain outside this application.

The drift-escape extension below converts this bound into an exclusion of
slow polynomial drift. Further arithmetic itinerary restrictions are still
needed to force descent in the remaining case. Merely restating a certificate
as a universal completeness assumption would not make progress.

## Drift escape and finite boundedness certificates

New source: `lean/Collatz/DriftEscape.lean`. Write M_t=3^j_t/2^t.
On an unbounded orbit, the first T+1 values are distinct positive integers,
so one n_t with t≤T is at least T+1. The sixth-power drift inequality gives

    (2^t)^6*(T+1)^5 ≤ (3^j_t*N)^6.

Thus the running maximum of M_t is at least (T+1)^(5/6)/N. This is not a
pointwise lower bound on each M_t.

If natural parameters a,b,C satisfy b<5a and M_t^(6a)≤C*(t+1)^b globally,
the orbit is bounded. Indeed the selected time above would give
(T+1)^(5a)≤C*N^(6a)*(T+1)^b, hence T+1≤C*N^(6a), a contradiction for
T=C*N^(6a). This excludes every rational polynomial drift exponent below
5/6, including uniformly bounded drift. The Lean statements use only
integer powers and inequalities; no numerical logarithm is evaluated.

The same proof needs the envelope only through a specified horizon T with
C*N^(6a)<T+1. `finite_drift_certificate_bounds_orbit` formalizes this finite
certificate. Its conclusion is boundedness, not reaching one. The sufficient
horizon may be very large. No computational record or universal coverage is
claimed.

In particular, this does not eliminate every critical-density itinerary:
logarithmically growing odd-step excess can already yield polynomial drift.
Faster drift and nontrivial cycles remain open tracks.

## Validation and artifacts

Selective builds of `Collatz.CorrectionGrowth` and `Collatz.DriftEscape`, and
the expanded `analysis/audit_theorems.py --build`, succeed. The 57 selected
declarations use only standard foundational axioms; five correction-growth
and four drift-escape results are included. The new modules have no `sorry`,
new axiom, or `native_decide`.
This is not independent kernel replay or a full nested-library build.
No literature-priority claim is made.

The technical paper is `paper/correction_growth.tex` and `.pdf`; the guide
is `paper/correction_growth_guide.tex` and `.pdf`. Both compile without
warnings, and all nine rendered pages of the expanded pair were visually inspected.
