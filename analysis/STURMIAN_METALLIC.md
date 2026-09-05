# An infinite excluded family and a shorter rotation window

Date: 2026-09-04. This result is proved in this repository; no claim of
literature priority or a proof of the full Collatz conjecture is made.

## Unconditional theorem

For every integer `m ≥ 6`, define

```
t_m = (sqrt(m² + 4) - m) / 2
alpha_m = 1 / (1 + t_m).
```

No natural-number Terras orbit has the mechanical parity itinerary of
slope `alpha_m`, for any real intercept. This remains true after any
finite orbit prefix. Lean also proves that these slopes are irrational,
strictly increasing, and satisfy `0 < 1 - alpha_m < 1/(m+1)`.

The first few slopes, rounded for illustration only, are
0.8603796100 (m=6), 0.8771507064 (m=7), 0.8903882032 (m=8), and
0.9099019514 (m=10). No rounded value enters the proof.

Sources:

- `lean/Collatz/SturmianWindow.lean`: maximal-fractional-part coverage.
- `lean/Collatz/SturmianFamily.lean`: abstract exclusion from arbitrarily
  large bracketing levels with `6q ≤ Q ≤ Cq`, for fixed C.
- `lean/Collatz/SturmianMetallic.lean`: explicit recurrence, all root and
  denominator certificates, family exclusion, irrationality and accumulation.
- [Technical paper](../paper/metallic.pdf) and
  [companion guide](../paper/metallic_guide.pdf), with matching LaTeX sources.

## 1. The short-window argument

Suppose `q alpha = p + delta`, `Q alpha = P - epsilon`, with positive
q, Q, delta and epsilon, and `epsilon ≤ delta`. For every intercept,
some index below `q+Q` has fractional part in `[1-delta, 1)`.

Otherwise choose an index n maximizing the fractional part among those
finitely many indices. If n<Q, replace it with n+q; the fractional part
increases by delta. If n≥Q, replace it with n-Q; it increases by epsilon.
The replacement index is still in range. Under the assumed absence of
visits, neither increase wraps past 1. Both contradict maximality.

This needs no coprimality or determinant hypothesis. A determinant-one
condition is used separately for separation, via the previously proved
`sturmian_separation_of_neighbors`. Shifting the intercept proves coverage
in every window of length `G=q+Q`. The half-open target interval is handled
exactly. This supplies the needed window without a three-distance theorem.

## 2. A uniform asymptotic margin

For `0 ≤ alpha ≤ 1` and `2 ≤ a=3^alpha`, let a certified level satisfy
`6q ≤ Q ≤ Cq`, with C fixed across levels. Put `d=Q-6q`, `G=q+Q`. Then

```
q+G = 8q+d,       Q+G = 13q+2d,
G ≤ (C+1)q,      a^8 ≤ 6561 < 8192 = 2^13,      a ≤ 4.
```

The endpoint size inequality follows from

`24(3N+3(C+1)q+1) * (6561/8192)^q < 1`.

The base is strictly below one, so this holds eventually for each fixed
seed N and constant C. Unbounded lower denominators supply a suitable
level. The existing endpoint and level theorems complete the exclusion.
The constants are sufficient, not asserted optimal.

## 3. Explicit integer and error recurrences

Start with `(q,Q,p,P)=(1,1,0,1)`. For a fixed m, set

```
q' = q + mQ,        p' = p + mP,
Q' = mq' + Q,       P' = mp' + P.
```

For `t=t_m`, `alpha=1/(1+t)`, let `delta_k=(t²)^k alpha` and
`epsilon_k=t delta_k`. The identity `t²+mt=1` proves

```
q_k alpha = p_k + delta_k,
Q_k alpha = P_k - epsilon_k,
P_k q_k - p_k Q_k = 1.
```

Every error is positive and below 1; epsilon≤delta. For m≥6, after the
initial level, `6q_k ≤ m q_k ≤ Q_k ≤ (m+1)q_k`. Also `k+1 ≤ q_k`.
Thus the abstract criterion applies with `C=m+1`. No external
continued-fraction formalization or mathematical axiom is used.

## Verification and remaining work

`lake build Collatz.SturmianWindow Collatz.SturmianFamily
Collatz.SturmianMetallic` succeeds. The selected declaration audit is
reproduced with `python3 analysis/audit_theorems.py --build`; it records
exact types and transitive axiom dependencies. This is ordinary Lean
checking and axiom inspection, not independent kernel replay or a fresh
rebuild of every dependency and nested library.

This theorem covers a countable set of slopes, each with every intercept.
It does not cover an interval of slopes, all Sturmian words, arbitrary
nonmechanical itineraries, critical-boundary divergence, or all nontrivial
cycles. In particular, the accumulation at slope 1 supplies no continuity
argument that would cover nearby slopes. Parameters 3, 4 and 5 are outside
this conservative family criterion; the earlier silver theorem treats
the slope corresponding to m=2 separately.

The next proof priority is a useful weighted-defect extension of exact
block repetition, followed by an independent restriction on possible
integer counterexample itineraries. Merely listing more excluded slopes
does not supply that coverage bridge.
