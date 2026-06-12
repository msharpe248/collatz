# The Rung-1 Attack: Automatic Itineraries via Mahler's Method

**Status: open problem with a concrete, classical-shaped attack plan.
Nothing in this document claims to prove the Collatz conjecture or even
rung 1. It records the exact functional equation, the verified failure
of the cheap route, and what the genuine route requires.**

All numerical claims below are verified by
`analysis/mahler_experiments.py` (experiments 1–4). The formal
infrastructure cited (`dcoef_closed`, `eq_of_itinerary_eq`, the cocycle
law, the density floor) is machine-checked in
`lean/Collatz/Ladder.lean` and `lean/Collatz/Shadow.lean`.

---

## 1. The target

**The ladder.** Order potential divergent orbits by the complexity of
their parity itineraries. Rung zero is formal
(`divergent_itinerary_aperiodic`): a divergent orbit's itinerary is
never eventually periodic. Rung one is the next class up:

> **Rung 1 (target).** No positive integer's Terras itinerary is a
> fixed point (or shifted fixed point) of a constant-length
> substitution with uniform block weight in the supercritical density
> band.

Why this matters even though the class is countable and measure-zero:
divergent orbits are pinned to odd-step density ≥ log 2/log 3 = 0.6309…
(`density_floor`), and the slowest escapees cling to the critical line,
where the admissible words are the most *ordered* aperiodic words
(Sturmian/automatic territory — the shadow-clustering experiments show
their 3-adic footprint collapsing). Rung 1 is the first place where the
exclusion has to engage genuine aperiodicity, and — as shown below — it
lands in classical transcendence theory rather than in a new swamp.

**The running example.** σ: 1 → 110, 0 → 011, constant length L = 3,
both blocks containing a = 2 ones. Its fixed point from 1,

w = 110 110 011 011 110 011 …,

has uniform density 2/3 = 0.667 > 0.6309 — squarely in the band where a
divergent orbit could live.

## 2. The realization and why it is one number

By the infinite-precision parity bijection (`eq_of_itinerary_eq`), an
itinerary w determines at most one integer. Concretely, the exact form
2^T·T^T(n) = 3^{j}·n + d(w_{<T}) (`terras_exact_form`) gives

n ≡ −3^{−j_T}·d(w_{<T})  (mod 2^T),

so the candidate integer is the 2-adic limit

x(w) = −lim_T 3^{−j_T} d(w_{<T}) ∈ ℤ₂,

with d(w) = Σ_{w_i=1} 2^i·3^{#ones after i} (`dcoef_closed`). An
integer n has itinerary w **iff** x(w) = n in ℤ₂. Rung 1 for the class
of w is exactly: **x(w) is never a positive integer.**

## 3. The Mahler functional equation (the clean form)

Let F(z) = Σ_{i≥0} w_i z^i ∈ ℤ[[z]] be the generating function of the
fixed point. Splitting indices into σ-blocks (w_{3i}, w_{3i+1},
w_{3i+2}) = σ(w_i), with σ(1) = 110 contributing z^{3i}(1+z) and
σ(0) = 011 contributing z^{3i}(z+z²):

**F(z) = (z+z²)/(1−z³) + (1−z²)·F(z³).**

(Verified coefficient-wise to degree 900, exactly, in ℚ[[z]].) This is
the textbook Mahler setup: d = 3, rational-function coefficients,
iteration z → z³.

**The evaluation point.** Unwinding the realization series through the
block structure (the cocycle law `dcoef_add` plus the block corrections
d(σ(1)) = 5, d(σ(0)) = 10) gives the exact 2-adic identity

**x(w) = −10 + (5/9)·F₂(8/9),**

where F₂(8/9) means the series Σ w_i (8/9)^i summed in ℚ₂ — convergent
because |8/9|₂ = |8|₂ = 1/8 < 1. (Verified to 600 bits of 2-adic
precision against the realization map.) So:

> x(w) ∈ ℤ ⟺ F₂(8/9) ∈ ℚ.
>
> **Rung 1 for this word needs only the IRRATIONALITY of one 2-adic
> Mahler value — not transcendence.**

**The tower form.** Iterating the equation at z = 8/9 → (8/9)³ →
(8/9)⁹ → … gives, with u_k := Σ w_i α_k^i/β_k^{i+1} = (1/β_k)F₂(α_k/β_k)
and (α_k, β_k) = (8^{3^k}, 9^{3^k}):

u_k = c_k + e_k·u_{k+1},  c_k = α_k(α_k+β_k)/(β_k³−α_k³),  e_k = β_k²−α_k²,

so u₀ = 136/217 + 17·u₁, etc. The heights of the tower constants grow
doubly exponentially, like 9^{3^k}. (The finite-level identities are
exact in ℚ; verified.)

**Double convergence.** In the supercritical band a·log₂3 > L the point
z = 2^L/3^a satisfies |z|_∞ < 1 *as well as* |z|₂ = 2^{−L} < 1: the
series converges in ℝ and in ℚ₂ simultaneously, automatically, exactly
for the dangerous densities. (Here 8/9: real value of x is ≈ −6.5701;
the 2-adic value is a different number — see §4.)

## 4. The cheap route, and its verified failure

Two natural shortcuts both fail, and it is worth recording exactly how.

**(a) Product formula / "the real value is not an integer".** The real
sum and the 2-adic sum of the same rational series are *different
numbers* (nothing identifies them; compare Σ2^i = −1 in ℤ₂). The real
value −6.5701… being a non-integer says nothing about the 2-adic
value. Unrolling the tower under the assumption x(w) = n ∈ ℤ forces
every u_k to be an explicit rational, but their numerators and
denominators are *allowed* to grow like 9^{3^k} — and the tower's own
constants grow at exactly that rate. The product formula over all
places closes without contradiction. Dead end, verified.

**(b) Liouville from truncation.** Truncating the series after N terms
gives rational approximations p_N/q_N → F₂(8/9) with q_N = 9^N and
2-adic error |F₂(8/9) − p_N/q_N|₂ ≤ 2^{−3N}. The approximation exponent
is

3N·log 2 / (N·2·log 3) = (3 log 2)/(2 log 3) = **0.9464 < 1.**

Not even Liouville-violating — irrationality does not follow from any
amount of this. (Note the constant: it is the critical-density ratio
again, in the form (L·log 2)/(a·2·log 3); the same coincidence
log 2/log 3 that runs the density program caps the cheap approximation
exponent below 1 throughout the supercritical band.)

**This failure is the precise reason Mahler's method exists.** Mahler's
auxiliary-function construction manufactures, from the functional
equation, approximations of quality growing like the *square* of the
naive ones (degree-n auxiliary polynomials in z and F give exponent
~ n along the orbit z^{3^k}), which is how the classical method proves
transcendence of F(α) with no Liouville-grade input. The cheap route's
0.946 is not a wall; it is the entry fee.

## 5. What the genuine route requires

The classical statement (Mahler 1929; Nishioka, *Mahler Functions and
Transcendence*, LNM 1631): if F ∈ ℚ[[z]] satisfies F(z) = A(z) +
B(z)F(z^d) with A, B ∈ ℚ(z), F is transcendental over ℚ(z), and α is
an algebraic number with 0 < |α| < 1 whose orbit α^{d^k} avoids the
singularities of A, B, then F(α) is transcendental. The proof is
archimedean but its ingredients are place-generic: auxiliary
polynomial, order-of-vanishing zero estimate, height inequality,
iteration along the orbit.

What must be checked or built for our instance:

1. **F transcendental over ℚ(z).** Since the coefficients take finitely
   many values, F is rational iff w is eventually periodic
   (Fatou/Szegő). The fixed point of σ is aperiodic (σ is primitive;
   standard substitution-dynamics criteria; experimentally the
   realization digit-tails are random-like, exp 2). So yes —
   needs a short clean writeup, not new mathematics.
2. **Orbit avoids singularities.** A(z) = (z+z²)/(1−z³) has poles at
   cube roots of unity; |（8/9)^{3^k}|₂ = 8^{−3^k} → 0, and
   |1 − z²|₂ = |17/81|₂ = 1 along the orbit: clean.
3. **The 2-adic transposition.** This is the real work item. The
   evaluation place is ℚ₂ (the series diverges at the archimedean place
   of interest — rather, converges to the *wrong* number), so we need
   Mahler's method with the analytic lemma replaced by its
   non-archimedean counterpart (in ℂ_p the maximum principle and
   Schwarz-type lemmas are if anything cleaner). p-adic versions of
   Mahler's method exist in the literature in several forms
   (irrationality and transcendence results for Mahler-type values:
   Bundschuh, Väänänen, and others; the function-field analogue is
   fully developed by Fernandes). **The key literature question:** is
   there a citable theorem covering "F ∈ ℚ[[z]] Mahler of degree d
   over ℚ(z), α ∈ ℚ with 0 < |α|_p < 1, orbit non-singular ⟹ F_p(α)
   irrational (or transcendental)"? If yes, rung 1 for this word is an
   *application*. If not, the proof is an adaptation of Nishioka's
   Chapters 1–2 to ℚ₂ — bounded, classical work, but real work.
4. **Shifts.** An orbit's itinerary is a *tail* of the fixed point.
   Shifted automatic words satisfy finite inhomogeneous Mahler systems
   (the shift by r < 3^k composes with the substitution into a finite
   system relating F and finitely many shifted generating functions) —
   standard in the theory (Adamczewski–Faverjon handle exactly such
   systems), but it enlarges the bookkeeping.
5. **The whole class, not one word.** Every constant-length-L
   substitution whose blocks all contain a ones, with 2^L < 3^a
   (supercritical), gives the same shape: evaluation of an automatic
   generating function at z = 2^L/3^a, |z|₂ = 2^{−L} < 1, |z|_∞ < 1.
   One theorem covers the class.

**Literature pointers.** Mahler (1929, 1930); Loxton–van der Poorten
(values of Mahler functions, the automatic-numbers program); Becker
(1991–94); Ku. Nishioka (LNM 1631, the standard reference); Bundschuh &
Väänänen (irrationality/measures for Mahler-type values, including
non-archimedean settings); Adamczewski–Bugeaud 2007 (transcendence of
automatic *reals* — NOT directly applicable: x(w)'s binary digits are
not automatic, only the series coefficients are; the functional
equation is the correct interface); Adamczewski–Faverjon (Mahler method
made effective; algebraic relations among values = functional
relations; whether their lifting theorem has a p-adic analogue is the
sharpest version of the key question); Fernandes (Mahler's method over
function fields — the template for transposing the machinery to a new
place); Philippon (algebraic independence in Mahler's method).

## 6. Calibration (the 5x+1 test)

Any principle claiming to resolve divergence must fail to "prove" the
same for 5x+1, where divergence (almost surely) really happens. This
attack passes the filter *in the right way*: for 5x+1 the same
computation lands at z = 2^L/5^a (e.g. 8/25), and the same Mahler
argument would exclude integers with *that exact automatic itinerary*
under 5x+1 — a true and consistent statement (the known 5x+1 escapees,
like 7, have generic-looking itineraries of density ≈ 0.49, nowhere
near a substitution fixed point). The method excludes specific symbolic
classes; it does not manufacture a global convergence principle. The
3x+1-specific content stays where it belongs: in the density floor
that pins divergent orbits to the band where the ordered words live.

## 7. Honest scope and the work plan

Closing rung 1 excludes a countable, measure-zero class of itineraries;
the conjecture would remain wide open above it (morphic, Sturmian, and
beyond — and `no_finite_certificate` already says no bounded-memory
argument tops the ladder). The value is structural: it would be the
first rung where Collatz divergence meets transcendence theory through
an exact, machine-checked interface (`dcoef_closed` → cocycle → block
law → functional equation), with every reduction step verified.

Plan, in order:
1. Literature determination on the 2-adic Mahler irrationality theorem
   (§5.3). Outcome A: citable — write the rung-1 note. Outcome B:
   absent — adapt Nishioka to ℚ₂ for d = 3, rational coefficients,
   single equation (the minimal needed case).
2. Aperiodicity-⟹-transcendence-of-F writeup (Fatou + primitivity).
3. The shift system (§5.4).
4. The class statement (§5.5), then the paper.

## Appendix: verified numbers

| Quantity | Value | Where verified |
|---|---|---|
| Block corrections d(σ(1)), d(σ(0)) | 5, 10 | exp 1 |
| Block law d(σ(w)) = Σ 8^i 9^{T−1−i} d(σ(w_i)) | exact, 200 random words | exp 1 |
| Functional equation F(z) = (z+z²)/(1−z³) + (1−z²)F(z³) | exact to degree 900 | exp 4 |
| 2-adic identity x(w) = −10 + (5/9)F₂(8/9) | exact mod 2^600 | exp 4 |
| Tower: u₀ = 136/217 + 17u₁; c_k = α(α+β)/(β³−α³), e_k = β²−α² | exact finite-level identities | exp 4 |
| Real value of realization series | −6.57014472950… | exp 4 |
| Cheap Liouville exponent (3 log 2)/(2 log 3) | 0.946394… < 1 | exp 4 |
| Control: (110)^∞ realizes −5 | exact | exp 2 |
| Shadow clustering of automatic shifts | 117/300 distinct vs 300/300 random | exp 3 |
