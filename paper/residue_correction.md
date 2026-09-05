# A ninth-power correction bound from residue exclusion

Collatz proof project — September 5, 2026

## Abstract

We strengthen the project's sixth-power ideal-correction bound by using the
fact that every positive shortcut Collatz orbit eventually avoids multiples
of three. On an injective prefix avoiding one and starting outside multiples
of three, we prove

    (N+c_T)^9 ≤ N^9(2j_T+1).

Every unbounded positive orbit has a tail satisfying this at all lengths.
A corresponding drift excursion bound improves the exponent 5/6 to 8/9,
with a finite certificate and a global polynomial-envelope boundedness theorem.
All stated results are formalized in Lean. No universal drift envelope,
convergence theorem, or exclusion of nontrivial cycles is obtained. No claim
of literature priority is made.

## Setting and residue reduction

Let T(n)=n/2 for even n and T(n)=(3n+1)/2 for odd n. Write x_t=T^t(N),
j_t for the number of odd values before time t, and c_t for the ideal
correction normalized by

    2^t x_t = 3^j_t (N+c_t).

The previously formalized product identity is

    (N+c_t)/N = product over odd positions i<t of (1+1/(3x_i)).

If n is not divisible by three, neither is T(n). An odd step always lands
outside the multiples of three. A positive even value strictly decreases
under halving, so well-founded induction proves that every positive orbit
eventually reaches a value not divisible by three. All subsequent values
remain outside that residue class.

## The finite-prefix theorem

Assume N>0, N is not divisible by three, and the values x_i for i<t are
distinct and different from one. Then

    (N+c_t)^9 ≤ N^9(2j_t+1).

For each odd value x_i, define its rank r_i=floor((x_i−1)/3). The allowed odd
values are 5,7,11,13,... and their ranks are 1,2,3,4,... . Thus the ranks are
positive and distinct, with 3r_i≤x_i.

For every real r≥1,

    (1+1/(9r))^9 ≤ (2r+1)/(2r−1).

Clearing the positive denominators leaves the polynomial

    1 + 79r + 2754r² + 55404r³ + 704214r⁴ + 5786802r⁵
      + 29760696r⁶ + 82904796r⁷ + 43046721r⁸,

which is nonnegative. Hence each ninth-power correction factor is at most
(2r_i+1)/(2r_i−1). This ratio decreases with r_i. The product over any j
distinct positive ranks is therefore at most the product over ranks 1,...,j,
which telescopes to 2j+1. Lean proves the finite-set product bound directly
by induction on cardinality, removing the maximum rank.

Applying this to the exact correction product proves the theorem.

## Every unbounded orbit is covered after a finite shift

An unbounded deterministic orbit cannot repeat a value. It also cannot visit
one, since that would force the trivial cycle. Choose K so that M=T^K(N)
is not divisible by three. The tail remains unbounded. The finite-prefix
result therefore yields, simultaneously for every t,

    (M+c_t(M))^9 ≤ M^9(2j_t(M)+1).

This applies to every hypothetical unbounded positive orbit, including one
whose original seed is divisible by three. The shift K and normalization M
must be retained; the theorem is not stated with the original N in place of M.
The asymptotic correction exponent is 1/9 rather than the previous 1/6.
The constants differ, so this is not claimed to improve every tiny prefix.

## Drift escape and finite certificates

For a positive unbounded orbit starting at N not divisible by three, every
prefix horizon H has some t≤H with x_t≥H+1, by injectivity. Combining this
with the ninth-power bound and j_t≤H gives

    (2^t)^9(H+1)^8 ≤ 2(3^j_t N)^9.

Equivalently, the multiplicative drift 3^j_t/2^t has a prefix excursion of
at least (H+1)^(8/9)/(2^(1/9)N). Every unbounded positive orbit has a tail
satisfying this statement at all horizons.

The formal finite-certificate theorem assumes natural C,a,b,H with

    b < 8a,
    2^a C (N^9)^a < H+1,

and, for every t≤H,

    ((3^j_t)^9)^a ≤ C(t+1)^b ((2^t)^9)^a.

It concludes that the orbit from N is bounded. Here N>0 and N is not divisible
by three. To prove this, raise the excursion inequality to power a, combine
with the envelope, and cancel the positive powers. Since b+1≤8a, this forces
H+1≤2^a C(N^9)^a, contradicting the threshold.

A global envelope of this form supplies the finite certificate by taking
H=2^a C(N^9)^a. Its drift exponent is b/(9a)<8/9. The corresponding earlier
criterion used exponents below 5/6. This strengthens the excluded slow-drift
range. It does not assert that every orbit satisfies such an envelope.

## Verification and remaining gap

Source: `lean/Collatz/ResidueCorrection.lean`.
The following declarations are included in the 77-declaration audit:

- `idealC_ninth_bound_of_prefix`
- `unbounded_eventual_ninth_bound`
- `unbounded_eventual_ninth_escape`
- `finite_ninth_drift_certificate`
- `bounded_orbit_of_ninth_polynomial_drift`

The module builds and the selected audit reports only standard foundational
axioms. No new axiom, `sorry`, or `native_decide` is used. Three exact-arithmetic
Python controls check the rank inequality and finite products, actual eligible
prefixes from seeds through 500, and residue entry and preservation through
seed 1024. These controls are not evidence that an unbounded orbit exists.

Reproduce from the repository root:

```sh
PATH=/Users/msharpe/.elan/bin:$PATH python3 analysis/audit_theorems.py --build
python3 -m unittest discover -s analysis -p 'test_residue_correction.py'
```

The unbounded case with faster drift remains open. Boundedness alone also
permits hypothetical nontrivial cycles. A proof of Collatz still needs to
exclude those cases. This result strengthens a universal necessary condition
on escaping orbits; it does not supply the missing coverage theorem.
