# A tenth-power correction bound from forbidden sibling pairs

Collatz proof project — September 5, 2026

## Abstract

We incorporate a joint orbit restriction into the correction-product argument.
An unbounded shortcut Collatz orbit cannot contain both odd n and 4n+1.
Replacing certain occupied larger siblings by their absent smaller partners
gives an injective comparison set with larger correction weights. An explicit
rank bound yields a tenth-power correction estimate, improving the preceding
ninth-power estimate. Every unbounded positive orbit has a tail satisfying
this bound, and a corresponding drift excursion exponent improves from 8/9
to 9/10. Finite and global conditional boundedness theorems are proved in Lean.
Faster drift and nontrivial cycles remain unexcluded. No literature-priority
claim is made.

## Weighted finite-set theorem

Let S be a finite set of distinct odd integers greater than five, none
divisible by three. Suppose S never contains both n and 4n+1 for an odd n.
Then

    [ product over x in S of (1+1/(3x)) ]^10 ≤ 2|S|+1.

The bound uses more than the individual residue restrictions.

Define a compression map

    c(x) = (x−1)/4, if x ≡ 5 (mod 24),
           x,       otherwise.

When x≡5 modulo 24, its parent is 1 modulo six. Both parent and child are
odd and not divisible by three. The forbidden-pair hypothesis ensures that
an occupied child is replaced by an absent parent. Two different children
have different parents. Thus c is injective on S.

Moreover c(x)≤x, so replacing x by c(x) increases the factor 1+1/(3x).
Because x>5, the replacement is greater than one. The image consists of
values greater than one with residues

    1, 7, 11, 13, 17, 19, 23 modulo 24.

These comparison values need not themselves lie on the original orbit.
That is intentional: injectivity and domination of the weights are the
properties needed for the upper bound.

## Exact ranks and the tenth power

For an allowed comparison value y=24q+r, assign ranks

| r | 1 | 7 | 11 | 13 | 17 | 19 | 23 |
|---|---:|---:|---:|---:|---:|---:|---:|
| rank(y) | 7q | 7q+1 | 7q+2 | 7q+3 | 7q+4 | 7q+5 | 7q+6 |

Since y>1, these ranks are positive. They are distinct for distinct comparison
values, and the finite residue table gives 10 rank(y)≤3y. Consequently, for
r_x=rank(c(x)),

    1+1/(3x) ≤ 1+1/(10r_x).

For any real r≥1,

    (1+1/(10r))^10 ≤ (2r+1)/(2r−1).

After clearing positive denominators, the difference is the nonnegative
polynomial

    1 + 98r + 4300r² + 111000r³ + 1860000r⁴ + 21000000r⁵
      + 159600000r⁶ + 780000000r⁷ + 2100000000r⁸ + 1000000000r⁹.

The product of (2r+1)/(2r−1) over any j distinct positive integer ranks is
at most its product over ranks 1,...,j, namely 2j+1. This proves the
finite-set theorem. Lean checks the compression, injectivity, rank table,
weight comparison, and product argument separately.

## Application to an escaping orbit

Write x_t=T^t(N), where T is the shortcut Collatz map, and j_t for the odd
count before t. Define the ideal correction by

    2^t x_t = 3^j_t (N+c_t).

For N>0, the previously formalized product identity is

    (N+c_t)/N = product over odd positions i<t of (1+1/(3x_i)).

Assume the orbit is unbounded and N is not divisible by three. The odd values
are distinct, never divisible by three, and greater than five: visiting one
or five would lead to the trivial cycle. The preceding sibling theorem
excludes every pair n,4n+1. Applying the weighted finite-set theorem gives

    (N+c_t)^10 ≤ N^10(2j_t+1).

Every positive orbit eventually leaves the multiples of three and never
returns. Every unbounded positive orbit therefore has some shift K such
that, with M=T^K(N), the displayed bound holds for the tail from M at every
length. The normalization uses M, not the original seed N.

The new exponent 1/10 is stronger than 1/9 with the same factor 2j+1.
This is a necessary condition on every escaping orbit after a finite shift;
no distributional or summability assumption is needed for that condition.

## Drift excursions and boundedness certificates

For an unbounded orbit from N>0 not divisible by three, every horizon H has
some t≤H with x_t≥H+1. The correction bound then yields

    (2^t)^10 (H+1)^9 ≤ 2(3^j_t N)^10.

Thus the drift 3^j_t/2^t must make prefix excursions of size at least
(H+1)^(9/10)/(2^(1/10)N). Every unbounded positive orbit has a tail satisfying
this statement at all horizons.

The finite-certificate theorem assumes natural C,a,b,H with

    b < 9a,
    2^a C (N^10)^a < H+1,

and, for all t≤H,

    ((3^j_t)^10)^a ≤ C(t+1)^b ((2^t)^10)^a.

It concludes that the orbit is bounded, for N>0 not divisible by three.
The proof raises the excursion inequality to power a, combines it with the
envelope, and cancels positive factors to contradict the threshold.
A global envelope supplies the certificate by taking H=2^a C(N^10)^a.
Its rational drift exponent is b/(10a)<9/10.

No such envelope is proved for all orbits. Boundedness also does not establish
that an orbit reaches one. Improving this exponent alone cannot close either
of those missing steps.

## Verification

Source: `lean/Collatz/SiblingCorrection.lean`.
Five declarations are included in the selected 84-declaration audit:

- `SiblingCorrection.pair_free_product_bound`
- `unbounded_eventual_tenth_bound`
- `unbounded_eventual_tenth_escape`
- `finite_tenth_drift_certificate`
- `bounded_orbit_of_tenth_polynomial_drift`

All are in namespace `Collatz` (the first has the additional namespace shown).
The module builds and the audit reports only standard foundational axioms.
No new axiom, `sorry`, or `native_decide` is used.

Three exact-arithmetic Python controls check comparison ranks below 10000,
all pair-free subsets of size at most five from the eligible values 7–61,
and eligible actual trajectory prefixes from seeds through 500. The control
also demonstrates that compression identifies 7 and 29 if pair-freeness is
omitted. These finite checks do not verify the Collatz conjecture.

Reproduce from the repository root:

```sh
PATH=/Users/msharpe/.elan/bin:$PATH python3 analysis/audit_theorems.py --build
python3 -m unittest discover -s analysis -p 'test_sibling_correction.py'
```

The result completes the weighted-pair argument proposed in the preceding
note. Further merging-path restrictions may strengthen the comparison set,
but the full proof still requires coverage of faster-drift orbits and the
exclusion of nontrivial cycles. Collatz remains unproved.
