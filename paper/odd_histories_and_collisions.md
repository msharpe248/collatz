# Long odd histories and a forbidden pair on escaping orbits

Collatz proof project — September 5, 2026

## Abstract

We formalize two complementary facts in Lean. Every positive odd integer not
divisible by three is the endpoint of genuine histories with any prescribed
number of odd steps, starting at larger seeds. However, an unbounded orbit
cannot contain both odd n and 4n+1, since their forward paths merge. The first
fact limits further deletion of individual values based only on a fixed
finite history; the second supplies a joint restriction on orbit values.
Neither proves Collatz. These elementary formalizations carry no literature
priority claim.

## Arbitrarily long histories

Use the shortcut map T(n)=n/2 for even n and T(n)=(3n+1)/2 for odd n.
For any y>0 with y odd and 3 not dividing y, and any natural K, there are
natural n,t such that

    n ≥ y+K,   n odd,   3 does not divide n,
    3K ≤ t ≤ 6K,   T^t(n)=y,
    the number of odd steps before t equals K.

The starting seed n varies with K. This is not a single forward infinite
orbit or a divergent-orbit construction.

For one backward step, choose a according to the residue of y modulo nine:

| y mod 9 | 1 | 2 | 4 | 5 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|
| a | 4 | 3 | 6 | 3 | 4 | 5 |

Then n=(2^a y−1)/3 is an integer, n>y, n is odd, and n is not divisible by
three. The equation 3n+1=2^a y gives one odd step followed by a−1 even steps,
ending at y. Iterating the construction K times proves the theorem, with
total shortcut length between 3K and 6K. Since the starting value is not
divisible by three, every value along each history also avoids multiples
of three, by the preceding residue-preservation theorem.

In particular, no allowed positive odd target can be deleted merely on the
ground that a sufficiently long, but fixed finite, odd history precedes it.
This does not rule out a restriction specific to unbounded orbits, a
seed-dependent eventual statement, or a frequency restriction on values.

## A joint restriction from merging paths

**Theorem.** If the orbit from N is unbounded and n is odd, that orbit cannot
contain both n and 4n+1.

Indeed,

    T^2(4n+1)=3n+1,
    T^3(4n+1)=T(n).

Suppose T^i(N)=n and T^j(N)=4n+1. Then T^(i+1)(N)=T^(j+3)(N).
An unbounded deterministic orbit is injective, so i+1=j+3 and i=j+2.
The first displayed identity now forces n=3n+1, impossible for a natural n.

The conclusion excludes the pair. It does not exclude either value by itself,
and it does not establish a contradiction for every possible escaping orbit.
It also does not rule out all nontrivial cycles, where injectivity over all
natural times would fail.

## Implication for the correction argument

The ninth-power correction bound used distinct odd values outside multiples
of three, without joint restrictions on those values. The pair theorem gives
additional information. When n is 1 modulo six, both n and 4n+1 lie in that
allowed set, and at least one must be absent from an escaping orbit.

A possible next step is to incorporate these disjoint pairs into the weighted
correction product. Because smaller values contribute larger factors, such
an argument must control weights as well as cardinality. No improved product
exponent from this pairing is claimed in this note; that bound remains to be
proved. The ninth-power result is still the current established exponent.

## Formal verification

Source: `lean/Collatz/OddPrehistory.lean`.
Audited declarations:

- `Collatz.arbitrarily_long_odd_prehistory`
- `Collatz.unbounded_excludes_odd_siblings`

Supporting lemmas prove the explicit predecessor table and its actual
shortcut iteration. The selected audit now covers 79 declarations with only
standard foundational axioms. No new axiom, `sorry`, or `native_decide` is used.
Two Python controls replay histories of zero through ten odd steps for all
eligible targets below 1000 and verify the merging identities on odd values
below 1000. These are controls of the construction, not a computational proof
of Collatz.

Reproduce from the repository root:

```sh
PATH=/Users/msharpe/.elan/bin:$PATH python3 analysis/audit_theorems.py --build
python3 -m unittest discover -s analysis -p 'test_odd_prehistory.py'
```

Collatz remains unproved. The result identifies a joint orbit constraint to
use next, while guarding against an unsupported strengthening of individual
residue exclusion.

Subsequent update: the proposed weighted-pair bound is now proved. See the
[tenth-power correction paper](sibling_correction.md) and its
[guide](sibling_correction_guide.md). The previously open weighted step above
is resolved; the full Collatz coverage gaps remain open.
