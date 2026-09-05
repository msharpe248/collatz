# Lower barriers for the canonical ideal-tracking error

Collatz proof project — September 5, 2026

## Abstract

For a positive shortcut Collatz seed with bounded ideal correction, we prove
that its limiting correction is strictly greater than one. The same holds
on every tail, and some shifted limiting correction is strictly greater than
two. Consequently, a uniform bound on all shifted corrections must exceed
two, and the orbit cannot be identified with the floor of its canonical
geometric ideal. These are conditional lower barriers, not an upper bound,
a proof of existence of such a seed, or a proof of Collatz. The elementary
formalization is not presented as a literature-priority claim.

## Definitions

Write x_t=T^t(n), where T(n)=n/2 for even n and T(n)=(3n+1)/2 for odd n.
Let j_t count the odd steps before t and D_t be the integer correction:

    2^t x_t = 3^j_t n + D_t.

The ideal correction is c_t(n)=D_t/3^j_t. In the main project,
`Supercritical n` means that these real numbers are bounded above. It does
not mean that a strict asymptotic density gap has been established.
Under this hypothesis, c_t increases to c_infinity(n), named `idealLimit n`.
The tracking identity is

    x_t = (n+c_infinity(n)) 3^j_t/2^t - c_infinity(x_t).

Bounded correction propagates to every tail. A separate, stronger property,
`UniformSupercritical n B`, bounds c_s(x_t) by the same B for all s,t.
The project has not proved this stronger property from bounded correction.

## The lower bound one

The finite master inequalities give

    3^j_t ≤ D_t + 2^j_t,

and hence

    c_t(n) ≥ 1-(2/3)^j_t.

Every positive orbit has arbitrarily many odd steps. To see this, a positive
value cannot keep halving forever; induction gives a future odd value.
After that odd step the value stays positive, so the argument repeats.
Taking arbitrarily large odd counts and using c_t(n)≤c_infinity(n) yields

    c_infinity(n) ≥ 1.

Every natural seed also eventually takes an even step. If it stayed odd
through an arbitrarily long prefix of length L, the parity congruence would
force n≡2^L−1 modulo 2^L. Choosing 2^L>n+1 contradicts this. This argument
uses the already formalized Mersenne trajectory and parity congruence.

Choose a prefix of length t that includes an even step, so j_t<t.
The tracking identity and affine formula give the exact limit ledger

    3^j_t c_infinity(n) = D_t + 2^t c_infinity(x_t).

The tail correction is at least one. Therefore

    3^j_t c_infinity(n) ≥ D_t+2^t > D_t+2^j_t ≥ 3^j_t.

Thus **c_infinity(n)>1**, and the same argument applies to every tail.

## A shifted lower bound two

At an even orbit value m, the one-step tracking identity simplifies to

    c_infinity(m) = 2 c_infinity(m/2).

The positive successor has limiting correction greater than one, so
c_infinity(m)>2. Since an even value always occurs, some shifted correction
exceeds two. If a common B bounds all shifted finite corrections, it also
bounds their limits; therefore **B>2**.

Finally, the canonical ideal differs from x_t by c_infinity(x_t)>1:

    x_t+1 < (n+c_infinity(n)) 3^j_t/2^t.

In particular, x_t is not the floor of this canonical ideal. This statement
concerns the specified normalization, not every possible approximation or
change of variables.

## What this says about the confinement-library route

A source review of the nested `rwst__lean-code/Z32` modules found results
about fractional parts of a fixed geometric progression, such as
{xi(3/2)^k}. Our canonical ideal instead uses 3^j_t/2^t. Even on the odd-step
clock, the elapsed shortcut time remains variable. A transport theorem is
needed before applying the fixed-multiplier statements.

A confinement hypothesis is also needed. Bounded c_t(n) alone supplies
neither a common bound on all shifted c_infinity(x_t) nor confinement of
those quantities modulo one to a certified window. The lower barriers above
exclude the particularly simple absolute bounds B≤2 and the canonical-floor
identification.

They **do not** exclude fractional-part confinement: a number larger than
two can still have its fractional part in a short interval. They also do
not prove that all shifted corrections are unbounded. These distinctions
must be retained when considering a different bridge to the library.

The nested sources were reviewed, not built or independently axiom-audited
in this pass. They use a different pinned Lean toolchain and are not imported
by the new main-project module.

## Verification and remaining work

Source: `lean/Collatz/IdealBarrier.lean`.
Selected audit declarations:

- `Collatz.one_lt_idealLimit`
- `Collatz.uniformSupercritical_bound_gt_two`
- `Collatz.ideal_tracking_gap_gt_one`

Supporting theorems prove unbounded odd count on positive orbits and the
shifted lower barrier. The main module builds, and the selected 87-declaration
audit reports only standard foundational axioms. No new axiom, `sorry`, or
`native_decide` is used.

Two exact-arithmetic Python controls check the finite geometric lower bound,
its equality on initial Mersenne odd runs, and the strict finite certificate
after a first even step. They do not construct or test a positive seed with
bounded limiting correction; no such seed is known here.

```sh
PATH=/Users/msharpe/.elan/bin:$PATH python3 analysis/audit_theorems.py --build
python3 -m unittest discover -s analysis -p 'test_ideal_barrier.py'
```

The bounded-correction case remains open. A usable confinement argument
still needs a justified change of dynamics and an independently proved
confinement property. The full Collatz proof also remains incomplete.
