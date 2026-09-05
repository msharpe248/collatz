# Guide to the ninth-power correction bound

The project now has a stronger Lean-verified restriction on how a hypothetical
escaping Collatz orbit could behave.

The argument uses a simple extra fact: after finitely many steps, a positive
orbit never visits a multiple of three again. Its odd values therefore lie
among 5,7,11,13,... if it also avoids the trivial cycle. An escaping orbit
cannot repeat values, so each of these odd values can contribute to the
correction product only once.

That thinner list improves the correction-growth exponent from 1/6 to 1/9.
The argument applies to every hypothetical escaping positive orbit after a
finite shift; it does not assume a typical or random distribution of values.

The resulting drift restriction is stronger too. The multiplier 3^j/2^t
must make excursions growing at least at exponent 8/9 over prefix horizons,
up to a constant depending on the tail's starting value. Previously the
proved exponent was 5/6.

Consequently, a proved global polynomial drift envelope with exponent strictly
below 8/9 forces boundedness for a seed not divisible by three. There is also
a finite version with an explicit threshold. Every positive orbit eventually
enters the residue class restriction used by this argument.

This does not prove Collatz. We have not proved that all potential escaping
orbits have slow drift, and boundedness alone does not eliminate nontrivial
cycles. The result narrows what a counterexample could do.

The [technical paper](residue_correction.md) gives the exact inequalities,
proofs, hypotheses, Lean declarations, and validation commands. The selected
77-declaration audit uses only standard foundational axioms.
