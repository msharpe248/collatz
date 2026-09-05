# Guide to the tenth-power correction bound

The forbidden-pair result now produces a stronger numerical theorem in Lean.
Every hypothetical escaping positive orbit has a tail with correction growth
bounded by a tenth-root expression. The previous bound used a ninth root.

The idea is to use which values cannot occur together. If an escaping orbit
contains an odd value 4n+1, it cannot also contain n. For suitable residues,
we replace the larger value by this absent smaller partner in a comparison
set. The replacement increases the correction weight, so it remains a valid
upper bound. The forbidden-pair theorem ensures distinct values stay distinct.

The comparison set has fewer allowed residues. Ranking its members makes
the correction product telescope and yields the tenth-power estimate.
This is a proved weighted argument, not a random-orbit model.

The associated drift threshold improves from 8/9 to 9/10. A proved polynomial
drift envelope below 9/10 forces boundedness for a positive seed not divisible
by three, and there is an explicit finite version. Every positive orbit
enters the needed residue restriction after finitely many steps.

The unresolved part is substantial: we have not proved such a slow-drift
envelope for every possible escaping orbit. Boundedness alone also leaves
hypothetical nontrivial cycles. The result strengthens a necessary condition;
it does not prove Collatz.

The [technical paper](sibling_correction.md) gives the exact bounds, proof,
Lean declarations, and tests. The selected audit covers 84 declarations with
only standard foundational axioms.
