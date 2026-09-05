# Guide: individual values versus pairs of values

The previous correction bound improved by excluding multiples of three.
It is tempting to keep improving it by deleting more residue classes after
waiting for a longer history.

Lean now verifies why that particular shortcut needs care: every positive
odd value not divisible by three can occur after any prescribed number of
odd steps. The construction starts farther back at a larger seed each time.
It does not build a divergent orbit, and it does not rule out restrictions
that use divergence itself.

There is, however, a useful restriction on pairs. An escaping orbit cannot
contain both odd n and 4n+1. Their forward paths merge, which would force a
repeated value at incompatible times. Lean proves this for every hypothetical
unbounded orbit.

This points to the next correction argument: account for which values can
occur together, rather than only listing individually allowed values. We
still need to prove the resulting weighted-product bound. The ninth-power
correction estimate remains the best exponent established by this track.

The [technical paper](odd_histories_and_collisions.md) gives the construction,
merging proof, Lean declarations, and validation commands. Neither theorem
proves Collatz or eliminates all nontrivial cycles.
