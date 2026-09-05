# Guide: excluding a whole itinerary class

The project now has a Lean proof excluding Sturmian parity itineraries in
the standard definition: exactly L+1 distinct blocks at every length L.
This also rules out a Sturmian tail after any finite number of steps.

The argument is short. Two equal parity blocks force the corresponding
orbit values to agree modulo a large power of two. Early orbit values are
smaller than that modulus. Thus, if the orbit never repeats a value, its
early blocks must all be different.

This gives more blocks than a Sturmian word permits. More generally, a
uniform complexity envelope with slope below 5/3 forces the orbit to be
bounded. A bounded orbit then has only a bounded number of distinct blocks,
which also contradicts the Sturmian count L+1.

A stronger asymptotic complexity result was already proved by Dubickas in
2009. This pass formalizes an explicit rational version and its consequence;
it is not a new mathematical discovery.

The theorem uses the complexity definition directly. The link to the
slope-and-intercept mechanical words used elsewhere in the repository has
not yet been ported into this proof.

The [technical paper](parity_complexity.md) gives the exact statements,
literature reference, Lean declarations, and validation. No universal upper
bound on Collatz itinerary complexity is proved, so this class exclusion
does not settle Collatz.


Update: the mechanical-word bridge described above is now proved for all
irrational slopes and all intercepts. See [the follow-up paper](mechanical_complexity.pdf)
and [guide](mechanical_complexity_guide.pdf). The earlier gap statements
describe the state before this follow-up.
