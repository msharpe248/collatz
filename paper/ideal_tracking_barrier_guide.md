# Guide: checking the ideal-tracking route

The project has an exact formula comparing a Collatz orbit with a geometric
ideal. One proposed route was to connect that formula with library results
about fractional parts of geometric progressions.

This pass checked the gap between those two settings. The library uses a
fixed multiplier such as 3/2. The Collatz formula uses 3^j/2^t, with j counting
odd steps and t counting all steps. These are different clocks, and no
transport theorem joining them has been proved here.

Lean also verifies a useful lower barrier. If a positive seed has bounded
ideal correction, its limiting correction is greater than one on every tail,
and greater than two on some tail. Thus a common bound of two or less is
impossible. The actual orbit value is also more than one below its canonical
geometric ideal, so it is not simply that ideal's floor.

This does not disprove a fractional-part approach. A large correction can
still have a fractional part in a small interval. What is missing is a proof
of the required confinement and a valid change of dynamics—not just the
tracking identity itself.

The [technical paper](ideal_tracking_barrier.md) gives the exact hypotheses,
proof, Lean declarations, and verification boundary. The result guards against
an unsupported shortcut; it does not exclude every bounded-correction orbit
or prove Collatz.
