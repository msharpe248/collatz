# Guide: why a correction bound and congruence still leave a gap

The previous work established two ingredients: an upper bound on a suffix's
correction, and an exact congruence test for whether a seed follows a given
parity word. It was natural to try combining them to exclude long paradoxical
segments.

The new Lean theorem shows a limitation of that combination. If we let the
correction be any integer below the bound, we can manufacture arithmetic data
that say the orbit returns exactly to its starting seed. This works for every
fixed positive prefix at every sufficiently large target length.

It does **not** manufacture a real Collatz cycle. The selected number need not
be the correction of any word with the required length and odd count. For
example, the relaxed arithmetic can describe a sixteen-step return from 3
with six odd steps. Direct iteration actually ends at 2 with eight odd steps.

The exact congruence theorem remains valid. It applies to the correction
computed from an actual word. The error would be applying it to an arbitrary
number merely because that number lies below a correction bound.

What the proof needs next is information about **which corrections occur**,
and how those corrections interact with seed residues. Additional orbit
bounds may eliminate the particular artificial family constructed here; the
result does not rule out such improvements. An eventual proof still needs a
restriction that works as the length and odd count grow.

The companion [technical note](correction_attainability.md) gives the theorem,
explicit witness, proof, Lean declaration, and validation commands. This is a
verified limitation of one method; Collatz remains open.
