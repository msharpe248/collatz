# Paradoxical-cylinder research instrument

Updated 2026-09-05. This pass is a formalization and small-case reproduction,
not a new claimed literature result or a proof of Collatz.

The motivating primary source is Rozier and Terracol,
[Paradoxical behavior in Collatz sequences](https://arxiv.org/html/2502.00948v3),
Definition 1.1 and Section 3. A paradoxical segment has a contracting
multiplicative coefficient but an endpoint at least as large as its positive
seed; intermediate descent is allowed. Their finiteness implication covers
both ways Collatz could fail, unlike an unbounded-orbit-only exclusion.

## Library findings

The pinned `rwst__lean-code/RT/CRozLemma32.lean` already contains
`RT.CRoz_lemma_32` and `RT.CRoz_cor_33`, representing the infinite-segment
construction and finiteness-to-Collatz reduction. This pass inspected source,
not their compiled axiom closures. The nested v4.34.0-rc2 toolchain is not
installed and the requested compiled module is absent. Do not report these
headlines as independently audited here.

Nearby `RT/FinitePar.lean`, `ExcursionRecords.lean`, and `CrossingLemmas.lean`
contain explicit cited computational axioms. `paradoxical/CanonicalShape.lean`
already treats the all-circuit uniformity issue. A per-circuit bound cannot
silently be upgraded to a uniform bound over all circuit counts. These modules
are not imported by the new main-project theorem.

## New main-project implementation

`lean/Collatz/Paradoxical.lean` defines `IsParadoxical` in the main map
convention. It proves exact cylinder and canonical-residue equivalences.
For a residue r modulo 2^L, write u=T^L(r), A=3^j_L(r), and n=r+2^L*q.
If A<2^L, the complete interval is:

    0<n, r≤u, q≤(u-r)/(2^L-A).

The separate r≤u condition avoids a false q=0 witness from truncated natural
subtraction. Positivity is explicit, including at length zero and residue zero.

`paradoxical_eight_iff` proves, for every n>2, that length eight is paradoxical
exactly for n in {7,9,18,19,25}. A kernel-decided table covers all 256 residues
and proves the quotient is zero; this is an all-seed theorem, not a bounded
seed check. Ordinary `decide` is used, not `native_decide`.

## Exact finite census

`paradoxical_cylinders.py` incrementally enumerates all residues, transports
the endpoint and odd count, and solves the quotient interval without a seed
cutoff. `paradoxical_census.json` records lengths 1–20. It finds five segments,
all at length eight, with seeds 7,9,18,19,25. Their first descent times are
respectively 7,2,1,4,2: none is a counterexample to coefficient stopping-time
equality. The Python output is not extracted from Lean or kernel-certified.

The three unit tests pass: all residues through length ten are compared with
direct iteration; interval membership and adjacent endpoints through length
eight are compared with direct seeds; known and truncation-boundary controls
are checked. Every emitted census segment is replayed directly as well.

The selected module build and expanded 60-declaration audit pass with standard
foundational axioms only. The three-page formal note and one-page guide in
`paper/paradoxical_cylinders*` compile without warnings and were visually checked.

## What the evidence changes next

Do not duplicate the nested finiteness implication or treat this small census
as evidence sufficient for all lengths. Exponential enumeration becomes the
bottleneck. The next useful target is a rigorous pruning rule for contracting
words, or an independently proved restriction uniform across circuit counts.
Any proposed rule must preserve the five known length-eight examples and must
not confuse endpoint non-descent with absence of earlier descent.
