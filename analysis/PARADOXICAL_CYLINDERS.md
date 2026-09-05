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

The selected module builds and expanded 64-declaration audit pass with standard
foundational axioms only. The expanded five-page formal note and two-page guide
in `paper/paradoxical_cylinders*` compile without warnings; all seven pages were
visually checked.

## Proved prefix pruning

`lean/Collatz/ParadoxicalPruning.lean` proves the suffix bound
d(v)≤2^(h-k)*(3^k−2^k), where h is suffix length and k its odd count.
The bound is already present in the literature cited above (Theorem 2.2),
and is proved directly here by induction. For prefix length s and correction D,
composition gives total correction at most

    U_k = 3^k*D + 2^(s+h-k)*(3^k−2^k).

Let m be a lower bound on the possible seed and a the prefix odd count.
When 3^(a+k)<2^(s+h), the strict inequality

    U_k < (2^(s+h)−3^(a+k))*m

excludes every realized completion with that odd count. The Python search
tests every possible suffix count; it uses no unproved monotonicity shortcut.
For each prefix, m is the smallest seed at least three in its residue class.

`paradoxical_pruned.py` performs depth-first residue lifting and applies this
rule. It asserts the affine identity at every visited node and directly
replays each emitted segment. Six unit tests cover the old interval method,
every short suffix bound through length eight, exhaustive comparison through
length fourteen, and correct reporting of an interrupted work-limited search.

The recorded selected-length results in `paradoxical_pruned_results.json` are:

| Length | Visited tree nodes | Full residue count | Segments | Status |
|---|---:|---:|---:|---|
| 8 | 201 | 256 | 5 | Complete |
| 20 | 1,095 | 1,048,576 | 0 | Complete |
| 27 | 38,425 | 134,217,728 | 50 | Complete |
| 32 | 28,443 | 4,294,967,296 | 0 | Complete |
| 40 | 123,887 | 1,099,511,627,776 | 0 | Complete |
| 65 | 2,000,000 | 2^65 | Not determined | Work limit; 21 pending nodes |

These are selected lengths, not all lengths through forty. The completed
searches cover all seeds above two at those lengths. The traversal and larger
counts are tested Python, not Lean-extracted code or kernel-certified census
proofs. The pruning inequality is a Lean theorem. The length-eight census
remains independently proved in Lean.

## What the evidence changes next

Do not duplicate the nested finiteness implication or treat fixed-length
censuses as evidence sufficient for all lengths. The first rigorous pruning
rule is now available and substantially reduces the tested trees. The next
useful target is an independently proved restriction uniform across lengths
or circuit counts, or a formal certificate checker connecting the pruned
traversal to all-seed Lean statements at larger lengths. The length-65 resource
limit is computational, not a mathematical obstruction.
Any proposed rule must preserve the five known length-eight examples and must
not confuse endpoint non-descent with absence of earlier descent.
