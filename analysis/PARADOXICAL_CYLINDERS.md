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

The selected module builds and expanded 72-declaration audit pass with standard
foundational axioms only. The expanded six-page formal note and three-page guide
in `paper/paradoxical_cylinders*` compile without warnings; all nine pages were
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
replays each emitted segment. Nine unit tests cover the old interval method,
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

## Proved limitation and next direction

`lean/Collatz/PruningLimit.lean` proves that every fixed prefix envelope
survives at every target length L ≥ s+2*(a+2*m)+1. The witness k=2*m
has contracting coefficient yet satisfies U_k ≥ (2^L−3^(a+k))*m.
Taking the maximum threshold proves simultaneous survival for any fixed finite
family. The new Python control checks these thresholds on all residue prefixes
through depth seven.

This is a limitation of the relaxed test, not a realizable suffix or a
counterexample to Collatz. A fixed finite tree of these tests cannot close
all sufficiently large lengths. Growing depth and stronger arithmetic remain
possible. The next useful target is compatibility between a suffix's correction
and the seed residue that realizes it, or a separate restriction uniform in
length. Increasing a finite search budget does not supply that theorem.

Do not duplicate the nested finiteness implication or treat fixed-length
censuses as an all-length proof. Any proposed rule must preserve the five
known length-eight examples and distinguish endpoint non-descent from absence
of earlier descent.

## Exact arithmetic compatibility bridge

`Collatz.WordCongruence` now proves, for every natural seed n and Boolean word w,
with L=length(w), A=3^ones(w), D=correction(w):

    Realizes n w ↔ 2^L divides A*n+D.

Endpoint integrality forces every parity, not just the last step. Induction
recovers the first parity modulo two and cancels its factor of two before
applying the same argument to the tail. Combining this with the affine identity
gives the exact joint criterion:

    Realizes n w and IsParadoxical L n
      ↔ 0<n and A<2^L and 2^L divides A*n+D and (2^L-A)*n≤D.

Both declarations pass the selected axiom audit. An independent direct-orbit
control compares both equivalences on every word through length eight and
seeds in two complete residue periods, including zero and the empty word.
This is proof infrastructure, not a new all-length exclusion theorem.

For example, w=00011111 has A=243, D=1688 and modulus 256. Its correction
inequality allows 3≤n≤129, but the congruence forces n≡248 (mod 256), so
none of those seeds realizes it. The actual length-eight example from n=7
has D=347 and does meet both conditions. Discarding residue compatibility
therefore loses essential information even with the exact correction.

The existing paper and guide describe the preceding 66-declaration snapshot.
This arithmetic bridge brings the current audit to 68; no mathematical novelty
or uniform finiteness is claimed for it. The next substantive task remains a
uniform bound on the interaction of correction and realizing residue, rather
than merely enumerating the exact criterion at additional fixed lengths.

The next pass proved a further limitation: the correction envelope plus full
endpoint congruence still admits artificial exact returns for every fixed
positive affine prefix at all sufficiently large lengths. These corrections
need not be attained by any suffix word. See `paper/correction_attainability.md`
and `Collatz.CongruenceRelaxation`. The current selected audit has 69 declarations.

`Collatz.CorrectionDecode` now supplies exact deterministic attainability
checking by reconstructing the word from correction bits and verifying its
odd count and correction. The artificial return example fails this stronger
test. The current audit covers 72 declarations; three additional Python tests
compare reconstruction with exhaustive word sets. This does not bound the
set of successful lengths or corrections. See the updated attainability note.

## Update: completed length-65 census (2026-09-05)

The previous incomplete length-65 record is superseded. Lean now proves
maximal-odd-count envelope monotonicity and its finite seed bound. The search
uses those results to test one count per node and replay short candidate
intervals with exact eight-step residue maps. At length 65 it completes
with 5,324,915 tree nodes and 27,386,515 candidate checks: 244 segments,
seeds 73 through 4547, all with 41 odd steps and earlier descent. There are
no pending branches. Run `python3 analysis/paradoxical_pruned.py --work-limit
20000000` from the root to reproduce the selected lengths. Ten controls pass;
the new bounds are included in the 124-declaration standard-foundations audit.
The fixed-length Python census remains distinct from a kernel-certified
all-seed theorem and supplies no all-length finiteness claim. The technical
paper and guide contain the current method, counts, and verification limits.
