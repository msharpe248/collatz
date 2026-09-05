# Active proof program

Updated 2026-09-05. The Collatz conjecture remains open. This ledger separates
proved family exclusions from the unproved claim that all counterexamples
belong to an excluded family.

## Completed in this research pass

| Direction | Checked result | Scope |
|---|---|---|
| Sturmian itineraries | `Silver.no_itinerary`, `Silver.no_eventual_itinerary` | Slope √2/2, every intercept and natural seed; unconditional |
| Infinite Sturmian family | `Metallic.no_itinerary`, `Metallic.no_eventual_itinerary` | Every integer m≥6, slope 1/(1+(√(m²+4)−m)/2), every intercept and natural seed; unconditional |
| Short rotation windows | `rotation_window_of_neighbors` | Every window of length q+Q from positive bracketing errors ε≤δ; no three-distance theorem |
| General family criterion | `no_itinerary_of_unbounded_neighbors` | Explicit unbounded levels with 6q≤Q≤Cq and fixed C |
| Family geometry | `Metallic.alpha_irrational`, `alpha_strictMono`, `alpha_close_to_one` | Distinct irrational slopes, with 0<1−α_m<1/(m+1) |
| Finite defect certificates | `ParityDefects.few_defects_force_return` | At most D shift disagreements over (2^(D+1)−1)(q+K) comparisons force a q-step return; N+1≤2^K |
| Edited periodic templates | `ParityDefects.near_power_force_return`, `near_power_bound_orbit` | At most e edits, arbitrary positions, explicit exponential horizon; positive period bounds the orbit |
| Period-two convergence | `ParityDefects.few_defects_two_reaches_one`, `near_two_power_reaches_one` | Positive seed plus the finite period-two certificate implies reaching 1 |
| Sharper defect horizons | `sharp_few_defects_force_return`, `sharpCheckpoint_growth`, `sharpCheckpoint_le_old` | Universal ceiling(3u/5)+K height envelope; geometric window factor 8/5 instead of 2, never longer than the original horizon |
| Rotation arithmetic | `sturmian_separation_of_neighbors`, `rotation_window_of_grid` | General certified approximation inputs; no cited axioms |
| Size control | `sturmian_size_at_endpoint` | One endpoint replaces all earlier size tests |
| Block comparisons | `WordAffine.adjacent_swap`, `compare`, `compare_dvd`, `compare_bound` | Exact identities and conditional height obstructions |
| Survivor geometry | `Cylinder.prefix_transport`, `mem_parameters`, `parameters_convex` | Exact finite-height quotient intervals |
| Correct experimental bound | `prefix_power_initial_bound` | Retains the affine correction after shifting an orbit |
| Critical-boundary discipline | `supercritical_of_geometric` | Explicit summable inverse-drift hypothesis, not universal divergence |
| Exact correction characterization | `supercritical_iff_summable_reciprocal` | For every positive seed, bounded ideal correction iff the reciprocal orbit series converges; no density hypothesis |
| Escape consequence | `supercritical_orbit_tendsto_atTop` | Bounded correction forces eventual escape from every finite bound; converse not established |
| Polynomial correction control | `idealC_sixth_bound_of_prefix`, `unbounded_idealC_sixth_bound` | (N+c_T)^6 ≤ N^6(j_T+1); every unbounded positive orbit, without summability or density assumptions |
| Finite drift restriction | `unbounded_nondescent_drift` | 2^(6T) ≤ 3^(6j_T)(j_T+1) at every non-descent time of an unbounded positive orbit |
| Drift escape | `unbounded_prefix_drift_escape` | On every prefix, some drift 3^j_t/2^t is at least (T+1)^(5/6)/N; a running-maximum statement |
| Slow-drift exclusion | `bounded_orbit_of_subcritical_polynomial_drift` | Global rational polynomial drift exponent below 5/6 forces boundedness, not necessarily reaching one |
| Finite drift certificate | `finite_drift_certificate_bounds_orbit` | A finite envelope through T with C*N^(6a)<T+1 and b<5a forces a bounded orbit |
| Paradoxical cylinders | `paradoxical_quotient_interval`, `paradoxical_residue_iff` | Exact fixed-length quotient intervals, no seed cutoff; global finiteness remains open |
| Checked small classification | `paradoxical_eight_iff` | All seeds above two at length eight: exactly 7,9,18,19,25; reproduction, not a new discovery |
| Prefix pruning | `WordAffine.prune_paradoxical_completion` | A suffix correction envelope excludes whole contracting completion classes above a certified seed floor |
| Dependency audit | `audit_theorems.py`, `theorem_audit.json` | Selected declarations, printed types and axioms, pinned library provenance |

See [STURMIAN_SILVER.md](STURMIAN_SILVER.md) for the new theorem's proof.
The [paper](../paper/silver.pdf) and [friendly guide](../paper/silver_guide.pdf)
provide the publication versions. Significant future results should also
receive a paper and guide in `paper/`, following its README.
The subsequent infinite-family result is in
[STURMIAN_METALLIC.md](STURMIAN_METALLIC.md), with its
[paper](../paper/metallic.pdf) and [guide](../paper/metallic_guide.pdf).
The finite near-periodicity extension is in
[PARITY_DEFECTS.md](PARITY_DEFECTS.md), with its
[paper](../paper/defects.pdf) and [guide](../paper/defects_guide.pdf).
The main source modules were rebuilt selectively. This does not mean the
large KL certificates or all nested libraries were rebuilt or independently
kernel-replayed during this pass.

The reciprocal characterization is in [RECIPROCAL.md](RECIPROCAL.md), with
its [paper](../paper/reciprocal.pdf) and [guide](../paper/reciprocal_guide.pdf).
The selected theorem audit now covers 90 declarations using only standard
foundational axioms.
The subsequent correction-growth result is in
[CORRECTION_GROWTH.md](CORRECTION_GROWTH.md), with its
[paper](../paper/correction_growth.pdf) and
[guide](../paper/correction_growth_guide.pdf).

## Experiments and controls

The paradoxical route and library reuse findings are in
[PARADOXICAL_CYLINDERS.md](PARADOXICAL_CYLINDERS.md). The exact Python census
through length 20 has no seed cutoff and finds only the five length-eight
segments. All have earlier descent. Only the length-eight classification is
kernel-proved; the broader census is tested Python. This does not establish
finiteness across all lengths. The source theorem reducing global finiteness
to Collatz is already present in the nested RT project and was not re-audited
in this pass.

The new proved suffix envelope supports `paradoxical_pruned.py`: selected
lengths 27 and 40 complete in 38,425 and 123,887 tree nodes, respectively,
finding 50 and zero segments. The length-65 run is explicitly incomplete at
two million nodes. These are tested Python censuses using a Lean-proved
pruning rule, not kernel-certified larger-length classifications. No
all-length cutoff is established.

`sturmian_prefix_power.py` now produces exact integer excluded-height
certificates, using the correction term in `prefix_power_initial_bound`.
Its finite mechanical words use rational arithmetic; floating-point inputs
are rejected. Finite continued-fraction approximants are labeled as such.
The old numerical slope labels contained inaccuracies and have been replaced
by the computed values. No finite experiment is called an all-intercepts proof.

`survivor_cylinders.py` intersects affine inequalities in one quotient.
At height 4096 and depth 12, it found 227 survivors including 1. Every
survivor above 1 descended within the 1000-step follow-up limit; the largest
observed stopping time was 81 Terras steps (seeds 703 and 1407). This is a
small control experiment, not a new computational Collatz verification record.

`mahler_certificate_search.py` explores constant-weight substitutions,
checks finite functional-equation coefficients, and screens exact Padé
candidates by their dominant height/valuation exponents. The output
[mahler_candidates.json](mahler_candidates.json) includes the existing
`0→011, 1→110` example and `0→011, 1→101`. For the latter, the degree-two
form `1+(-1+z²)F(z)` has observed leading term `−z⁵` and passes the strict
integer exponent comparison. This is an experimental candidate, not a new
Lean irrationality theorem. Generalized infinite transport, nonvanishing,
and height-certificate proofs remain to be supplied.

`test_research_certificates.py` compares the certificate arithmetic with
direct Terras trajectories, checks survivor intervals against enumeration,
checks swap identities, and replays the finite Mahler candidates.

## Missing mathematical bridges

1. **Other Sturmian slopes.** The short-window argument and an explicit
   recurrence now exclude an infinite family accumulating at slope 1.
   This is not all slopes or an interval of slopes. The conservative
   sixfold criterion leaves parameters 3–5 and broader continued-fraction
   families outside the new theorem.
2. **Useful defect bounds.** A finite near-periodicity class is now excluded
   from unbounded orbits, using disjoint windows instead of raw swap costs.
   The sufficient horizon is exponential in the disagreement or edit
   count. A universal 3/5-bit height bound has now reduced the geometric
   window factor from 2 to 8/5. No independent universal sparsity bound
   is proved; that coverage step remains open.
3. **Ordinary integer coverage.** Prove an independently meaningful
   restriction forcing every counterexample into an excluded class. No
   complexity-versus-defect dichotomy has been established.
4. **Critical-boundary orbits.** Bounded ideal correction is not known for
   every hypothetical divergent orbit. It is now proved equivalent to
   summability of reciprocal orbit values. An escaping orbit with divergent
   reciprocal sum is the precise remaining coverage case. The residue-based
   tenth-root bound improves the tail drift threshold to 9/10, with finite
   and global conditional boundedness theorems for seeds not divisible by
   three. Every positive orbit eventually satisfies that residue restriction.
   This does not exclude faster drift or all critical-density orbits, and does
   not make correction bounded in the remaining case. Even a proof of
   coverage would not itself exclude bounded-correction orbits.
5. **Survivor exhaustion.** Exact interval computation is not a termination
   proof. Universal finite-height exhaustion is equivalent to universal
   descent; using it as a completeness assumption would be circular.
6. **Cycles.** The new itinerary exclusions do not prove that all nontrivial
   cycles are absent. Existing finite/class-specific cycle exclusions remain
   the cycle track's current boundary.
7. **Imported dependencies.** Selected external modules contain cited or
   unfinished axioms. Port and audit precise declarations before using them
   in an unconditional theorem; preserve map-convention bridges.

KL exponent improvements remain a separate density-results track. The
rotation-family, finite defect, and universal height refinements are now
proved. The next proof-focused priority is an independent restriction on
possible integer counterexample itineraries. Improved sufficient horizons
do not establish that every counterexample must meet their sparsity bounds.

## Limitation of fixed prefix envelope pruning

`Collatz.PruningLimit` proves that each relaxed prefix test survives every
length L ≥ s+2*(a+2*m)+1, using odd-count witness k=2*m. Any fixed finite
family therefore survives simultaneously at all sufficiently large lengths.
This rules out uniform closure by a fixed finite tree of these tests alone;
it constructs no realizable orbit. The next arithmetic target is the joint
constraint on suffix correction and its realizing seed residue. The theorem
and finite-family consequence are included in the 66-declaration audit and
documented in `paper/paradoxical_cylinders*`.

The subsequent `Collatz.WordCongruence` bridge proves that affine endpoint
integrality is equivalent to realizing the complete parity word, and combines
it with the correction inequality into an exact paradoxical-word criterion.
These two declarations bring the current audit to 68. This preserves the
arithmetic omitted by the envelope but does not yet bound it uniformly.
See `analysis/PARADOXICAL_CYLINDERS.md` for the statement and a false-candidate
example eliminated by the congruence.

## Correction attainability boundary

`Collatz.WordAffine.relaxed_closing_correction` in module
`Collatz.CongruenceRelaxation` proves that an arbitrary
correction inside the suffix envelope can satisfy an artificial exact return
at every sufficiently large target length for any fixed positive affine prefix.
The construction supplies no actual suffix word. Endpoint congruence therefore
cannot by itself repair the envelope relaxation. Additional orbit constraints
are not ruled out. The next target must control attainable corrections as both
length and odd count grow. The 69-declaration audit includes this result;
`paper/correction_attainability.md` and its guide document it.

The subsequent `Collatz.CorrectionDecode` module reconstructs a word from its
length, odd count, and correction, then checks the reconstructed data exactly.
It proves attainability equivalence, uniqueness, and the complete joint
paradoxical criterion. Kernel controls reject the artificial (16,6,194421)
correction and accept the genuine (8,5,347) correction. The current selected
audit has 72 declarations. This is infrastructure; no new uniform exclusion
is established. The companion paper and guide were updated accordingly.

## Residue-based ninth-power correction bound

`Collatz.ResidueCorrection` uses eventual avoidance of multiples of three to
rank the distinct odd values of an escaping orbit more tightly. The finite
prefix theorem assumes a positive seed not divisible by three, no repetition,
and avoidance of one, and gives (N+c_T)^9 ≤ N^9(2j_T+1). Every unbounded positive
orbit has a tail obeying this at all lengths; no density or summability
assumption is needed for that necessary condition.

The resulting tail drift excursion exponent improves from 5/6 to 8/9.
A finite rational polynomial drift certificate below 8/9 forces boundedness
for a seed not divisible by three, with threshold 2^a*C*(N^9)^a < T+1.
The global-envelope corollary is also proved. No such envelope is asserted
for all orbits, and boundedness still leaves the nontrivial-cycle question.
Five new audit targets bring the selected total to 77. The paper and guide
are `paper/residue_correction.md` and `paper/residue_correction_guide.md`.

## Finite-history support and joint orbit exclusions

`Collatz.OddPrehistory` proves that every positive odd target not divisible
by three has genuine histories with any prescribed number K of odd steps,
starting at seeds at least y+K and using between 3K and 6K shortcut steps.
This prevents deleting further individual targets solely from a fixed finite
history requirement; it does not address restrictions specific to divergence.

It also proves that an unbounded orbit cannot contain both odd n and 4n+1.
Their paths merge, contradicting injectivity at incompatible times. This is
joint information beyond residue exclusion. The weighted
set bound proposed here is now proved in `Collatz.SiblingCorrection`: compression
replaces occupied children congruent to 5 modulo 24 by their absent parents.
Injectivity, weight domination, and rank control yield the tenth-power bound.
The selected audit has 79 declarations. The new paper and guide are
`paper/odd_histories_and_collisions*`.

## Tenth-power bound from sibling exclusion

`Collatz.SiblingCorrection` completes the weighted argument. A finite set of
odd values above five, outside multiples of three and containing no sibling
pair, satisfies the tenth-power product bound ≤2*card+1. Every unbounded
positive orbit has a tail with (M+c_T)^10 ≤ M^10(2j_T+1), improving the ninth
bound with the same right-hand factor. Tail drift excursions have exponent
9/10, with finite and global conditional boundedness criteria below 9/10.
Five new audit targets bring the total to 84. The paper and guide are
`paper/sibling_correction*`.

The pair argument preserves relations between values rather than merely
excluding individual residues. Broader merging-path classes are a possible
next source of restrictions. However, exponent refinements alone do not
supply a universal upper drift envelope or eliminate nontrivial cycles;
those coverage gaps remain the decisive requirements for Collatz.

## Bounded-correction coverage review

`Collatz.IdealBarrier` proves c_infinity(n)>1 for every positive seed with
bounded ideal correction. Every tail has the same strict lower bound, and
some tail exceeds two. Hence UniformSupercritical n B implies B>2, and the
canonical geometric ideal lies more than one above the actual orbit value.
These are lower barriers, not an inferred upper bound or confinement result.

The nested Z32 source review concerns fractional parts of fixed (p/q)^k
progressions. Applying it here needs both a transport from the variable
3^j_t/2^t clock and a proved fractional confinement hypothesis. Neither is
supplied by Supercritical or the tracking identity. The barrier does not
exclude fractional confinement in a translated window, nor show that shifted
corrections are unbounded. Nested sources were not compiled or audited here.
Three new targets bring the current audit to 87. The paper and guide are
`paper/ideal_tracking_barrier*`. A proof of that missing transport and
confinement, or another unconditional exclusion of bounded-correction
positive orbits, remains a central coverage target.

## General parity complexity obstruction

`Collatz.ParityComplexity` formalizes the state-congruence/height argument:
if N+1≤2^K, every unbounded orbit has at least 5q+1 parity factors of length
3q+K. A uniform factor-complexity slope below 5/3 forces boundedness. Since
bounded orbits have bounded factor complexity, no natural seed or shifted
seed satisfies the Sturmian condition p(L)=L+1 for every L.

This closes the abstract Sturmian complexity class, beyond the earlier
individual rotation-family exclusions. It does not yet port the equivalence
between `mech alpha rho` and the factor-complexity definition, so no new
all-slopes mechanical-word Lean statement is claimed. The next concrete
transport task is the mechanical-word factor upper bound, together with
irrational-slope aperiodicity. No universal low-complexity coverage statement
for Collatz counterexamples is available.

Dubickas (2009), Theorem 5, already proves a stronger asymptotic Collatz-word
complexity lower bound. This is a main-project formalization and consequence,
not a mathematical novelty claim. Three new targets bring the selected audit
to 90. Paper and guide: `paper/parity_complexity*`.
