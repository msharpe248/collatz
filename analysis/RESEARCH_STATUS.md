# Active proof program

Updated 2026-09-05. The Collatz conjecture remains open. This ledger separates
proved family exclusions from the unproved claim that all counterexamples
belong to an excluded family.

Latest literature check: `analysis/SEED_DEPENDENT_ROUTE_REVIEW.md` records
why the Rozier–Terracol Section 6 delay-bound chain is conditional and
cannot supply the missing convergence premise. The nested predicate
explicitly contains reach-one, its existence declaration has `sorry`,
and the Rhin estimate is a cited axiom. No such premise was imported.
The newer Niu note was withdrawn for duplication. This review adds no
new theorem. Subsequent work is recorded below and in the current theorem audit.

Recent additions: the auxiliary bridge is formalized in `AffineBridge` (commit
947cc1c). Subsequent source-witness, exponent-return, and cycle-bridge experiments
remain conditional and do not close coverage. `RESIDUE_PRECISION_REVIEW.md` now
records five kernel-checked precision/count findings for a proposed literature
input; the selected declaration audit now contains 228 entries. The new `BridgeGrowth`
bound rules out lowering cycle charge through arbitrary forward bridge
interleavings and justifies pruning those states in the affine bridge search.
`InverseCycleBridge` now verifies a signed 2 <- 47 -> 425 -> 2 excursion
with charge change -7. Its all-quotient transfer premise is explicit. The
constructor handles every tested base parameter 16..1000, but still needs
base-target convergence and therefore does not prove global coverage. See
`paper/inverse_cycle_bridge.tex` and its companion guide.
The subsequent `CycleCylinderBoundary.no_smaller_cycle_base` theorem rules out
bootstrapping any parameter 2^k-1 from a proper smaller canonical base whose
target reaches the cycle by the binary depth. This is an all-depth obstruction
to that particular coverage argument, not to Collatz. Further cycle-certificate
censuses do not remove it; see `paper/cycle_cylinder_boundary.tex`.
`EarlyInverseBridge` now supplies the conditional early step 59+192Q ->39+128Q,
with no target-cycle premise. Its general predecessor template only treats
u=2 mod 3. The complete depth-12 census covers 407/4096 w-residues in u=3w+2;
other parameter classes and global coverage remain open. See
`paper/early_inverse_bridge.tex`.

## Completed in this research pass

| Direction | Checked result | Scope |
|---|---|---|
| Affine-pair induction certificates | `AffineTransfer.merge_36`, `affine_pair_return_2308`, `AffineTransfer.return_2308` | Direct transfer on 36+64Q; conditional reduction from 2308+4096Q to smaller 45+81Q. Both all-quotient families are kernel checked; global rule coverage unproved |
| Affine-transfer scope check | `collatz_iff_restricted_affine_transfer`, `all_bounded_iff_restricted_affine_transfer` | Transfer z to 9z+2 on z=2 mod 3 is equivalent to full Collatz when using reach-one, or to nondivergence when using boundedness; transfer premises remain unproved |
| Classical odd-run merge applicability | `garner_merge_iff`, `single_even_exit_pair`, `least_unbounded_odd_run_exit` | Any run length: a double-even exit merges n with n-1; the single-even exit gives endpoint pair 9z+2 and z. Garner/LaDue identities, not new universal coverage |
| Fixed-table coverage obstruction | `MergeRuleObstruction.only_inverse_odd`, `no_rule_on_initial_class` | Kernel-checked congruence classification; written arbitrary-horizon construction permits only retracing odd runs. Does not exclude new rules or seed-dependent horizons |
| Quantitative merge chains | `CoefficientBound.merge`, `NeverContracts.smaller_merge_chain_447` | Exact coefficient-deficit transport after shifting; a three-rule chain excludes the progression 447 + 549755813888Q from least positive NC seeds; no universal coverage |
| Certified merge progressions | `MergeRuleTable.rules_valid`, `MergeRule.sound` | 360 kernel-checked rules apply to every natural quotient, conditional on noncontraction |
| NC-prefix injectivity | `NCPrefixInjective.equal_count_injective_31` | Equal endpoint and odd count force equal seeds when both prefixes are NC and time is at most 31; interval bound fails at 32, not an injectivity counterexample |
| Growing consecutive returns | `arbitrarily_many_growing_returns` | For each finite R, a positive seed has R consecutive growing four-step returns to two modulo nine; different seed for each R, no infinite escape |
| Sampled nondivergence equivalence | `all_bounded_iff_sampled_contraction` | Nondivergence is equivalent to universal contraction at residue-two visits; exact coverage by sampled-noncontracting tails, not full NeverContracts |
| Contracting residue returns | `even_steps_between_two_mod_nine`, `contracting_two_mod_nine_segment_descends` | At most six even steps between visits; contracting first returns have sharp length bound sixteen and strictly descend for every seed above two; eventual contraction remains open |
| Forward residue coverage | `exists_two_mod_nine`, `arbitrarily_late_two_mod_nine` | Every positive orbit visits two modulo nine arbitrarily late; formalization of Monks et al., no noncontraction property at the selected visit |
| Inverse-search obstruction | `bounded_odd_inverse_obstruction`, `arbitrarily_large_inverse_obstructions` | Every fixed odd-step budget leaves the class 1 modulo 3^K without a noncontracting predecessor segment; total length unrestricted, no noncontracting target asserted |
| Noncontracting tails | `unbounded_iff_noncontracting_tail`, `all_orbits_bounded_iff_all_contract` | Exact reduction of nondivergence to universal coefficient contraction; arbitrarily late noncontracting tails cover every hypothetical unbounded positive orbit |
| First contraction | `first_contraction_seed_bound`, `descent_of_contraction_le65`, `return_le65_reaches_one` | Sharper seed bound at any first contraction; coefficient contraction by time 65 implies descent for every seed above one; positive returns of length at most 65 reach one |
| Universal correction coverage | `unbounded_orbit_reciprocal_summable`, `supercritical_iff_unbounded_orbit` | All unbounded positive natural orbits have summable reciprocals and bounded correction; no escape exclusion |
| Full mechanical classification | `mechanical_classification`, `eventual_mechanical_reaches_one` | All real slopes and intercepts; positive global seed is 1 or 2 with slope 1/2; any mechanical tail forces reaching one |
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
| Escape consequence | `supercritical_orbit_tendsto_atTop`, `unbounded_orbit_supercritical` | Bounded correction forces eventual escape; unboundedness now implies bounded correction as well |
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
The selected theorem audit now covers 160 declarations using only standard
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

The proved suffix envelope supports `paradoxical_pruned.py`. Maximal-count
monotonicity and early resolution of finite seed intervals now reduce
lengths 27 and 40 to 955 and 2,889 tree nodes, respectively, finding 50 and
zero segments. The length-65 census is now complete: 5,324,915 tree nodes
and 27,386,515 direct candidate checks find 244 segments, all with earlier
descent. These are tested Python censuses using Lean-proved bounds, not
kernel-certified larger-length classifications. No all-length cutoff is
established. Earlier incomplete length-65 records below are historical.

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

1. **Mechanical branch completed.** `mechanical_classification` now proves
   that a positive natural seed with any globally mechanical itinerary has
   slope 1/2 and seed 1 or 2. Any mechanical tail forces reaching one.
   Irrational, rational, arbitrary-intercept, and nonprimitive cases are
   covered. Further slope-specific exclusions are not a coverage priority.
2. **Useful defect bounds.** A finite near-periodicity class is now excluded
   from unbounded orbits, using disjoint windows instead of raw swap costs.
   The sufficient horizon is exponential in the disagreement or edit
   count. A universal 3/5-bit height bound has now reduced the geometric
   window factor from 2 to 8/5. No independent universal sparsity bound
   is proved; that coverage step remains open.
3. **Ordinary integer coverage.** Prove an independently meaningful
   restriction forcing every counterexample into an excluded class. No
   complexity-versus-defect dichotomy has been established.
4. **Correction coverage completed.** `OrbitSummability` now proves that
   EVERY unbounded positive natural orbit has summable reciprocals and
   bounded ideal correction. This follows from an explicit finite packing
   argument, not a strict density gap or imported density axiom. The inverse
   drift 2^t/3^j tends to zero. What remains is to exclude the bounded-correction
   unbounded orbits themselves. No uniform absolute bound across all shifted
   corrections is supplied. Nontrivial cycles remain separate.
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


## Full mechanical-word bridge (2026-09-05)

The transport task above is now complete in `Collatz.MechanicalComplexity`.
`mechanical_complexity_le` proves p(L) <= L+1 directly by ordered floor
thresholds, for any real slope and intercept satisfying HasItin. This forces
boundedness. A repeated state gives a return, and `mechanical_return_slope`
proves q*alpha = oddSteps q N by telescoping at every multiple of the period.
Thus `no_irrational_mechanical` and `no_eventual_irrational_mechanical` exclude
ALL irrational slopes and intercepts for all natural seeds and tails.
The previous statement that this bridge was unported is historical.

This is a classical class exclusion formalized in the main project, not a
new proof of Collatz. Rational mechanical slopes yield boundedness without
cycle identification. No complexity envelope for arbitrary itineraries is
provided. Further slope-specific exclusion work is no longer needed to
establish irrational mechanical coverage; the next research target should
address general counterexample coverage or rational/balanced cycle structure.

Five new declarations bring the selected audit to 95. Paper and guide:
`paper/mechanical_complexity.pdf`, `paper/mechanical_complexity_guide.pdf`
(with editable LaTeX).


## Endpoint-swapped cycle words (2026-09-05)

`Collatz.EndpointCycles` connects Knight's high-cycle cancellation idea to
actual natural orbit returns. For every Boolean middle u, if 1u0 and 0u1
are realized at returning seeds x and y, then u=[] and x=1,y=2. No palindrome,
coprimality, or common-orbit assumption is needed. The single-orbit shift
corollary is also checked. Three declarations bring the selected audit to 98.

Three exact finite controls pass: all middles of lengths 0..12; endpoint-pair
rotation witnesses for reduced mechanical slopes 0<p<q<=80; and a negative
coverage control, word 11100 (rational cyclic value 19/5). No universal
mechanical rotation bridge is inferred from these tests. That bridge, period
reduction, and eventual-tail transport remain the next concrete tasks.
No general cycle or escape exclusion follows.

Provenance: nested tcosmo__Knight2026_lean/Knight2026/NoHighCycles.lean,
with fresh arithmetic proof in the main definitions. No nested module or
custom axiom imported. The publisher gives Knight's article as 114812,
DOI 10.1016/j.disc.2025.114812; the nested summary's article 114425 and
HAL-04206985v3 are incorrect (challenge catalog links HAL-04261183).
Paper and guide: paper/endpoint_cycles.pdf and paper/endpoint_cycles_guide.pdf.


## Mechanical branch completed (2026-09-05)

`MechanicalPeriod` transports rational periods to actual returns and arbitrary
word rotations to shifted orbit states. `RationalGrid` proves coprime phase
surjectivity and the endpoint-swapped extreme words uniformly for every
0<p<q. `RationalMechanical` identifies every real intercept with its exact
finite grid phase. Gcd reduction handles nonprimitive rational presentations.

`mechanical_reaches_one`: positive natural seed plus HasItin, with arbitrary
real slope/intercept, reaches one. `mechanical_classification` strengthens
this to alpha=1/2 and N=1 or N=2. `eventual_mechanical_reaches_one` lifts the
result from any tail. The rotation/intercept gaps recorded in the preceding
historical entries are now closed. No universal mechanical-tail hypothesis
is proved or assumed for arbitrary positive seeds. Such coverage would itself
settle Collatz; do not replace the requested conjecture with this class result.

Nine declarations bring the selected audit to 107; main Lean build and four
exact regression controls pass. Paper and guide: mechanical_classification.pdf
and mechanical_classification_guide.pdf under paper/, with LaTeX sources.
Next research priority: independent restrictions on general counterexamples,
or a general descent/cycle argument outside the completed mechanical class.


## Universal orbit packing and correction coverage (2026-09-05)

`Collatz.packing_bound` (in module OrbitPacking) proves
8^m card(S) <= 2*216^m+243^m for every finite S below 32^m on which T^(5m)
is injective. Every unbounded orbit is coalescence-free at every fixed time,
so the bound applies to all its finite subsets, including late orbit values.
The two bounds are the small image for odd count <3m and the binomial tail
for count >=3m. Both come from the main project's existing theorems.

`OrbitSummability` sums reciprocal values over geometric shells. The budget
is 54*(27/32)^m + (243/8)*(243/256)^m. Time injectivity preserves multiplicities
when replacing a finite orbit prefix by its value set. Thus EVERY unbounded
positive orbit has summable reciprocals and bounded ideal correction.
`supercritical_iff_unbounded_orbit` proves the exact positive-seed equivalence;
`unbounded_inverse_drift_tendsto_zero` gives the inverse-drift limit.

This supersedes earlier claims in this ledger and correction papers that an
unbounded orbit with divergent reciprocal sum was an unresolved coverage case.
The critical density floor alone still does not prove summability; the new
packing argument supplies the missing independent input. No strict density
gap or uniform absolute bound on every shifted ideal correction follows.
All hypothetical unbounded positive orbits are now in the existing ideal
framework; exclusion within that framework and general cycles remain open.

Provenance: Garcia–Tal 1999, DOI 10.4064/aa-90-3-245-250, equation (6) and
Corollary 1 support the literature implication highlighted in MathOverflow
question 513539. The original paper was checked in full. The Lean proof uses
an independent explicit origin-based packing specialization and imports no
external density axiom. No mathematical novelty claim.
Six declarations bring the audit to 113; three exact controls pass.
Paper and guide: paper/orbit_summability.pdf and paper/orbit_summability_guide.pdf.

## Relative tail correction (2026-09-05)

`RelativeCorrection.lean` adds a direct corollary of universal summability:
for every unbounded positive orbit, the ratio of the shifted limiting
correction to the current orbit value tends to zero. The exact identity is
`c_infinity(n_t)/n_t = (c_infinity(N)-c_t(N))/(N+c_t(N))`.
The numerator tends to zero and the denominator has a positive limit.
Both declarations are included in the selected theorem audit.

This is a routine consequence, not a new exclusion theorem. It does not
imply bounded absolute correction or rounding of the ideal to the orbit:
`IdealBarrier.one_lt_idealLimit` still puts the absolute correction above
one at every shift. An arithmetic contradiction requires additional input.

## Explicit value tails and correction envelope (2026-09-05)

`OrbitSummability.lean` now proves a uniform reciprocal bound for any finite
set of unbounded-orbit values above `32^K`, with no restriction on their
occurrence times. Its explicit budget is
`B_K = (1728/5)(27/32)^K + (7776/13)(243/256)^K`, and tends to zero.
The finite proof telescopes shell budgets, retaining the sharper remainder
`B_K - B_(K+d)` below the upper endpoint `32^(K+d)`.

If an unbounded positive orbit stays above `32^K` at every time, its full
reciprocal series is at most `B_K` and
`idealLimit N <= N * (exp B_K - 1)`. The all-times lower bound is explicit
in both theorem statements; the starting value alone is insufficient.

The attempted rounding route still fails: Lean also proves
`32^K * (exp B_K - 1) >= (1728/5) * 27^K`.
This concerns the upper envelope, not the actual correction. The estimate
therefore cannot provide an absolute error below one, even at the smallest
allowed seed. Further arithmetic input, rather than this envelope alone,
is needed to exclude escape. General cycles remain unresolved as well.

Five new audit targets bring the total to 120. The Lean build and audit
pass with standard foundations only; the three existing exact packing
controls pass. The summability paper and guide include these results and
the previous relative-correction identity.

## Maximal-count pruning and completed length 65 (2026-09-05)

Four new theorems in `ParadoxicalPruning.lean` prove that the completion
correction envelope increases with the allowed suffix odd count, that only
the largest admissible count needs testing, and that every paradoxical
completion lies below the resulting finite seed bound. The Python search
precomputes these tests and resolves a prefix class directly when its
remaining quotient interval has at most sixteen candidates. Exact
8-step affine residue lookups accelerate replay; successes are also replayed
one step at a time. This preserves the all-seed scope at each fixed length.

The length-65 result replaces the former incomplete census: 244 segments,
seeds 73 through 4547, all with 41 odd steps and an earlier descent. The
search visits 5,324,915 nodes, resolves 2,662,431 candidate intervals, checks
27,386,515 seeds, and has zero pending nodes. The earlier all-count run
extended to twenty million nodes was still incomplete; an intermediate
individual-step replay run was interrupted for performance and supplied no
census result. The final run uses the tested block replay implementation.

Ten Python tests pass, including agreement with exhaustive small searches,
the old all-count rule, enabled/disabled interval resolution, and a separate
individual-step scan below 65,536 reproducing all 244 witnesses. That last
scan verifies only its finite slice; absence of higher seeds depends on the
complete pruned traversal. The Lean build and 124-declaration audit pass
with standard foundations only. The traversal is not Lean-extracted, and
its complete larger-length census is not a kernel-certified enumeration.
The paper and guide in `paper/paradoxical_cylinders.*` are updated.

Historical arithmetic lead, now completed below: at a *first* coefficient contraction, all preceding
inverse drifts are at most one, so the correction increments suggest
`3*c_T <= oddSteps T N`. Combined with a paradoxical endpoint, this would
bound the seed far more sharply than the unrestricted envelope. This is
not yet formalized here. It concerns first coefficient crossings, whereas
the 244 length-65 examples allow earlier coefficient crossings/descent.
It would still require an all-length argument to prove Collatz.

## First contraction and kernel-checked descent through 65 (2026-09-05)

`FirstContraction.lean` proves the proposed all-time conditional correction
bound: if `2^s <= 3^(oddSteps s N)` for every `s<T`, then
`3*dcoef T N <= oddSteps T N * 3^(oddSteps T N)`.
At a contracting, non-descending endpoint this implies
`3*(2^T-3^j)*N <= j*3^j`, where `j=oddSteps T N`.
Seeds above that bound descend at the endpoint.

For `T<=65`, a kernel-decided table bounds every such seed by 1185 (the
largest integer bound occurs at T=65, j=41). A recursive Boolean checker
accepts descent immediately and otherwise requires noncontraction at every
visited time through its horizon. Its general soundness theorem and a
second kernel-decided table cover all seeds 2 through 1185. No native-decide
axiom, custom axiom, or sorry is used.

The resulting theorem `descent_of_contraction_le65` covers every natural
seed above one: any coefficient contraction within 65 steps implies actual
descent at or before that time. It does not assume every seed contracts
within the horizon. Strong induction on a returning seed, using the existing
strict cycle coefficient inequality, gives `return_le65_reaches_one`.
Every positive return of length at most 65 reaches one.

This kernel theorem now explains the earlier-descent property in the
length-65 census for every possible seed, without kernel-certifying the
244-element census list. The generic seed bound has no time cutoff, but
the finite tables do. Later contraction times, orbits with no contraction,
and longer nontrivial cycles remain open. No priority or cycle-bound record
claim is made. Seven targets bring the standard-foundations audit to 131;
the selected build passes. Paper and guide: `paper/first_contraction.*`
and `paper/first_contraction_guide.*`.

## Exact reduction to noncontracting tails (2026-09-05)

`NoncontractingTail.lean` defines `NeverContracts N` as the infinite
condition `forall t, 2^t <= 3^(oddSteps t N)`. On every unbounded positive
orbit the inverse drift tends to zero and starts at one, so it attains a
global maximum. The multiplicative cocycle shows that the seed at this
maximum is noncontracting. Applying the construction to each shifted orbit
gives such tails beyond every prescribed time, not at every late index.

Conversely, a positive noncontracting seed is unbounded: if its values were
bounded by B, the exact correction identity would give `idealC t N <= B`.
Bounded correction forces escape, contradicting the value bound.
Thus `unbounded_iff_noncontracting_tail` is a genuine orbit-level
biconditional. The global `all_orbits_bounded_iff_all_contract` equates
nondivergence with the existence of a coefficient contraction for every
positive seed. Neither side is established. Nontrivial cycles are not
excluded by this equivalence.

Backward arithmetic begins with `neverContracts_of_prefix`: a finite
prefix with all coefficients at least one, followed by a noncontracting
tail, preserves the property. In particular an odd predecessor does so.
Every noncontracting seed is odd, and a seed N congruent to 2 modulo 3
has the smaller positive odd noncontracting predecessor `(2*N-1)/3`.
Consequently a least positive noncontracting seed cannot be 2 modulo 3.
This is a restriction on a least seed, not an exclusion of that residue
on arbitrary orbits. Residues 0 and 1 remain unresolved.

The module build and selected 139-declaration standard-foundations audit
pass. Eight new targets cover the reduction and backward transport.
Paper and guide: `paper/noncontracting_tails.*` and
`paper/noncontracting_tails_guide.*`. No mathematical priority claim.

The next arithmetic task is to exclude the positive `NeverContracts`
class, now proved to cover all escape. A finite-horizon certificate alone
cannot do that. Backward transport may restrict a least seed further, but
there is no current proof that every remaining residue has a smaller
admissible predecessor. In particular, a residue reduction must preserve
the full noncontraction property; merely finding a merging predecessor
or an unbounded seed in an arithmetic progression would not suffice.

## Fixed odd-step inverse coverage is obstructed (2026-09-05)

`InverseBarrier.lean` proves the sharper canonical-residue endpoint bound
`terras_iter t r < 3^(oddSteps t r)` for every `r < 2^t`. Binary residue
lifting gives an intermediate endpoint below twice the ternary scale; the
next even or odd step preserves the strict bound at its new odd count.
This strengthens the factor-two bound previously sufficient for packing,
without changing that earlier valid argument.

For any positive-length segment with `2^t <= 3^j`, the endpoint cannot be
one modulo `3^j`. Otherwise canonical reduction would give endpoint one;
the exact affine identity forces the canonical seed to be one, and the
strict cycle coefficient inequality contradicts noncontraction.

Consequently if `y = 1 mod 3^K`, any segment ending at y with at most K odd
steps must have a contracting final coefficient, however many even steps
it contains. Thus no `NeverContracts` predecessor reaches y within that
odd-step budget. The targets `1+3^(K+1)*(B+1)` provide arbitrarily large
obstructions outside multiples of three. They are NOT asserted to satisfy
`NeverContracts`, and their convergence is not decided by this theorem.

This rules out uniform fixed-odd-budget predecessor coverage of this
residue class as a standalone least-seed exclusion. It does not rule out
target-dependent budgets or a separate exclusion of the remaining class.
The explicit boundary example `3 -> 5 -> 8 -> 4` has two odd steps and
coefficient 9/8, illustrating why a one-odd-step restriction cannot simply
be dropped from the finite-segment conclusion. The theorem also requires
positive total length, excluding identity segments.

Five new targets bring the selected audit to 144, with standard foundations
only; the Lean build passes. Paper and guide: `paper/inverse_barrier.*` and
`paper/inverse_barrier_guide.*`. No priority claim. The previous plan to
extend fixed-budget inverse residue coverage must account for this exact
unresolved class. Full exclusion of positive noncontracting seeds and
nontrivial cycles remains open.


## Forward residue coverage and the selection gap (2026-09-05)

`ResidueCoverage.lean` formalizes Monks et al., arXiv:1204.3904v2,
Corollary 5.8: every positive natural orbit visits two modulo nine.
Applying the theorem to any tail gives visits beyond any prescribed time.
The proof combines the exact six-vertex residue graph outside multiples
of three with the existing parity-injectivity proof that every natural
orbit has an even value (`IdealBarrier.exists_even_value`, now public).
No literature axiom is imported. The convergence reduction
`reaches_one_of_two_mod_nine` leaves convergence on that progression as
an explicit unproved premise.

This resolves the factual coverage question, but does not close the
proposed connection to noncontracting tails. Coverage and noncontracting
tail selection produce different existential witnesses; no theorem says
that a residue-two visit is also a noncontracting starting point.
Consequently the least-noncontracting-seed restriction cannot be combined
with coverage to claim a contradiction. The next useful target must
control both the arithmetic residue and inverse-drift maxima, or replace
that selection argument with a different invariant. Merely adding more
strongly sufficient progressions does not supply this missing property.

Primary source: https://arxiv.org/abs/1204.3904, Corollary 5.8.
Paper and guide: `paper/residue_coverage.*` and
`paper/residue_coverage_guide.*`. This is a known result formalized here,
not a mathematical priority claim or a proof of Collatz.

The module build and expanded 148-declaration audit pass using only
standard foundations. Both one-page PDFs were rendered and visually checked.


## Contracting first returns have a sharp finite bound (2026-09-05)

The next-return graph on two modulo nine does have growing branches:
11 -> 17 -> 26 -> 13 -> 20. So return coverage alone is not descent.
However `ResidueCoverage.lean` now proves at most six even steps occur
before the next visit. A potential on the other allowed residues takes
values H(1)=5, H(5)=4, H(7)=3, H(8)=2, H(4)=1. An even step lowers it
by at least one; odd steps do not increase it. The first step accounts
for the sixth possible even step. This permits arbitrarily long odd runs.

If the coefficient contracts, j odd steps and t total steps satisfy
3^j < 2^t and t <= j+6. Since 3^11 > 64*2^11 and the inequality persists
for larger j, necessarily j <= 10 and t <= 16. The bound is attained by
the actual first return from 147440 to 132860, with ten odd and six even
steps, including a kernel check of all intermediate residues.

More strongly, `contracting_two_mod_nine_segment_descends` proves that
all such contracting segments strictly descend when n>2. For n>=573,
the exact growth inequality and a finite arithmetic table through length
sixteen prove descent. The remaining n<573 are checked by an ordinary
Lean `decide` table using the actual avoidance and coefficient hypotheses.
The final theorem has no seed-height or time cutoff in its assumptions.
It applies even when the endpoint has not yet returned to residue two.
The exceptional seed two has the contracting return 2 -> 1 -> 2.

This controls contracting branches of the induced map, not whether an
orbit eventually takes one or whether repeated growing returns are
impossible. It does not close the noncontracting-tail selection gap.
The paper and guide `paper/residue_coverage.*` and its companion are
updated; no mathematical priority claim is made.

Verification: the full selected build passes (7829 jobs); all 152 audited
declarations use standard foundations only. The revised two-page paper
and one-page guide were rendered and visually checked.


## Multiple-return test: unrestricted extension rejected (2026-09-05)

The proposed extension of first-return descent to arbitrary later
residue-two visits is false. `later_two_mod_nine_visit_can_be_paradoxical`
checks T^46(470)=479, j=29, and 3^29<2^46, with both endpoints two modulo
nine. The same proof checks the earlier visit T^2(470)=353<470. Thus this
is not a counterexample to descent at the first cumulative coefficient
contraction observed at a visit.

`analysis/residue_return_stopping.py` tests that latter candidate, using
exact integers and explicitly reporting time-censored seeds. The saved
JSON covers all 999,999 seeds 11,20,...,8999993 with a 3000-step cap.
All completed before the cap; all first sampled contracting endpoints
were smaller. The longest was n=1689023, t=225, endpoint=196274, j=140,
with 45 positive-time visits. `first_sampled_contraction_225` independently
checks that individual witness and every earlier sampled noncontraction
in Lean. The full scan is Python evidence, not a universal theorem.
Boundary tests distinguish an exhausted cap from a completed stopping
time and distinguish a later paradoxical visit from the first contraction.

This leaves TWO separate unproved claims: descent at an arbitrary first
sampled contraction, and existence of such a contraction for every seed.
The previously proved sixteen-step first-return bound addresses neither
claim across multiple returns; the 225-step witness makes that difference
concrete. No convergence theorem or new universal hypothesis was added.
The paper and guide were updated to keep these scopes explicit.

Context: Rozier and Terracol study the distinction between coefficient
and actual stopping in arXiv:2502.00948. The sampled-residue experiment
here is not asserted to resolve their coefficient-stopping conjecture.

Verification: 154 audited declarations use standard foundations only;
the selected build and three experiment boundary tests pass. The updated
two-page paper and one-page guide were rendered and visually checked.


## Sampled contraction existence is exactly nondivergence (2026-09-05)

`SampledContraction.lean` defines `SampledNeverContracts n`: n is two
modulo nine and every later visit to that progression has coefficient
at least one. Its `deficit` theorem chooses the last sampled visit before
an arbitrary time and uses the six-even-step bound to prove
2^t <= 64*3^j_t at every time. Its `unbounded` theorem shows a positive
seed with this property must escape: an orbit bound B would bound the
ideal correction by 64B, contradicting the earlier correction equivalence.

Conversely, `unbounded_has_sampled_noncontracting_tail` first moves an
unbounded orbit to a residue-two visit and maximizes its inverse
coefficient over sampled times. The inverse coefficient tends to zero,
so a finite sampled maximum exists. The cocycle then proves sampled
noncontraction at that starting point. This supplies simultaneous residue
and SAMPLED noncontraction, resolving that weaker selection problem.
It does not supply full NeverContracts; the intervening bound is 1/64.

`all_bounded_iff_sampled_contraction` gives the exact global equivalence.
The sampled-contraction existence obligation from the previous turn is
therefore the nondivergence problem itself, not an additional independent
obligation. Neither side is proved. The separate sampled-stopping descent
candidate remains open, and nontrivial cycles remain unexcluded.

Paper and guide: `paper/sampled_contraction.*` and
`paper/sampled_contraction_guide.*`. No new axiom, finite experiment as
premise, or mathematical priority claim is used.

Verification: selected build passes (7830 jobs), and all 158 audited
declarations use standard foundations only. Both one-page PDFs were
rendered and visually checked.


## Fixed powers of the return map cannot force descent (2026-09-05)

`GrowingReturns.lean` proves an explicit universal finite construction.
If n=16q+11, its next four iterates are 24q+17,36q+26,18q+13,27q+20.
The parity is 1101 and the coefficient is 27/16. If n is also two modulo
nine, q is zero modulo nine; intermediate residues are 8,8,4 and the
endpoint is two. This is an actual strictly growing first return.

The identity 16*(11*T^4(n)+23)=27*(11*n+23) consumes one power of sixteen
in the divisibility condition. The explicit recurrence n_0=2,
n_(R+1)=144*n_R+299 satisfies 11*n_R+23=45*144^R and n_R=2 mod9.
Thus every finite R is realized by R successive growing first returns.
The public theorem includes positivity, all intermediate residues, the
final residue, strict growth at each return, and total odd count 3R.
The earlier exploratory replay at R=1,2,4,...,128 agreed; the final proof
is induction over all R, not an extrapolation from those calculations.

This disproves the proposed uniform fixed-power contraction/descent
shortcut. The quantifiers are forall R exists n_R, not exists n forall R.
It supplies no infinite unbounded positive seed and does not refute
seed-dependent eventual contraction. Repeatedly enlarging a uniform
return budget therefore cannot close the current proof program.
The next argument must use arithmetic information about the individual
seed or a nonuniform termination measure. The Collatz goal remains open.

Paper and guide: `paper/growing_returns.*` and
`paper/growing_returns_guide.*`. No mathematical priority claim.

Verification: the selected build passes (7831 jobs); all 159 audited
declarations use standard foundations only. Both one-page PDFs were
rendered and visually checked.


## Independent reassessment and a failed valuation budget (2026-09-05)

The repository ideation skill was applied with three isolated parallel
frames (available capacity), then scoring and three focused follow-ups.
The full pool, scores, traps, and decisions are in
`analysis/ROUTE_REASSESSMENT.md`. It produced no complete proof route.
The next retained candidate is exact admissible word replacement for a
least unbounded seed, with the existence obligation left explicit.

A concrete divisibility-reset proposal was tested immediately. For the
fixed growing branches 1101 and 101, let n=16*64^r-5, r>=1, and y=T^4(n).
`GrowingReturns.unbounded_reserve_reset` proves n=11 mod144, y=65 mod72,
11n+23=32 mod64, and y+7=27*64^r. Thus the incoming branch reserve has
valuation five, but the next branch reserve has valuation 6r. A uniform
bound on reset gains for a fixed pair is false. This does not exclude
all possible amortized potentials using richer arithmetic information.
The growing-return paper and guide are updated with the exact scope.

`analysis/reassessment_checks.py` independently replays seven reset-family
members and checks the binary carry identity on 65,536 seeds. The carry
identity is an experimental implementation check here, not a new Lean
termination theorem. Finite initial binary support alone has not supplied
a signed bound on future carry or high-bit flux. No such hypothesis was
introduced into the proof project.

Verification: all 160 selected declarations pass the standard-foundations
audit, the selected build passes, and the exact reassessment checks pass.
The revised one-page paper and one-page guide were visually checked.


## Exact word replacement and its coverage boundary (2026-09-05)

`lean/Collatz/WordSurgery.lean` proves five selected declarations:
- `WordAffine.replacement_iff`: an exact affine identity characterizes
  actual equal-length/equal-count merging words.
- `WordAffine.replacement_of_correction_shift`: an attainable correction
  increase by 3^j times delta yields the seed n-delta; positivity requires
  delta<n and strict descent requires delta>0.
- `WordAffine.garner_stem_merge`: the classical infinite stem family,
  attributed to Garner via Elia and Tucker; no novelty or coverage claim.
- `no_equal_count_smaller_merge_27`: for every time t and 0<x<27, endpoint
  equality and odd-count equality cannot both hold. The proof combines
  a finite kernel check through time 70 with an all-time cycle argument.
- `smaller_merge_excludes_least_unbounded`: any smaller positive merging
  predecessor contradicts least-unboundedness, without replacement-path
  noncontraction. Existence of that predecessor remains unproved.

`analysis/word_surgery.py` exhausts all words through depth 18. At depth
18 it covers 193,309 of 262,144 binary cylinders, including 1,391 of 7,495
noncontracting-prefix words. Every canonical certificate is replayed.
Three tests pass, including an independent brute-force comparison of the
census through depth 9. The counts are finite Python evidence only.
The boundary seed 27 converges: it refutes unconditional universal
same-length/same-count replacement, not conditional least-unbounded
coverage. Variable odd counts and lengths remain possible next steps.

Verification: selected build passes (7832 jobs); all 165 selected
declarations use standard foundations only. The technical paper and
plain-language guide are `paper/word_surgery.*` and
`paper/word_surgery_guide.*`. Collatz remains open.


## Variable odd counts do not enlarge the tested survivor cover (2026-09-05)

New Lean theorems in `WordSurgery.lean`:
- `lower_count_merge_bound`: if T^t(x)=T^t(n) and j_t(x)<j_t(n), then
  3n < x + 2^(t-j_t(x)).
- `lower_count_merge_gt_twice`: under the same hypotheses and n>=2^t,
  x>2n. Lower-count replacements cannot supply a smaller predecessor there.
- `higher_count_merge_lifts`: compatible canonical endpoints with count
  difference d merge for quotients q=q0+3^d*Q and p=Q.

The exact Python comparison in `analysis/variable_count_surgery.py` checks
all nonnegative cylinder quotients via finite residue sets. At every depth
1 through 18, there are zero additions from varying odd counts to the
noncontracting-prefix cylinders missed by equal-count replacement. At
depth 18, this leaves 6,104 out of 7,495 noncontracting-prefix cylinders.
The result is finite-depth evidence, not an arbitrary-depth redundancy
lemma. Canonical rows are independently replayed through depth 9; quotient
formulas are tested on every pair through depth 6, including successful
higher-count lifts outside the restricted survivor set.

The paper and guide `paper/word_surgery.*` are updated. The next experiment
will allow different replacement lengths. No smaller-predecessor existence
hypothesis for a least unbounded seed has been proved. Collatz remains open.

Verification: selected build passes (7832 jobs), and all 168 audited
declarations use standard foundations only. Both three-test surgery suites
pass. The updated two-page paper and one-page guide were rendered and
visually checked.


## Dominating unequal-length merges preserve noncontraction (2026-09-05)

New module `lean/Collatz/DominatingMerge.lean` proves:
- `neverContracts_of_dominating_merge`: if n is noncontracting,
  T^s(x)=T^t(n), every prefix through s at x is noncontracting, and
  2^s*3^j_t(n) <= 2^t*3^j_s(x), then x is noncontracting at every time.
  There is no unsupported noncontraction assumption on the shifted tail.
- `dominating_merge_111_family`: for every Q, the smaller positive seed
  103+4096Q merges after twelve steps with 111+4374Q after one step,
  with odd counts eight and one and a noncontracting replacement prefix.
- `NeverContracts.smaller_merge_111`: full noncontraction transfers from
  the larger to the smaller seed. Thus a least positive noncontracting
  seed cannot lie in this progression. No such seed is constructed and
  no universal coverage is asserted.

`analysis/variable_length_surgery.py` searches both lengths through 18.
Among 7,495 canonical seeds below 2^18 with noncontracting prefixes,
1,391 have the previous equal-time/equal-count smaller merge. Variable
lengths add 3,768, all with the stronger domination certificate; 937
selected certificates use positive forward time. The search leaves
2,336 seeds unresolved, beginning 27,327,447,495,639,667,703,763.
These are finite seeds, not entire lifted cylinders. Every certificate
and every selected forward-prefix hypothesis is independently replayed.
Two tests pass, including comparison to all smaller seeds at depth 8
and five sample members of the infinite family.

Paper and guide: `paper/dominating_merges.*` and
`paper/dominating_merges_guide.*`. The global existence theorem for a
smaller noncontracting merging seed is still missing. Nontrivial cycles
are also not excluded. Collatz remains open.

Verification: selected build passes (7833 jobs); all 171 audited
declarations use standard foundations only. Both new tests pass. The
one-page technical paper and one-page guide were visually checked.


## 360 merge progressions checked by the Lean kernel (2026-09-05)

`lean/Collatz/MergeProgression.lean` defines finite `MergeRule` data and
its exact `Valid` obligations: positive strict seed ordering, actual
endpoint equality, noncontracting replacement prefixes, coefficient
domination, ternary balance, and ordered seed increments. `MergeRule.sound`
proves conditional noncontraction descent for every natural quotient.
The original and replacement seeds have forms n+2^t*a*Q and x+2^s*b*Q.
The balance 3^j*a=3^k*b preserves the shared endpoint; 2^s*b<=2^t*a
preserves strict seed ordering. No positivity or parity assumption is
hidden in a relaxed correction interval.

`analysis/merge_progressions.py` normalizes the 3,768 successful dominating
certificates into 360 distinct progressions. Its containment filter
removes no additional distinct rule in this run. The generated
`lean/Collatz/MergeRuleTable.lean` uses ordinary `decide` to kernel-check
every rule. `rules_valid` and `certified_rule_sound` establish validity
and conditional descent for any listed rule at every natural quotient.
The Python search's completeness remains separate and is not kernel
certified. The list does not supply universal coverage of NC seeds.

Tests check anchor normalization, progression containment including lower
bounds, and exact correspondence between JSON data and generated Lean
source. The previous small-depth exhaustive comparison still passes.
Regeneration checks that all source certificates are covered and that
none of the 2,336 previously unresolved seeds gains an in-budget rule
from normalization. No all-depth or full-Collatz conclusion follows.

The existing dominating-merges paper and guide now include the generic
lifting theorem and kernel-certified list. The next research step must
address applicability outside this finite rule collection; a universal
existence premise has not been established.

Verification: selected build passes (7835 jobs), and all 174 audited
declarations use standard foundations only. Three progression tests and
two variable-length tests pass. Collatz remains open.

The revised two-page technical paper and one-page guide were rendered
and visually checked.


## All-seed equal-count NC-prefix injectivity through 31 steps (2026-09-05)

`lean/Collatz/NCPrefixInjective.lean` proves that, for every t<=31 and
all natural n,m, if both prefixes through t are noncontracting and have
the same endpoint and odd count, then n=m. This is an all-seed theorem,
not an exhaustive seed-bound computation. The proof uses a 32-by-32
kernel-checked correction-envelope table, induction along the actual
prefix, and the interval

    3^j <= d_t(n)+2^j < 5*3^j.

For t>=2 both seeds must be 3 modulo 4. Equal endpoints and odd counts
then force their difference below four, hence equality. Times zero and
one are handled separately. The public `correction_interval_31` and
`equal_count_injective_31` declarations state the exact scope.

Two kernel-certified boundary examples prevent overstatement:
- `different_counts_collision`: 31 and 95 both reach 182 at time seven,
  with NC prefixes and odd counts six and five. Equal count is essential.
- `correction_interval_fails_at_32`: n=3384695803 has an NC prefix through
  32, j=21 and d=54020229503, violating the strict upper interval. This
  is not a counterexample to injectivity at time 32.

The exploratory `nc_collision_search.py` exhausts NC prefixes, with a
conservative allocation guard and an explicit non-completion status at
its state cap. The saved run completed through depth 30, containing
12,771,274 prefixes at that depth, without equal-count collisions.
That enumeration is not used in the Lean proof. Reproduce it with
--max-depth 30 --max-states 13000000; the default run is smaller.
`nc_correction_envelope.py` reproducibly generates the much smaller Lean
certificate. Six tests pass, covering direct orbit comparisons, the
resource-cap status, table agreement, and the two boundary examples.

The paper and guide are `paper/nc_prefix_injectivity.*` and
`paper/nc_prefix_injectivity_guide.*`. The result excludes distinct
same-time/equal-count dominating replacements through 31; it does not
exclude different lengths or counts and does not prove nondivergence or
rule out all nontrivial cycles. Arbitrary-time injectivity remains
unproved and would itself only clarify the merge approach, not establish
Collatz. The full goal remains open.

Verification: selected build passes (7836 jobs); all 178 audited
declarations use standard foundations only. Six new tests pass. Both
one-page PDFs were rendered and visually checked.
