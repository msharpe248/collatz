# Active proof program

Updated 2026-09-04. The Collatz conjecture remains open. This ledger separates
proved family exclusions from the unproved claim that all counterexamples
belong to an excluded family.

## Completed in this research pass

| Direction | Checked result | Scope |
|---|---|---|
| Sturmian itineraries | `Silver.no_itinerary`, `Silver.no_eventual_itinerary` | Slope √2/2, every intercept and natural seed; unconditional |
| Rotation arithmetic | `sturmian_separation_of_neighbors`, `rotation_window_of_grid` | General certified approximation inputs; no cited axioms |
| Size control | `sturmian_size_at_endpoint` | One endpoint replaces all earlier size tests |
| Block comparisons | `WordAffine.adjacent_swap`, `compare`, `compare_dvd`, `compare_bound` | Exact identities and conditional height obstructions |
| Survivor geometry | `Cylinder.prefix_transport`, `mem_parameters`, `parameters_convex` | Exact finite-height quotient intervals |
| Correct experimental bound | `prefix_power_initial_bound` | Retains the affine correction after shifting an orbit |
| Critical-boundary discipline | `supercritical_of_geometric` | Explicit summable inverse-drift hypothesis, not universal divergence |
| Dependency audit | `audit_theorems.py`, `theorem_audit.json` | Selected declarations, printed types and axioms, pinned library provenance |

See [STURMIAN_SILVER.md](STURMIAN_SILVER.md) for the new theorem's proof.
The [paper](../paper/silver.pdf) and [friendly guide](../paper/silver_guide.pdf)
provide the publication versions. Significant future results should also
receive a paper and guide in `paper/`, following its README.
The main source modules were rebuilt selectively. This does not mean the
large KL certificates or all nested libraries were rebuilt or independently
kernel-replayed during this pass.

## Experiments and controls

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

1. **Other Sturmian slopes.** Reuse the determinant/grid method on another
   explicit recurrence, or prove quantitative conditions for a family. The
   √2/2 theorem alone does not imply exclusion of every Sturmian slope.
2. **Useful defect bounds.** The swap identity is proved; a small number of
   swaps need not have a small weighted cost. Find a class with controlled
   weighted defects and prove an exclusion theorem for that class.
3. **Ordinary integer coverage.** Prove an independently meaningful
   restriction forcing every counterexample into an excluded class. No
   complexity-versus-defect dichotomy has been established.
4. **Critical-boundary orbits.** Bounded ideal correction is not known for
   every hypothetical divergent orbit. The geometric sufficient condition
   does not dispose of the complementary case.
5. **Survivor exhaustion.** Exact interval computation is not a termination
   proof. Universal finite-height exhaustion is equivalent to universal
   descent; using it as a completeness assumption would be circular.
6. **Cycles.** The new itinerary exclusions do not prove that all nontrivial
   cycles are absent. Existing finite/class-specific cycle exclusions remain
   the cycle track's current boundary.
7. **Imported dependencies.** Selected external modules contain cited or
   unfinished axioms. Port and audit precise declarations before using them
   in an unconditional theorem; preserve map-convention bridges.

KL exponent improvements remain a separate density-results track. The next
proof-focused priority is extending the now-proved rotation-grid method,
followed by a genuine defect-controlled itinerary family.
