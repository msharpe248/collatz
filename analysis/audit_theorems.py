#!/usr/bin/env python3
"""Audit selected exact declarations; distinguish artifacts from rebuilds.

Run from any directory. --build rebuilds selected modules before querying.
--include-kl14 also imports the large existing KL14 certificate. Outputs a
JSON theorem index including statements, axiom dependencies, and provenance.
"""
import argparse
import datetime
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = [
    ("Collatz.FirstContraction", "Collatz.first_contraction_correction_bound", "Scaled correction is bounded by the odd count while every earlier coefficient is noncontracting"),
    ("Collatz.FirstContraction", "Collatz.first_contraction_seed_bound", "All-time conditional seed bound for a non-descending first coefficient contraction"),
    ("Collatz.FirstContraction", "Collatz.descent_at_first_contraction", "Seeds above the explicit first-contraction bound descend at that endpoint"),
    ("Collatz.FirstContraction", "Collatz.contractionCheck_sound", "Soundness of the finite executable descent-versus-contraction checker"),
    ("Collatz.FirstContraction", "Collatz.descent_by_first_contraction_65", "Every seed above one descends by its first coefficient contraction if it occurs within 65 steps"),
    ("Collatz.FirstContraction", "Collatz.descent_of_contraction_le65", "Any coefficient contraction within 65 steps forces prior or simultaneous descent for every seed above one"),
    ("Collatz.FirstContraction", "Collatz.return_le65_reaches_one", "Every positive natural return of length at most 65 reaches one; small finite-horizon exclusion"),
    ("Collatz.ParadoxicalPruning", "Collatz.WordAffine.completion_envelope_mono", "Completion envelope increases with the allowed suffix odd count"),
    ("Collatz.ParadoxicalPruning", "Collatz.WordAffine.completion_test_mono", "Only the largest admissible suffix odd count is needed for the relaxed necessary test"),
    ("Collatz.ParadoxicalPruning", "Collatz.WordAffine.prune_paradoxical_completion_max", "A maximal-count pruning inequality excludes every realized suffix below that count"),
    ("Collatz.ParadoxicalPruning", "Collatz.WordAffine.paradoxical_completion_seed_bound", "Every paradoxical completion lies in the finite seed interval implied by the maximal-count envelope"),
    ("Collatz.OrbitSummability", "Collatz.unbounded_reciprocal_value_tail", "Explicit geometric reciprocal budget for all finite orbit-value sets above a threshold"),
    ("Collatz.OrbitSummability", "Collatz.unbounded_reciprocal_tsum_le", "Full reciprocal series bound for an unbounded orbit staying above the threshold"),
    ("Collatz.OrbitSummability", "Collatz.orbitTailBudget_tendsto_zero", "The explicit value-tail budget tends to zero"),
    ("Collatz.OrbitSummability", "Collatz.unbounded_idealLimit_le_tailBudget", "Threshold-dependent limiting correction upper bound; requires a lower bound on every orbit value"),
    ("Collatz.OrbitSummability", "Collatz.tail_correction_envelope_lower", "The upper envelope grows even at the smallest admissible seed; not a lower bound on the actual correction"),
    ("Collatz.RelativeCorrection", "Collatz.relative_shifted_idealLimit", "Exact relative shifted correction identity for positive seeds with bounded correction"),
    ("Collatz.RelativeCorrection", "Collatz.unbounded_relative_correction_tendsto_zero", "Relative shifted correction tends to zero on every unbounded positive orbit; no absolute error bound"),
    ("Collatz.OrbitPacking", "Collatz.packing_bound", "Finite power-saving bound for equal-time injective sets below 32^m"),
    ("Collatz.OrbitPacking", "Collatz.unbounded_orbit_packing", "All unbounded natural orbits obey the finite packing bound at every scale"),
    ("Collatz.OrbitSummability", "Collatz.unbounded_orbit_reciprocal_summable", "Every unbounded positive natural orbit has summable reciprocals; unconditional coverage"),
    ("Collatz.OrbitSummability", "Collatz.unbounded_orbit_supercritical", "Every unbounded positive natural orbit has bounded ideal correction"),
    ("Collatz.OrbitSummability", "Collatz.supercritical_iff_unbounded_orbit", "For positive seeds bounded ideal correction is equivalent to unboundedness"),
    ("Collatz.OrbitSummability", "Collatz.unbounded_inverse_drift_tendsto_zero", "Inverse multiplicative drift tends to zero on every unbounded positive orbit; no strict density gap"),

    ("Collatz.MechanicalPeriod", "Collatz.mechanical_period_return", "Integral slope increment forces an actual natural return at the initial seed"),
    ("Collatz.MechanicalPeriod", "Collatz.WordAffine.endpoint_rotations_trivial", "Endpoint-swapped rotations of an actual return word force the trivial cycle"),
    ("Collatz.RationalGrid", "Collatz.RationalGrid.extreme_words", "Uniform endpoint-swapped structure of the extreme phases of every reduced rational grid"),
    ("Collatz.RationalGrid", "Collatz.RationalGrid.grid_reaches_one", "Every reduced rational grid itinerary reaches one; all integer phases"),
    ("Collatz.RationalMechanical", "Collatz.rational_itinerary_grid", "Exact infinite coding of arbitrary real intercepts by a finite rational phase"),
    ("Collatz.RationalMechanical", "Collatz.reduced_rational_mechanical_reaches_one", "All reduced rational slopes strictly between zero and one, all real intercepts"),
    ("Collatz.RationalMechanical", "Collatz.mechanical_reaches_one", "All real slopes and intercepts, positive natural seed with mechanical itinerary reaches one"),
    ("Collatz.RationalMechanical", "Collatz.mechanical_classification", "Positive natural seed with global mechanical itinerary has slope one half and seed one or two"),
    ("Collatz.RationalMechanical", "Collatz.eventual_mechanical_reaches_one", "Any positive natural orbit with any mechanical tail reaches one"),

    ("Collatz.EndpointCycles", "Collatz.WordAffine.endpoint_cancellation", "Exact endpoint-swap correction identity for every finite middle word"),
    ("Collatz.EndpointCycles", "Collatz.WordAffine.endpoint_returns_trivial", "Two actual natural returns with words 1u0 and 0u1 force empty u and seeds 1 and 2"),
    ("Collatz.EndpointCycles", "Collatz.WordAffine.endpoint_cycle_shift_trivial", "Endpoint-swapped return words within one orbit force the trivial cycle"),

    ("Collatz.MechanicalComplexity", "Collatz.mechanical_complexity_le", "Every mechanical parity itinerary has at most L+1 global factors"),
    ("Collatz.MechanicalComplexity", "Collatz.bounded_of_mechanical", "Any mechanical parity itinerary forces boundedness; eventual cycle not identified"),
    ("Collatz.MechanicalComplexity", "Collatz.mechanical_return_slope", "A return forces period times mechanical slope to equal its odd-step count"),
    ("Collatz.MechanicalComplexity", "Collatz.no_irrational_mechanical", "All irrational real slopes, all real intercepts, all natural seeds"),
    ("Collatz.MechanicalComplexity", "Collatz.no_eventual_irrational_mechanical", "Every shifted natural seed excludes every irrational mechanical itinerary"),

    ("Collatz.ParityComplexity", "Collatz.ParityComplexity.unbounded_factor_floor", "Every unbounded orbit has at least 5q+1 distinct parity factors of length 3q+K when N+1 <= 2^K"),
    ("Collatz.ParityComplexity", "Collatz.ParityComplexity.bounded_of_linear_complexity", "A uniform factor-complexity slope below 5/3 forces boundedness; no universal envelope assumed"),
    ("Collatz.ParityComplexity", "Collatz.ParityComplexity.no_sturmian_complexity", "No natural seed has exactly L+1 factors at every length; standard Sturmian complexity definition"),
    ("Collatz.IdealBarrier", "Collatz.one_lt_idealLimit", "Positive seed with bounded ideal correction; strict lower bound one on the limiting correction"),
    ("Collatz.IdealBarrier", "Collatz.uniformSupercritical_bound_gt_two", "Uniform bound on every shifted finite correction must exceed two; no uniform upper bound inferred"),
    ("Collatz.IdealBarrier", "Collatz.ideal_tracking_gap_gt_one", "Canonical geometric ideal lies more than one above every orbit value under bounded correction"),
    ("Collatz.SiblingCorrection", "Collatz.SiblingCorrection.pair_free_product_bound", "Tenth-power weighted product bound for distinct odd values above five, coprime to three, with no sibling pair"),
    ("Collatz.SiblingCorrection", "Collatz.unbounded_eventual_tenth_bound", "Every unbounded positive orbit has a tail with tenth-power correction control"),
    ("Collatz.SiblingCorrection", "Collatz.unbounded_eventual_tenth_escape", "Every unbounded positive orbit has a tail with drift excursions at exponent 9/10"),
    ("Collatz.SiblingCorrection", "Collatz.finite_tenth_drift_certificate", "Finite rational polynomial drift certificate below 9/10 forces boundedness outside multiples of three"),
    ("Collatz.SiblingCorrection", "Collatz.bounded_orbit_of_tenth_polynomial_drift", "Global rational polynomial drift envelope below 9/10; boundedness, not convergence"),
    ("Collatz.OddPrehistory", "Collatz.arbitrarily_long_odd_prehistory", "Every positive odd target coprime to three has genuine histories of any odd-step count; starting seed varies"),
    ("Collatz.OddPrehistory", "Collatz.unbounded_excludes_odd_siblings", "An unbounded orbit cannot contain both odd n and 4n+1; pair exclusion, not exclusion of either value individually"),
    ("Collatz.ResidueCorrection", "Collatz.idealC_ninth_bound_of_prefix", "Distinct prefix avoiding one, positive seed not divisible by three; ninth-power correction bound"),
    ("Collatz.ResidueCorrection", "Collatz.unbounded_eventual_ninth_bound", "Every unbounded positive orbit has a tail with ninth-power correction control at every length"),
    ("Collatz.ResidueCorrection", "Collatz.unbounded_eventual_ninth_escape", "Every unbounded positive orbit has a tail with drift excursions at exponent 8/9"),
    ("Collatz.ResidueCorrection", "Collatz.finite_ninth_drift_certificate", "Finite rational polynomial drift certificate below 8/9 forces boundedness outside multiples of three"),
    ("Collatz.ResidueCorrection", "Collatz.bounded_orbit_of_ninth_polynomial_drift", "Global rational polynomial drift envelope below 8/9, seed not divisible by three; boundedness, not convergence"),
    ("Collatz.CorrectionDecode", "Collatz.WordAffine.decodeCorrection_correct", "Deterministic reconstruction recovers every finite Boolean word"),
    ("Collatz.CorrectionDecode", "Collatz.WordAffine.correctionAttainable_iff", "Exact correction acceptance iff a word with the specified length, count and correction exists"),
    ("Collatz.CorrectionDecode", "Collatz.WordAffine.attainable_paradoxical_iff", "Attainability plus numerical criterion is equivalent to an actual paradoxical word; no uniform exclusion"),
    ("Collatz.CongruenceRelaxation", "Collatz.WordAffine.relaxed_closing_correction", "Artificial suffix correction in the envelope closes every fixed positive prefix at sufficiently large lengths; no attainability claim"),
    ("Collatz.WordCongruence", "Collatz.WordAffine.realizes_iff_dvd", "Exact parity realization iff affine numerator is divisible by the full power of two"),
    ("Collatz.WordCongruence", "Collatz.WordAffine.realizes_paradoxical_iff", "Joint congruence and correction criterion; all natural seeds and finite words"),
    ("Collatz.Density", "Collatz.collatz_iff_descent", "Universal descent equivalence"),
    ("Collatz.NoGo", "Collatz.no_finite_certificate", "Bounded positive multiplier; fixed window and contraction"),
    ("Collatz.Rung1", "Collatz.no_shifted_sigWord_itinerary", "One substitution, every natural start and shift"),
    ("Collatz.Sturmian", "Collatz.sturmian_level", "Separation, coverage and size are hypotheses"),
    ("Collatz.SturmianEndpoint", "Collatz.sturmian_level_endpoint", "Separation and coverage; size checked at endpoint"),
    ("Collatz.SturmianApprox", "Collatz.sturmian_separation_of_neighbors", "Determinant-one bracket and positive errors"),
    ("Collatz.SturmianApprox", "Collatz.rotation_window_of_grid", "Bezout, approximation and width certificates"),
    ("Collatz.SturmianSilver", "Collatz.Silver.no_itinerary", "Unconditional for slope sqrt(2)/2, every intercept"),
    ("Collatz.SturmianSilver", "Collatz.Silver.no_eventual_itinerary", "Unconditional exclusion after every finite orbit prefix"),
    ("Collatz.SturmianWindow", "Collatz.rotation_visit_of_neighbors", "Short q+Q window from two positive bracketing errors, epsilon at most delta"),
    ("Collatz.SturmianWindow", "Collatz.rotation_window_of_neighbors", "Every shifted q+Q window and every intercept"),
    ("Collatz.SturmianFamily", "Collatz.no_itinerary_of_unbounded_neighbors", "Explicit unbounded bracketing-level hypothesis, sixfold separation and bounded ratios"),
    ("Collatz.SturmianMetallic", "Collatz.Metallic.no_itinerary", "Unconditional for every integer m >= 6, every intercept and natural seed"),
    ("Collatz.SturmianMetallic", "Collatz.Metallic.no_eventual_itinerary", "Unconditional metallic-family exclusion after every finite orbit prefix"),
    ("Collatz.SturmianMetallic", "Collatz.Metallic.alpha_irrational", "Every integer parameter m >= 2"),
    ("Collatz.SturmianMetallic", "Collatz.Metallic.alpha_strictMono", "Distinct slopes: strict monotonicity in every natural parameter"),
    ("Collatz.SturmianMetallic", "Collatz.Metallic.alpha_close_to_one", "Explicit error 0 < 1-alpha_m < 1/(m+1)"),
    ("Collatz.SturmianMetallic", "Collatz.Metallic.excluded_slopes_arbitrarily_close_to_one", "A parameter m >= 6 within every positive distance of one"),
    ("Collatz.ParityDefects", "Collatz.return_or_parity_defect", "Every checkpoint either returns after q steps or has a nearby shift disagreement"),
    ("Collatz.ParityDefects", "Collatz.ParityDefects.checkpoint_formula", "Exact geometric checkpoint horizon"),
    ("Collatz.ParityDefects", "Collatz.ParityDefects.few_defects_force_return", "Finite defect-count certificate of an exact q-step return"),
    ("Collatz.ParityDefects", "Collatz.ParityDefects.count_le_twice_template_errors", "At most two shift disagreements per edited template letter"),
    ("Collatz.ParityDefects", "Collatz.ParityDefects.near_power_force_return", "Finite approximate periodicity certificate; arbitrary edit positions"),
    ("Collatz.ParityDefects", "Collatz.ParityDefects.near_power_bound_orbit", "Positive period and near-power certificate imply bounded orbit, not necessarily trivial cycle"),
    ("Collatz.ParityDefects", "Collatz.ParityDefects.unbounded_forces_defects", "Unbounded trajectories exceed every prescribed defect count at an explicit horizon"),
    ("Collatz.ParityDefects", "Collatz.ParityDefects.few_defects_two_reaches_one", "Positive seed and period-two defect certificate imply reaching one"),
    ("Collatz.ParityDefects", "Collatz.ParityDefects.near_two_power_reaches_one", "Positive seed near a period-two template with explicit finite bounds implies reaching one"),
    ("Collatz.DefectHeight", "Collatz.terras_iter_three_halves", "Universal shifted-height bound with exact 3/2 multiplier"),
    ("Collatz.DefectHeight", "Collatz.ParityDefects.height_from_growthBits", "Universal ceiling(3u/5)+K bit-height envelope"),
    ("Collatz.DefectHeight", "Collatz.ParityDefects.few_defects_return_of_height", "Finite return certificate from any monotone certified bit-height envelope"),
    ("Collatz.DefectHeight", "Collatz.ParityDefects.sharp_few_defects_force_return", "Shorter universal defect horizons, no additional orbit hypothesis"),
    ("Collatz.DefectHeight", "Collatz.ParityDefects.sharpCheckpoint_growth", "Division-free geometric bound with base 8/5"),
    ("Collatz.DefectHeight", "Collatz.ParityDefects.sharpCheckpoint_le_old", "The new horizon is never larger than the previous horizon"),
    ("Collatz.DefectHeight", "Collatz.ParityDefects.sharp_near_power_force_return", "Edited-template return certificate at the shorter horizon"),
    ("Collatz.DefectHeight", "Collatz.ParityDefects.sharp_few_defects_two_reaches_one", "Positive seed and sharper period-two certificate imply reaching one"),
    ("Collatz.DefectHeight", "Collatz.ParityDefects.sharp_unbounded_forces_defects", "Necessary defect count for every unbounded orbit at the shorter horizon"),
    ("Collatz.WordAffine", "Collatz.WordAffine.adjacent_swap", "All finite Boolean prefix and suffix words"),
    ("Collatz.WordAffine", "Collatz.WordAffine.compare_bound", "Realized equal-length/equal-weight words, distinct endpoints"),
    ("Collatz.Cylinder", "Collatz.Cylinder.prefix_transport", "Every prefix up to cylinder depth"),
    ("Collatz.Cylinder", "Collatz.Cylinder.mem_parameters", "Finite height and prefix non-descent"),
    ("Collatz.Cylinder", "Collatz.Cylinder.parameters_convex", "Two surviving quotients and one between them"),
    ("Collatz.PrefixCertificate", "Collatz.prefix_power_initial_bound", "Unbounded orbit and a repeated parity block"),
    ("Collatz.Ideal", "Collatz.fract_ideal", "Bounded correction (Supercritical), not inferred from divergence"),
    ("Collatz.IdealBounds", "Collatz.supercritical_of_geometric", "Explicit summable inverse-drift bound; not asserted for every divergent orbit"),
    ("Collatz.Reciprocal", "Collatz.reciprocal_sum_ledger", "Finite telescoping reciprocal bound for every positive seed"),
    ("Collatz.Reciprocal", "Collatz.idealC_exp_reciprocal_bound", "Finite exponential correction bound for every positive seed"),
    ("Collatz.Reciprocal", "Collatz.supercritical_iff_summable_reciprocal", "Exact characterization of bounded ideal correction, not universal divergent-orbit coverage"),
    ("Collatz.Reciprocal", "Collatz.supercritical_orbit_tendsto_atTop", "Bounded correction forces eventual escape from every finite bound"),
    ("Collatz.CorrectionGrowth", "Collatz.reciprocal_product_le_card", "Finite product bound for distinct positive integers"),
    ("Collatz.CorrectionGrowth", "Collatz.idealC_sixth_bound_of_prefix", "Finite prefix with no repeated values and no visit to one"),
    ("Collatz.CorrectionGrowth", "Collatz.unbounded_idealC_sixth_bound", "Every unbounded positive orbit; no summability or density gap assumption"),
    ("Collatz.CorrectionGrowth", "Collatz.unbounded_sixth_drift_bound", "Exact integer drift restriction for every unbounded positive orbit"),
    ("Collatz.CorrectionGrowth", "Collatz.unbounded_nondescent_drift", "Seed-independent drift restriction at a non-descent time of an unbounded orbit"),
    ("Collatz.DriftEscape", "Collatz.unbounded_prefix_drift_escape", "Running maximum drift must exceed a power-law threshold on every prefix"),
    ("Collatz.DriftEscape", "Collatz.finite_drift_certificate_bounds_orbit", "Finite polynomial drift envelope and explicit horizon force boundedness, not necessarily reaching one"),
    ("Collatz.DriftEscape", "Collatz.bounded_orbit_of_subcritical_polynomial_drift", "Any global rational polynomial drift exponent strictly below 5/6 forces boundedness"),
    ("Collatz.DriftEscape", "Collatz.bounded_orbit_of_bounded_drift", "Uniformly bounded multiplicative drift forces a bounded positive orbit"),
    ("Collatz.Paradoxical", "Collatz.paradoxical_quotient_interval", "Exact finite-length contracting cylinder interval without a seed cutoff"),
    ("Collatz.Paradoxical", "Collatz.paradoxical_residue_iff", "Complete decomposition of arbitrary positive seeds into residue cylinders"),
    ("Collatz.Paradoxical", "Collatz.paradoxical_eight_iff", "All seeds above two at length eight: exactly 7, 9, 18, 19, 25; kernel-decided residue table"),
    ("Collatz.WordAffine", "Collatz.WordAffine.correction_append", "Exact composition identity for finite parity words"),
    ("Collatz.ParadoxicalPruning", "Collatz.WordAffine.correction_upper", "Sharp suffix correction upper bound by length and odd count"),
    ("Collatz.ParadoxicalPruning", "Collatz.WordAffine.completion_correction_upper", "Uniform correction bound for every completion of a specified odd count"),
    ("Collatz.ParadoxicalPruning", "Collatz.WordAffine.prune_paradoxical_completion", "Strict envelope inequality excludes all realized completions above a certified seed floor"),
    ("Collatz.PruningLimit", "Collatz.WordAffine.completion_envelope_survives", "Explicit target-length threshold beyond which every fixed relaxed prefix envelope admits an odd-count budget"),
    ("Collatz.PruningLimit", "Collatz.WordAffine.finite_envelopes_eventually_survive", "Any finite collection of fixed relaxed envelopes simultaneously survives all sufficiently large lengths; no realizability claim"),
]


def run(args, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"Command failed: {args}\n{result.stdout}\n{result.stderr}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--include-kl14", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / "analysis/theorem_audit.json")
    args = parser.parse_args()
    targets = list(TARGETS)
    if args.include_kl14:
        targets.append(("Collatz.KL14", "Collatz.K14.density_bound", "Finite-scale lower bound with explicit constants"))
    modules = sorted({module for module, _, _ in targets})
    if args.build:
        subprocess.run(["lake", "build", *modules], cwd=LEAN, check=True)
    imports = "\n".join(f"import {module}" for module in modules)
    queries = "\n".join(f"#check {name}\n#print axioms {name}" for _, name, _ in targets)
    with tempfile.TemporaryDirectory(prefix="collatz-audit-") as directory:
        query = Path(directory) / "Audit.lean"
        query.write_text(imports + "\n" + queries + "\n")
        output = run(["lake", "env", "lean", str(query)], LEAN)
    found = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
    entries = []
    all_clean = True
    for module, name, scope in targets:
        if name not in found:
            raise RuntimeError(f"Missing axiom output for {name}")
        axioms = [x.strip() for x in found[name].split(",") if x.strip()]
        clean = set(axioms) <= STANDARD
        all_clean &= clean
        source = LEAN / (module.replace(".", "/") + ".lean")
        declaration = name.rsplit(".", 1)[1]
        line = next((i for i, text in enumerate(source.read_text().splitlines(), 1)
                     if re.search(rf"\btheorem\s+{re.escape(declaration)}\b", text)), None)
        entries.append({"declaration": name, "source": str(source.relative_to(ROOT)),
                        "line": line, "scope": scope, "axioms": axioms,
                        "standard_foundations_only": clean})
    libraries = []
    for toolchain in sorted((ROOT / "library/repos").glob("*/lean-toolchain")):
        libraries.append({"repository": toolchain.parent.name,
                          "commit": run(["git", "rev-parse", "HEAD"], toolchain.parent).strip(),
                          "toolchain": toolchain.read_text().strip(),
                          "audit_status": "not checked by this main-project audit"})
    report = {
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "main_commit": run(["git", "rev-parse", "HEAD"]).strip(),
        "main_worktree_status": run(["git", "status", "--short"]),
        "toolchain": (LEAN / "lean-toolchain").read_text().strip(),
        "selected_modules_built": args.build,
        "verification_scope": "Lean axiom inspection; no independent kernel replay or clean rebuild",
        "all_selected_standard_foundations_only": all_clean,
        "theorems": entries, "library_provenance": libraries, "lean_output": output,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Audited {len(entries)} declarations; standard foundations only: {all_clean}")
    print(args.output)
    if not all_clean:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
