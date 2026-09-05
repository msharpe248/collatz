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
    ("Collatz.Density", "Collatz.collatz_iff_descent", "Universal descent equivalence"),
    ("Collatz.NoGo", "Collatz.no_finite_certificate", "Bounded positive multiplier; fixed window and contraction"),
    ("Collatz.Rung1", "Collatz.no_shifted_sigWord_itinerary", "One substitution, every natural start and shift"),
    ("Collatz.Sturmian", "Collatz.sturmian_level", "Separation, coverage and size are hypotheses"),
    ("Collatz.SturmianEndpoint", "Collatz.sturmian_level_endpoint", "Separation and coverage; size checked at endpoint"),
    ("Collatz.SturmianApprox", "Collatz.sturmian_separation_of_neighbors", "Determinant-one bracket and positive errors"),
    ("Collatz.SturmianApprox", "Collatz.rotation_window_of_grid", "Bezout, approximation and width certificates"),
    ("Collatz.SturmianSilver", "Collatz.Silver.no_itinerary", "Unconditional for slope sqrt(2)/2, every intercept"),
    ("Collatz.SturmianSilver", "Collatz.Silver.no_eventual_itinerary", "Unconditional exclusion after every finite orbit prefix"),
    ("Collatz.WordAffine", "Collatz.WordAffine.adjacent_swap", "All finite Boolean prefix and suffix words"),
    ("Collatz.WordAffine", "Collatz.WordAffine.compare_bound", "Realized equal-length/equal-weight words, distinct endpoints"),
    ("Collatz.Cylinder", "Collatz.Cylinder.prefix_transport", "Every prefix up to cylinder depth"),
    ("Collatz.Cylinder", "Collatz.Cylinder.mem_parameters", "Finite height and prefix non-descent"),
    ("Collatz.Cylinder", "Collatz.Cylinder.parameters_convex", "Two surviving quotients and one between them"),
    ("Collatz.PrefixCertificate", "Collatz.prefix_power_initial_bound", "Unbounded orbit and a repeated parity block"),
    ("Collatz.Ideal", "Collatz.fract_ideal", "Bounded correction (Supercritical), not inferred from divergence"),
    ("Collatz.IdealBounds", "Collatz.supercritical_of_geometric", "Explicit summable inverse-drift bound; not asserted for every divergent orbit"),
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
