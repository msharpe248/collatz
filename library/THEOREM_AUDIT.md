# Theorem trust and reuse index

The bibliographic manifest records project status. It does not certify the
axiom dependencies of every declaration in a repository.

The reproducible main-project declaration audit is
[analysis/theorem_audit.json](../analysis/theorem_audit.json). It records the
main toolchain, exact printed statements, axiom lists, source locations,
worktree provenance, and each nested repository's pinned commit and toolchain.
Run `python3 analysis/audit_theorems.py --build` to rebuild and inspect the
selected main modules. `--include-kl14` additionally imports the large KL14
certificate; independent kernel replay is not performed by this script.

| Candidate dependency | Local evidence | Reuse requirement |
|---|---|---|
| Main `Collatz` declarations in the JSON audit | Printed axiom dependencies | Preserve the exact quantified statement and hypotheses |
| Monks `Monks2006/Proof.lean` | Explicit `primitive_root_two_mod_three_pow` and `back_trace_dense` axioms | Discharge imported axioms or keep the result explicitly conditional |
| Knight `Knight2026/HighCycle.lean`, `Circuit.lean` | Explicit mathematical axioms for extremality and circuit bounds | Inspect the desired theorem's actual dependency closure |
| Hercher `Collatz/CFBestApprox.lean` | Candidate convergent sign/recurrence helpers; not kernel-audited here | Port narrow helpers across the toolchain boundary and inspect dependencies |
| rwst `ForMathlib/Combinatorics/SubwordComplexity.lean` | Candidate finite Morse–Hedlund helper; not kernel-audited here | Check statement coverage and dependencies before relying on it |
| rwst `AB/StammeringSequences.lean`, transcendence modules | Deliberate cited axioms are present | An axiom-free wrapper does not remove imported mathematical axioms |
| Tao repository | Challenge stubs and historical comments coexist with main results | Audit the selected headline theorem; raw `sorry` counts do not establish its closure |
| Other bibliographic entries | Pinned source available, declaration audit not performed here | Keep status as unqueried until exact output is recorded |

Map conventions matter: distinguish the ordinary Collatz map, the shortcut
Terras map, and odd-only Syracuse acceleration. Orbit merging in a sufficient
set theorem is different from every forward orbit visiting the set. A bound
conditional on a verified finite range is different from a kernel proof of
that range. These distinctions belong in theorem statements and bridges.
