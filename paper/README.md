# Papers and companion guides

Significant research results should be documented here as a technical paper
and a plain-language guide, each with editable LaTeX source and a compiled PDF.
Related supporting lemmas can be collected in the same paper. Clearly separate
proved statements, explicit hypotheses, finite experiments, and open coverage
arguments; do not turn an experimental candidate into a theorem in the prose.

| Topic | Paper | Guide |
|---|---|---|
| All irrational mechanical itineraries excluded | [mechanical_complexity.pdf](mechanical_complexity.pdf) | [mechanical_complexity_guide.pdf](mechanical_complexity_guide.pdf) |
| Critical line and bounded-certificate obstruction | [nogo.pdf](nogo.pdf) | [nogo_guide.pdf](nogo_guide.pdf) |
| Krasikov–Lagarias density bounds | [klbound.pdf](klbound.pdf) | [klbound_guide.pdf](klbound_guide.pdf) |
| The 3-adic shadow | [shadow.pdf](shadow.pdf) | [shadow_guide.pdf](shadow_guide.pdf) |
| Word-complexity ladder | [ladder.pdf](ladder.pdf) | [ladder_guide.pdf](ladder_guide.pdf) |
| Automatic itinerary exclusion | [rung1.pdf](rung1.pdf) | [rung1_guide.pdf](rung1_guide.pdf) |
| Unconditional Sturmian exclusion at slope 1/√2, and supporting arithmetic | [silver.pdf](silver.pdf) | [silver_guide.pdf](silver_guide.pdf) |
| Short rotation windows and an infinite family of Sturmian exclusions | [metallic.pdf](metallic.pdf) | [metallic_guide.pdf](metallic_guide.pdf) |
| Finite parity defects and approximate-periodicity certificates | [defects.pdf](defects.pdf) | [defects_guide.pdf](defects_guide.pdf) |
| Bounded correction exactly equals reciprocal-orbit summability | [reciprocal.pdf](reciprocal.pdf) | [reciprocal_guide.pdf](reciprocal_guide.pdf) |
| Sixth-root correction, polynomial drift exclusion, and finite boundedness certificates | [correction_growth.pdf](correction_growth.pdf) | [correction_growth_guide.pdf](correction_growth_guide.pdf) |
| Exact paradoxical cylinders, prefix pruning, and fixed-length searches | [paradoxical_cylinders.pdf](paradoxical_cylinders.pdf) | [paradoxical_cylinders_guide.pdf](paradoxical_cylinders_guide.pdf) |

The matching `.tex` files are the editable sources. The newest formal status
and remaining proof gaps are in [RESEARCH_STATUS.md](../analysis/RESEARCH_STATUS.md).
Older papers retain their historical scope and may describe steps that later
papers have completed.

To rebuild the latest pair with Tectonic:

```sh
tectonic paper/paradoxical_cylinders.tex
tectonic paper/paradoxical_cylinders_guide.tex
```

After editing, check the compiler log, cross-references, and rendered pages.
The current theorem audit is [theorem_audit.json](../analysis/theorem_audit.json).

- [Correction attainability](correction_attainability.md) and
  [guide](correction_attainability_guide.md): Lean-proved limitation of combining
  a relaxed suffix correction interval with exact endpoint congruence. Markdown
  sources; no claim of an actual cycle or uniform Collatz proof.

- [Ninth-power correction bound](residue_correction.md) and
  [guide](residue_correction_guide.md): residue exclusion strengthens the
  eventual correction exponent to 1/9 and the drift excursion exponent to
  8/9, with finite and global conditional boundedness theorems in Lean.

- [Odd histories and collisions](odd_histories_and_collisions.md) and
  [guide](odd_histories_and_collisions_guide.md): arbitrary finite odd histories
  for every allowed target, and a forbidden pair on every unbounded orbit.
  The weighted correction improvement from pairs remains open.

- [Tenth-power correction bound](sibling_correction.md) and
  [guide](sibling_correction_guide.md): forbidden sibling pairs strengthen the
  correction exponent to 1/10 and the conditional drift threshold to 9/10.

- [Ideal-tracking lower barriers](ideal_tracking_barrier.md) and
  [guide](ideal_tracking_barrier_guide.md): strict lower bounds on limiting
  corrections, exclusion of uniform bounds at most two, and the unresolved
  transport and confinement needed for the geometric-progression library.

- [Parity complexity](parity_complexity.md) and [guide](parity_complexity_guide.md):
  an explicit complexity floor, conditional boundedness below slope 5/3, and
  exclusion of the entire Sturmian class in its factor-complexity definition.
  The mechanical-word equivalence has not been ported into this result.
