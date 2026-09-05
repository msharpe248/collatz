# Papers and companion guides

Significant research results should be documented here as a technical paper
and a plain-language guide, each with editable LaTeX source and a compiled PDF.
Related supporting lemmas can be collected in the same paper. Clearly separate
proved statements, explicit hypotheses, finite experiments, and open coverage
arguments; do not turn an experimental candidate into a theorem in the prose.

| Topic | Paper | Guide |
|---|---|---|
| Critical line and bounded-certificate obstruction | [nogo.pdf](nogo.pdf) | [nogo_guide.pdf](nogo_guide.pdf) |
| Krasikov–Lagarias density bounds | [klbound.pdf](klbound.pdf) | [klbound_guide.pdf](klbound_guide.pdf) |
| The 3-adic shadow | [shadow.pdf](shadow.pdf) | [shadow_guide.pdf](shadow_guide.pdf) |
| Word-complexity ladder | [ladder.pdf](ladder.pdf) | [ladder_guide.pdf](ladder_guide.pdf) |
| Automatic itinerary exclusion | [rung1.pdf](rung1.pdf) | [rung1_guide.pdf](rung1_guide.pdf) |
| Unconditional Sturmian exclusion at slope 1/√2, and supporting arithmetic | [silver.pdf](silver.pdf) | [silver_guide.pdf](silver_guide.pdf) |

The matching `.tex` files are the editable sources. The newest formal status
and remaining proof gaps are in [RESEARCH_STATUS.md](../analysis/RESEARCH_STATUS.md).
Older papers retain their historical scope and may describe steps that later
papers have completed.

To rebuild the latest pair with Tectonic:

```sh
tectonic paper/silver.tex
tectonic paper/silver_guide.tex
```

After editing, check the compiler log, cross-references, and rendered pages.
The current theorem audit is [theorem_audit.json](../analysis/theorem_audit.json).
