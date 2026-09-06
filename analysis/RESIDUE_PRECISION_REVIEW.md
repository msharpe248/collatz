# Residue precision review — 2026-09-05

The previous cycle-bridge checkpoint made progress but left global coverage open.
This pass checked a possible literature input before using it in the proof.

Primary source: Edward Y. Chang,
[A structural reduction of the Collatz conjecture to one-bit orbit mixing,
arXiv:2603.25753v1](https://arxiv.org/html/2603.25753v1), accessed September 5,
2026. The source itself leaves deterministic orbit balance open. We examined
specific finite-map statements in Theorem 4.2 and Section 5.2, not the entire paper.

## Kernel-checked findings

`Collatz.ResidueMapAudit` contains five public declarations:

- `gap_precision_witness`: 3 and 35 agree modulo 32 and are both 3 modulo 4,
  but their shortcut outputs have residues 5 and 21 modulo 32.
- `no_gap_map_mod32`: no function of the input remainder alone predicts every
  such gap output modulo 32.
- `gap_lift_formula`: T(3+32q)=5+48q for every natural q. The parity of the
  quotient is the missing bit in the proposed same-precision transition.
- `burst_precision_witness`: 29 and 61 agree modulo 32, whereas their compressed
  outputs 11 and 23 disagree modulo eight.
- `canonical_burst_counts_32`: canonical representatives below 32 yield two
  burst inputs whose compressed images are 3 modulo eight and one whose image
  is 7 modulo eight. Thus the signed difference at depth five is +1, not -1.
  The absolute difference remains one.

The latter distinction matters: interpreting residue notation as canonical
representatives may define finite counts, but does not make those representative
transitions valid for arbitrary integer lifts. The signed count discrepancy is
separate from this precision issue.

All five declarations build and pass the selected theorem axiom audit. The
Syracuse computations use the existing map definition and explicit kernel-checked
normalization of its valuation recursion, rather than native evaluation or a
custom arithmetic axiom. The 32-entry filter counts use those computed values.

## Research decision

Do not import these residue statements as a universal transition or mixing theorem.
Extra input precision repairs the demonstrated gap-step ambiguity; other finite
state descriptions require their own dependence checks. Even a corrected residue
map would still need pointwise orbit control. These findings neither disprove all
results in the source nor rule out a corrected reduction.

The paper and guide in `paper/residue_precision_audit*` document the exact scope.
No contact with the author or external publication was performed. No new global
Collatz theorem is claimed.
