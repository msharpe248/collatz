# Review of the delay-bound route

Reviewed 2026-09-05 after the growing-return construction. This is a
source and hypothesis review, not a new mathematical result or a complete
dependency audit of the nested repository.

## Sources checked

- [Rozier and Terracol, arXiv:2502.00948v4](https://arxiv.org/html/2502.00948v4),
  especially Corollary 3.3 and Section 6.
- [Niu, arXiv:2605.13886](https://arxiv.org/abs/2605.13886): withdrawn in v2
  on May 20, 2026. The stated reason is duplication of Rozier–Terracol's
  enumeration and related observations, not an announced mathematical error.
- Local `library/repos/rwst__lean-code/RT/Heuristic.lean`.
- Local `library/repos/rwst__lean-code/CITED/RhinLogForm.lean`.
- Local `library/repos/rwst__lean-code/RT/CRozLemma32.lean`, final
  `CRoz_cor_33` statement and proof entry.

## What is conditional

The source's finiteness argument compares an exponentially small upper
bound for a logarithmic gap against a polynomial lower bound. The upper
bound uses conjectural global delay and excursion estimates. These are
not unconditional bounds that can now be imported to settle the goal.

The local definition `Conjecture62 α β` explicitly includes

```lean
∀ n : ℕ, 2 ≤ n → (∃ i, T_iter i n = 1) ∧ (dT n : ℝ) ≤ α * Real.log n
```

along with positivity of the constants and a global excursion bound.
The reach-one conjunct matters because `dT` defaults to zero if there
is no hitting time. A bound on that default-valued function alone would
not prove convergence. The formal predicate correctly keeps convergence
explicit; it is stronger than the missing convergence obligation.

The declarations `conjecture_61` and `conjecture_62` both contain `sorry`.
The surrounding comments and attributes identify them as open research.
The conditional theorem `heuristic_chain` takes `hConj : Conjecture62 α β`
as an explicit argument. Its proof does not establish that premise.

The declaration `Rhin.logForm_lower_bound` is explicitly an `axiom` in
`CITED/RhinLogForm.lean`. It represents a cited transcendence estimate.
This observation concerns the Lean trust footprint, not the truth of
Rhin's published mathematics. Proving or assuming that lower bound alone
would not supply the missing global delay/excursion upper bounds.

The local `CRoz_cor_33` theorem takes finiteness of all paradoxical pairs
with starting term above two as an explicit premise. A finite-length
census such as our length-65 computation does not discharge it.

## Decision for the main proof program

Do not import the open conjecture declarations or use `Conjecture62` as
an established hypothesis. Do not describe the Section 6 chain as an
unconditional proof of finiteness. No such import or assumption was added
to the main Lean project during this review.

The withdrawn Niu note supplies no independent new route beyond the
primary paper examined here. The fixed-return budget is already ruled
out by our explicit construction. A viable next estimate must instead
be proved from properties of an individual hypothetical counterexample,
without presupposing a global hitting time. Existing reciprocal
summability and relative-correction decay are available for this purpose;
they do not currently provide the required delay or excursion bound.

No new theorem, resolution of a conjecture, or completed nested-library
axiom audit is claimed by this review.
