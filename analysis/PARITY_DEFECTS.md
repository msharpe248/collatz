# Finite near-periodicity certificates

Date: 2026-09-05. Proved in `lean/Collatz/ParityDefects.lean`.
No literature priority or proof of the full Collatz conjecture is claimed.
Publication versions: [paper](../paper/defects.pdf) and
[guide](../paper/defects_guide.pdf), with matching LaTeX sources.

## Exact finite theorem

Suppose N+1≤2^K. Count the disagreements
`T^t(N) mod 2 ≠ T^(t+q)(N) mod 2` for 0≤t<L.
If there are at most D and `L ≥ (2^(D+1)-1)(q+K)`, then
`T^(s_k+q)(N)=T^s_k(N)` at one of the checkpoints
`s_k=(2^k-1)(q+K)`, 0≤k≤D.

For q>0 this bounds the entire orbit and makes its tail periodic with
period dividing q. It does not classify all cycles. For q=2 and N>0,
Lean proves that the certificate implies reaching 1.

If a parity prefix of length L+q differs in at most e letters from a
q-periodic template, there are at most 2e shift disagreements. Therefore
`L ≥ (2^(2e+1)-1)(q+K)` forces a return. Edit positions are unrestricted;
there is no odd-density or bounded-ideal-correction hypothesis.

## Proof mechanism

The height bound is `T^u(N)+1 ≤ 2^u(N+1) ≤ 2^(u+K)`.
If no q-shift disagreement occurs for s+q+K comparisons starting at s,
the two starts `T^s(N)` and `T^(s+q)(N)` share that many parity letters.
The parity congruence theorem forces them to be equal: otherwise their
maximum is at least 2^(s+q+K), contradicting the height bound.

Thus failure to return at s forces a disagreement in `[s,2s+q+K)`.
The checkpoints satisfy `s_(k+1)=2s_k+q+K`, so these windows are disjoint.
D+1 failed returns require D+1 different disagreements. For the template
extension, an edited letter at i can affect only comparisons i and i-q.

The initial weighted-swap route exposed a limitation: one swap after i
initial zero letters changes the affine correction by 2^i. Swap count
alone cannot provide a uniform small correction bound. The new argument
uses the intervals between disagreements and pays an exponential length
cost in their count.

## Worked controls and verification

For N=3, K=2, q=2, the only shift disagreements below L=60 are at
times 0, 1 and 3. The threshold is (2^4-1)*4=60. The checkpoints are
0, 4, 12 and 28; the return already occurs at s=4, at orbit value 2.
The same orbit differs from `w(t)=t mod 2` only at times 0 and 3.
For e=2, the template threshold is L=124, requiring 126 parity letters.
These finite counts and thresholds were checked with Lean's kernel-checked
`decide` in a temporary control file; they are not computation records.

`lake build Collatz.ParityDefects` passes. The expanded command
`python3 analysis/audit_theorems.py --build` audits 35 declarations,
including the new return, template, boundedness and period-two results.
Only standard foundational axioms occur. This is ordinary Lean checking
and axiom inspection, not independent kernel replay or a fresh rebuild
of all dependencies.

## Remaining gap

The required horizon grows exponentially with the number of defects.
No theorem says every hypothetical counterexample has a sparse enough
near-periodic prefix to meet it. `unbounded_forces_defects` proves a
necessary condition: every unbounded orbit has more than D disagreements
by the stated horizon, for every positive lag and every D.

This is a symbolic obstruction to an itinerary class. Checking its long
prefix is not proposed as a faster cycle-detection algorithm. General
periods still leave cycle classification open. Period two implies the
trivial cycle, but universal availability of its certificate is unproved.
Since an orbit reaching 1 eventually alternates, assuming universal
availability would rephrase the desired convergence.

Next: derive independent, noncircular restrictions on defect counts or
sharpen the window growth using proved local height information.
