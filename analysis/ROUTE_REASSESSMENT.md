# Independent proof-route reassessment

2026-09-05. The task remains a Lean proof of Collatz, not a collection of
reductions. The repository ideation skill was used with three isolated
parallel generators (the available child-agent capacity), followed by
scoring and three independent focused follow-ups. No full proof emerged.

## Wide set

Scores are prioritization judgments, not probabilities of proving Collatz.
N = novelty relative to this project, V = viability of a concrete next
investigation, F = fit to the full goal. Weighted score: .35N + .40V + .25F.

### Ordinary integers inside the 2-adic model

- Force infinite nonzero seed digits through carries [N7 V4 F9].
- Exclude integer alignment in shrinking inverse intervals [N6 V3 F9].
- Track nested growing-prefix constraints [N5 V5 F8].
- Characterize ordinary-integer membership in the inverse limit [N6 V3 F9].
- Build a finite-support carry tiling [N8 V4 F8].

### Affine replacements and congruence compatibility

- Replace a prefix by a smaller admissible predecessor [N8 V5 F8].
- Compare smallest cylinder representatives [N5 V6 F8].
- Audit overlapping return certificates [N6 V5 F8].
- Track terminal ternary authorization classes [N4 V8 F8].

### Divisibility consumption and replenishment

- Charge growing returns for ternary carries [N7 V5 F8].
- Prove rigidity of successive exact valuations [N7 V4 F8].
- Telescope a return divisibility ledger [N7 V5 F8].
- Use modular checksum clocks modulo 3^a-1 [N7 V5 F6].
- Track variable affine overflow maps [N7 V6 F8].

### Correction and binary carry observables

- Classify rational inverse expansions [N7 V2 F9].
- Track denominators of residual ideal correction [N6 V3 F8].
- Preserve positional binary carry conservation [N8 V7 F8].
- Synchronize nearby seeds and overflow [N3 V8 F7].

## Converge

The top fresh, concrete investigations after excluding already-covered
ideas were carry conservation (7.60), variable affine overflow (6.85),
and admissible word surgery (6.80).

- **Carry conservation:** a new exact observable, with a direct finite
  implementation check. No sign condition has been established.
- **Variable overflow:** an explicit transition determinant makes proposed
  divisibility ranks falsifiable. Its first uniform-reset conjecture fails.
- **Starred non-obvious candidate: admissible word surgery.** It could use
  least-unbounded-seed minimality without preserving full NeverContracts,
  but existence of a suitable replacement remains a serious open issue.

Traps rejected or deferred:

- Cylinder transport and terminal ternary congruences are already proved;
  reformulating them does not provide an exclusion.
- A nested system may contain a 2-adic integer without a positive natural
  seed; compactness cannot exchange these domains.
- Shrinking real intervals may keep containing the same integer; shrinking
  width alone is not a contradiction.
- An arbitrary real correction has no established rational denominator to
  track. A rationality classification would introduce another hard problem.
- A carry ledger cannot charge high-bit information twice or silently
  assume that later high-bit flux is absent.

## Focus: carries

For binary digits b_i of n, set b_-1=0 and c_0=1. Local addition gives
c_(i+1)=floor((b_i+b_(i-1)+c_i)/2). If C is the sum of outgoing carries,
the exact identity is s2(3n+1)+C=2*s2(n)+1. Over shortcut orbits, even
steps preserve digit sum, so the odd-step identities telescope. Retaining
positions or a moving spatial boundary might expose information that
the ordinary affine identity discards. The load-bearing risk is that
this is only a reformulation with no signed bound on later boundary flux.

First action completed: `reassessment_checks.py` checks all 65,536 seeds
below 2^16, including zero and termination of the carry trace. This finite
check is not a Lean proof or an orbit termination argument.

Children: moving high-bit boundaries; first spatial moments of carries;
separate support expansion from total carry count; test any proposed sign
against the existing arbitrarily long growing-return families.

## Focus: variable overflow

Write a return branch as F_w(n)=(A_w*n+B_w)/D_w and its reserve as
q_w(n)=(A_w-D_w)*n+B_w. A repeated branch satisfies
q_w(F_w(n))=A_w*q_w(n)/D_w. A switch to v instead gives

    (A_w-D_w) q_v(F_w(n))
      = A_w(A_v-D_v) q_w(n)/D_w + C_wv,
    C_wv = (A_w-D_w)B_v - (A_v-D_v)B_w.

The first test was whether a fixed branch pair has bounded valuation
recharge. It does not. Choose w=1101, v=101, so their data are (27,23,16)
and (9,7,8), and C_wv=54. For r>=1, set n=16*64^r-5 and y=F_w(n).
Then v2(11*n+23)=5, while y+7=27*64^r has valuation 6r. These are actual
consecutive growing returns. The finite replay checks r=1,2,4,...,64;
`GrowingReturns.unbounded_reserve_reset` proves the parameterized residue
and identity certificate in Lean. A proof that debits block length while assuming bounded reset gains needs
additional accounting: high seed bits can pay for a large reset. This
does not rule out every potential built from branch and valuation data.

Children: determinant valuation classes; simultaneous constraints from
three blocks; shared-fixed-point switches; symbolic treatment of long
odd runs. None currently supplies a decreasing global measure.

## Focus: admissible word surgery

Let N be a least positive unbounded seed and y a later orbit value. A word
of length s, odd count k and attainable correction d yields a smaller
positive merging predecessor exactly when

    2^s*y = d (mod 3^k),
    2^s*y - 3^k*(N-1) <= d <= 2^s*y - 3^k.

The inequalities here are integer inequalities, not truncated natural
subtractions. Such a predecessor would contradict minimality. Unlike a
least-NeverContracts argument, the intermediate coefficients need not all
be noncontracting. The risk is hiding the whole convergence problem in
the assertion that such a word exists. The repository already has exact
attainability and congruence checks, but not that existence theorem.

First concrete next action: test equal-length, equal-count replacements
with d>D and d=D modulo 3^k, on actual prefixes; record failure separately
from infeasibility at all lengths. Children: adaptive endpoint selection,
valuation-guided odd budgets, local swaps with congruence repair, and
attainable-correction gap bounds.

## Provocation

Can a smaller merging predecessor be forced using several different
forward endpoints together, even when no single endpoint admits a useful
fixed-budget inverse argument? This is the next candidate to test, not an
assumption to insert into Lean.


## Word-replacement test completed (2026-09-05)

`Collatz.WordSurgery` now proves the exact equal-length/equal-count
replacement criterion, the correction-shift certificate, and the classical
Garner stems 1^a00 / 01^(a-1)01. These stems are established literature,
not a new discovery: Elia and Tucker, Section 3,
https://arxiv.org/abs/1511.09141 (full paper consulted). Their work also
warns that Garner's proposed stem classification is not exhaustive.

The exhaustive depth-18 census finds 193,309 covered binary cylinders out
of 262,144, including 1,391 of the 7,495 whose every prefix coefficient
is noncontracting. Every reported canonical merging pair is replayed
independently; equal counts transport it to all lifts. These are Python
counts, not a kernel-certified census or asymptotic estimate.

Lean proves an all-time boundary: no x with 0<x<27 can merge with 27 at
an equal time and equal odd count. A finite kernel check through time 70
plus exact odd-count inequalities on the 1,2 cycle proves the all-time
statement. Thus the unrestricted universal version of this method is
false. Since 27 converges, this does not refute coverage conditional on
least-unboundedness. The smaller-merge contradiction to least-unboundedness
is separately formalized and needs no noncontraction of the replacement.

Next experiment: allow the replacement odd count to vary, with exact
attainability and seed positivity retained. Cylinder transport with equal
slopes no longer applies unchanged: ternary congruences must also track
the cylinder quotient. No universal existence premise has been inserted.


## Variable odd-count comparison completed (2026-09-05)

`analysis/variable_count_surgery.md` derives a finite endpoint-residue test
that accounts for every nonnegative quotient, not merely the canonical
seed or sampled lifts. At every depth 1 through 18, changing the odd count
adds no smaller same-time merging predecessor to any noncontracting-prefix
cylinder missed by equal-count replacement. At depth 18, all 6,104 such
remaining cylinders fail both the lower- and higher-count tests. This is
an exact Python census, not a kernel-certified all-depth theorem.

Three new Lean declarations support the arithmetic: the universal bound
3n < x + 2^(t-j_x) for a lower-count same-time merge; its consequence
x>2n when n>=2^t; and the exact higher-count merging lift formula on a
ternary progression of binary-cylinder quotients. The technical paper
and guide have been updated. The next experiment should vary replacement
length, and distinguish meeting before forward descent from merely
rediscovering a later orbit value already below the starting seed.


## Variable lengths produce additional certificates (2026-09-05)

The bounded search now varies both forward time and replacement length
from zero through 18, for canonical seeds 0<n<2^18 whose first 18
coefficients never contract. Of 7,495 such seeds, 1,391 were covered by
the previous equal-time/equal-count test. Variable lengths add 3,768,
leaving 2,336 unresolved. All additions have certificates preserving full
noncontraction; 937 selected certificates use positive forward time.
These are finite seed counts, not all-quotient cylinder coverage. The
smallest uncovered seeds include 27, 327, 447, 495, 639, 667 and 703.
No original path descends before a certified meeting.

`Collatz.DominatingMerge` formalizes the exact condition: the replacement
prefix must be noncontracting and its final coefficient must dominate the
original prefix coefficient. This avoids the invalid inference that a
shift of a noncontracting seed must itself be noncontracting. The cocycle
then proves full noncontraction of the replacement from that of the
original, even when the meeting times differ.

The infinite family N=111+4374Q, M=103+4096Q, Q>=0, merges at T(N)=T^12(M).
The coefficients are 3/2 and 3^8/2^12, with domination ratio 2187/2048.
Lean proves the actual parities, prefix inequalities, and 0<M<N, and hence
NeverContracts N implies NeverContracts M. It excludes this progression
for a least positive noncontracting seed, not arbitrary noncontracting
seeds, and it does not prove convergence of the entire progression.

Next action: examine the unresolved seeds and compress successful
certificates into seed-dependent arithmetic rules, keeping coefficient
transport and positivity explicit. Merely increasing a fixed search
length cannot be treated as a universal proof.


## Arithmetic rule lifting and kernel validation (2026-09-05)

The previous 3,768 dominating certificates now normalize to 360 distinct
arithmetic progressions. All 360 finite rules pass Lean kernel validation;
the generic `MergeRule.sound` theorem proves each progression for every
natural quotient. The output is in `MergeRuleTable.lean`, with reproducible
JSON and source generation in `analysis/merge_progressions.py`.

For base counts j,k use quotient steps a=3^max(k-j,0), b=3^max(j-k,0).
The increments 2^t*a and 2^s*b preserve the endpoint and are ordered by
the coefficient-domination inequality. Backward normalization is stopped
before positivity or strict seed ordering fails, and Lean independently
checks the resulting base certificate. This improves the scope of the
verified examples but does not prove that the rule union covers all
hypothetical least noncontracting seeds.

The source census remains Python evidence. The validity of every retained
rule and its all-quotient extension are kernel certified. Regeneration
checks all 2,336 unresolved source seeds against the retained union; none
is falsely reclassified as covered. Further work must find an applicability
argument using rules that may depend on the seed, rather than treating a
finite list as a full proof.


## A structural constraint on equal-count NC merges (2026-09-05)

The zero-addition observation for varying counts at fixed time was tested
through depth 20, still with no additions; this remains finite evidence.
A separate NC-only collision search found no equal-count collision through
depth 30. General injectivity without matching counts is false already
at time seven (31 and 95 merge at 182 with counts six and five).

The finite pattern has a compact proof through time 31 for all natural
seeds. `NCPrefixInjective` bounds d+2^j between 3^j and 5*3^j using a
kernel-checked arithmetic envelope. Both seeds are 3 modulo 4; an equal
count/endpoint merge forces their difference below four and hence zero.
The interval itself fails at time 32 for an actual NC-prefix seed, also
kernel certified. The injectivity question at time 32 and beyond remains
open here; interval failure is not an injectivity counterexample.

This is a limitation of same-time/equal-count noncontraction-preserving
surgery, not a new proof of Collatz. An all-time extension would need
relative correction control or additional parity information. For the
main goal, variable-length/count applicability remains the unproved
load-bearing step; finite injectivity must not replace that objective.

## Shifted merge chains with exact coefficient deficits (2026-09-05)

The initial applicability check found that the 360 retained rules have
maximum boost 3/2. Their affine intercepts have mixed signs (257 positive,
103 negative, none zero), so neither arbitrarily strong single-rule boosts
nor a uniform negative additive correction is available from this table.
This evidence motivated chaining rules while retaining a quantitative
bound on a shifted orbit, rather than assuming shifted noncontraction.

`MergeDeficit.lean` represents a coefficient floor a/b by
`CoefficientBound a b n := ∀ i, a*2^i ≤ b*3^oddSteps i n`.
A shift of a NeverContracts seed has floor 1/C_k(N). A merge of boost rho
and an NC replacement prefix changes the inverse floor D to max(1,D/rho).
The merge and binary-cylinder versions are proved by natural arithmetic.
The kernel-checked all-quotient example is

    NeverContracts (447 + 549755813888Q)
      → NeverContracts (307 + 376572715308Q),

with a positive, strictly smaller replacement. It uses a shift of 23 and
three rules. Intermediate deficits remain above one; the final bound is
one. Thus the proof explicitly handles the shifted-tail applicability gap.
It does not prove that the new progression, or all possible chains,
covers every hypothetical least NC seed.

The exact DAG search processes decreasing seeds and keeps the smallest
deficit found at each seed. Among the 2,336 previously unresolved canonical
seeds at depth 18, shifts through 64 yield 1,012 chain certificates, 1,216
coefficient contractions before a certificate, and 108 horizon exits.
No 10,000-state-per-shift cap is reached. Of the successful seeds, 182
have no single-rule witness at any searched shift before contraction;
101 selected chain witnesses start at shifts at most 18. All saved chains
pass independent direct-orbit replay. Search completeness is Python
evidence; only the general transport and explicit infinite family are
newly kernel certified. The selected audit now covers 183 declarations.

The next substantive obligation is structural coverage or a useful
obstruction to such coverage. Increasing finite orbit horizons alone
would mostly rediscover known convergence of the sampled small seeds.
An approach based on these chains must force enough accumulated boost
and a final seed below the original, with actual rule congruences, for
arbitrary hypothetical least NC seeds. Even that would address
nondivergence; exclusion of nontrivial cycles remains a separate task.
