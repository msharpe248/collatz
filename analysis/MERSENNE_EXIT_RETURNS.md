# Smaller-exponent returns: three new obligations, no closed coverage gain

Status: exact symbolic experiment and independently replayed certificates;
not a Lean theorem. This extends the exit investigation without claiming
that the added conditional rules close the induction.

Let `F(e)` mean `ReachesOne(3^e-7) -> ReachesOne(3^(e+1)-10)` for
`e >= 5`, `e = 1 mod 4`. A positive drop d divisible by four preserves
this family. A sufficient return certificate consists of

- `T^s(3^e-7) = T^s(3^(e-d)-7)`;
- `T^t(3^(e+1)-10) = T^t(3^(e-d+1)-10)`.

These imply `F(e-d) -> F(e)` when `e-d >= 5`. The source and target
clocks s and t may differ. Each individual equality uses the same clock
on its two sides. To certify it uniformly, write `Y=3^(e-d)`. The
upper and lower affine numerators must have identical coefficients of Y
and identical constants. Equality at a single numerical seed is insufficient.

## Exact bounded census

The saved census uses depth 20, drops 4, 8, 12, and 16, and all 65,536
eligible exponent residues modulo 262,144. There are 2,334 residues with
some source return, 76 with some target return, and five where both
returns use the same drop. All five use d=4:

| Exponent residue | Source clock | Target clock | Direct merge by depth 20? |
|---:|---:|---:|:---:|
| 24541 | 20 | 18 | yes |
| 173669 | 20 | 20 | yes |
| 207273 | 13 | 20 | no |
| 216957 | 19 | 20 | no |
| 247389 | 16 | 20 | no |

The three additional classes reduce respectively to residues 207269,
216953, and 247385. None of these premises has a direct merge by depth
20, and none has a pair-return rule in this census. Consequently the
combined table discharges no additional residue beyond direct merges.
It adds three conditional obligations, not three proved cases.

## Why this matters for the next step

There is also a general limitation on this kind of bounded closure.
If both return equalities hold by clock D, they persist to D. If the
smaller pair has a direct merge by D, transitivity gives a direct merge
of the larger pair by D as well. The affine equalities compose in the
same way. Thus closing these pair returns using only direct merges
already within the same depth bound cannot enlarge an exhaustive
uniform direct-merge census at that bound.

These returns might become useful with a different terminal proof,
additional transfer operations, or deeper certificates for the premises.
They do not currently justify expanding the Lean library by five more
isolated rules. The next search should seek a proof mechanism that
changes these unresolved premises, rather than counting them as coverage.
No impossibility beyond the specified certificate family is asserted.

## Reproduce

- `python3 analysis/mersenne_exit_returns.py`
- `python3 -m unittest discover -s analysis -p 'test_mersenne*.py'`

The saved artifact is `mersenne_exit_returns_results.json`. Tests compare
an exhaustive depth-12 census against full integer trajectories, replay
all five depth-20 certificates at three positive quotient lifts, and
verify that the three new premises are unresolved by the combined table.
