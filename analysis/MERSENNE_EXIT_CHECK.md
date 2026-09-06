# Symbolic exits from the growing Mersenne prefix

For `k=6h+4`, the reduced source and target reach
`3^(4h+5)-7` and `3^(4h+6)-10` at time k. Thus write the exit
pair as `X-7, 3X-10`, with `X=3^e`, `e=4h+5`.

The search uses affine numerators `(aX+b)/2^t`. It accepts a merge only
when both coefficients and constants agree. Parities come from X modulo
`2^D`; negative representatives in the symbolic calculation do not assert
negative natural orbits. Each accepted rule is independently replayed on
positive lifts.

The exponent period `2^(D-2)` is valid for D>=3: start from
`3^2 = 1 mod 8` and repeatedly square; a congruence modulo `2^s`
lifts to one modulo `2^(s+1)`. Only exponents one modulo four are eligible.

| Exit depth bound | Eligible exponent residues | Covered | Unresolved | First cylinder rules |
|---|---:|---:|---:|---:|
| 12 | 256 | 1 | 255 | 1 |
| 16 | 4096 | 110 | 3986 | 44 |
| 20 | 65536 | 2879 | 62657 | 538 |

The saved JSON is the depth-16 census. These counts are experimental,
not Lean coverage theorems. Unresolved means no uniform direct merge
within this bound, not nonconvergence.

## First rule

For `X = 2995 + 4096Q`,

`T^12(X-7) = T^12(3X-10) = 533 + 729Q`.

The two paths have six and five odd steps respectively; both affine
numerators are `729X-187`. Since `3^981 = 2995 mod 4096` and
`3^1024 = 1 mod 4096`, this applies whenever
`e = 981 + 1024z`, equivalently `k = 1468 + 1536z`.
It gives a merge at reduced clock `k+12`, after a prefix of unbounded
length. This is compatible with the preceding prefix obstruction.

`lean/Collatz/MersenneExit.lean` contains the exact prefix identities and
the first progression's merge, strict parameter decrease, and the
conditional transfer implication. The whole search census is not imported
into Lean. The formal transfer theorem still requires a smaller-parameter
premise: for `w=(2^k-7)/9`, inverse transfer uses `v=8w+5 < u=9w+6`.
This result does not prove that premise for all such v or cover all k.

## Reproduce

- `python3 analysis/mersenne_exit_search.py --depth 16`
- `python3 -m unittest discover -s analysis -p 'test_mersenne*.py'`
- From `lean/`: `lake build Collatz.MersenneExit`

Tests compare the small census with full integer trajectories, replay all
44 saved symbolic rules at four positive quotient lifts, verify exponent
congruences, and check the complete first Mersenne prefix and exit.

The next mathematical task is to obtain enough exit transfers or exponent
reductions for a well-founded induction. The present sparse coverage does
not establish such an induction.
