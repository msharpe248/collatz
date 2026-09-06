# Actual requests of the odd-run transfer proof

The new Lean theorem `reachesOne_below_of_odd_run_requests` proves
convergence of every positive n<N from precisely the following sufficient
request schema: assume A(v) whenever there exist natural a,m with

`a >= 2`, `m > 0`, `m odd`, `2^a*m <= N`, and `36v+27 = 3^a*m`.

The previous `reachesOne_below_pow_two` now follows from this theorem and
the odd-run size bound. Its statement is unchanged. This narrows the
hypotheses of the proof construction; it does not assert that every
listed transfer instance is necessary for every proof of convergence.

## Finite enumeration

For a fixed a, the admissible m are 1 modulo four when a is odd and
3 modulo four when a is even. This is equivalent to the single-even
branch condition `3^a*m = 3 mod 4`. Enumerating these progressions up
to N/2^a gives all requests, with duplicates removed.

| Seed bound | Distinct requests | Instances in the sufficient interval | Largest request |
|---:|---:|---:|---:|
| 256 | 21 | 182 | 60 |
| 4096 | 341 | 14762 | 4920 |
| 65536 | 5461 | 1195742 | 398580 |

These census numbers are Python computations, not imported Lean certificates.
The smaller set is still unproved as a whole; fewer hypotheses do not mean
that the remaining hypotheses have been discharged.

## Smallest seed requesting a parameter

For a fixed v, write `4v+3 = 3^r*m` with m not divisible by three.
The smallest seed whose single-even odd-run branch requests v is

`minimum_seed(v) = 2^(r+2)*m - 1`.

Indeed, `36v+27=9*(4v+3)`, so admissible exponents a run from 2 through
r+2. Increasing a while dividing m by three multiplies n+1 by 2/3,
so the largest a minimizes the seed. All remaining oddness and modulo-four
conditions follow from the original equality. This is a written arithmetic
argument; the minimum formula has not yet been formalized in Lean.

For a cutoff u of available transfer parameters, the first unavailable
request occurs at

`N(u) = min { minimum_seed(v) : v >= u }`.

The script computes N(u) without scanning infinitely many v. At each a,
it takes the smallest m in the required modulo-four class with
`3^a*m >= 36u+27`. It starts with the available candidate 16u+11
(a=2, v=u) and stops when `2^a-1` exceeds the best candidate. No later
a can improve the minimum, because m>=1.

Examples: N(1)=27, N(15)=111, N(60)=127, N(61)=415, N(100)=447,
and N(1000)=1791. The first missing request at u=61 is parameter 87
at seed 415. The previously justified dyadic cutoff there is 128.
The exact-request theorem gives the logical criterion for using such a
cutoff, but the algorithm's output has not been supplied as a Lean proof
of its universal request-bound premise.

## Validation and next step

`test_transfer_requests.py` compares the progression enumeration against
an independent scan over seeds, checks the minimum-seed formula, and
exhaustively checks the first unavailable request for u=1..256. The saved
artifact is `transfer_requests_results.json`.

Run `python3 analysis/transfer_requests.py` and
`python3 -m unittest discover -s analysis -p 'test_transfer_requests.py'`.
The formal request schema is in `lean/Collatz/BoundedTransfer.lean`.

A next useful formal step is to certify the optimized cutoff or exploit
its first missing requests in the induction. Neither the request schema
nor its finite enumeration proves global coverage or the Collatz conjecture.
