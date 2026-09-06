# Direct descent after the Mersenne exit

Status: finite exact-integer experiment and an elementary written lower
bound; no new Lean theorem or global convergence result.

For h>=0 the original parameter is `u(h)=16*64^h-1`. The reduced target
after its growing prefix is `B(h)=729*81^h-10`. The experiment looks for
the first d with `T^d(B(h)) < u(h)`.

## Evidence

Every h from 0 through 512 has such a descent within the cap of 20,000
steps. The largest first-descent clock is 1098 at h=453, with 592 odd
steps. The first twelve clocks, starting at h=0, are
`30,63,30,50,41,70,48,54,40,38,41,160`.
These finite witnesses do not establish a uniform bound. For example,
the candidate bound `d <= 4h+100` already fails at h=11, 19, and 45.
No fitted bound is promoted to a conjecture or imported into Lean.

The script preserves depth limits as unresolved observations. The saved
JSON records all 513 clocks, odd counts, and exact necessary lower bounds.
Tests independently reconstruct first-hit trajectories for h=0..63 and
check the full census summary.

## Every fixed exit-depth bound fails on this family

For positive n, every shortcut step is at least n/2, so
`2^d*T^d(B) >= B`. Strict descent below u requires `2^d*u > B`.
The exact necessary integer lower bound is therefore
`bit_length(floor(B/u))`, which the script records without logarithms.

A simple growing bound is `d >= floor(h/3)+6`. Write h=3m+r with
0<=r<3. Since `81^3 > 2*64^3` and `81^r >= 64^r`,
`81^h >= 2^m*64^h`. Consequently

`B(h) > 2^(m+5)*u(h)`.

Indeed, subtracting the right side from the lower estimate for B leaves
at least `217*2^m*64^h + 32*2^m - 10 > 0`. Any d<=m+5 is impossible
by the elementary per-step lower bound. Thus no fixed number of steps
after the exit can prove all these descents. This does not obstruct the
previously formalized exit merges, which require no descent below u.

## The induction premise must stay explicit

A descent below u proves convergence of B only if convergence of the
smaller endpoint is available. In ordinary strong induction, convergence
of every positive m<u would suffice. The current affine-transfer induction
instead assumes smaller transfer statements `A(v)`; those statements are
not assertions that all smaller integers converge.

The proof of `collatz_iff_restricted_affine_transfer` in
`lean/Collatz/AffineConvergence.lean` uses an odd-run endpoint as its
transfer argument. It does not provide a theorem bounding that transfer
argument by the original seed. Therefore it cannot be silently truncated
to infer convergence of all m<u from the premises `A(v)` for v<u.
For a concrete example, seed 511 has odd-run length nine. Its predecessor
510 reaches 1640 after eleven steps, while 511 reaches 14762. These are
`3*546+2` and `27*546+20`, so this proof construction invokes parameter
546, which is larger than seed 511. This refutes the proposed bound on
this construction, not every possible bounded-transfer theorem.
No such implication is assumed by this experiment.

A useful next result would need both a variable-length descent argument
and a valid way to supply its convergence premise, or a transfer
construction that directly reuses the known source orbit. Merely replacing
an unresolved exit merge with a numerically observed descent does not
complete the current induction.

## Reproduce

- `python3 analysis/mersenne_exit_descent.py`
- `python3 -m unittest discover -s analysis -p 'test_mersenne_exit_descent.py'`
