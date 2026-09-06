# Mersenne prefixes of the three-step inverse template

Status: written arithmetic argument with exact-integer tests; **not yet
formalized in Lean**. This concerns one transfer template, not Collatz
convergence in general.

For `k = 4 mod 6`, put `u = 2^k - 1` and `w = (2^k - 7)/9`.
The three-step inverse template starts its reduced comparison at
`A₀ = 243w + 175 = 27·2^k - 14` and
`B₀ = 243w + 182 = 27·2^k - 7`.
Here `T(n)` is `n/2` for even n and `(3n+1)/2` for odd n.

For every `0 ≤ t ≤ k`, let `j` and `l` count odd steps in the
source and target respectively. The exact formulas are:

- At `t = 0`, `A₀ = 27·2^k - 14` and `j = 0`.
- For `t = 1 + 3m + r`, `0 ≤ r < 3`,
  `j = 2m + [r ≠ 0]` and
  `A_t = 27·3^j·2^(k-t) - c_r`.
- For `t = 3m + r`, `0 ≤ r < 3`,
  `l = 2m + [r ≠ 0]` and
  `B_t = 27·3^l·2^(k-t) - c_r`.

The constants are `(c₀,c₁,c₂) = (7,10,5)`. After the initial even
source step, these formulas follow the negative cycle
`-7 → -10 → -5 → -7`. At each step before k, the positive power-of-two
term is even, so the constants determine the parity. Substitution into
the two branches of T proves the formulas by induction.

## What this excludes

An extra forward transfer in `two_early_bridges.py` requires the
all-quotient slope condition `3^(j+2) ≤ 2^t`. It fails throughout this
prefix. At zero the comparison is `9 > 1`; at times `1+3m`, `2+3m`,
and `3+3m`, the left sides are respectively `9·9^m`, `27·9^m`, and
`27·9^m`, while the right sides are `2·8^m`, `4·8^m`, and `8·8^m`.
Thus no first extra forward transfer is admissible by time k, regardless
of the allowed number of such transfers.

The uniform direct merge criterion also fails. At zero the endpoints
differ by seven. At positive times congruent to zero or one modulo
three, `j = l - 1`. At times congruent to two, the counts agree but
`B_t - A_t = 5`. Hence this template cannot certify these parameters
at depth at most k.

This does not exclude later certificates, different inverse templates,
or a different transfer condition. A fixed depth bound cannot resolve
all the listed Mersenne parameters using this template.

## Reproduction and next research decision

Run `python3 analysis/mersenne_inverse_prefix.py` and
`python3 -m unittest discover -s analysis -p 'test_mersenne_inverse_prefix.py'`.
The tests compare the formulas against direct trajectories for every
`k = 0..100` and every `t ≤ k`.

The saved probes use `k = 4,10,...,64`, depth 300, and at most one extra
forward transfer. Nine produce certificates, all after k, and their
quotient lifts are replayed at 0, 1, and 7. Exponents 10 and 28 reach
the depth limit; these are unresolved probes, not impossibility results.

Further work should examine symbolic exits after this growing prefix
or a different inverse template. Merely raising a fixed depth does not
address the unbounded prefix length.
