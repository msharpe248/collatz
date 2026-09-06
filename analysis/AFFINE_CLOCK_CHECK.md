# Clock rigidity for power-of-three cylinder slopes

The proposed extension of the Mersenne exit-return search was to let the
upper and lower exponent trajectories use different clocks. For uniform
ordinary-orbit equalities on a shared binary cylinder, that extension
cannot yield additional certificates when the initial slopes differ only
by powers of three.

## Formal statement

`Collatz.uniform_orbit_clock_rigidity` in `lean/Collatz/AffineClock.lean`
proves the following. Let s,t <= D. If, for every natural Q,

`T^s(r + 2^D * 3^a * Q) = T^t(v + 2^D * 3^b * Q)`,

then s=t and `oddSteps(s,r)+a = oddSteps(t,v)+b`.
No convergence or cycle-entry premise is used.

The cylinder transport formula gives slopes

`3^(oddSteps(s,r)+a) * 2^(D-s)` and
`3^(oddSteps(t,v)+b) * 2^(D-t)`.

Evaluating an affine equality at Q=0 and Q=1 forces the slopes to be
equal. Coprimality of powers of two and three forces equality of their
respective exponents. The bound s,t <= D then gives s=t.

This is an elementary arithmetic restriction, formalized to delimit the
search space; no novelty claim is made. The module also exposes the
underlying slope lemma and the affine-endpoint version.

## Application and limits

For an exponent drop d, writing Y=3^(e-d) makes the two initial slopes
3^d and 1 (or 3^(d+1) and 3). Thus a fixed-parity, affine-identity
certificate for an exponent return cannot gain anything by using
unequal clocks on those two ordinary orbit segments. The existing search
already permits the source equality and target equality to have different
clocks from each other; that freedom is unaffected.

This does not exclude:

- equality at individual starting values without a uniform cylinder;
- constructions whose parity descriptions vary with the quotient;
- initial slope ratios containing powers of two;
- auxiliary transfer or inverse operations outside the compared ordinary
  orbit segments.

The theorem applies directly to the all-quotient symbolic certificates
used by the current search. It is not a theorem that every conceivable
proof of an exponent-family implication must use equal clocks.

Together with `MERSENNE_EXIT_RETURNS.md`, this removes two redundant
extensions of the present method: adding unequal clocks under these
slope assumptions, and closing same-clock returns solely by direct merges
within the same fixed depth. A useful next extension must change a premise
or operation covered by these restrictions.

## Verification

From `lean/`, run `lake build Collatz.AffineClock`. From the repository
root, with the pinned Lean toolchain on PATH, run
`python3 analysis/audit_theorems.py --build`.
