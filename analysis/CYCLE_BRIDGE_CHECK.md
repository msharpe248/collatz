# Exact behavior of late cycle bridges — 2026-09-05

The preceding exponent-return checkpoint made experimental progress but did not
close the terminal family. This check returns to the auxiliary-transfer proof
state and identifies what an unlimited number of one particular kind of bridge
can accomplish. It is a certificate-construction result conditional on finite
base-orbit convergence, not a proof of universal transfer.

## Cycle invariant

At clock t the symbolic source has the form x+3^p*2^(D-t)*Q. When x is 1 or 2,
define

    L(x,p,t) = 2p-t + indicator(x=1).

One ordinary Collatz step preserves L: 2 goes to 1 without an odd step, and 1
goes to 2 with one odd step. At a fixed clock, L determines both the cycle state
and p, since its parity determines the indicator. Thus the two symbolic endpoints
coincide exactly when their charges agree, once both base states lie in the cycle.

At x=2 a transfer bridge replaces (2,p) by (20,p+2). The orbit segment

    20, 10, 5, 8, 4, 2, 1, 2

has seven steps and two odd steps. Including the bridge, the total p increment is
four. Consequently the completed excursion raises L by exactly 2*4-7=1.
We forbid further bridges during this excursion for this restricted mechanism.

## Exact scope of the construction

Assume the two base orbits at parameter u>0 have reached {1,2}, and let delta be
target charge minus source charge.

- If delta=0, their symbolic endpoints already match.
- If delta>0, delta completed cycle excursions make the charges match.
- If delta<0, no number of these excursions can match them: waiting preserves
  the charges and each excursion raises the source charge by one.

Each excursion uses the recursive parameter

    v = 3^(p-1)*2^(D-t)*Q.

To guarantee v<u+2^D*Q for every natural Q, require 3^(p-1)<=2^t. Waiting two
steps at x=2 multiplies this slope ratio by 3/4, so sufficiently long waiting
makes the inequality true. For any finite number of excursions the construction
therefore has a finite valid schedule. At its final clock D, all earlier path
parities lift correctly to the cylinder u+2^D*Q, and all recursive parameters
are strictly smaller. The implementation has an explicit cap and reports any
cap separately; its cap is not used to claim an all-time obstruction.

These are written arithmetic arguments. The new construction is not a Lean
coverage theorem. Its individual transfer inference steps use the rule already
formalized in Collatz.AffineBridge; the general schedule and invariant have not
been formalized here.

## Finite census

For base parameters 1..1000, this restricted construction produces 698 conditional
all-quotient certificates. The other 302 have negative cycle gaps. The largest
certificate uses 36 bridges and reaches clock 412. There are no cap outcomes.
All saved certificates are independently replayed on integer quotients 0,1,7,
checking the entire path, each recursive parameter, and the endpoint slope.

The 302 figure does not mean these parameters are unsolvable: earlier bridges
may have different effects. A subsequent Lean theorem in `Collatz.BridgeGrowth`
now rules out lowering charge even with bridges inserted inside excursions; see
`paper/bridge_growth.tex`. Nor does the
698 figure count independently proved transfer implications: smaller transfer
premises remain explicit. Parameter zero is excluded because its bridge parameter
would not be strictly smaller at Q=0; it can instead be a separately checked base
case.

## Consequence for the full goal

This supplies a constructive alternative to brute-forcing bridge counts when the
cycle gap is nonnegative. It proves why merely repeating the same late bridge
cannot address the negative gap cases. However it uses convergence of the base
target to locate its cycle charge. Assuming that for every base target would
already assume the convergence problem. It therefore cannot be used as an
unconditional global coverage argument.

A future improvement should act before the unknown target reaches the cycle or
provide a new symbolic family with proved closure. Increasing this restricted
bridge budget cannot remove the identified directional obstruction. This is an
experimental-method note, not a new Collatz proof or a priority claim.

Reproduce: `python3 analysis/cycle_bridge_search.py`.
Tests: `python3 -m unittest discover -s analysis -p test_cycle_bridge_search.py`.
