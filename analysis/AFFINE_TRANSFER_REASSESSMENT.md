# Affine-transfer strategy reassessment — 2026-09-05

## Brief

Find a mechanism that extends actual induction coverage, rather than another
reformulation equivalent to Collatz. The old two certificate criteria fail at
all future times for 812 of the 1001 tested parameters, even though their pairs
converge. Finite base cases could handle these; the experiment does not establish
an infinite obstruction. The previous status-only turn made no research progress;
this continuation implemented, tested, and formalized the selected mechanism.

Used the repository ideation skill with three isolated generator frames, six
ideas each, scaled to the three available worker slots. All generators completed
before selection; three independent focus tasks then deepened the shortlist.
Scores below are subjective research-priority scores, not probabilities of
proving Collatz. Weighted score is .35N + .40V + .25F. Viability means a concrete
research step can be implemented, not that the global argument is established.

## Wide set, grouped by underlying approach

### Ordinary integers inside compatible local descriptions

- I1: Invert infinite parity coding into an integrality obstruction. [N3 V3 F9]
- I3: Use the moving boundary between finite integers and 2-adic approximations. [N2 V5 F9]
- I4: Force incompatible real and 2-adic approximation requirements. [N4 V4 F9]
- R1: Force least positive representatives of valuation cylinders to diverge. [N3 V4 F9]
- R2: Reconstruct rationals from valuation prefixes to exclude integer seeds. [N3 V4 F9]
- R5: Quantify escape of bounded positive witnesses across nested cylinders. [N2 V3 F9]
- U2: Couple real, 2-adic, and 3-adic coordinates. [N4 V4 F9]

### Carry and resource accounting

- I2: Express persistent growth as a multiplication-carry constraint. [N2 V5 F8]
- I6: Make additive corrections spend a finite arithmetic reserve. [N2 V3 F8]
- R3: Charge expanding blocks a debt in initial binary information. [N2 V3 F9]
- R6: Audit the moving boundary of carries in multiplication by three. [N1 V5 F9]

### Inverse ancestry and global populations

- I5: Require an impossible tower of inverse ancestors sharing a tail. [N2 V5 F9]
- R4: Force a smaller counterexample through inverse ancestry. [N2 V5 F9]
- U1: Use conserved flux of the whole counting measure. [N6 V3 F8]
- U4: Use coefficientwise uniqueness of a stopping-time generating function. [N6 V2 F8]

### Broader proof states with exact semantics

- U3: A finite configuration of coupled orbits supplies smaller transfer bridges. [N7 V5 F9]
- U5: Order guarded affine programs by a well-founded resource. [N6 V5 F9]
- U6: Alternate descent within an exactly intertwined affine family. [N6 V4 F9]

## Converge

1. **U3, score 6.70, selected for implementation (★).** Every new bridge has
   a precise soundness rule and an independently checkable strict parameter
   decrease. It can add certificates outside the old pair-return shape.
2. **U5, score 6.35.** The premise already supplies a finite source termination
   witness; consuming that witness might replace numerical parameter descent.
3. **U6, score 5.90.** Exact affine closure is explicit and permits tests of
   proposed ranks rather than relying on a qualitative analogy.

Traps, excluded from the shortlist:

- I6: A finite correction reserve cannot be assumed; prior experiments already
  exhibit unbounded replenishment.
- R3: Finite initial bits are not automatically a consumable resource: carries
  generate new high bits.
- R5 (and R1 without a quantitative new inequality): exchanging nested-cylinder
  quantifiers merely restates the unresolved positive-integer obstruction.
- U1: Density or total mass alone cannot exclude a single escaping atom.
- U4: Formal series uniqueness does not by itself provide finite hitting witnesses.

Several other ideas repeat directions already investigated in this repository.
The ranking favors a falsifiable new mechanism over renaming the global gap.

## Focus

### U3: auxiliary orbit bridges

Maintain a finite graph of orbit segments whose marked vertices are known to
converge, initially supplied by the smaller partner. Exact Collatz steps permit
marks to propagate through orbit segments in either direction. A marked vertex
3v+2 supplies a new marked vertex 27v+20 whenever v is strictly below the original
parameter, by strong induction. Several auxiliary orbits may then connect to the
distinguished target. A symbolic version must preserve both constant and slope,
not merely equality at one integer seed.

**Risk:** saturation need not terminate or cover every target; arbitrary finite
certificates do not supply a global decreasing measure for unresolved states.

**First step, executed:** implement up to two forward bridges per symbolic path,
require every bridge parameter to decrease for all quotients, and compare with
the old criteria. This finds 599 certificates through clock 30 for parameters
0..1000, including 421 of the 812 terminal-without-old-certificate cases. The
remaining 402 hit the depth limit; no state caps occurred. The first prototype
omitted repeated bridges at one clock; the final implementation computes closure
and is independently compared with an exhaustive path search.

Variations: explore inverse branches of marked vertices; choose bridges that
approach the target; compress symbolic certificate families; maintain several
unresolved obligations each with its own decreasing dependency.

Lean now verifies the general one-bridge rule and the all-quotient family
28+4096Q -> 21+3072Q. The earlier pair criteria fail forever at the base parameter
28, so this is an actual enlargement of the certificate repertoire. The premise
at the smaller parameter remains explicit. See `paper/affine_bridges.tex` and guide.

### U5: consume the source termination witness

Represent a guarded obligation by two affine endpoint maps L and H. Exact
identities T^a L(q)=L'(v(q)) and T^b H(q)=H'(v(q)) transfer the obligation to
another guarded state. Induct on the least source hitting time, with a secondary
rank for zero-source transitions. A positive source step decreases this time only
when it does not pass the first hit of one. Cases reaching one before the block
ends need separate target proofs. Program equivalence must include guards and
integer domains as well as affine coefficients.

**Risk:** the target endpoints exposed when the source reaches one may form an
unbounded family. Source termination alone does not prove those targets converge;
using their unproved stopping times as a rank would be circular.

**First step, deferred:** bound exploration to 200 normalized states and blocks
of at most eight steps, reporting uncovered guards and unsolved terminal-source
obligations rather than declaring a successful finite sample to be coverage.

Variations: coefficient-height ranks; multisets of source hitting times; existing
merge certificates as leaves; exponent-indexed symbolic states; direct induction
on a shortest source trace in Lean.

### U6: exactly intertwined affine relations

Let a paired state have y=ax+b, with slope 2^i3^j and rational offset in Z[1/6],
restricted to positive integral endpoints. If source and target parity bits are
e and f, synchronous stepping gives a'=3^(f-e)a and
b'=(3^f*b+f-a'*e)/2. This follows from 2T(x)=3^e*x+e and is an exact relation,
not a convergence result. Asynchronous steps also stay in this affine family.
Candidate terminal rules are explicit orbit meetings and independently checked
terminating targets. A proposed macro-step rank is (|i|+|j|, |y-x|), ordered
lexicographically.

**Risk:** exact closure is cheap; a decreasing rank is the substantive missing
part. Both exponent complexity and separation can increase under valid steps.

**First step, deferred:** test all 0<=u<4096 with source/target advances at most
12, recording the first seed with neither a terminal certificate nor rank decrease.
Even full sample success would require symbolic guard coverage before use in Lean.

Variations: synchronous-only slopes 3^j; amortized finite-state credit; residue-
dependent ranks; a third auxiliary endpoint; bounded denominator families.

## Provocation and next decision

Can source-witness consumption justify a symbolic bridge when numerical parameter
descent fails, while keeping every source-at-one target obligation explicitly
solvable? That would combine U3 and U5 at the actual remaining obstruction.
Before increasing brute-force depth, inspect whether unresolved symbolic states
admit such a rule. No universal saturation, rank, or Collatz proof is claimed.
