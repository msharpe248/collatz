# Source-witness and affine-rank checks — 2026-09-05

The previous goal turn made concrete progress: commit 947cc1c formalized an
auxiliary bridge and saved its census. This follow-up tests two proposed ways
of extending coverage. Neither tested shortcut supplies a global proof.

## Initial rank success is uninformative

The proposed affine state is y=a*x+b with a=2^i*3^j. The candidate rank is
(|i|+|j|, |y-x|), ordered lexicographically. For the initial transfer state,
a=9, b=2, and x=3u+2. Every tested u=0..4095 admits a strict rank decrease with
at most twelve steps on either orbit. In fact every initial state admits one:

- If x is even, advancing both endpoints once keeps slope 9 and halves their
  distance. Both endpoints are even.
- If x is odd, advance only the source. The new relation is y=6*x'-1, whose
  exponent complexity is still two. Since x>1 and x<x'<y, the distance decreases.

Thus the proposed initial-state experiment cannot distinguish a viable global
rank from one that immediately becomes stuck in a successor state.

The implemented greedy continuation prefers a terminal leaf, then the smallest
rank, then the shortest total advance. At u=1 it chooses (x,y)=(8,47), with
relation y=6x-1 and rank (2,39). No pair of advances s,t in 0..12 gives a smaller
rank, an orbit meeting, or target one. The independent test reconstructs exact
slopes using rational affine composition and checks every pair of advances.

This refutes the particular greedy strategy with this twelve-step window, not
all paths, all window sizes, or every rank. With window 100 the same example
terminates; the test explicitly checks that distinction. A different choice at
an earlier state might avoid this dead end. No claim of a global rank obstruction
is justified by the finite failure.

## Consuming the source witness leaves an unbounded target family

Take x0=2^(2m+1), y0=9*x0+2, m>=0. These are admissible transfer partners since
x0=2 mod 3; their parameter is (x0-2)/3. The source first reaches one at time
k=2m+1. At this exact time the target is

    T^k(y0) = 3^(m+2)+1.

Derivation: y0=2+2^k*9, so cylinder transport gives
T^k(y0)=T^k(2)+3^oddSteps(k,2)*9. The trivial cycle gives T^k(2)=1 and
oddSteps(k,2)=m. Before the source terminates all its steps are even, so its
normalized endpoint relation at time k is y=3^(m+2)*x+1. These slopes and terminal
targets are distinct and unbounded as m increases.

The script checks the first 201 members against direct integer orbits and exact
rational intertwining. The general deduction above is a written arithmetic
argument, not a new Lean declaration. The existing Cylinder.transport theorem
provides its formal ingredient. No mathematical priority claim is made.

An exact finite enumeration of terminal affine states cannot contain this whole
family. This does not exclude symbolic exponent-indexed states, merging by richer
semantics, independently proving these targets converge, or changing the schedule.
It specifically shows why source-at-one is not automatically a discharged leaf.
No convergence theorem for all 3^(m+2)+1 is established here.

## Consequence for the next research step

Do not increase the initial-state sample: its success follows from the elementary
two-case argument. Do not treat a bounded set of normalized terminal states as
complete. Any source-witness induction needs a proved terminal-target family rule
or another resource that survives exhaustion of the source witness. The auxiliary
parameter bridges from the preceding commit remain valid, but these tests do not
remove their global coverage gap.

Reproduce with `python3 analysis/source_witness_search.py`; the saved JSON includes
the rank failure and 201 terminal-family examples. Run
`python3 -m unittest discover -s analysis -p test_source_witness_search.py`.
This is a failed-candidate research log, not a new proof milestone; the latest
significant Lean result remains documented in the auxiliary-bridge paper and guide.
