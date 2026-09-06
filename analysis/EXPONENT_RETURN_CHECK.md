# Exponent-return check — 2026-09-05

The preceding checkpoint b5b9d1e identified terminal targets 3^(m+2)+1 after
consuming a source hitting witness. This experiment tests a concrete way to close
that family: induction on the exponent using same-clock orbit merging with a
smaller exponent. This is a subordinate research route, not a replacement for the
full Collatz goal; even a proof of this family would not cover all transfer states.

## Uniform criterion

For a fixed realized parity prefix, write

    2^t T^t(3^k+1) = 3^j 3^k + (3^j+c).

For the candidate lower exponent k-d, write the corresponding expression using
odd count l and correction e. A uniform merge requires

    l=j+d,       3^j+c=3^l+e.

These conditions ensure identical expressions as functions of 3^k. Testing only
endpoint equality at a single exponent would be insufficient. The script checks
both endpoint equality and the odd-count condition, then asserts the correction
identity independently.

The integer P=2^max(1,t-2) is a period of 3 modulo 2^t. Hence exponent shifts by P
preserve the first t parities of both partners. The criterion extends to every
positive exponent in the same residue class with k>d. This is an exact written
lifting argument, not a new Lean theorem. Existing cylinder and affine-iterate
results provide its ingredients.

For example, k=29 modulo 32 gives, at t=7 and d=1,

    j=2, c=76;       l=3, e=58;
    T^7(3^k+1)=T^7(3^(k-1)+1)=(9*3^k+85)/128.

Thus reaching one for the smaller exponent implies it for the larger on this
exponent progression. No mathematical priority claim is made, and this elementary
certificate has not been promoted to a separate significant-result paper.

## Coverage experiment

At t<=12 and decrement 1<=d<=8, the complete 1024 exponent residues have:

- 154 residues with a uniform decreasing-exponent merge;
- 870 residues unresolved by these rules.

The search chooses representatives above the largest decrement so the finite
base-exponent boundary cannot cause a false missing residue. Saved rules apply
only where k>d. The 154/1024 proportion concerns exponent congruence classes; it
is not a density claim about arbitrary Collatz starting integers.

Tests check all saved rules at their smallest admissible exponents and at two
larger exponent lifts, independently compare complete small censuses, and replay
the explicit k=29 modulo 32 rule. The census is Python evidence, not kernel-
certified coverage. No assertion is made that unresolved residues lack longer or
different kinds of exponent reductions.

## Decision

The simplest bounded exponent-return mechanism does not close the terminal
family. Extending search depth alone would still leave a coverage theorem to
prove. Keep these reductions available as possible terminal-family rules, but do
not treat source-witness induction as resolved. A useful next step must compress
unresolved obligations symbolically or supply a genuinely new decreasing resource.

Reproduce with `python3 analysis/exponent_return_search.py`. Tests:
`python3 -m unittest discover -s analysis -p test_exponent_return_search.py`.
