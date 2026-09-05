# Endpoint congruence does not repair a relaxed correction interval

Collatz proof project — September 5, 2026

## Abstract

We prove in Lean that every fixed positive affine prefix admits an artificial
suffix correction satisfying the standard correction envelope, a contracting
coefficient, and exact return to the starting seed, at every sufficiently large
target length. The construction does not produce a parity word or a Collatz
cycle. It shows that endpoint congruence combined with this correction interval
is insufficient for uniform exclusion. The missing condition is attainability
of the correction by a word with the specified length and odd count.
This is a limitation of the research method, not a proof of Collatz or a claim
of literature priority.

## Definitions and theorem

Use the shortcut map T(n)=n/2 for even n, and T(n)=(3n+1)/2 for odd n.
For a prefix of length s, odd count a, correction D, initial seed n>0, and
endpoint v, its affine identity is

    2^s v = 3^a n + D.

For a suffix of length h and odd count k, the current envelope bounds its
correction d by

    d ≤ 2^(h-k)(3^k−2^k).

**Theorem.** For any natural s,a,D,n,v with n>0 and the displayed affine
identity, for every

    L ≥ s + 2(a+2n) + v + 1,

there exist natural k,d such that

    k ≤ L−s,
    3^(a+k) < 2^L,
    d ≤ 2^(L−s−k)(3^k−2^k),
    3^(a+k)n + 3^kD + 2^s d = 2^L n.

The last equality is stronger than endpoint congruence and non-descent:
it is an artificial exact return.

## Proof

Set k=2n and h=L−s. The length hypothesis implies h≥k and
3^(a+k)≤2^(2(a+k))<2^L. Since v≤2^v,

    3^k v ≤ 2^(2k+v) ≤ 2^h ≤ 2^h n.

Thus d=2^h n−3^k v is a natural number. Induction gives
(n+1)2^(2n)≤3^(2n): the induction step uses 4(n+2)≤9(n+1).
Consequently n2^k≤3^k−2^k, and

    d ≤ 2^h n ≤ 2^(h−k)(3^k−2^k).

Finally, substitute the definition of d and the prefix identity:

    3^(a+k)n + 3^kD + 2^s d
      = 3^k(3^a n+D) + 2^s(2^h n−3^k v)
      = 2^L n.

## Why this is not a cycle construction

For an actual Boolean word w, the separately proved theorem
`realizes_iff_dvd` states that n realizes w exactly when
2^length(w) divides 3^ones(w)n+correction(w). Its correction is the recursively
computed correction of that particular word. It cannot be replaced by an
arbitrary integer in an enclosing interval.

Here d is selected arithmetically. The theorem supplies no word with correction
d, length L−s, and k odd letters. For example, take the empty prefix at n=v=3,
L=16, and k=6. The construction gives d=194421, below the envelope 680960,
and 729·3+194421=65536·3. The actual sixteen-step trajectory from 3 ends at 2
and has eight odd steps. The artificial data are incompatible with that orbit.

## Formal verification and scope

Source: `lean/Collatz/CongruenceRelaxation.lean`.
Declaration: `Collatz.WordAffine.relaxed_closing_correction`.
Its proof uses the explicit odd-budget inequality from `Collatz.PruningLimit`
and elementary natural-number arithmetic. No new axiom, `sorry`, or
`native_decide` is used. The selected 69-declaration audit reports only standard
foundational axioms. Nine Python controls pass; the new control checks this
construction on all residue prefixes through depth seven, at the stated
threshold and five steps beyond it.

Reproduce from the repository root:

```sh
PATH=/Users/msharpe/.elan/bin:$PATH python3 analysis/audit_theorems.py --build
python3 -m unittest discover -s analysis -p 'test_paradoxical*.py'
```

This limitation concerns the stated relaxation. It does not rule out adding
other orbit inequalities, using increasing prefix depth, or bounding attainable
corrections by a different argument. In particular, the fixed odd-count witness
may be excluded by additional positivity or growth bounds. No impossibility
claim is made for every residue-based method.

The next substantive objective is a restriction on the attainable correction
set that remains useful as both word length and odd count grow. The congruence
equivalence alone does not provide that restriction. Collatz remains unproved.
