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

## Subsequent formalization: exact reconstruction

`lean/Collatz/CorrectionDecode.lean` now supplies a deterministic test for the
missing attainability condition. Given h,k,D, reconstruct a word of length h.
If D is even, its first letter must be zero and continue with (h−1,k,D/2).
If D is odd, its first letter must be one and continue with
(h−1,k−1,(D−3^(k−1))/2), using natural subtraction. Finally recompute the
word's odd count and correction, and accept only if both exactly equal k,D.
The final check rejects invalid parameters and any misleading truncated subtraction.

The reason is the defining identity

    correction(b :: w) = (if b then 3^ones(w) else 0) + 2 correction(w).

The power of three is odd, so the low bit of the correction fixes b. Induction
proves that reconstruction recovers every actual word. Conversely, successful
final checks provide the required word themselves. Thus the test accepts
exactly the attainable corrections; fixed length, odd count, and correction
also determine at most one word.

Lean proves `decodeCorrection_correct`, `correctionAttainable_iff`, and
`attainable_paradoxical_iff`. The last equivalence says that attainability,
positivity, coefficient contraction, endpoint congruence, and the correction
inequality together describe an actual paradoxical word. This is an exact
criterion, not an exclusion theorem.

Ordinary kernel `decide` verifies that (h,k,D)=(8,5,347) is attainable and
(16,6,194421) is not. The latter rejects the artificial return above. The Python
implementation `analysis/correction_decode.py` is independently tested against
all words through length ten and exhaustive attainable sets through length
seven, including invalid inputs and genuine length-eight examples. It is not
extracted from Lean. Three additional controls pass. The current audit covers
72 declarations with standard foundations only; the earlier 69 count describes
the preceding limitation snapshot.

The criterion avoids enumerating words when testing one proposed correction.
It does not avoid searching the possible corrections or lengths. The open
mathematical task remains a uniform restriction on accepted data, so this
formalization supplies infrastructure rather than a new Collatz exclusion.
