# Varying odd counts at fixed time

This is an exact finite-depth Python experiment with Lean-supported
arithmetic identities. The census itself is not kernel certified.
No global Collatz or least-unbounded coverage conclusion follows.

## Complete quotient test

Fix t, put L=2^t, and write canonical seeds r,s in [0,L). Let their
odd counts be j,k and endpoints e,f. The library proves e<3^j, f<3^k,
and transports all lifts by

    T^t(r+Lq) = e+3^j q.

Thus a replacement s+Lp merges with r+Lq exactly when

    f+3^k p = e+3^j q.

The enumeration stores the smallest canonical seed for every (j,e).
An equal-count improvement covers every lift of the original cylinder.
The experiment examines the noncontracting-prefix cylinders that have
no such improvement.

If k<j, compatibility forces f=e modulo 3^k, and
p=floor(e/3^k)+3^(j-k)q. For q>=1, p>=3q and hence
s+Lp > r+Lq. A smaller predecessor therefore requires q=0, e=f and
s<r. All such possibilities are present in the finite endpoint table.
The Lean theorem `lower_count_merge_gt_twice` gives the stronger general
bound x>2n whenever n>=2^t, the endpoints agree, and j_t(x)<j_t(n).
Its underlying `lower_count_merge_bound` states

    3n < x + 2^(t-j_t(x)).

If k>j, compatibility is possible exactly when f=e modulo 3^j.
Since 0<=e<3^j, write f=e+3^j q0 with q0>=0. Put d=k-j. Then

    q = q0 + 3^d Q,   p = Q.

These formulas describe every compatible pair of nonnegative quotients.
The equality is formalized as `higher_count_merge_lifts`. For every Q>=1,
the replacement is positive and strictly smaller: d>=1 implies
L(q0+(3^d-1)Q)>s-r. Thus one finite residue intersection detects infinitely
many larger seeds with a useful higher-count replacement. It is not enough
to test only q=0, or a few chosen lifts.

## Results

`python3 analysis/variable_count_surgery.py` exhausts every parity word
at every depth 1 through 18. At depth 18, 7,495 words have all prefix
coefficients at least one. Equal-count replacement already covers 1,391;
6,104 remain. None of these remaining cylinders has a smaller merging
predecessor with a different odd count, for any nonnegative quotient.
The lower-count and higher-count tests both report zero additions at
every tested depth. Detailed counts are in
`variable_count_surgery_results.json`.

The statement covers all seeds in these finitely many cylinders but does
not cover arbitrary depths. In particular, no structural theorem saying
that odd-count variation is always redundant has been established.
Uncovered finite prefixes are not infinite noncontracting natural orbits.

Tests independently replay every canonical row through depth 9 and check
both quotient formulas on all word pairs through depth 6, including
positive higher-count examples outside the survivor restriction.

## Consequence for the next step

Simply raising or lowering the odd-count budget at the same short forward
time does not improve the tested noncontracting survivor cover. The next
experiment should vary the replacement length as well, retaining exact
attainability and positivity. It must distinguish an inverse meeting before
forward descent from merely rediscovering a later, already smaller orbit
value. The universal existence obligation remains the central gap.
