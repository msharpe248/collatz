# Novel approaches from other areas (2026-06-10, late)

Out-of-the-box directions, each grounded in what the six pillars + three
killers already establish. Ranked by (chance of yielding a real result)
× (novelty). Honest status flags throughout; novelty claims need
literature checks before any are pursued publicly.

The organizing reframe (the bridge out of our own results): the parity
bijection (Parity.lean), taken to its k → ∞ limit, makes the itinerary
map a BIJECTION between ℤ₂ and infinite binary words, computable in both
directions prefix-by-prefix. So "find a divergent orbit" ⟺ "write an
infinite supercritical word whose unique 2-adic realization has
eventually-zero digits." The whole problem becomes a statement in
combinatorics on words + p-adic arithmetic. `itinerary_inverse.py` is
the working instrument (backward affine recursion; k letters give the
realization mod 2^k exactly).

**Critical subtlety that creates the opening:** "x rational ⟹ itinerary
eventually periodic" is OPEN (it is exactly non-divergence for rational
orbits); only the converse is a theorem (eventually periodic ⟹ rational,
by solving the affine fixed-point equation). Every classification of
which structured words can realize rationals is therefore new territory.

## 0. THE 3-ADIC SHADOW PROGRAM (2026-06-12 — the flagship)

**The reduction, in one line:** a divergent Collatz orbit must compress
its own base-3 digit stream by ~5%, forever — and that statement is
quantitative, finite at every scale, and sits in recognized deep water
(joint ×2/×3 rigidity) with an explicit numeric gap.

**Mechanism (verified numerically, machinery already in Lean):**
- The exact master identity 2^T·n_T = 3^j·n₀ + d(w) has d depending
  only on the parity word w (the dcoef recursion). Reduce mod 3^j: the
  n₀ term dies — **n_T mod 3^j is an explicit function of the word
  alone** (verified: 20k random starts, no collisions).
- A surviving/divergent window has supercritical words: at most
  Σ_{j≥0.631T} C(T,j) ≈ 2^(0.95T) of them. But 3^j ≈ 2^(1.0003T)
  classes exist (note δ·log₂3 = 1 EXACTLY at δ = critical — the gap
  1 − H(0.6309) ≈ 0.05 is the entropy deficit).
- So surviving orbits are confined to an exponentially thin explicit
  subset of Z/3^j: measured 2.17% at T=18 (j=12), ratio ~2^(−0.05T).
- Divergent orbits genuinely have liminf parity density ≥ log2/log3
  (per-step multiplicative accounting once n_t are all large — NOT a
  consequence of the master inequalities, a separate provable lemma).

**Why this unifies everything we have:** the parity bijection supplies
w ↦ 3-adic shadow; the dichotomy caps word entropy; NoGo explains why
pointwise counting cannot finish (the thin sets are inhabited —
critical_adversary lives there); the three killers said base-2-only and
base-3-only statistics die — this is the genuinely joint object. Even
steps consume 2-adic digits; odd steps produce 3-adic digits; the
conjecture is the assertion that the production cannot run entropy-
deficient forever.

**Phase 1 — DONE (2026-06-12, lean/Collatz/Shadow.lean, axiom-free):**
- terras_exact_form: 2^T·n_T = 3^j·n + dcoef (the identity the master
  inequalities bound; propext+Quot.sound only).
- dcoef_modEq + shadow_modEq: the correction and the 3-adic residue are
  functions of the parity word alone (n ≡ m mod 2^T ⇒ n_T ≡ m_T mod 3^j).
- dcoef_add: THE COCYCLE LAW d(w₁w₂) = 3^(j₂)d(w₁) + 2^(|w₁|)d(w₂) —
  the ℤ₂×ℤ₃ skew product in integer form, fully formal.
- density_floor: orbits with all values ≥ N surviving T steps satisfy
  2^T·N^j ≤ (3N+1)^j — the finite form of "divergent ⇒ liminf density
  ≥ critical" (NOT derivable from the master inequalities; new).
- shadow_compression + surviving_shadow_mem: survivors' (j, residue)
  pairs lie in a set with 2^(17(T-1)/27)·card ≤ 3^T while each fiber
  has 3^j > 2^(T-1) classes — the 3-adic mirror of Terras.lean with
  identical constants.

**Phase 2:** the reduction statement, stated cleanly: Collatz
divergence ⟺ an integer orbit whose 3-adic digit stream admits a
sustained ≥(1−H(0.631))≈5% compression. Ergodic form: the skew product
on ℤ₂×ℤ₃ (base = parity shift, fiber contracted by |3|₃ on odd steps)
has fiber Lyapunov exponent −δ·log₂3 ≤ −1 vs base entropy H(δ) ≤ 0.95:
limit measures of divergent orbits have 3-adic marginal of dimension
≤ 0.95. Missing rigidity statement R: integer-orbit limit measures
must have full-dimensional 3-adic marginal. R ⟹ no divergence.

**Phase 3 experiments (shadow_experiments.py, 2026-06-12):**
- TRUE entropy below the bound: at critical-j slices the distinct
  shadows grow at ~0.75-0.77 bits/step vs 0.80 for word counts (T ≤ 21;
  both still rising) — the word→shadow map has persistent collisions:
  the real compression exceeds the formalized H(δ) bound. (Caveat:
  small-T rates not yet asymptotic.)
- CROSS-SCALE RIGIDITY: at 2T=18, the joint (prefix-shadow, full-shadow)
  distribution has 12,522 pairs vs 11,522 full values — the full shadow
  almost DETERMINES the prefix shadow (1.09 prefixes/full on average;
  0.5% of the product bound). Scale-consistency is a strong active
  constraint, exactly what the cocycle law predicts; unexplored lever.
- STRUCTURED WORDS CLUSTER: 400 near-critical Sturmian words produce
  only 167 distinct shadows vs 400/400 for random matched-density words
  — structured itineraries live in an even thinner 3-adic set,
  connecting the forbidden-itineraries program (#1) to this one:
  arithmetic exclusion of structured divergence should be attacked
  through the shadow.

**Phase 3 (attack fronts on the compression statement):**
- structured words: eventually periodic = rational cycles (dead);
  Sturmian/substitutive = the forbidden-itineraries program (#1 below)
  attacks the SAME target from the word side;
- counting/arithmetic: study the explicit map w ↦ 2^(−T)·d(w) mod 3^j
  on supercritical words — equidistribution properties of d(w) would
  quantify how the thin sets sit, and consistency-across-scales for a
  single orbit is an unexplored constraint;
- the known wall, honestly: full R is joint-normality-type
  (Furstenberg-adjacent; cf. popcount(3^j) open). The contribution is
  converting Collatz INTO that single statement with a numeric gap.

## 1. Forbidden itineraries (combinatorics on words + p-adic Mahler method)

**Claim to attack:** no Sturmian word (any irrational slope) is the
itinerary of a rational 2-adic — in particular of an integer. Slowly
divergent orbits are forced toward quasi-Sturmian itineraries near the
critical slope (the dichotomy pins their density), so even partial
results carve real chunks off the divergence problem.

**Why plausible:** Sturmian words are S-adic limits of substitutions
(Ostrowski structure). Along the substitution hierarchy the realization
satisfies a tower of contracting 2-adic affine equations — a Mahler-type
self-similarity. Rationality should force eventual periodicity through
such towers (the p-adic analogue of Loxton–van der Poerten / Adamczewski–
Bugeaud style rigidity for automatic/Sturmian objects). Check literature:
p-adic versions exist for digit expansions; the itinerary version may be
genuinely open and reachable.

**Evidence:** telescope runs — critical-slope Sturmian realization has
random-looking digit tails (225/448 ones, max run 12); rational slopes
collapse to the known cycles, exactly as the theory demands.

**First steps:** (a) prove the warm-up: substitution FIXED POINTS (single
primitive substitution, supercritical letter frequency) never realize
rationals; (b) verify at scale with the telescope (each test is O(k)
bignum ops — millions of words/hour); (c) the Lean-able fragment:
realization of (cycle word)^∞ is the cycle rational (finite version
already in Parity.lean/Critical.lean).

## 2. Krasikov–Lagarias exponent record — **DONE (2026-06-11)**

Pursued and landed: see `KL_RECORD.md`. The 2003 record x^0.84 (their
k = 11 LP, 59k classes) is improved to **x^0.895** (k = 17, 43M
classes), with exact rational certificates at every level
(0.853, 0.863, 0.8724, 0.8812, 0.888, 0.895). The unlock: feasibility
of their LP at fixed λ is a monotone-homogeneous-concave fixed point
problem — certificates are vectors with F(c) ≥ c, found by power
iteration (Collatz–Wielandt), no LP solver needed. Engine validated
against all ten published table entries to seven decimals.
Remaining upside: k = 18+ (compute-bound), and formalizing KL Thm 2.2
in Lean to make it the first machine-verified density exponent.

## 3. Empirical-measure rigidity reduction (ergodic theory / ×2×3)

**Idea:** from a hypothetical divergent orbit, take weak-* limits of the
empirical measures of (n_t mod 2^∞, n_t mod 3^∞) on ℤ₂ × ℤ₃. The limit
is invariant for the Collatz skew product, where ×3 acts as a 3-adic
shift and halving as a 2-adic shift — the two shifts of Furstenberg's
×2×3 world, coupled. Divergence forces the limit measure to carry
supercritical parity density along stretches; Haar would force density
1/2. The target: identify the precise Rudolph–Johnson-type rigidity
statement R (positive entropy for the coupled action ⟹ Haar component)
such that R ⟹ no divergent orbits.

**Deliverable even short of R:** the reduction itself, made precise, is
a paper — it would locate the conjecture's divergence half INSIDE the
measure-rigidity program, matching where our three killers point
(base-2 statistics die on ×3, base-3 on /2). Status: deep water;
Tao's "Syracuse random variables" and Lagarias's surveys are the
neighbors to check first.

## 4. Proof-theoretic lower bounds from the no-go theorem (logic)

`no_finite_certificate` says: no proof of descent exists whose only
memory of n is bounded. That is the SEMANTIC shadow of a syntactic
class: induction arguments whose invariants are bounded-width (residue
predicates, automaton states). Translating the no-go theorem into "the
Collatz conjecture has no proof in proof system P" for a natural P
(e.g., bounded-window amortized induction over automatic predicates;
fragments related to IΔ₀-style bounded arithmetic with automatic
oracles) would be a new genre: a machine-verified UNPROVABILITY-SHAPE
theorem for a famous open problem. Conway's undecidability of the
generalized problem says some specificity is mandatory; this would say
exactly how much, lower-bounding the logical complexity of any proof.

**First step:** define P so that P-proofs compile to finite-memory
certificates (the compilation is the theorem); the no-go theorem then
does all the work. Mostly a definitional/translation paper + Lean.

## 5. Disproof side: the structured-seed search (and the 3n−1 control)

If Collatz is false, the witness is invisible to forward search but
might have STRUCTURED itinerary. The telescope inverts the search:
enumerate substitutive/S-adic supercritical words, compute realizations
mod 2^k, flag integer-like digit tails. Massively parallel; each
candidate costs microseconds.

**Control experiment with real signal available:** run the same
machinery on the 3n−1 map (= 3n+1 on negative integers), where multiple
nontrivial cycles EXIST (−5, −17 worlds) and divergence is genuinely
suspected. If the telescope methodology can rediscover known structure
there and surface divergence candidates, that validates it where
positive results are possible. Any divergence certificate for 3n−1
would be a major result in its own right (it is the standard "this is
what failure looks like" benchmark).

## 6. Tropical/min-plus spectral framing (modest but unifying)

The master inequalities are min-plus linear: orbits are paths in a
tropical matrix algebra over (window, density) space, and our Karp
searches were literally tropical eigenvalue computations (max-mean
cycle = tropical spectral radius = log 3/2 at every truncation — the
no-go theorem). The conjecture says the infinite system restricted to
integer orbits has negative tropical growth. Studying the truncation →
infinity spectral gap quantitatively could turn "the corridor narrows
at rate O(1/B)" (Critical.lean) into a clean statement about
convergence of tropical spectra — a tidy unification, possibly a survey
-grade contribution rather than a breakthrough.

## 7. Computer-assisted functional equations (analysis)

Berg–Meinardus: the conjecture is equivalent to a 3-term functional
equation for generating functions on the unit disk having only trivial
solutions. Nobody (check) has attacked the functional equation with
modern rigorous numerics (interval arithmetic, computer-assisted
contraction arguments à la Lorenz/Tucker). Risky: the equivalence may
just re-encode the difficulty. Worth one feasibility week, not more.

---

### Recommended order of attack

1. **#2 (KL exponent)** — highest probability of a citable new theorem.
2. **#1 (forbidden itineraries)** — most novel; instrument exists; the
   substitution-fixed-point warm-up looks provable.
3. **#5 (3n−1 control + structured search)** — cheap, validates tools,
   and is the only honest disproof program on the table.
4. **#4 (proof-theoretic translation)** — leverages existing Lean work
   almost verbatim.
5. **#3 (rigidity reduction)** — the deep bet; do the literature pass
   first.
