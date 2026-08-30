> **Status (2026-08-29).** Historical research log (June 2026). Since then: rung 1 closed (`Rung1.lean`), prefix-power/Sturmian theorems (`PrefixPower.lean`, `Sturmian.lean`), and the Krasikov–Lagarias exponent machine-verified past the 2003 record (`KLGrid.lean`, `KL13.lean`). Items below marked open may no longer be.

# Research directions (status: 2026-06-10, evening update)

The repo has five formal pillars: no-go (`NoGo.lean`), density corridor
(`Density.lean`), cycle bounds (`Cycles.lean`), parity bijection
(`Parity.lean`), Terras a.e. finite form (`Terras.lean`). Directions
from here, ordered by tractability × value.

## 1. Digit-automaton potentials (MAJOR UPDATE — see findings)

**The idea.** `no_finite_state_certificate` kills potentials whose memory
of n is bounded. A weighted automaton reading ALL binary digits of n is
not bounded-memory: W(n) can range over n^α scales. The family evades the
no-go theorem's hypotheses.

**Experiment 1** (`automaton_potentials.py`, V(n) = n·c^popcount(n)):
- Confirmed: contracts on the Mersenne adversary exactly when c > 9/4
  (measured boundary log₂c = 1.17 matches theory).
- Discovery: sparse strings whose popcount rises under 3n+1 kill any
  c > 1. Two-sided squeeze.

**Experiment 2** (`rational_cycles.py`, 2026-06-10 evening):
- **The adversary spectrum**: enumerated all T-cycles on rationals a/q,
  q ≤ 99 odd (every such rational is 2-adic; integers ≡ x mod 2^L shadow
  it for L steps). Sixteen positive-drift cycles found — all on negative
  rationals — topped by −1 (drift 0.585, parity density 1), −65/49
  (0.268, 0.8), −19/11 (0.189, 0.75), −5 (0.057, 2/3), −17 (0.009).
  Each is a Mersenne-style adversary family; NoGo.lean's −1 is just the
  extreme point. (Worth formalizing: terras_mersenne generalizes to a
  shadowing lemma for any a/q.)
- **The full 1-state family V = n·2^(g1·ones + g0·zeros) is dead across
  the (g0,g1) plane**: hill-climbing finds +16..+44 log₂ risers in every
  cell of the sweep, including where Mersenne contracts at −10.9.
- **Mechanism diagnosed** (two independent killers):
  (i) *Weight injection*: a sparse string's ORBIT can descend (measured
      Δlog₂n = −8.3 over 40 steps) while its potential explodes (+56),
      because ones-density recovers 0.025 → 0.315 toward typical. Any
      weight that varies over n^Θ(1) scales admits start points with
      artificially low potential that the dynamics refills.
  (ii) *Global rewrite*: the odd step ×3-rewrites the entire remaining
      bit string — popcount is not digit-locally controlled under T.
      Even the −65/49 cycle shadow pumps the potential (+54.9/60 steps)
      despite a local-consumption model predicting contraction.

**Sharpened picture.** Base-2 digit statistics die on ×3 rewrites;
base-3 statistics would die symmetrically on /2 rewrites. A useful weight
statistic must be quasi-invariant under BOTH ×3-with-carry and halving —
i.e. it lives on the joint 2-adic/3-adic structure (ℤ₆ = ℤ₂ × ℤ₃, where
×3 is a 3-adic shift and /2 is a 2-adic shift). That is exactly the
Furstenberg ×2/×3 joint-rigidity landscape, consistent with the folklore
that this is where Collatz's true difficulty lives. The repo's old
certificate_search.py (joint 2/3-adic residues, bounded memory) was the
finite shadow of this; the unbounded version is the frontier.

**Experiment 3** (`transducer_search.py`, 2026-06-10 night): CEGIS over
all 16 two-state weighted digit automata. log V is linear in the weight
vector, so fitting weights against an adversary pool is piecewise-linear
min-max (subgradient); the adversary phase uses Mersenne, rational-cycle
shadows, exact minimal-weight strings (DP — the optimal injection
seeds), shift injections, and hill-climbing; violators join the pool.

- **Methodology lessons (both mattered):** (1) a validity floor is
  required — without min-cycle-mean(g) ≥ −(1−δ) the optimizer returns
  inverted potentials V ~ n^(−γ) whose contraction certifies nothing;
  (2) attacks must include EVEN numbers — window chains pass through
  even anchors, and odd-only search produced a false survivor.
- **THE THIRD KILLER (new): shift re-alignment.** The best candidate
  found was the trailing-run automaton (state = "still in the trailing
  1s", i.e. it tracks ν₂(n+1) — exactly the predictor of Mersenne
  rising stretches), V ≈ n^1.79 · 4.64^(ν₂(n+1)): it pre-charges for
  rises and genuinely contracts along them. It dies to the shift
  injection n = 2·(2^k−1): ONE halving re-aligns the read head and
  releases the stored weight at once (measured +86.8 at k=40; window
  ratio +52.9 over B=30). Any LSB-anchored state suffers this; Syracuse
  anchoring doesn't escape (a single Syracuse step can also jump
  ν₂(m+1) arbitrarily).
- **Verdict: all 16 structures dead** with floor + full attacks.

**The three killers** (any digit-weight certificate must survive all):
1. *Injection* — extreme-low-weight strings whose statistics the
   dynamics refills (min-weight DP strings make this constructive);
2. *Global ×3 rewrite* — digit statistics are not locally controlled
   under the odd step;
3. *Shift re-alignment* — halvings re-anchor the automaton and release
   stored potential in one step.

Killer 3 is evaded exactly by SHIFT-COHERENT weights — sliding k-gram
statistics (position-independent substring frequencies). The 1-gram
(popcount) and 2-gram (digram structure (0,1,0,1)) cases are dead by
killers 1–2. Sharpest conjecture: **no k-gram weight at any k certifies
descent** — min-weight k-gram strings are periodic words, and their
orbits re-typicalize (the open mixing ingredient).

**Concrete next steps:**
- (a) k-gram no-go (the shift-coherent subfamily): empirics at k = 3,4
  via the same CEGIS (state = last k−1 bits); then attempt the proof
  for periodic-word injections using Critical.lean-style realized
  parity words rather than explicit bit strings.
  CAUTION (learned earlier): naive Mersenne branches need
  popcount(3^j) ~ j/2 — an OPEN problem (only loglog bounds, Stewart).
  Route around explicit bit counts.
- (b) 3-state CEGIS sweep (4096 structures — needs the tiered screen)
  if any doubt remains; expectation: dead by the three killers.
- (c) Joint 2-adic/3-adic unbounded weights: W from base-6 digits or
  (n mod 2^a, n mod 3^b) with a,b growing. The ×2/×3 rigidity frontier;
  exploratory.

## 2. Quantitative no-go (Lean, medium)

`no_finite_certificate` assumes a constant window B. Strengthen: any
valid certificate from cutoff N₀ must have window B ≥ c·log N₀ (the
Mersenne orbit forces it). Makes the "log₂ n information budget" of
`Density.lean` a theorem about all certificates. Mostly reuses existing
machinery.

## 3. Deeper cycle exclusion (Lean, medium)

`Cycles.lean` excludes Terras-cycles of length ≤ 183 given the 2^71
verification. The wall at (T,j) = (184,116) is Diophantine: the element
bound 3^116·2^68/(2^184−3^116) ≈ 2^71.25 first exceeds 2^71 there.
To push past it, formalize the continued-fraction lower bound
|2^T − 3^j| > 3^j/T^C (Baker-type bounds are out of reach, but the
elementary convergent argument gives explicit exclusions per convergent
window). Target: cycle length > 10^10 à la Eliahou, formal.

## 4. Terras 1976 in Lean (DONE — finite form, 2026-06-10)

`Parity.lean` has the structural core (parity bijection, every pattern
realized, binomial law). `Terras.lean` completes the finite-form theorem:
`no_descent_window_bound` — non-descenders in [2^k, 2^(k+1)) number
≤ 3^k/2^(17(k−1)/27) ≈ 2^(0.955k), and `divergent_window_bound` for
never-descenders. Key simplifications found en route (vs the plan):

- No exact d_t(r) linear form needed: `early_no_descent_forces_density`
  (contrapositive of the dichotomy) already gives per-n classification,
  and `oddSteps_modEq` transfers it across the class. (The d_t identity
  is still worth having for a sharper *coefficient* stopping time — only
  if a future result needs it.)
- No entropy/Chernoff needed: the weighted binomial theorem in integers,
  2^m·∑_{j≥m} C(k,j) ≤ ∑ C(k,j)2^j = 3^k, gives the exponential tail
  with zero real analysis. Threshold 17/27 < log₃2 via 3^17 ≤ 2^27.

Remaining (optional packaging): natural-density-zero over [1, N] as a
limit statement (sum the windows; Filter.atTop machinery), and the σ(n)
stopping-time vocabulary. Mathematical content is done.

## 5. Equidistribution frontier (research, speculative)

The corridor theorems say a proof must track unbounded orbit
information. The cleanest target: show no orbit's odd-step density can
converge to a limit > log 2/log 3 (weaker than the conjecture, stronger
than anything known for individual orbits). Even a conditional result
(e.g., under 2-adic equidistribution of the orbit) would clarify what
the missing ingredient really is.
