# Notes for the revision of nogo.tex — ABSORBED

Status 2026-06-10 (late): the revision was applied. nogo.tex now covers
all six pillars + the experimental program; everything below is folded
in. Kept for the record of what changed and for the pre-submission
checklist at the bottom (citations to verify, novelty search).

Original notes follow:

## New formal results to add

1. **Density forcing** (`Density.lean`, all axiom-free):
   - Master inequality: 2^T·(T^T(n)+1) ≤ 3^j·(n + 2^(T−j)), j = oddSteps.
     Sharp: equality on the Mersenne orbit (`terras_growth_bound_sharp`).
   - Dichotomy: non-descent by step T forces supercritical odd density
     (2^T < 2·3^j) or > log₂ n spent halvings (`no_descent_dichotomy`).
   - Descent reduction: CollatzConjecture ↔ every n ≥ 2 drops below
     itself under Terras (`collatz_iff_descent`).
   - Narrative: completes the "corridor" — the conjecture IS the density
     statement, and NoGo says bounded-memory arguments can't decide it.

2. **Cycle bounds** (`Cycles.lean`):
   - Lower master inequality: 3^j·(n+1) ≤ 2^T·T^T(n) + 2^j.
   - Cycle pinch: 3^j < 2^T strictly; every cycle element n satisfies
     n·2^T < n·3^j + 3^j·2^(T−j) (classical Diophantine bound, formal).
   - `cycle_check_183`: kernel `decide` (propext only!) verifies the
     bound forces n < 2^71 for all T ≤ 183. With Barina's 2^71
     verification as an explicit hypothesis: no nontrivial cycle with
     ≤ 183 halvings. First Diophantine wall: (T,j) = (184,116), where
     the element bound 3^116·2^68/(2^184−3^116) ≈ 2^71.25 first
     exceeds 2^71.

3. **Experiments** (`analysis/automaton_potentials.py`,
   `analysis/rational_cycles.py`): digit-automaton potentials evade the
   no-go hypotheses, but:
   - V(n) = n·c^popcount(n) contracts on Mersenne iff c > 9/4 (measured
     boundary log₂c = 1.17 matches theory); sparse strings kill any c > 1.
   - The adversary spectrum behind NoGo's −1 is the set of positive-drift
     T-cycles on rationals a/q (q odd): 16 found for q ≤ 99, all negative,
     topped by −1 (drift .585), −65/49 (.268), −19/11 (.189), −5, −17.
     Possible paper figure: drift vs parity-density scatter of all cycles.
   - The full 1-state family n·2^(g1·ones+g0·zeros) is empirically dead
     across the plane. Two mechanisms: weight injection (orbit descends
     while potential explodes — popcount recovers from sparse toward
     typical) and the ×3 global rewrite (popcount is not digit-local
     under T; even cycle shadows pump it).
   - Narrative hook: base-2 statistics die on ×3, base-3 on /2; viable
     weights must live on joint ℤ₂ × ℤ₃ structure — the Furstenberg
     ×2/×3 rigidity landscape. The no-go theorem's moral extends
     experimentally to unbounded digit weights; proving it is the next
     theorem target ("1-state digit no-go").
   - CEGIS sweep (`transducer_search.py`): all 16 two-state weighted
     digit automata refuted (with the validity floor V ≥ n^δ enforced
     and even anchors attacked). Discovered the third killer, *shift
     re-alignment*: the strongest candidate (trailing-run automaton,
     V ≈ n^1.79·4.64^(ν₂(n+1)) — pre-charges for Mersenne stretches)
     dies when one halving of n = 2(2^k−1) releases its stored weight
     (+86.8 measured). Three killers total: injection, ×3 rewrite,
     shift re-alignment. Shift-coherent (k-gram) weights evade only
     the third; 1- and 2-gram cases dead. Paper-worthy as a systematic
     refutation methodology: CEGIS + min-weight-string DP + the
     rational-cycle adversary spectrum.

4. **Parity-vector theorem** (`Parity.lean`, added later same day):
   Terras' bijection formalized — first k parities ↔ n mod 2^k
   (`parity_of_modEq`/`modEq_of_parity`), every pattern realized
   (`parity_pattern_realized`), binomial law `card_oddSteps`:
   exactly C(k,j) residues mod 2^k take j odd steps. Cross-checked
   numerically for k ≤ 12. This is the combinatorial engine for a
   future Terras-a.e. section; if that lands, the paper's arc becomes
   no-go → corridor → measure: worst case impossible, average case
   provable, the gap between them IS the conjecture.

5. **Terras' theorem, finite form** (`Terras.lean`, same day): the
   capstone — `no_descent_window_bound`: non-descenders in
   [2^k, 2^(k+1)) number ≤ 3^k/2^(17(k−1)/27) ≈ 2^(0.955k), i.e. a
   2^(−0.045k) fraction; `divergent_window_bound` for never-descenders.
   Proof chain: dichotomy → supercritical classification →
   window↔residue transfer (one integer per class) → binomial law →
   integer weighted-binomial tail bound (2^m·tail ≤ (1+2)^k, no real
   analysis anywhere). Numerically verified k ≤ 18 (fraction falls
   0.50 → 0.029). First formalization of any Collatz density result,
   as far as we know — headline claim for the revised paper, verify
   novelty before submission (search for Lean/Coq/Isabelle Collatz
   formalizations; known ones cover definitions/small facts only).

6. **The critical line** (`Critical.lean`, late same day): the density
   dichotomy is SHARP. `no_descent_of_supercritical_prefix` (converse of
   the dichotomy, via the lower master inequality);
   `critical_adversary` (parity word 1^j 0^s realized via the Terras
   bijection — non-descenders at every supercritical density; Mersenne
   is the s=0 extreme); `critical_line_sharp` (for every window B,
   arbitrarily large n with no descent and 2^B ≤ 3^j ≤ 3·2^B — density
   within O(1/B) of log2/log3). Numerically confirmed (j=100: density
   0.6329 vs critical 0.6309, no descent through 158 steps). Paper
   framing: the corridor now has *sharp constants on both walls* —
   forbidden below the critical line, inhabited just above it, at every
   scale; the conjecture is whether any integer stays in the strip at
   all scales at once. Suggested figure: (window B, density) plane with
   dichotomy wall, adversary band, Mersenne point, and the 16 rational
   cycles from rational_cycles.py plotted as the dynamical spectrum.

## Framing changes

- Title/abstract: from "a no-go theorem" to "the corridor: no-go +
  density forcing + cycle walls".
- The information-budget story is now quantitative in both directions:
  log₂ n bits is exactly the horizon (Density) and exactly what finite
  observers lack (NoGo).
- Add a "verified statements" table mapping paper claims → Lean names,
  with the axiom audit (#print axioms output) for each.

## Items to verify before submitting any revision

- Cite Barina (2020) J. Supercomputing for the 2^71 range; check
  current verified frontier (may have moved past 2^71).
- Cite Terras (1976), Everett (1977) for the density/stopping-time
  lineage; Eliahou (1993) for cycle-length lower bounds; Simons & de
  Weger for cycle exclusion state of the art.
- Re-run `lake build` + axiom checks on the release toolchain and
  record versions.
