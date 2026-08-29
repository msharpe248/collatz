# Collatz at the Critical Line

The Collatz conjecture is **open**. This repository does not prove it.
What it contains is a machine-verified account of where it is provably
hard and where it is provably almost true: a no-go theorem for an entire
family of attempted proofs, sharp density theorems pinning the
conjecture to the critical
odd-step density log 2/log 3, the first formalized Collatz density
result (Terras' theorem, finite form), Diophantine cycle exclusions,
and a systematic experimental program on what lies beyond. The full
story is in the paper: [paper/nogo.pdf](paper/nogo.pdf), with a
non-specialist guide at [paper/nogo_guide.pdf](paper/nogo_guide.pdf).

It also contains a new unconditional result: **π_a(x) ≥ x^0.895** — the
number of integers below x whose 3x+1 orbit contains a (any a ≢ 0
mod 3), improving the x^0.84 record of Krasikov–Lagarias (2003) by
scaling their own program to 43 million congruence classes with exact
integer certificates — and, **machine-verified end to end,
π₁(x) = Ω(x^0.8569)**, the first kernel-checked exponents *exceeding* the
twenty-year-old published record x^0.84 (the record itself, γ = 0.8418,
was first formalized by [Menta2357/collatz-classical](https://github.com/Menta2357/collatz-classical),
July 2026, via KL's own elimination argument)
([lean/Collatz/KL13.lean](lean/Collatz/KL13.lean), 531,441 classes; and
[lean/Collatz/KL12.lean](lean/Collatz/KL12.lean), x^0.8476: the Krasikov–Lagarias
difference inequalities *with their advanced term*, proved by a root
induction that sidesteps their elimination argument
([lean/Collatz/KLGrid.lean](lean/Collatz/KLGrid.lean)), plus a
177,147-class certificate decided by the Lean kernel — no
`native_decide`, no floating point). The earlier verified exponent
x^0.63201 ([lean/Collatz/Krasikov50.lean](lean/Collatz/Krasikov50.lean))
was the first above the critical constant log 2/log 3 = 0.63093. See
[paper/klbound.pdf](paper/klbound.pdf) (guide:
[paper/klbound_guide.pdf](paper/klbound_guide.pdf)) and
[analysis/KL_RECORD.md](analysis/KL_RECORD.md).

A third paper develops the reduction layer: **the 3-adic shadow** — a
divergent Collatz orbit is exactly an integer that compresses its own
base-3 digit stream by ≈ 4.5%, at every scale, forever; all core
theorems machine-verified, plus the experimental discoveries
(cross-scale rigidity, Sturmian clustering). See
[paper/shadow.pdf](paper/shadow.pdf) (guide:
[paper/shadow_guide.pdf](paper/shadow_guide.pdf)) and
[lean/Collatz/Shadow.lean](lean/Collatz/Shadow.lean).

A fourth paper opens **the word-complexity ladder**: order potential
divergent orbits by the complexity of their parity itineraries and
exclude class by class. Rung zero is machine-verified (divergent
itineraries are never eventually periodic), and **rung one is now
closed for the running example, machine-verified**: no orbit's
itinerary is the fixed point of σ: 1→110, 0→011 (density 2/3, above
the critical line) or any shift of it. The reduction to the
irrationality of the 2-adic Mahler value F₂(8/9) is discharged by
Mahler's method in degree one — a Padé certificate on ten letters, the
functional equation, and a height ledger that closes because
2^27 > 28·9^7 — in purely integer form, no p-adic analysis
([lean/Collatz/Rung1.lean](lean/Collatz/Rung1.lean),
numerics in [analysis/pade_rung1.py](analysis/pade_rung1.py)). See
[paper/rung1.pdf](paper/rung1.pdf) (guide:
[paper/rung1_guide.pdf](paper/rung1_guide.pdf)) for rung one, and
[paper/ladder.pdf](paper/ladder.pdf) (guide:
[paper/ladder_guide.pdf](paper/ladder_guide.pdf)),
[lean/Collatz/Ladder.lean](lean/Collatz/Ladder.lean), and
[analysis/RUNG1_ATTACK.md](analysis/RUNG1_ATTACK.md).

## The conjecture

For any positive integer n: halve it if even, replace it by 3n+1 if odd.
**Claim**: every starting value eventually reaches 1. Verified by
computation up to 2^71 (Barina); unproven in general.

## What is actually proved here (Lean 4, no axioms, no `sorry`)

All results depend only on Lean's standard foundations (`propext`,
`Classical.choice`, `Quot.sound`).

### The no-go side ([lean/Collatz/NoGo.lean](lean/Collatz/NoGo.lean))

| Theorem | Statement |
|---|---|
| `terras_mersenne` | T^j(2^L − 1) = 3^j·2^(L−j) − 1 for j ≤ L: the integers 2^L − 1 shadow the 2-adic fixed point −1 and rise for L straight steps |
| `no_uniform_descent_bound` | For every window B and cutoff N₀, some n ≥ N₀ has no descent within B steps |
| `uniform_descent_53_false` | The plausible-looking uniform-descent claim `∀ n > 300, ∃ t ≤ 53, collatz_iter t n < n` is false — witness 2^28 − 1 (smallest violator: 447) |
| `no_finite_certificate` | **The no-go theorem**: no bounded multiplicative potential V(n) = n·W(n) with contraction factor ρ < 1 over a bounded window certifies descent |
| `no_finite_state_certificate` | Corollary for finite-state observers: no residue-class scheme (any modulus), no finite-automaton potential, can certify descent |

In words: any argument whose memory of n is a bounded amount of
information — a residue class, an automaton state, a bounded potential —
is defeated by n = 2^L − 1, because −1 is a fixed point of the odd
Collatz branch on the 2-adic integers with drift log(3/2) > 0, and
2^L − 1 imitates it for L steps.

### The density side ([lean/Collatz/Density.lean](lean/Collatz/Density.lean))

The positive-direction companion: survival without descent *requires*
high odd-step density, quantified exactly. Writing j = `oddSteps T n`
for the number of odd iterates among the first T Terras iterates:

| Theorem | Statement |
|---|---|
| `terras_growth_bound` | **The master inequality**: 2^T·(T^T(n)+1) ≤ 3^j·(n + 2^(T−j)), an exact integer bound with no division and no truncated subtraction |
| `terras_growth_bound_sharp` | The bound is sharp: on the Mersenne orbit n = 2^L − 1, T = L it is an equality (and `oddSteps_mersenne`: all L steps are odd) |
| `no_descent_dichotomy` | If n hasn't dropped below itself by step T, then either 2^T < 2·3^j (odd density is supercritical, > log 2/log 3 ≈ 0.6309 up to one step) or n < 2^(T−j) (more than log₂ n halvings have already been spent) |
| `early_no_descent_forces_density` | Inside the log₂ n-bit information budget of n, survival forces supercritical density |
| `collatz_iff_descent` | **The descent reduction**: the Collatz conjecture is *equivalent* to "every n ≥ 2 eventually drops strictly below itself under the Terras map" |

Together the two files pin the conjecture into a corridor, formal at
both walls: it is *exactly* the claim that no orbit sustains
supercritical odd density forever (`Density.lean`), and no argument
that remembers only boundedly much about n can prove that claim
(`NoGo.lean`).

### The cycle side ([lean/Collatz/Cycles.lean](lean/Collatz/Cycles.lean))

| Theorem | Statement |
|---|---|
| `terras_lower_bound` | The lower master inequality: 3^j·(n+1) ≤ 2^T·T^T(n) + 2^j |
| `cycle_three_pow_lt` | On a nontrivial cycle, 3^j < 2^T strictly |
| `cycle_min_bound` | Every cycle element satisfies n·2^T < n·3^j + 3^j·2^(T−j) — cycles need 3^j to approximate 2^T from below with extreme precision |
| `cycle_check_183` | Kernel-verified (plain `decide`, no trusted code): for all T ≤ 183 the cycle bound forces n < 2^71 |
| `no_small_terras_cycle` | Assuming the verified range below 2^71 (Barina, stated as an explicit hypothesis), no nontrivial cycle has ≤ 183 halvings; the first Diophantine wall is (T, j) = (184, 116), where the element bound ≈ 2^71.25 first exceeds 2^71 |

### The parity side ([lean/Collatz/Parity.lean](lean/Collatz/Parity.lean))

Terras' 1976 parity-vector theorem, formalized:

| Theorem | Statement |
|---|---|
| `parity_of_modEq` / `modEq_of_parity` | **The bijection**: the first k parities of a Terras orbit depend exactly on n mod 2^k, in both directions |
| `oddSteps_modEq` | The odd-step count over k steps is a function of n mod 2^k |
| `parity_pattern_realized` | Every parity pattern of length k is realized by some r < 2^k — the Mersenne adversary (all-ones) is one point of a complete spectrum |
| `card_oddSteps` | **The binomial law**: exactly C(k, j) residues mod 2^k take j odd steps in their first k steps |

### The measure side ([lean/Collatz/Terras.lean](lean/Collatz/Terras.lean))

Terras' 1976 theorem, finite form — the first density result of the
subject, formalized:

| Theorem | Statement |
|---|---|
| `choose_tail_bound` | Weighted binomial theorem in pure integers: 2^m·∑_{j≥m} C(k,j) ≤ 3^k |
| `tail_exponent` | Supercritical density forces j ≥ 17(k−1)/27 (via 3^17 ≤ 2^27) |
| `no_descent_window_bound` | **Terras' theorem**: the integers in [2^k, 2^(k+1)) that don't drop below themselves within k steps number ≤ 3^k/2^(17(k−1)/27) ≈ 2^(0.955k) — a vanishing ≈ 2^(−0.045k) fraction of the window |
| `divergent_window_bound` | Same bound for integers whose orbit *never* descends: almost every integer has finite stopping time |

### Beating the 2003 record, machine-verified ([lean/Collatz/KLGrid.lean](lean/Collatz/KLGrid.lean), [lean/Collatz/KL12.lean](lean/Collatz/KL12.lean))

Krasikov–Lagarias' inequality (D3) for classes m ≡ 8 (mod 9) contains an *advanced* term — the child (2a−1)/3 is smaller than a, so its tree is counted at a larger relative scale — and a plain induction on scale cannot use it; KL prove their Theorem 2.2 by a back-substitution/elimination procedure whose termination uses Kőnig's lemma. Truncating the term instead (Applegate–Lagarias 1995; `Krasikov50.lean`) caps the exponent near 0.66. The advanced term is worth ≈ 0.19 in the exponent.

| Theorem | Statement |
|---|---|
| `G50.cap_shift29` | 2·cap(t+29) ≤ 3·cap(t): the exact grid offset for the advanced branch (2^(29/50) = 1.4946 < 3/2) |
| `G50.cnt_rec_two`, `cnt_rec_five`, `cnt_rec_eight` | The three KL difference inequalities per root, the last with the exact offset t+129 |
| `G50.growth_root` | **The growth theorem with the advanced term**: for any level k ≥ 2, rate p/q and certificate satisfying `CertOK`, every root a ≡ 2 (3) reaching 8 has cnt(a, cap(t)·a) ≥ c_a·(p/q)^t/Cmax. Proved by strong induction over roots on the measure M(t,a) = 10t + ⌊log₂(a^498)⌋, which drops by 4, 3, 1 along the three branches because 3^498 > 2^789 — no elimination, no Kőnig; the 1/50-grid rounding (29 < 50·log₂(3/2) = 29.25) is exactly the slack that makes the measure well-founded |
| `K13.density_bound` | **The record**: #{n ≤ 80000·2^y reaching 1} ≥ (387326/16777216)·(101195/100000)^(50y)·const, i.e. π₁(x) = Ω(x^0.8569), γ = 50·log₂(101195/100000) > 0.8418 (KL 2003). Certificate: 531,441 classes mod 3^13 as 243 packed shards in three files (`KL13Data`, `KL13Check0–2`), each class decided by `decide +kernel` (≈2¼ hours, ≈23 GB) |
| `K12.density_bound` | The same at k = 12: #{n ≤ 80000·2^y reaching 1} ≥ (554204/16777216)·(101182/100000)^(50y)·const, i.e. π₁(x) = Ω(x^0.8476), γ = 50·log₂(101182/100000) > 0.8418 (KL 2003, k = 11). Certificate: 177,147 classes mod 3^12 as 81 packed 32-bit shards; every class condition decided by `decide +kernel` (≈15 min, ≈18 GB) |

The truncated system's ceiling (γ ≈ 0.66 at every k) and the exact-offset system's values (0.800 at k=8 … 0.849 at k=12, 0.859 at k=13) are tabulated by `analysis/kl_grid_certificate.py` and the scratch bisection; the informal record 0.895 (k = 17, 43 million classes) is the same system at a level the kernel has not yet been asked to check.

### The density exponent ([lean/Collatz/Krasikov.lean](lean/Collatz/Krasikov.lean))

The first machine-verified density lower bound for the 3x+1 problem:

| Theorem | Statement |
|---|---|
| `phi_rec_two/five/eight` | Krasikov's difference inequalities (integer-grid form), proved from the backward-tree combinatorics: subtree injections + disjointness via cycle-freeness above 8 |
| `K5.cert_ok` | An 81-class integer certificate for modulus 3^5, growth rate λ = 137/100, kernel-verified by `decide` (propext only) |
| `K5.growth` | The certificate induction: phi ≥ Δ·c_m·(137/100)^y in pure natural-number arithmetic |
| `density_lower_bound` | **#{n ≤ 8·2^y reaching 1} ≥ 0.31·(1.37)^y** — i.e. π₁(x) = Ω(x^0.4543), exceeding every published bound before 1995 (Krasikov 1989: x^0.43) |

(The full Krasikov–Lagarias program reaches x^0.895 informally — see
[paper/klbound.pdf](paper/klbound.pdf); this formalizes its integer-grid
weakening end-to-end.)

### A density exponent above the critical line ([lean/Collatz/Krasikov50.lean](lean/Collatz/Krasikov50.lean))

The 1/50-grid refinement of the same pipeline, at modulus 3^8: a
machine-verified exponent **above** the critical odd-step density
log 2/log 3 = 0.63093…

| Theorem | Statement |
|---|---|
| `cap_quad` / `cap_shift1` / `cap_shift21` | The interleaved-geometric cap sequence cap(t) = 2^(t/50)·r[t mod 50] doubles exactly every 50 grid steps, and grows fast enough that the difference-inequality branches retard by only 21/50 resp. 1/50 of a doubling (kernel-checked table conditions; the key margin is 2^(21/50) = 1.3382 > 4/3) |
| `phi50_rec_two/five/eight` | Krasikov's difference inequalities on the 1/50 grid |
| `K8.cert_ok` | A 2187-class integer certificate for modulus 3^8 at rational rate μ = 1261/1250 per grid step, kernel-verified by chunked `decide` |
| `K8.wit_ok` | Every class m ≡ 2 (mod 3) of modulus 3^8 contains a small root a = m + 6561q (q ∈ {0,1}) whose Terras orbit reaches 8 in ≤ 146 steps — kernel-evaluated orbits, all 2187 of them |
| `K8.density_bound` | **#{n ≤ 80000·2^y reaching 1} = Ω((1261/1250)^(50y)) = Ω(x^γ), γ = 50·log₂(1261/1250) = 0.63201… > 0.63093… = log 2/log 3** |

The exponent crosses the critical line: the verified count of integers
reaching 1 grows strictly faster than x^(log 2/log 3), the density at
which the divergence question lives. (Krasikov 1989 proves x^0.43 on
paper; this is the first kernel-checked bound, and it exceeds every
published bound before Applegate–Lagarias 1995.) Every certificate
condition is a pure integer inequality — no roots, no real numbers —
decided over the 2187 residue classes in chunks of 243.

### The 3-adic shadow ([lean/Collatz/Shadow.lean](lean/Collatz/Shadow.lean))

The reduction layer: divergence as sustained 3-adic compression.

| Theorem | Statement |
|---|---|
| `terras_exact_form` | The exact identity 2^T·T^T(n) = 3^j·n + d, d = `dcoef T n` |
| `shadow_modEq` | **The shadow congruence**: n ≡ m (mod 2^T) ⇒ T^T(n) ≡ T^T(m) (mod 3^j) — the orbit's 3-adic residue is a function of its parity word alone |
| `dcoef_add` | **The cocycle law** d(w₁w₂) = 3^(j₂)·d(w₁) + 2^(\|w₁\|)·d(w₂): the ℤ₂×ℤ₃ skew product in integer form |
| `density_floor` | Orbits with values ≥ N survive only at density ≥ log 2/log((3N+1)/N) → log 2/log 3: divergent orbits are pinned to the critical density |
| `shadow_compression` / `surviving_shadow_mem` | Survivors' 3-adic residues are confined to ≤ 3^T/2^(17(T−1)/27) ≈ 2^(0.955T) values inside fibers of > 2^(T−1) classes — a sustained ≈ 4.5% compression of the 3-adic digit stream, with the same constants as the 2-adic Terras theorem |

### The word-complexity ladder ([lean/Collatz/Ladder.lean](lean/Collatz/Ladder.lean))

| Theorem | Statement |
|---|---|
| `eq_of_itinerary_eq` | Integers with identical full parity itineraries are equal (the infinite-precision parity bijection) |
| `divergent_itinerary_aperiodic` | **Rung zero**: a divergent orbit's itinerary is never eventually periodic — periodic itineraries belong only to bounded orbits |
| `dcoef_closed` | The closed form d(w) = Σ_{w_i=1} 2^i·3^(#ones after i) — the engine of the Mahler-method attack on the automatic rung |

### Rung one ([lean/Collatz/Rung1.lean](lean/Collatz/Rung1.lean))

| Theorem | Statement |
|---|---|
| `preS_three` | The Mahler functional equation F(z) = (z+z²)/(1−z³) + (1−z²)F(z³) as an exact identity between homogenised prefix sums |
| `link` | An orbit whose itinerary is the s-shift of w forces x(w) = (2^s n − d_s)/3^{j_s}: a rational with odd denominator, in congruence form for every prefix length |
| `Hyp_succ` | The tower transport: the functional equation carries the rational-value hypothesis from α_k = (8/9)^{3^k} to α_{k+1} |
| `pade_base` | The certificate: p₀ + p₁·F with p₀ = 1+z³−z⁴, p₁ = −1+z−z²+z³ vanishes to order exactly 9 at 0 with leading coefficient −1 |
| `level_dvd` | At level k the Padé value Z_k is a nonzero multiple of 2^{9·3^{k+1}} — the exact 2-adic size |
| `lv_bounds`, `final_ineq` | The height ledger: \|Z_k\| ≤ 7·3^k·9^{7·3^k}·max(\|D₀\|,\|u₀\|), and 2^{27·3^k} beats it once k ≥ that maximum |
| `core` | **F₂(8/9) is irrational** (no rational with odd denominator satisfies the prefix congruences) |
| `no_shifted_sigWord_itinerary` | **Rung one, running example**: no natural number's Terras itinerary is w or any shift of w |

### The prefix-power criterion ([lean/Collatz/PrefixPower.lean](lean/Collatz/PrefixPower.lean))

| Theorem | Statement |
|---|---|
| `prefix_power` | If the itinerary of n is ℓ-periodic on its first M letters (begins with a possibly fractional power of a word of length ℓ), then T^ℓ(n) = n or 2^(M−ℓ) ≤ max(n, T^ℓ(n)) — n and T^ℓ(n) share M−ℓ parities, so they are congruent mod 2^(M−ℓ) |
| `prefix_power_bound` | Size form: 2^M ≤ 2^ℓ·n + 3^o·(n + 2^ℓ), i.e. (e−1)ℓ ≤ o·log₂3 + log₂(n+1) + O(1) for an initial e-th power with o ones per period; the threshold exponent 1 + δ·log₂3 is exactly 2 on the critical line |
| `prefix_power_divergent` | On a divergent orbit the bound holds at every tail position (a periodic tail would bound the orbit) |

Sturmian words of slope α are q_k-periodic over stretches of length ≈ q_k + q_{k+1} (three-distance structure), an initial exponent ≥ 2.6, so numerically ([analysis/sturmian_prefix_power.py](analysis/sturmian_prefix_power.py)) the criterion's margin grows linearly with prefix length for every tested slope above the critical line and every intercept.

### Sturmian itineraries: the level theorem ([lean/Collatz/Sturmian.lean](lean/Collatz/Sturmian.lean))

For the mechanical word w_n = ⌊(n+1)α+ρ⌋ − ⌊nα+ρ⌋ with 2 ≤ 3^α (above the critical line), an approximation qα = p + δ (0 < δ < 1), and "visits" {nα+ρ} ≥ 1−δ:

| Theorem | Statement |
|---|---|
| `mech_shift` | w_{n+q} = w_n unless n or n+1 is a visit |
| `visit_sep` | Two visits are ≥ Q apart if ‖mα‖ ≥ δ for 0 < m < Q (Lagrange's best-approximation property for convergents, taken as a hypothesis) |
| `dcoef_le_of_itin` | On such an itinerary the correction term satisfies d_s ≤ 3s·3^{sα} — because 2 ≤ 3^α |
| `sturmian_level` | **The level theorem**: if in addition every window of length G contains a visit (three-distance theorem, G = q_k + q_{k+1}, taken as a hypothesis) and 2^(Q−3+s) > 3^((q+s)α+1)(3N+3s+1) for all s ≤ G, then N does not have itinerary w |

The size condition holds at level k whenever the partial quotient a_{k+1} exceeds (1+2η)/(1−η), η = α·log₂3 − 1; so, given the two classical Diophantine facts, every Sturmian itinerary whose slope has infinitely many partial quotients ≥ 2 (for α < 0.789), ≥ 3 (α < 0.883), ≥ 4 (α < 0.946) or ≥ 6 (any α < 1) is excluded, at every intercept. Golden-tail slopes (partial quotients eventually 1) are excluded numerically up to α ≈ 0.9 but need the long returns q_k + q_{k+1}, not proved here. The two Diophantine facts are not formalized.

### The critical line ([lean/Collatz/Critical.lean](lean/Collatz/Critical.lean))

The density dichotomy is **sharp**:

| Theorem | Statement |
|---|---|
| `no_descent_of_supercritical_prefix` | Converse of the dichotomy: supercritical prefixes (2^t ≤ 3^(j_t)) force non-descent |
| `critical_adversary` | For any j, s with 2^(j+s) ≤ 3^j, arbitrarily large integers take j odd then s even steps with no descent — adversaries at every supercritical density (Mersenne is s = 0) |
| `critical_line_sharp` | For every window B, arbitrarily large n have no descent in B steps with 2^B ≤ 3^j ≤ 3·2^B: odd density pinned within O(1/B) of log 2/log 3 |

The pillars interlock: every finite behavior occurs exactly once
(`parity_pattern_realized` — why worst-case certificates die), behaviors
are binomially distributed (`card_oddSteps`), survival requires the
exponentially rare supercritical tail (`no_descent_dichotomy`) — and
that tail is *inhabited* at every scale, arbitrarily close to the
critical density (`critical_line_sharp`). The non-descenders are a
vanishing minority (`no_descent_window_bound`), and the conjecture is
exactly universal descent (`collatz_iff_descent`). **Almost-all is now
formal; all is the conjecture** — precisely whether any single integer
tracks the critical strip at every scale simultaneously, a question
`no_finite_certificate` proves no bounded-memory argument can settle.

## What a real proof must overcome

Worst-case reasoning over finitely many bits treats the bits revealed by
successive halvings as adversarial, and the adversarial bit-string
(all ones) climbs forever. A proof must show that no actual orbit
sustains odd-step density ≥ log 2 / log 3 ≈ 63.09% indefinitely — an
equidistribution statement about individual orbits in ℤ₂. This is
precisely where the strongest known result (Tao 2019, "almost all orbits
attain almost bounded values") stops short of the full conjecture.
`Density.lean` makes the reduction formal: the conjecture is equivalent
to universal descent (`collatz_iff_descent`), and avoiding descent
provably costs supercritical odd density (`no_descent_dichotomy`).

## Layout

```
collatz/
├── lean/
│   └── Collatz/
│       ├── Basic.lean    # Collatz/Syracuse definitions, 2-adic valuation lemmas
│       ├── NoGo.lean     # the no-go theorem and its corollaries
│       ├── Density.lean  # density forcing, sharpness, the descent reduction
│       ├── Cycles.lean   # Diophantine cycle bounds, no cycles ≤ 183 halvings
│       ├── Parity.lean   # Terras' parity bijection and the binomial law
│       ├── Terras.lean   # Terras' theorem: almost all n descend (finite form)
│       ├── Critical.lean # the density dichotomy is sharp at log2/log3
│       ├── Krasikov.lean   # machine-verified density exponent x^0.4543
│       ├── KLGrid.lean    # KL inequalities WITH the advanced term: root induction, generic in k and p/q
│       ├── KL12.lean      # verified γ = 0.8476 > 0.84, 81 kernel-checked shards
│       ├── KL13*.lean     # verified γ = 0.8569: data + 3 check files (243 shards) + theorem
│       ├── Krasikov50.lean # 1/50-grid: exponent x^0.63201, above critical
│       ├── Shadow.lean   # the 3-adic shadow: divergence = compression
│       ├── Ladder.lean   # word-complexity ladder: rung zero + d(w) closed form
│       ├── Rung1.lean    # rung one: 2-adic Mahler method in degree one, integer form
│       ├── PrefixPower.lean # prefix-power criterion: initial powers vs 2-adic congruence
│       └── Sturmian.lean # Sturmian itineraries: the level theorem (Lagrange + three-distance as hypotheses)
├── analysis/
│   ├── certificate_search.py    # LP/max-mean-cycle search that motivated NoGo
│   ├── automaton_potentials.py  # digit-automaton potentials (evade the no-go)
│   ├── rational_cycles.py       # the positive-drift adversary spectrum
│   ├── transducer_search.py     # CEGIS refutation of 2-state digit certificates
│   └── IDEAS.md                 # research directions and current findings
└── paper/
    ├── nogo.tex/.pdf           # paper I: no-go + the critical corridor
    ├── klbound.tex/.pdf        # paper II: the x^0.895 record + formal x^0.632
    ├── shadow.tex/.pdf         # paper III: the 3-adic shadow
    ├── ladder.tex/.pdf         # paper IV: the word-complexity ladder
    └── *_guide.tex/.pdf        # non-specialist guides to each paper
```

## Build / run

```bash
cd lean && lake build            # checks all proofs (mathlib cache required)
python3 analysis/certificate_search.py   # residue-class certificate search
python3 analysis/rational_cycles.py      # the positive-drift adversary spectrum
python3 analysis/transducer_search.py    # CEGIS refutation of 2-state digit certs
cd paper && tectonic nogo.tex            # rebuild the paper
```

See [analysis/README.md](analysis/README.md) for what each script
reproduces. The residue-class search is infeasible at every modulus —
the blocking cycle is always the n ≡ −1 (mod 2^a) self-loop — and
`NoGo.lean` proves this is not bad luck but necessity. The paper
([paper/nogo.pdf](paper/nogo.pdf)) gives the complete account.

## License

MIT
