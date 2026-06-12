# Collatz at the Critical Line

The Collatz conjecture is **open**. This repository does not prove it.
What it contains is a machine-verified account of where it is provably
hard and where it is provably almost true: a no-go theorem for an entire
family of attempted proofs, sharp density theorems pinning the
conjecture to the critical
odd-step density log 2/log 3, the first formalized Collatz density
result (Terras' theorem, finite form), Diophantine cycle exclusions,
and a systematic experimental program on what lies beyond. The full
story is in the paper: [paper/nogo.pdf](paper/nogo.pdf).

It also contains a new unconditional result: **π_a(x) ≥ x^0.895** — the
number of integers below x whose 3x+1 orbit contains a (any a ≢ 0
mod 3), improving the x^0.84 record of Krasikov–Lagarias (2003) by
scaling their own program to 43 million congruence classes with exact
integer certificates. See [paper/klbound.pdf](paper/klbound.pdf) and
[analysis/KL_RECORD.md](analysis/KL_RECORD.md).

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
weakening end-to-end. Larger moduli and finer grids are mechanical
extensions of the same pipeline.)

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
│       └── Krasikov.lean # machine-verified density exponent x^0.4543
├── analysis/
│   ├── certificate_search.py    # LP/max-mean-cycle search that motivated NoGo
│   ├── automaton_potentials.py  # digit-automaton potentials (evade the no-go)
│   ├── rational_cycles.py       # the positive-drift adversary spectrum
│   ├── transducer_search.py     # CEGIS refutation of 2-state digit certificates
│   └── IDEAS.md                 # research directions and current findings
└── paper/
    ├── nogo.tex          # the paper (LaTeX source)
    └── nogo.pdf          # compiled paper
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
