# Analysis scripts

Empirical instruments accompanying the Lean formalization and the paper
(`paper/nogo.tex`). Pure Python 3 standard library — no dependencies.
All randomized scripts use fixed seeds, so every table in the paper is
reproducible byte-for-byte.

| script | what it does | paper section |
|---|---|---|
| `early_inverse_bridge_search.py` | exact early inverse induction rules in the parameter class two modulo three | `../paper/early_inverse_bridge.tex` |
| `inverse_cycle_bridge.py` | signed inverse excursions repair either cycle-charge mismatch for convergent base pairs | `../paper/inverse_cycle_bridge.tex` |
| `cycle_bridge_search.py` | constructive late-cycle transfer bridges and their exact directional limitation | `CYCLE_BRIDGE_CHECK.md` |
| `exponent_return_search.py` | uniform smaller-exponent merges for terminal targets 3^k+1; finite coverage census | `EXPONENT_RETURN_CHECK.md` |
| `source_witness_search.py` | rejects a bounded greedy affine-rank strategy and records unbounded source-at-one obligations | `SOURCE_WITNESS_CHECK.md` |
| `affine_bridge_search.py` | symbolic auxiliary-orbit transfer certificates with strict decrease for every quotient; explicit depth and state limits | `../paper/affine_bridges.tex`, `AFFINE_TRANSFER_REASSESSMENT.md` |
| `certificate_search.py` | Karp max-mean-cycle search for residue-class descent certificates over joint 2-adic/3-adic states; always blocked by the n ≡ −1 self-loop (the finite-resolution shadow of the no-go theorem) | §10.1 |
| `rational_cycles.py` | enumerates the T-cycles on rationals a/q (q ≤ 99 odd): the positive-drift cycles are the complete adversary spectrum behind the no-go theorem; also sweeps the 2-parameter 1-state digit potential adversarially | §10.2 |
| `automaton_potentials.py` | first digit-weight experiment: V(n) = n·c^popcount(n) — contracts on Mersenne iff c > 9/4, killed by sparse injection | §10.3 |
| `transducer_search.py` | CEGIS over all 16 two-state weighted digit automata, with the validity floor (min cycle mean ≥ −(1−δ)) and the full attack battery (Mersenne, cycle shadows, min-weight DP strings, shift injections, hill-climbing); refutes every structure | §10.3 |
| `itinerary_inverse.py` | the inverse-itinerary telescope: computes the unique 2-adic realization of ANY prescribed parity word mod 2^k (the k→∞ parity bijection run backward); cross-checks the rational cycle spectrum and tests structured aperiodic itineraries for integer realizations | — |
| `kl_exponent.py` | scales the Krasikov–Lagarias lower-bound program: power-iteration feasibility for their LP L_k^NT(λ) (monotone homogeneous fixed point — no LP solver), validated against their Table 2 to 7 decimals, then pushed k = 12..17 | KL_RECORD.md |
| `kl_certificate.py` | exact rational certification: λ = 2^(p/q), coefficient lower bounds by integer power comparison, every constraint checked in exact integer arithmetic — turns a float certificate into a referee-checkable proof per KL Thm 2.2 | KL_RECORD.md |
| `kl_export_certificate.py` | exports canonical certificate artifacts (raw little-endian int64 + sha256 sidecar); sample k=12 artifact ships in `certs/` | KL_RECORD.md |
| `kl_verify_independent.py` | clean-room second verifier: stdlib only, constraint system re-derived from KL §2, different coefficient bounding (10^21 + binary search), congruences asserted; passes all six levels, detects single-entry corruption | KL_RECORD.md |
| `kl_grid_certificate.py` | the GRID form of the KL system (exponents 100/79/129 in 1/50-doubling units, i.e. with the advanced term) — power iteration, exact integer check, packed shards for Lean | `KL_RECORD.md`, `lean/Collatz/KLGrid.lean` |
| `kl_lean_instance.py` | emits the Lean instantiation (`KL{k}Data`, `KL{k}Check*`, `KL{k}.lean`) of `G50.growth_root` from a grid certificate JSON | `lean/Collatz/KL13.lean`, `KL14.lean` |
| `pade_rung1.py` | the degree-one Padé/Mahler ledger for F₂(8/9): certificate, predicted 2-adic valuations, height accounting — the numerics behind `Rung1.lean` | `RUNG1_ATTACK.md`, `paper/rung1.tex` |
| `mahler_experiments.py` | the earlier rung-1 experiments: functional equation, realizations, shadow clustering, truncation exponent 0.946 | `RUNG1_ATTACK.md` |
| `sturmian_prefix_power.py` | prefix-power margins of Sturmian itineraries by slope and intercept — the numerics behind `Sturmian.lean` | `paper/rung1.tex` §7 |
| `ideal_experiments.py`, `shadow_experiments.py` | numerics for `Ideal.lean` and `Shadow.lean` | — |
| `IDEAS.md` | running research log: findings, the three killers, open directions | — |
| `NOVEL_APPROACHES.md` | cross-field attack plans: forbidden itineraries (words + p-adic Mahler), Krasikov–Lagarias exponent record, ×2×3 rigidity reduction, proof-theoretic lower bounds, the 3n−1 control experiment | — |

Typical runtimes on commodity hardware: seconds for the first three,
a few minutes for `transducer_search.py`.

Caveat on epistemic status: these scripts produce *experimental*
refutations — every kill is an explicit, checkable violator — but
"no certificate exists in this family" is a conjecture until proved
(see paper §13 for the proof program). The formal, kernel-checked
results live in `../lean/`.
