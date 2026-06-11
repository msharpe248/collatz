# Analysis scripts

Empirical instruments accompanying the Lean formalization and the paper
(`paper/nogo.tex`). Pure Python 3 standard library — no dependencies.
All randomized scripts use fixed seeds, so every table in the paper is
reproducible byte-for-byte.

| script | what it does | paper section |
|---|---|---|
| `certificate_search.py` | Karp max-mean-cycle search for residue-class descent certificates over joint 2-adic/3-adic states; always blocked by the n ≡ −1 self-loop (the finite-resolution shadow of the no-go theorem) | §10.1 |
| `rational_cycles.py` | enumerates the T-cycles on rationals a/q (q ≤ 99 odd): the positive-drift cycles are the complete adversary spectrum behind the no-go theorem; also sweeps the 2-parameter 1-state digit potential adversarially | §10.2 |
| `automaton_potentials.py` | first digit-weight experiment: V(n) = n·c^popcount(n) — contracts on Mersenne iff c > 9/4, killed by sparse injection | §10.3 |
| `transducer_search.py` | CEGIS over all 16 two-state weighted digit automata, with the validity floor (min cycle mean ≥ −(1−δ)) and the full attack battery (Mersenne, cycle shadows, min-weight DP strings, shift injections, hill-climbing); refutes every structure | §10.3 |
| `itinerary_inverse.py` | the inverse-itinerary telescope: computes the unique 2-adic realization of ANY prescribed parity word mod 2^k (the k→∞ parity bijection run backward); cross-checks the rational cycle spectrum and tests structured aperiodic itineraries for integer realizations | — |
| `IDEAS.md` | running research log: findings, the three killers, open directions | — |
| `NOVEL_APPROACHES.md` | cross-field attack plans: forbidden itineraries (words + p-adic Mahler), Krasikov–Lagarias exponent record, ×2×3 rigidity reduction, proof-theoretic lower bounds, the 3n−1 control experiment | — |

Typical runtimes on commodity hardware: seconds for the first three,
a few minutes for `transducer_search.py`.

Caveat on epistemic status: these scripts produce *experimental*
refutations — every kill is an explicit, checkable violator — but
"no certificate exists in this family" is a conjecture until proved
(see paper §13 for the proof program). The formal, kernel-checked
results live in `../lean/`.
