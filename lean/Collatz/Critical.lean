/-
  Collatz — The Critical Line

  This file contains NO axioms and NO claim to prove the conjecture.

  `Density.lean` proved one wall: an orbit segment with no descent must
  run supercritical odd density (`no_descent_dichotomy`: 2^B < 2·3^j for
  windowed integers). This file proves the opposite wall: that bound is
  SHARP. For every window B there are arbitrarily large integers with no
  descent in B steps whose odd density is within O(1/B) of the critical
  value log 2 / log 3 ≈ 0.6309 (`critical_line_sharp`):

      2^B ≤ 3^j ≤ 3·2^B,   j = oddSteps B n.

  Together: the non-descent density profiles achievable over a window B
  are exactly pinned to [critical, critical + O(1/B)]. The Collatz
  conjecture is the assertion that no integer rides the critical line
  forever — and both walls of that line are now formal.

  Construction: the extremal parity word is 1^j 0^s (all odd steps
  first), realized by an actual residue class via Terras' bijection
  (`parity_pattern_realized`); every prefix of the word is supercritical
  as long as 2^(j+s) ≤ 3^j, and a supercritical prefix forces non-descent
  by the lower master inequality (`no_descent_of_supercritical_prefix` —
  the exact converse of the dichotomy). This strengthens
  `no_uniform_descent_bound` (NoGo.lean), whose Mersenne adversary is
  the density-1 special case s = 0: adversaries exist at every
  supercritical density, all the way down to the critical line. The
  enumeration of positive-drift rational cycles (analysis/
  rational_cycles.py: −1, −65/49, −19/11, −5, −17, …) is the dynamical
  shadow of the same spectrum.
-/

import Collatz.Parity
import Collatz.Cycles

namespace Collatz

/-! ## Supercritical prefix forces non-descent (converse of the dichotomy) -/

/-- If every prefix of the first T steps is supercritical (2^t ≤ 3^(j_t)),
    the orbit never drops below its start within T steps. Exact converse
    of `no_descent_dichotomy`, via the lower master inequality. -/
theorem no_descent_of_supercritical_prefix (T n : ℕ)
    (h : ∀ t, t ≤ T → 2 ^ t ≤ 3 ^ oddSteps t n) :
    ∀ t, t ≤ T → n ≤ terras_iter t n := by
  intro t ht
  have hlow := terras_lower_bound t n
  have hsc := h t ht
  have hjt : oddSteps t n ≤ t := oddSteps_le t n
  have h2j2t : 2 ^ oddSteps t n ≤ 2 ^ t :=
    Nat.pow_le_pow_right (by norm_num) hjt
  have hchain : 2 ^ t * n + 2 ^ t ≤ 2 ^ t * terras_iter t n + 2 ^ t := by
    calc 2 ^ t * n + 2 ^ t
        ≤ 3 ^ oddSteps t n * n + 3 ^ oddSteps t n :=
          Nat.add_le_add (Nat.mul_le_mul_right n hsc) hsc
      _ = 3 ^ oddSteps t n * (n + 1) := by ring
      _ ≤ 2 ^ t * terras_iter t n + 2 ^ oddSteps t n := hlow
      _ ≤ 2 ^ t * terras_iter t n + 2 ^ t := Nat.add_le_add_left h2j2t _
  exact Nat.le_of_mul_le_mul_left
    (Nat.le_of_add_le_add_right hchain) (Nat.two_pow_pos t)

/-! ## The extremal parity word 1^j 0^s -/

/-- If the parity pattern of n over k steps is exactly "the first j
    positions odd", then every prefix count is min t j. -/
theorem oddSteps_of_parities_range (k j n : ℕ)
    (hS : parities k n = Finset.range j) :
    ∀ t, t ≤ k → oddSteps t n = min t j := by
  intro t ht
  rw [oddSteps_eq_card t n]
  have hext : parities t n = Finset.range (min t j) := by
    ext i
    simp only [parities, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hit, hpar⟩
      have hik : i ∈ parities k n := by
        simp only [parities, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hpar⟩
      rw [hS, Finset.mem_range] at hik
      omega
    · intro hi
      have hij : i < j := by omega
      have hit : i < t := by omega
      have hik : i ∈ parities k n := by rw [hS, Finset.mem_range]; exact hij
      simp only [parities, Finset.mem_filter, Finset.mem_range] at hik
      exact ⟨hit, hik.2⟩
  rw [hext, Finset.card_range]

/-- THE ADVERSARY FAMILY. For any j, s with 2^(j+s) ≤ 3^j there are
    arbitrarily large integers taking j odd steps then s even steps with
    no descent throughout — non-descenders of odd density j/(j+s), any
    supercritical density down to the critical line. The Mersenne
    adversary of `no_uniform_descent_bound` is the case s = 0. -/
theorem critical_adversary (j s N₀ : ℕ) (hsc : 2 ^ (j + s) ≤ 3 ^ j) :
    ∃ n, N₀ ≤ n ∧ oddSteps (j + s) n = j ∧
      ∀ t, t ≤ j + s → n ≤ terras_iter t n := by
  obtain ⟨r, hr, hS⟩ := parity_pattern_realized (j + s) (Finset.range j)
    (by intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega)
  have hone : 1 ≤ 2 ^ (j + s) := Nat.one_le_two_pow
  have hmod : (r + 2 ^ (j + s) * N₀) ≡ r [MOD 2 ^ (j + s)] := by
    show (r + 2 ^ (j + s) * N₀) % 2 ^ (j + s) = r % 2 ^ (j + s)
    exact Nat.add_mul_mod_self_left r (2 ^ (j + s)) N₀
  refine ⟨r + 2 ^ (j + s) * N₀, ?_, ?_, ?_⟩
  · calc N₀ = 1 * N₀ := (one_mul N₀).symm
      _ ≤ 2 ^ (j + s) * N₀ := Nat.mul_le_mul_right N₀ hone
      _ ≤ r + 2 ^ (j + s) * N₀ := Nat.le_add_left _ _
  · rw [oddSteps_modEq (j + s) hmod,
      oddSteps_of_parities_range (j + s) j r hS (j + s) le_rfl]
    exact Nat.min_eq_right (Nat.le_add_right j s)
  · apply no_descent_of_supercritical_prefix
    intro t ht
    have hmodt : (r + 2 ^ (j + s) * N₀) ≡ r [MOD 2 ^ t] :=
      Nat.ModEq.of_dvd (Nat.pow_dvd_pow 2 ht) hmod
    rw [oddSteps_modEq t hmodt,
      oddSteps_of_parities_range (j + s) j r hS t ht]
    rcases le_total t j with h | h
    · rw [Nat.min_eq_left h]
      exact Nat.pow_le_pow_left (by norm_num) t
    · rw [Nat.min_eq_right h]
      calc 2 ^ t ≤ 2 ^ (j + s) := Nat.pow_le_pow_right (by norm_num) ht
        _ ≤ 3 ^ j := hsc

/-! ## The critical line is sharp -/

/-- SHARPNESS OF THE DICHOTOMY. For every window B there are arbitrarily
    large integers with no descent within B steps whose odd-step count j
    is pinned to the critical line from above:

        2^B ≤ 3^j ≤ 3·2^B.

    `no_descent_dichotomy` forbids windowed non-descent below
    2·3^j ≤ 2^B; this theorem realizes it just above. The achievable
    non-descent densities over a window B are exactly the critical strip
    [log2/log3, log2/log3 + O(1/B)] — the Collatz conjecture is the
    claim that no integer stays in that strip at every scale. -/
theorem critical_line_sharp (B N₀ : ℕ) :
    ∃ n, N₀ ≤ n ∧ (∀ t, t ≤ B → n ≤ terras_iter t n) ∧
      2 ^ B ≤ 3 ^ oddSteps B n ∧ 3 ^ oddSteps B n ≤ 3 * 2 ^ B := by
  have hex : ∃ j, 2 ^ B ≤ 3 ^ j := ⟨B, Nat.pow_le_pow_left (by norm_num) B⟩
  classical
  set j := Nat.find hex with hjdef
  have hjspec : 2 ^ B ≤ 3 ^ j := Nat.find_spec hex
  have hjle : j ≤ B := Nat.find_le (Nat.pow_le_pow_left (by norm_num) B)
  obtain ⟨n, hN, hodd, hnd⟩ :=
    critical_adversary j (B - j) N₀ (by
      have : j + (B - j) = B := by omega
      rw [this]; exact hjspec)
  have hB : j + (B - j) = B := by omega
  rw [hB] at hodd hnd
  refine ⟨n, hN, hnd, by rw [hodd]; exact hjspec, ?_⟩
  rw [hodd]
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · rw [hj0]
    have : 1 ≤ 2 ^ B := Nat.one_le_two_pow
    simpa using by omega
  · have hmin : ¬ 2 ^ B ≤ 3 ^ (j - 1) := Nat.find_min hex (by omega)
    have h3 : 3 ^ j = 3 * 3 ^ (j - 1) := by
      have : j = (j - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [pow_succ]; ring
    omega

/-!
## What this means

Pair this file with `Density.lean`:

* `no_descent_dichotomy`  — no descent over window B (from a window
  position) FORCES 2^B < 2·3^j: density cannot fall below the critical
  line.
* `critical_line_sharp`   — non-descent IS achieved with 3^j ≤ 3·2^B:
  density pinned just above the critical line, at every window length,
  by arbitrarily large integers.

The corridor has width O(1/B) and is inhabited at every scale. Every
finite window is therefore powerless to decide descent near the critical
line — the formal content of `no_finite_certificate`, now with the
sharp constant. What remains open is precisely whether any single
integer tracks the critical strip at all scales simultaneously: that is
the Collatz conjecture.
-/

end Collatz
