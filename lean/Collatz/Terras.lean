/-
  Collatz — Terras' Theorem, Finite Form

  This file contains NO axioms and NO claim to prove the conjecture.

  THE THEOREM (Terras 1976, finite form). In every dyadic window
  [2^k, 2^(k+1)), the integers that fail to drop below themselves within
  k Terras steps number at most

      3^k / 2^(17(k-1)/27)  ≈  2^(0.955·k)

  — an exponentially vanishing fraction ≈ 2^(-0.045·k) of the window
  (`no_descent_window_bound`, stated as a clean integer inequality).
  In particular the same bound holds for integers whose orbit NEVER
  descends (`divergent_window_bound`): almost every integer has finite
  stopping time. This is the first density result of the subject, now
  fully formal at every finite scale.

  The proof composes the repo's pillars:
  1. survival without descent inside the window forces supercritical
     odd density 2^k < 2·3^j   (`early_no_descent_forces_density`);
  2. the window holds exactly one integer per residue mod 2^k, and j is
     a function of the residue   (`oddSteps_modEq`);
  3. residues are binomially distributed over j   (`card_oddSteps`);
  4. the supercritical binomial tail is exponentially small — by the
     weighted binomial theorem, purely in integers:
         2^m · ∑_{j≥m} C(k,j)  ≤  ∑_j C(k,j)·2^j  =  (1+2)^k = 3^k,
     with the supercritical threshold m = 17(k-1)/27 from 3^17 ≤ 2^27
     (17/27 = 0.6296… approximates log 2/log 3 = 0.6309… from below).

  What remains for the classical "natural density zero" phrasing is
  only limit packaging (summing windows); the mathematical content is
  this finite bound. And the corridor stands: by `no_finite_certificate`
  no bounded-memory argument can upgrade "almost every" to "every" —
  that gap IS the Collatz conjecture.
-/

import Collatz.Parity

namespace Collatz

/-! ## The supercritical threshold -/

/-- Supercritical density forces j ≥ 17(k-1)/27, since 3^17 ≤ 2^27. -/
theorem tail_exponent (k j : ℕ) (h : 2 ^ k < 2 * 3 ^ j) :
    17 * (k - 1) / 27 ≤ j := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have hk1 : k = (k - 1) + 1 := by omega
    have e : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [hk1]
      rw [pow_succ]
      ring
    have h1 : 2 ^ (k - 1) ≤ 3 ^ j := by omega
    have h17 : (2 : ℕ) ^ ((k - 1) * 17) ≤ 2 ^ (27 * j) := by
      calc (2 : ℕ) ^ ((k - 1) * 17) = (2 ^ (k - 1)) ^ 17 := pow_mul 2 (k - 1) 17
        _ ≤ (3 ^ j) ^ 17 := Nat.pow_le_pow_left h1 17
        _ = (3 ^ 17) ^ j := by rw [← pow_mul, Nat.mul_comm j 17, pow_mul]
        _ ≤ (2 ^ 27) ^ j := Nat.pow_le_pow_left (by norm_num) j
        _ = 2 ^ (27 * j) := (pow_mul 2 27 j).symm
    have h2 : (k - 1) * 17 ≤ 27 * j :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp h17
    have h3 : 17 * (k - 1) ≤ 27 * j := by omega
    calc 17 * (k - 1) / 27 ≤ 27 * j / 27 := Nat.div_le_div_right h3
      _ = j := by omega

/-! ## The binomial tail bound (weighted binomial theorem, pure integers) -/

theorem choose_tail_bound (k m : ℕ) :
    2 ^ m * ∑ j ∈ (Finset.range (k + 1)).filter (fun j => m ≤ j), k.choose j
      ≤ 3 ^ k := by
  have hbinom : (3 : ℕ) ^ k = ∑ j ∈ Finset.range (k + 1), 2 ^ j * k.choose j := by
    have h := add_pow (2 : ℕ) 1 k
    simp only [one_pow, mul_one, Nat.cast_id] at h
    norm_num at h
    exact h
  calc 2 ^ m * ∑ j ∈ (Finset.range (k + 1)).filter (fun j => m ≤ j), k.choose j
      = ∑ j ∈ (Finset.range (k + 1)).filter (fun j => m ≤ j),
          2 ^ m * k.choose j := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ (Finset.range (k + 1)).filter (fun j => m ≤ j),
          2 ^ j * k.choose j := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        simp only [Finset.mem_filter] at hj
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hj.2)
    _ ≤ ∑ j ∈ Finset.range (k + 1), 2 ^ j * k.choose j :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = 3 ^ k := hbinom.symm

/-! ## Counting supercritical residues -/

/-- The window [2^k, 2^(k+1)) holds exactly one integer per residue class
    mod 2^k, and oddSteps k is a class function: supercritical counts
    transfer. -/
theorem card_window_supercritical (k : ℕ) :
    ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
      (fun n => 2 ^ k < 2 * 3 ^ oddSteps k n)).card
    = ((Finset.range (2 ^ k)).filter
      (fun r => 2 ^ k < 2 * 3 ^ oddSteps k r)).card := by
  have h2k : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  apply Finset.card_bij (fun n _ => n - 2 ^ k)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨ha, hb⟩, hc⟩ := hn
    have hmod : oddSteps k (n - 2 ^ k) = oddSteps k n := by
      apply oddSteps_modEq
      show (n - 2 ^ k) % 2 ^ k = n % 2 ^ k
      have e : n - 2 ^ k + 2 ^ k = n := Nat.sub_add_cancel ha
      calc (n - 2 ^ k) % 2 ^ k
          = (n - 2 ^ k + 2 ^ k) % 2 ^ k := (Nat.add_mod_right _ _).symm
        _ = n % 2 ^ k := by rw [e]
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [hmod]; exact hc
  · intro a ha b hb h
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
    omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    refine ⟨r + 2 ^ k, ?_, by omega⟩
    have hmod : oddSteps k (r + 2 ^ k) = oddSteps k r := by
      apply oddSteps_modEq
      show (r + 2 ^ k) % 2 ^ k = r % 2 ^ k
      exact Nat.add_mod_right r (2 ^ k)
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, by rw [hmod]; exact hr.2⟩

/-- Supercritical residues mod 2^k number exactly the binomial tail
    ∑_{j : 2^k < 2·3^j} C(k, j). -/
theorem card_supercritical_residues (k : ℕ) :
    ((Finset.range (2 ^ k)).filter
      (fun r => 2 ^ k < 2 * 3 ^ oddSteps k r)).card
    = ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 2 ^ k < 2 * 3 ^ j),
        k.choose j := by
  have H : Set.MapsTo (fun r => oddSteps k r)
      ((Finset.range (2 ^ k)).filter
        (fun r => 2 ^ k < 2 * 3 ^ oddSteps k r) : Finset ℕ)
      ((Finset.range (k + 1)).filter
        (fun j => 2 ^ k < 2 * 3 ^ j) : Finset ℕ) := by
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr ⊢
    have := oddSteps_le k r
    exact ⟨by omega, hr.2⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  rw [Finset.filter_filter]
  have hset : (Finset.range (2 ^ k)).filter
      (fun r => 2 ^ k < 2 * 3 ^ oddSteps k r ∧ oddSteps k r = j)
      = (Finset.range (2 ^ k)).filter (fun r => oddSteps k r = j) := by
    apply Finset.filter_congr
    intro r _
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h]; exact hj.2, h⟩
  rw [hset, card_oddSteps]

/-! ## Terras' theorem, finite form -/

/-- TERRAS' THEOREM (finite form). The integers in [2^k, 2^(k+1)) that
    do not drop below themselves within k Terras steps number at most
    3^k / 2^(17(k-1)/27) ≈ 2^(0.955k) — an exponentially vanishing
    ≈ 2^(-0.045k) fraction of the window. -/
theorem no_descent_window_bound (k : ℕ) :
    2 ^ (17 * (k - 1) / 27) *
      ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => ∀ t, t ≤ k → n ≤ terras_iter t n)).card
      ≤ 3 ^ k := by
  -- survivors are supercritical (their window position grants the
  -- information-budget hypothesis of the dichotomy)
  have hsub : (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => ∀ t, t ≤ k → n ≤ terras_iter t n) ⊆
      (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => 2 ^ k < 2 * 3 ^ oddSteps k n) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    refine ⟨⟨h1, h2⟩, ?_⟩
    apply early_no_descent_forces_density k n (h3 k le_rfl)
    have hp : 2 ^ (k - oddSteps k n) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (Nat.sub_le k _)
    omega
  have h1 : ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => ∀ t, t ≤ k → n ≤ terras_iter t n)).card ≤
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 2 ^ k < 2 * 3 ^ j),
        k.choose j := by
    calc ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => ∀ t, t ≤ k → n ≤ terras_iter t n)).card
        ≤ ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => 2 ^ k < 2 * 3 ^ oddSteps k n)).card :=
          Finset.card_le_card hsub
      _ = ((Finset.range (2 ^ k)).filter
          (fun r => 2 ^ k < 2 * 3 ^ oddSteps k r)).card :=
          card_window_supercritical k
      _ = ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 2 ^ k < 2 * 3 ^ j),
            k.choose j := card_supercritical_residues k
  have h2 : (∑ j ∈ (Finset.range (k + 1)).filter (fun j => 2 ^ k < 2 * 3 ^ j),
        k.choose j) ≤
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 17 * (k - 1) / 27 ≤ j),
        k.choose j := by
    refine Finset.sum_le_sum_of_subset ?_
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨hj.1, tail_exponent k j hj.2⟩
  calc 2 ^ (17 * (k - 1) / 27) *
        ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
          (fun n => ∀ t, t ≤ k → n ≤ terras_iter t n)).card
      ≤ 2 ^ (17 * (k - 1) / 27) *
        ∑ j ∈ (Finset.range (k + 1)).filter (fun j => 2 ^ k < 2 * 3 ^ j),
          k.choose j := Nat.mul_le_mul_left _ h1
    _ ≤ 2 ^ (17 * (k - 1) / 27) *
        ∑ j ∈ (Finset.range (k + 1)).filter
          (fun j => 17 * (k - 1) / 27 ≤ j), k.choose j :=
        Nat.mul_le_mul_left _ h2
    _ ≤ 3 ^ k := choose_tail_bound k (17 * (k - 1) / 27)

open scoped Classical in
/-- Corollary for never-descending (in particular divergent or cyclic)
    integers: the same exponential bound. Almost every integer has
    finite stopping time. -/
theorem divergent_window_bound (k : ℕ) :
    2 ^ (17 * (k - 1) / 27) *
      ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
        (fun n => ∀ t, n ≤ terras_iter t n)).card
      ≤ 3 ^ k := by
  refine le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    (no_descent_window_bound k)
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, fun t _ => hn.2 t⟩

/-!
## What this means

At every scale k, the residues mod 2^k whose first k steps could carry a
non-descending integer form an exponentially small minority — yet by
`parity_pattern_realized` they are never empty, and by
`no_finite_certificate` no bounded-memory argument can ever rule them
out. The conjecture is precisely the assertion that no single integer
inhabits this vanishing minority at every scale simultaneously.

Almost-all is now formal; all is the conjecture.
-/

end Collatz
