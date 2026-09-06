import Collatz.Reciprocal
import Collatz.Cycles

/-! Lower barriers for the limiting ideal correction. These restrict a
possible confinement bridge; they do not establish its missing upper bound. -/
namespace Collatz
open Filter Topology

private theorem exists_odd_value (n : ℕ) (hn : 0 < n) :
    ∃ t, terras_iter t n % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have hs := two_mul_terras_even n he
      have hp := terras_iter_pos 1 n hn
      change 0 < terras n at hp
      obtain ⟨t, ht⟩ := ih (terras n) (by omega) hp
      exact ⟨t+1, ht⟩
    · exact ⟨0, ho⟩

theorem positive_orbit_odd_count_unbounded (K n : ℕ) (hn : 0 < n) :
    ∃ T, K ≤ oddSteps T n := by
  induction K generalizing n with
  | zero => exact ⟨0, by omega⟩
  | succ K ih =>
    obtain ⟨t, ht⟩ := exists_odd_value n hn
    obtain ⟨S, hS⟩ := ih (terras_iter (t+1) n) (terras_iter_pos (t+1) n hn)
    refine ⟨t+1+S, ?_⟩
    have ho : oddSteps 1 (terras_iter t n) = 1 := by simp [oddSteps, ht]
    rw [oddSteps_add, oddSteps_add t 1, ho]
    omega

private theorem idealC_ge_geometric (T n : ℕ) :
    1-(2/3 : ℝ)^oddSteps T n ≤ idealC T n := by
  have he := terras_exact_form T n
  have hl := terras_lower_bound T n
  have hn : 3^oddSteps T n ≤ dcoef T n+2^oddSteps T n := by nlinarith
  have hr : (3 : ℝ)^oddSteps T n ≤ (dcoef T n : ℝ)+(2 : ℝ)^oddSteps T n := by exact_mod_cast hn
  unfold idealC
  rw [div_pow]
  have hp : (0 : ℝ) < (3 : ℝ)^oddSteps T n := by positivity
  apply (le_div_iff₀ hp).mpr
  field_simp
  linarith

/-- Infinite positive trajectories have infinitely many odd steps, so the
all-odd geometric series is a universal lower barrier for bounded correction. -/
theorem one_le_idealLimit {n : ℕ} (hn : 0 < n) (h : Supercritical n) :
    1 ≤ idealLimit n := by
  have hb (K : ℕ) : 1-(2/3 : ℝ)^K ≤ idealLimit n := by
    obtain ⟨T, hT⟩ := positive_orbit_odd_count_unbounded K n hn
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2/3)
      (by norm_num : (2/3 : ℝ) ≤ 1) hT
    exact (by linarith : 1-(2/3 : ℝ)^K ≤ 1-(2/3 : ℝ)^oddSteps T n).trans
      ((idealC_ge_geometric T n).trans (idealC_le_limit h T))
  have ht : Tendsto (fun K : ℕ => 1-(2/3 : ℝ)^K) atTop (𝓝 1) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2/3)
      (by norm_num : (2/3 : ℝ) < 1)
    simpa using tendsto_const_nhds.sub hp
  exact le_of_tendsto ht (Filter.Eventually.of_forall hb)

theorem exists_even_value (n : ℕ) : ∃ t, terras_iter t n % 2 = 0 := by
  by_contra hh
  push_neg at hh
  let k := n+2
  have hp (t : ℕ) (ht : t < k) :
      terras_iter t n % 2 = terras_iter t (2^k-1) % 2 := by
    have ho : terras_iter t n % 2 = 1 := by have := hh t; omega
    rw [ho, mersenne_iter_odd k t ht]
  have hm := modEq_of_parity k n (2^k-1) hp
  have hn : n < 2^k := by have := (Nat.lt_two_pow_self : n+2 < 2^(n+2)); dsimp [k]; omega
  have hk : 0 < 2^k := by positivity
  have hs : 2^k-1 < 2^k := by omega
  have he : n = 2^k-1 := by simpa [Nat.ModEq, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hs] using hm
  have hl := (Nat.lt_two_pow_self : n+2 < 2^(n+2))
  dsimp [k] at he
  omega

private theorem limit_ledger {n : ℕ} (h : Supercritical n) (T : ℕ) :
    (3 : ℝ)^oddSteps T n*idealLimit n =
      (dcoef T n : ℝ)+(2 : ℝ)^T*idealLimit (terras_iter T n) := by
  have ht := tracking h T
  have he : (2 : ℝ)^T*(terras_iter T n : ℝ) =
      (3 : ℝ)^oddSteps T n*n+(dcoef T n : ℝ) := by
    exact_mod_cast terras_exact_form T n
  have hp : (2 : ℝ)^T ≠ 0 := by positivity
  field_simp at ht
  nlinarith

/-- Equality with the all-odd geometric barrier is impossible for a natural
seed: every such orbit eventually takes an even step. -/
theorem one_lt_idealLimit {n : ℕ} (hn : 0 < n) (h : Supercritical n) :
    1 < idealLimit n := by
  obtain ⟨t, ht⟩ := exists_even_value n
  have ho : oddSteps 1 (terras_iter t n) = 0 := by simp [oddSteps, ht]
  have hj : oddSteps (t+1) n < t+1 := by
    rw [oddSteps_add t 1, ho]
    have := oddSteps_le t n
    omega
  have hpN : 2^oddSteps (t+1) n < 2^(t+1) := Nat.pow_lt_pow_right (by omega) hj
  have hp : (2 : ℝ)^oddSteps (t+1) n < (2 : ℝ)^(t+1) := by exact_mod_cast hpN
  have he := terras_exact_form (t+1) n
  have hl := terras_lower_bound (t+1) n
  have hdN : 3^oddSteps (t+1) n ≤ dcoef (t+1) n+2^oddSteps (t+1) n := by nlinarith
  have hd : (3 : ℝ)^oddSteps (t+1) n ≤
      (dcoef (t+1) n : ℝ)+(2 : ℝ)^oddSteps (t+1) n := by exact_mod_cast hdN
  have hs := one_le_idealLimit (terras_iter_pos (t+1) n hn) (supercritical_shift h (t+1))
  have hledger := limit_ledger h (t+1)
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(t+1))
  have hpos : (0 : ℝ) < (3 : ℝ)^oddSteps (t+1) n := by positivity
  nlinarith

/-- Every bounded-correction positive orbit has a shifted limiting error
strictly above two. This is not an upper bound on any tail error. -/
theorem exists_two_lt_shifted_idealLimit {n : ℕ} (hn : 0 < n) (h : Supercritical n) :
    ∃ t, 2 < idealLimit (terras_iter t n) := by
  obtain ⟨t, ht⟩ := exists_even_value n
  let m := terras_iter t n
  have hm := supercritical_shift h t
  have hmp := terras_iter_pos t n hn
  have hnext := one_lt_idealLimit (terras_iter_pos 1 m hmp) (supercritical_shift hm 1)
  have he := tracking hm 1
  have ho : oddSteps 1 m = 0 := by simp [oddSteps, m, ht]
  have hs := two_mul_terras_even m ht
  have hsR : 2*(terras m : ℝ) = m := by exact_mod_cast hs
  change (terras m : ℝ) = ((m : ℝ)+idealLimit m)*3^oddSteps 1 m/2^1-
    idealLimit (terras m) at he
  norm_num [ho] at he
  simp only [terras_iter] at hnext
  refine ⟨t, ?_⟩
  change 2 < idealLimit m
  nlinarith

/-- A uniform bound over all shifted ideal corrections must exceed two. -/
theorem uniformSupercritical_bound_gt_two {n : ℕ} {B : ℝ} (hn : 0 < n)
    (h : UniformSupercritical n B) : 2 < B := by
  obtain ⟨t, ht⟩ := exists_two_lt_shifted_idealLimit hn h.supercritical
  exact ht.trans_le (h.limit_le t)

/-- The canonical geometric ideal is more than one above the actual orbit
value, so identifying that value with its floor would be incorrect. -/
theorem ideal_tracking_gap_gt_one {n : ℕ} (hn : 0 < n) (h : Supercritical n) (T : ℕ) :
    (terras_iter T n : ℝ)+1 <
      ((n : ℝ)+idealLimit n)*(3 : ℝ)^oddSteps T n/(2 : ℝ)^T := by
  have hl := one_lt_idealLimit (terras_iter_pos T n hn) (supercritical_shift h T)
  have ht := tracking h T
  linarith

end Collatz
