import Collatz.IdealBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Bounded ideal correction is exactly reciprocal-orbit summability.
No orbit-growth or density hypothesis is inferred for arbitrary seeds. -/

namespace Collatz

noncomputable def orbitReciprocal (n t : ℕ) : ℝ := 1 / (terras_iter t n : ℝ)

theorem orbitReciprocal_nonneg (n t : ℕ) : 0 ≤ orbitReciprocal n t := by
  unfold orbitReciprocal
  positivity

theorem inverse_drift_eq_reciprocal {n : ℕ} (hn : 0 < n) (t : ℕ) :
    (2 : ℝ)^t / (3 : ℝ)^oddSteps t n =
      ((n : ℝ) + idealC t n) * orbitReciprocal n t := by
  have hp : (0 : ℝ) < terras_iter t n := by exact_mod_cast terras_iter_pos t n hn
  have h := terras_iter_eq_ideal t n
  unfold orbitReciprocal
  have h2 : (2 : ℝ)^t ≠ 0 := by positivity
  have h3 : (3 : ℝ)^oddSteps t n ≠ 0 := by positivity
  field_simp at h ⊢
  nlinarith

theorem idealC_one_odd {n : ℕ} (hn : n % 2 = 1) : idealC 1 n = 1 / 3 := by
  have hd := dcoef_succ_odd (T := 0) hn
  have ho := oddSteps_succ_odd 0 n hn
  norm_num [idealC, hd, ho, oddSteps, hn]

theorem reciprocal_step_ledger {n : ℕ} (hn : 0 < n) (t : ℕ) :
    (n : ℝ) * orbitReciprocal n t ≤
      6 * (idealC (t+1) n - idealC t n) +
        (n : ℝ) * (orbitReciprocal n (t+1) - orbitReciprocal n t) := by
  have hc := idealC_mono n (Nat.le_succ t)
  have hp : (0 : ℝ) < terras_iter t n := by exact_mod_cast terras_iter_pos t n hn
  rcases Nat.mod_two_eq_zero_or_one (terras_iter t n) with he | ho
  · have heq : (2 : ℝ) * (terras_iter (t+1) n : ℝ) = terras_iter t n := by
      exact_mod_cast (terras_iter_succ' t n ▸ two_mul_terras_even (terras_iter t n) he)
    have hp' : (0 : ℝ) < terras_iter (t+1) n := by exact_mod_cast terras_iter_pos (t+1) n hn
    have hr : orbitReciprocal n (t+1) = 2 * orbitReciprocal n t := by
      unfold orbitReciprocal
      field_simp
      nlinarith
    rw [hr]
    nlinarith
  · have hs := idealC_add t 1 n
    rw [idealC_one_odd ho, inverse_drift_eq_reciprocal hn t] at hs
    have hnon := mul_nonneg (idealC_nonneg t n) (orbitReciprocal_nonneg n t)
    have hnext := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      (orbitReciprocal_nonneg n (t+1))
    nlinarith

theorem reciprocal_sum_ledger {n : ℕ} (hn : 0 < n) (T : ℕ) :
    (n : ℝ) * (∑ t ∈ Finset.range T, orbitReciprocal n t) ≤
      6 * idealC T n + (n : ℝ) * (orbitReciprocal n T - orbitReciprocal n 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, mul_add]
    linarith [reciprocal_step_ledger hn T]

theorem summable_reciprocal_of_supercritical {n : ℕ} (hn : 0 < n)
    (h : Supercritical n) : Summable (orbitReciprocal n) := by
  obtain ⟨B, hB⟩ := h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply summable_of_sum_range_le (orbitReciprocal_nonneg n) (c := 6 * B / n + 1)
  intro T
  have hb : idealC T n ≤ B := hB ⟨T, rfl⟩
  have hr : orbitReciprocal n T ≤ 1 := by
    unfold orbitReciprocal
    have hp : (1 : ℝ) ≤ terras_iter T n := by exact_mod_cast terras_iter_pos T n hn
    exact (div_le_one (by positivity)).mpr hp
  have hledger := reciprocal_sum_ledger hn T
  have hzero := orbitReciprocal_nonneg n 0
  apply (mul_le_mul_iff_right₀ hnR).mp
  have heq : (n : ℝ) * (6 * B / n + 1) = 6 * B + n := by field_simp
  rw [heq]
  nlinarith

theorem idealC_exp_reciprocal_bound {n : ℕ} (hn : 0 < n) (T : ℕ) :
    (n : ℝ) + idealC T n ≤
      n * Real.exp (∑ t ∈ Finset.range T, orbitReciprocal n t) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hcn := idealC_nonneg T n
    have hrn := orbitReciprocal_nonneg n T
    have hs := idealC_add T 1 n
    rw [inverse_drift_eq_reciprocal hn T] at hs
    have hmul := mul_le_mul_of_nonneg_left (idealC_one_le_one (terras_iter T n))
      (mul_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + idealC T n)
        (orbitReciprocal_nonneg n T))
    have hstep : (n : ℝ) + idealC (T+1) n ≤
        ((n:ℝ) + idealC T n) * (1 + orbitReciprocal n T) := by nlinarith
    have hexp : 1 + orbitReciprocal n T ≤ Real.exp (orbitReciprocal n T) := by
      linarith [Real.add_one_le_exp (orbitReciprocal n T)]
    rw [Finset.sum_range_succ, Real.exp_add, ← mul_assoc]
    exact hstep.trans (mul_le_mul ih hexp (by positivity)
      (by positivity))

theorem supercritical_of_summable_reciprocal {n : ℕ} (hn : 0 < n)
    (h : Summable (orbitReciprocal n)) : Supercritical n := by
  refine ⟨(n : ℝ) * Real.exp (∑' t, orbitReciprocal n t), ?_⟩
  rintro _ ⟨T, rfl⟩
  have hs := h.sum_le_tsum (Finset.range T) (fun t _ => orbitReciprocal_nonneg n t)
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hb := idealC_exp_reciprocal_bound hn T
  linarith

theorem supercritical_iff_summable_reciprocal {n : ℕ} (hn : 0 < n) :
    Supercritical n ↔ Summable (orbitReciprocal n) :=
  ⟨summable_reciprocal_of_supercritical hn, supercritical_of_summable_reciprocal hn⟩

/-- Bounded correction forces escape from every finite set, not merely an
unbounded subsequence. This does not assert the converse. -/
theorem supercritical_orbit_tendsto_atTop {n : ℕ} (hn : 0 < n)
    (h : Supercritical n) : Filter.Tendsto (fun t => terras_iter t n)
      Filter.atTop Filter.atTop := by
  have hz := (summable_reciprocal_of_supercritical hn h).tendsto_atTop_zero
  apply Filter.tendsto_atTop.mpr
  intro B
  have he : (0 : ℝ) < 1 / ((B : ℝ) + 1) := by positivity
  filter_upwards [hz.eventually_lt_const he] with t ht
  by_contra hb
  have hval : (terras_iter t n : ℝ) ≤ B := by exact_mod_cast (by omega : terras_iter t n ≤ B)
  have hp : (0 : ℝ) < terras_iter t n := by exact_mod_cast terras_iter_pos t n hn
  have hden : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  unfold orbitReciprocal at ht
  have hcross := (div_lt_div_iff₀ hp hden).mp ht
  linarith

end Collatz
