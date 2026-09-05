/-
  Collatz — Geometric-Ideal Tracking (a new angle on divergent orbits)

  This file contains NO axioms and NO claim to prove the conjecture.

  THE IDEA. The exact orbit identity (Shadow.lean, `terras_exact_form`)

      2^T · n_T = 3^{j_T} · n + d_T          (j_T = oddSteps T n, d_T = dcoef T n)

  says that n_T = (n + c_T) · 3^{j_T} / 2^T with the REAL "ideal constant"

      c_T(n) := d_T / 3^{j_T}   ∈ ℝ,   c_T ≥ 0,  c_T increasing in T.

  Under the explicit hypothesis that the sequence c_T is BOUNDED,
  it converges to c_∞(n). A strict uniform asymptotic density gap above
  log 2/log 3 suffices for boundedness; `density_floor` does not supply
  that gap for every divergent orbit. Passing to the limit in the
  cocycle law gives the TRACKING IDENTITY

      n_T = (n + c_∞(n)) · 3^{j_T} / 2^T  −  c_∞(n_T)          (∗)

  for every T: a supercritical orbit is an exact geometric ideal
  θ·3^{j_T}/2^T, θ = n + c_∞(n) > 0, minus a correction c_∞(n_T) ≥ 0
  that is the SAME functional applied to the shifted orbit.

  WHY THIS IS A NEW HANDLE. (∗) is an identity between an integer
  (n_T) and a real number; reading it mod 1,

      frac( θ · 3^{j_T} / 2^T ) = frac( c_∞(n_T) ).

  The left side is a ×3 / ×½ walk of ONE real number driven by the
  itinerary; the right side is a functional of the itinerary's tail.
  For structured itineraries (rung 1: automatic words) the tails c_∞(n_T)
  range over a set governed by the word's kernel — the same words whose
  2-adic realization is the Mahler value in analysis/RUNG1_ATTACK.md.
  The real place and the 2-adic place now constrain the same integer:
  x(w) ∈ ℤ₂ fixes n; θ ∈ ℝ fixes the orbit's growth; (∗) forces their
  interaction to be exactly integral at every step.

  CALIBRATION FILTER (analysis/NOVEL_APPROACHES.md). Everything here is
  generic in the multiplier: 5x+1 orbits satisfy the same identity with
  3 ↦ 5, and 5x+1 is believed to have divergent orbits. So (∗) is a
  TOOL, not a resolving principle; the 3x+1-specific content must come
  from the itinerary class (atypical density) fed into (∗).

  WHAT IS PROVED HERE (all machine-checked, no `sorry`):
  * `terras_iter_eq_ideal`   — n_T = (n + c_T)·3^{j_T}/2^T, exact;
  * `idealC_add`, `idealC_mono` — the real cocycle law and monotonicity;
  * `tracking_finite`        — the finite-horizon form of (∗), exact for all T, S;
  * `tendsto_idealC`         — convergence under boundedness (`Supercritical`);
  * `tracking`               — the limit identity (∗);
  * `orbit_le_ideal`, `orbit_ideal_error` — n_T ≤ θ·3^{j_T}/2^T, with the
    error bounded by B under uniform supercriticality;
  * `fract_ideal`            — the mod-1 rigidity equation.
-/

import Collatz.Ladder
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Collatz

open Filter Topology

/-! ## The partial ideal constant -/

/-- c_T(n) = d_T / 3^{j_T}: the real partial ideal constant of the
    length-T itinerary of n. -/
noncomputable def idealC (T n : ℕ) : ℝ :=
  (dcoef T n : ℝ) / (3 : ℝ) ^ oddSteps T n

theorem idealC_nonneg (T n : ℕ) : 0 ≤ idealC T n := by
  unfold idealC; positivity

@[simp] theorem idealC_zero (n : ℕ) : idealC 0 n = 0 := by
  simp [idealC]

/-- The exact orbit identity in real form: n_T = (n + c_T)·3^{j_T}/2^T. -/
theorem terras_iter_eq_ideal (T n : ℕ) :
    (terras_iter T n : ℝ) =
      ((n : ℝ) + idealC T n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T := by
  have h := terras_exact_form T n
  have hc : ((2 : ℝ) ^ T) * (terras_iter T n : ℝ) =
      (3 : ℝ) ^ oddSteps T n * (n : ℝ) + (dcoef T n : ℝ) := by
    exact_mod_cast h
  have h3 : (0 : ℝ) < (3 : ℝ) ^ oddSteps T n := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  unfold idealC
  field_simp
  linarith [hc]

/-- The real cocycle law: c_{S+T}(n) = c_S(n) + (2^S/3^{j_S}) · c_T(n_S). -/
theorem idealC_add (S T n : ℕ) :
    idealC (S + T) n =
      idealC S n + (2 : ℝ) ^ S / (3 : ℝ) ^ oddSteps S n *
        idealC T (terras_iter S n) := by
  unfold idealC
  rw [dcoef_add, oddSteps_add]
  push_cast
  rw [pow_add]
  have h1 : (0 : ℝ) < (3 : ℝ) ^ oddSteps S n := by positivity
  have h2 : (0 : ℝ) < (3 : ℝ) ^ oddSteps T (terras_iter S n) := by positivity
  field_simp

theorem idealC_mono (n : ℕ) : Monotone (fun T => idealC T n) := by
  refine monotone_nat_of_le_succ (fun T => ?_)
  have := idealC_add T 1 n
  simp only at this ⊢
  rw [this]
  have : 0 ≤ (2 : ℝ) ^ T / (3 : ℝ) ^ oddSteps T n * idealC 1 (terras_iter T n) := by
    have := idealC_nonneg 1 (terras_iter T n)
    positivity
  linarith

/-- The finite-horizon tracking identity, exact for every T and S:
    n_T = (n + c_{T+S}(n))·3^{j_T}/2^T − c_S(n_T). -/
theorem tracking_finite (T S n : ℕ) :
    (terras_iter T n : ℝ) =
      ((n : ℝ) + idealC (T + S) n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T
        - idealC S (terras_iter T n) := by
  rw [idealC_add, terras_iter_eq_ideal T n]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ oddSteps T n := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  field_simp
  ring

/-! ## The limit: supercritical orbits -/

/-- An orbit is *supercritical* (in the sense used here) when its partial
    ideal constants are bounded. This is an additional summability
    hypothesis, not a consequence of the critical density floor alone. -/
def Supercritical (n : ℕ) : Prop :=
  BddAbove (Set.range fun T => idealC T n)

/-- The ideal constant c_∞(n) = sup_T c_T(n) (= 0 by convention if unbounded). -/
noncomputable def idealLimit (n : ℕ) : ℝ := ⨆ T, idealC T n

theorem tendsto_idealC {n : ℕ} (h : Supercritical n) :
    Tendsto (fun T => idealC T n) atTop (𝓝 (idealLimit n)) :=
  tendsto_atTop_ciSup (idealC_mono n) h

theorem idealC_le_limit {n : ℕ} (h : Supercritical n) (T : ℕ) :
    idealC T n ≤ idealLimit n :=
  le_ciSup h T

theorem idealLimit_nonneg {n : ℕ} (h : Supercritical n) : 0 ≤ idealLimit n :=
  le_trans (idealC_nonneg 0 n) (idealC_le_limit h 0)

/-- Supercriticality propagates along the orbit. -/
theorem supercritical_shift {n : ℕ} (h : Supercritical n) (T : ℕ) :
    Supercritical (terras_iter T n) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T, ?_⟩
  rintro _ ⟨S, rfl⟩
  have hTS := hB ⟨T + S, rfl⟩
  simp only at hTS
  rw [idealC_add] at hTS
  have h3 : (0 : ℝ) < (3 : ℝ) ^ oddSteps T n := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hc := idealC_nonneg T n
  rw [le_div_iff₀ h2]
  have : (2 : ℝ) ^ T / (3 : ℝ) ^ oddSteps T n * idealC S (terras_iter T n) ≤ B := by
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ h3] at this
  linarith

/-- THE TRACKING IDENTITY (∗):
    n_T = (n + c_∞(n))·3^{j_T}/2^T − c_∞(n_T). -/
theorem tracking {n : ℕ} (h : Supercritical n) (T : ℕ) :
    (terras_iter T n : ℝ) =
      ((n : ℝ) + idealLimit n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T
        - idealLimit (terras_iter T n) := by
  -- take S → ∞ in `tracking_finite`
  have hA : Tendsto (fun S => idealC (T + S) n) atTop (𝓝 (idealLimit n)) :=
    (tendsto_idealC h).comp (by simpa [Nat.add_comm] using tendsto_add_atTop_nat T)
  have hB : Tendsto (fun S => idealC S (terras_iter T n)) atTop
      (𝓝 (idealLimit (terras_iter T n))) :=
    tendsto_idealC (supercritical_shift h T)
  have hR : Tendsto
      (fun S => ((n : ℝ) + idealC (T + S) n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T
        - idealC S (terras_iter T n)) atTop
      (𝓝 (((n : ℝ) + idealLimit n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T
        - idealLimit (terras_iter T n))) :=
    (((tendsto_const_nhds.add hA).mul tendsto_const_nhds).div_const _).sub hB
  have hL : Tendsto (fun _ : ℕ => (terras_iter T n : ℝ)) atTop
      (𝓝 (terras_iter T n : ℝ)) := tendsto_const_nhds
  have heq : (fun _ : ℕ => (terras_iter T n : ℝ)) =
      fun S => ((n : ℝ) + idealC (T + S) n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T
        - idealC S (terras_iter T n) := funext (fun S => tracking_finite T S n)
  rw [heq] at hL
  exact tendsto_nhds_unique hL hR

/-- A supercritical orbit never exceeds its geometric ideal. -/
theorem orbit_le_ideal {n : ℕ} (h : Supercritical n) (T : ℕ) :
    (terras_iter T n : ℝ) ≤
      ((n : ℝ) + idealLimit n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T := by
  rw [tracking h T]
  linarith [idealLimit_nonneg (supercritical_shift h T)]

/-- Uniform supercriticality: one bound B for every tail of the orbit. -/
def UniformSupercritical (n : ℕ) (B : ℝ) : Prop :=
  ∀ T S, idealC S (terras_iter T n) ≤ B

theorem UniformSupercritical.supercritical {n : ℕ} {B : ℝ}
    (h : UniformSupercritical n B) : Supercritical n :=
  ⟨B, by rintro _ ⟨T, rfl⟩; simpa using h 0 T⟩

theorem UniformSupercritical.limit_le {n : ℕ} {B : ℝ}
    (h : UniformSupercritical n B) (T : ℕ) : idealLimit (terras_iter T n) ≤ B :=
  ciSup_le (fun S => h T S)

/-- Bounded-error tracking: a uniformly supercritical orbit is its
    geometric ideal θ·3^{j_T}/2^T up to an error in [0, B] at every time. -/
theorem orbit_ideal_error {n : ℕ} {B : ℝ} (h : UniformSupercritical n B) (T : ℕ) :
    0 ≤ ((n : ℝ) + idealLimit n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T
          - (terras_iter T n : ℝ) ∧
    ((n : ℝ) + idealLimit n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T
          - (terras_iter T n : ℝ) ≤ B := by
  have hs := h.supercritical
  rw [tracking hs T]
  constructor
  · linarith [idealLimit_nonneg (supercritical_shift hs T)]
  · linarith [h.limit_le T]

/-- The mod-1 rigidity equation: the ×3/×½ walk of θ = n + c_∞(n) has
    fractional parts prescribed by the tails of the itinerary. -/
theorem fract_ideal {n : ℕ} (h : Supercritical n) (T : ℕ) :
    Int.fract (((n : ℝ) + idealLimit n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T) =
      Int.fract (idealLimit (terras_iter T n)) := by
  have := tracking h T
  have hx : ((n : ℝ) + idealLimit n) * (3 : ℝ) ^ oddSteps T n / (2 : ℝ) ^ T =
      idealLimit (terras_iter T n) + ((terras_iter T n : ℤ) : ℝ) := by
    push_cast; linarith
  rw [hx, Int.fract_add_intCast]

end Collatz
