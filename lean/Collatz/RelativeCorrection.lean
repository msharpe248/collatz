import Collatz.OrbitSummability

/-! Relative correction vanishes on every unbounded positive orbit.
This does not bound the absolute correction on shifted orbits. -/

namespace Collatz

/-- Exact normalized form of the correction cocycle. -/
theorem relative_shifted_idealLimit {N : ℕ} (hN : 0 < N)
    (hs : Supercritical N) (t : ℕ) :
    idealLimit (terras_iter t N) / (terras_iter t N : ℝ) =
      (idealLimit N - idealC t N) / ((N : ℝ) + idealC t N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := idealC_nonneg t N
  have hden : (N : ℝ) + idealC t N ≠ 0 := ne_of_gt (by linarith)
  have h2 : (2 : ℝ)^t ≠ 0 := by positivity
  have h3 : (3 : ℝ)^oddSteps t N ≠ 0 := by positivity
  have ht := tracking hs t
  rw [terras_iter_eq_ideal t N] at ht
  have he : idealLimit (terras_iter t N) =
      (idealLimit N - idealC t N) * (3 : ℝ)^oddSteps t N / (2 : ℝ)^t := by
    linear_combination ht
  rw [he, terras_iter_eq_ideal t N]
  field_simp

/-- Every unbounded positive orbit has vanishing relative shifted correction.
No convergence to zero of the absolute shifted correction is asserted. -/
theorem unbounded_relative_correction_tendsto_zero {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) :
    Filter.Tendsto (fun t => idealLimit (terras_iter t N) / (terras_iter t N : ℝ))
      Filter.atTop (nhds 0) := by
  have hs := unbounded_orbit_supercritical hN h
  have hc := tendsto_idealC hs
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlim := idealLimit_nonneg hs
  have hden : (N : ℝ) + idealLimit N ≠ 0 := ne_of_gt (by linarith)
  have hh := (hc.const_sub (idealLimit N)).div (hc.const_add (N : ℝ)) hden
  simpa only [relative_shifted_idealLimit hN hs, sub_self, zero_div] using hh

end Collatz
