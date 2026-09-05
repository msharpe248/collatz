import Collatz.SturmianApprox
import Mathlib.Data.Finset.Max

/-! A short rotation window from two bracketing errors. A maximal
fractional part replaces a three-distance theorem. -/

namespace Collatz

/-- Positive steps of size `δ` and `ε` close on the indices below `q + Q`.
If `ε ≤ δ`, their fractional parts cannot all miss `[1-δ, 1)`. -/
theorem rotation_visit_of_neighbors {α δ ε : ℝ} {q Q : ℕ} {p P : ℤ}
    (hq : 0 < q) (hQ : 0 < Q) (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hlo : (q : ℝ) * α = (p : ℝ) + δ)
    (hhi : (Q : ℝ) * α = (P : ℝ) - ε) (ρ : ℝ) :
    ∃ n : ℕ, n < q + Q ∧ visit α ρ δ n := by
  let f : ℕ → ℝ := fun n => Int.fract ((n : ℝ) * α + ρ)
  obtain ⟨n, hn, hmax⟩ := (Finset.range (q + Q)).exists_max_image f
    (Finset.nonempty_range_iff.mpr (by omega))
  have hnlt : n < q + Q := Finset.mem_range.mp hn
  by_contra h
  have hmiss : ∀ i, i < q + Q → f i < 1 - δ := by
    intro i hi
    have : ¬ visit α ρ δ i := fun hv => h ⟨i, hi, hv⟩
    exact lt_of_not_ge this
  have hfn := hmiss n hnlt
  have hfn0 : 0 ≤ f n := Int.fract_nonneg _
  have hfloor : (n : ℝ) * α + ρ - f n = (⌊(n : ℝ) * α + ρ⌋ : ℝ) := by
    change (n : ℝ) * α + ρ - (((n : ℝ) * α + ρ) -
      (⌊(n : ℝ) * α + ρ⌋ : ℝ)) = _
    ring
  by_cases hnQ : n < Q
  · have hnext : n + q < q + Q := by omega
    have heq : f (n + q) = f n + δ := by
      apply Int.fract_eq_iff.mpr
      refine ⟨by positivity, by linarith, ⌊(n : ℝ) * α + ρ⌋ + p, ?_⟩
      push_cast
      linear_combination hfloor + hlo
    have hm := hmax (n + q) (Finset.mem_range.mpr hnext)
    rw [heq] at hm
    linarith
  · have hnQle : Q ≤ n := by omega
    have hnext : n - Q < q + Q := by omega
    have heq : f (n - Q) = f n + ε := by
      apply Int.fract_eq_iff.mpr
      refine ⟨by positivity, by linarith, ⌊(n : ℝ) * α + ρ⌋ - P, ?_⟩
      rw [Nat.cast_sub hnQle]
      push_cast
      linear_combination hfloor - hhi
    have hm := hmax (n - Q) (Finset.mem_range.mpr hnext)
    rw [heq] at hm
    linarith

theorem rotation_window_of_neighbors {α δ ε : ℝ} {q Q : ℕ} {p P : ℤ}
    (hq : 0 < q) (hQ : 0 < Q) (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hlo : (q : ℝ) * α = (p : ℝ) + δ)
    (hhi : (Q : ℝ) * α = (P : ℝ) - ε) (ρ : ℝ) :
    ∀ a : ℕ, ∃ n, a ≤ n ∧ n < a + (q + Q) ∧ visit α ρ δ n := by
  intro a
  obtain ⟨n, hn, hv⟩ := rotation_visit_of_neighbors hq hQ hδ hε hεδ hlo hhi
    ((a : ℝ) * α + ρ)
  refine ⟨a + n, by omega, by omega, ?_⟩
  unfold visit at hv ⊢
  convert hv using 2
  push_cast
  ring

end Collatz
