import Collatz.Sturmian

/-! Elementary approximation inputs for the Sturmian level theorem.
The separation lemma uses a determinant-one pair bracketing the slope,
without importing a continued-fraction formalization or any cited axiom. -/

namespace Collatz

/-- A determinant-one pair on opposite sides of `α` supplies the exact
    separation hypothesis required by `sturmian_level`. -/
theorem sturmian_separation_of_neighbors {α δ ε : ℝ} {q Q : ℕ} {p P : ℤ}
    (hq : 0 < q) (hQ : 0 < Q) (hδ : 0 < δ) (hε : 0 < ε)
    (hlo : (q : ℝ) * α = (p : ℝ) + δ)
    (hhi : (Q : ℝ) * α = (P : ℝ) - ε)
    (hdet : P * (q : ℤ) - p * (Q : ℤ) = 1) :
    ∀ m : ℕ, 0 < m → m < Q → ∀ r : ℤ, δ ≤ |(m : ℝ) * α - r| := by
  intro m hm hmQ r
  let A : ℤ := P * m - (Q : ℤ) * r
  let B : ℤ := (q : ℤ) * r - p * m
  have hcoord : (m : ℤ) = A * q + B * Q := by
    dsimp [A, B]
    linear_combination -(m : ℤ) * hdet
  have hrcoord : r = A * p + B * P := by
    dsimp [A, B]
    linear_combination -r * hdet
  have he : (m : ℝ) * α - r = (A : ℝ) * δ - (B : ℝ) * ε := by
    have hmR : (m : ℝ) = (A : ℝ) * q + (B : ℝ) * Q := by exact_mod_cast hcoord
    have hrR : (r : ℝ) = (A : ℝ) * p + (B : ℝ) * P := by exact_mod_cast hrcoord
    linear_combination α * hmR - hrR + (A : ℝ) * hlo + (B : ℝ) * hhi
  have hqI : (0 : ℤ) < q := by exact_mod_cast hq
  have hQI : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hmI : (0 : ℤ) < m := by exact_mod_cast hm
  have hmQI : (m : ℤ) < Q := by exact_mod_cast hmQ
  by_cases hA : A ≤ 0
  · have hB : 1 ≤ B := by
      by_contra h
      have hB0 : B ≤ 0 := by omega
      have h1 := mul_nonpos_of_nonpos_of_nonneg hA (le_of_lt hqI)
      have h2 := mul_nonpos_of_nonpos_of_nonneg hB0 (le_of_lt hQI)
      omega
    have hA1 : A ≤ -1 := by
      by_contra h
      have hA0 : A = 0 := by omega
      have hmul := mul_le_mul_of_nonneg_right hB (le_of_lt hQI)
      rw [hA0] at hcoord
      nlinarith
    have hAR : (A : ℝ) ≤ -1 := by exact_mod_cast hA1
    have hBR : (0 : ℝ) ≤ B := by exact_mod_cast (show 0 ≤ B by omega)
    have hmul := mul_le_mul_of_nonneg_right hAR (le_of_lt hδ)
    have hbmul := mul_nonneg hBR (le_of_lt hε)
    have hx : (m : ℝ) * α - r ≤ -δ := by linarith
    exact le_trans (by linarith : δ ≤ -((m : ℝ) * α - r)) (neg_le_abs _)
  · have hA1 : 1 ≤ A := by omega
    have hB : B ≤ 0 := by
      by_contra h
      have hB1 : 1 ≤ B := by omega
      have h1 := mul_pos (show 0 < A by omega) hqI
      have h2 := mul_le_mul_of_nonneg_right hB1 (le_of_lt hQI)
      nlinarith
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA1
    have hBR : (B : ℝ) ≤ 0 := by exact_mod_cast hB
    have hmul := mul_le_mul_of_nonneg_right hAR (le_of_lt hδ)
    have hbmul := mul_nonpos_of_nonpos_of_nonneg hBR (le_of_lt hε)
    have hx : δ ≤ (m : ℝ) * α - r := by linarith
    exact hx.trans (le_abs_self _)

/-- An explicit Bezout certificate gives every rational grid point. -/
theorem grid_surjective {G : ℕ} {P U V : ℤ} (hG : 0 < G)
    (hbez : U * P + V * (G : ℤ) = 1) (z : ℤ) :
    ∃ n : ℕ, n < G ∧ ∃ k : ℤ, (n : ℤ) * P = z + k * G := by
  let a : ℤ := z * U % (G : ℤ)
  have hGI : (0 : ℤ) < G := by exact_mod_cast hG
  have ha0 : 0 ≤ a := Int.emod_nonneg _ (ne_of_gt hGI)
  have haG : a < G := Int.emod_lt_of_pos _ hGI
  refine ⟨a.toNat, ?_, -(z * V + (z * U / G) * P), ?_⟩
  · rwa [Int.toNat_lt ha0]
  · rw [Int.toNat_of_nonneg ha0]
    have hdiv : a + (G : ℤ) * (z * U / G) = z * U := Int.emod_add_mul_ediv _ _
    linear_combination P * hdiv + z * hbez

/-- Elementary uniform rotation coverage from a sufficiently accurate lower
    rational approximation. The width condition is division-free. This uses
    a slightly larger grid instead of the full three-distance theorem. -/
theorem rotation_visit_of_grid {α δ ε : ℝ} {G : ℕ} {P U V : ℤ}
    (hG : 0 < G) (hδ : δ < 1) (hε : 0 ≤ ε)
    (hbez : U * P + V * (G : ℤ) = 1)
    (happrox : (G : ℝ) * α = (P : ℝ) + ε)
    (hwidth : 1 + (G : ℝ) * ε ≤ (G : ℝ) * δ) :
    ∀ ρ : ℝ, ∃ n : ℕ, n < G ∧ visit α ρ δ n := by
  intro ρ
  let z : ℤ := ⌈(G : ℝ) * (1 - δ - ρ)⌉
  obtain ⟨n, hn, k, hk⟩ := grid_surjective hG hbez z
  have hGR : (0 : ℝ) < G := by exact_mod_cast hG
  have hnR : (n : ℝ) < G := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hzlo : (G : ℝ) * (1 - δ - ρ) ≤ z := Int.le_ceil _
  have hzhi : (z : ℝ) < (G : ℝ) * (1 - δ - ρ) + 1 := Int.ceil_lt_add_one _
  have hkR : (n : ℝ) * P = (z : ℝ) + (k : ℝ) * G := by exact_mod_cast hk
  let y : ℝ := (n : ℝ) * α + ρ - k
  have hy : (G : ℝ) * y = (z : ℝ) + (G : ℝ) * ρ + (n : ℝ) * ε := by
    dsimp [y]
    linear_combination (n : ℝ) * happrox + hkR
  have hne0 := mul_nonneg hn0 hε
  have hneG := mul_le_mul_of_nonneg_right (le_of_lt hnR) hε
  have hylo : 1 - δ ≤ y := by nlinarith
  have hyhi : y < 1 := by nlinarith
  have hy0 : 0 ≤ y := by linarith
  have hf : Int.fract ((n : ℝ) * α + ρ) = y := by
    apply Int.fract_eq_iff.mpr
    refine ⟨hy0, hyhi, k, ?_⟩
    dsimp [y]
    ring
  exact ⟨n, hn, by unfold visit; rw [hf]; exact hylo⟩

theorem rotation_window_of_grid {α δ ε : ℝ} {G : ℕ} {P U V : ℤ}
    (hG : 0 < G) (hδ : δ < 1) (hε : 0 ≤ ε)
    (hbez : U * P + V * (G : ℤ) = 1)
    (happrox : (G : ℝ) * α = (P : ℝ) + ε)
    (hwidth : 1 + (G : ℝ) * ε ≤ (G : ℝ) * δ) (ρ : ℝ) :
    ∀ a : ℕ, ∃ n, a ≤ n ∧ n < a + G ∧ visit α ρ δ n := by
  intro a
  obtain ⟨n, hn, hv⟩ := rotation_visit_of_grid hG hδ hε hbez happrox hwidth
    ((a : ℝ) * α + ρ)
  refine ⟨a + n, by omega, by omega, ?_⟩
  unfold visit at hv ⊢
  convert hv using 2
  push_cast
  ring

end Collatz
