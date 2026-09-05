import Collatz.SturmianWindow
import Collatz.SturmianEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! An all-intercepts exclusion criterion from unbounded bracketing levels.
The constants are deliberately conservative: sixfold separation suffices
uniformly for every supercritical slope at most one. -/

namespace Collatz

structure SturmianNeighborLevel (α : ℝ) where
  q : ℕ
  Q : ℕ
  p : ℤ
  P : ℤ
  δ : ℝ
  ε : ℝ
  q_pos : 0 < q
  Q_pos : 0 < Q
  delta_pos : 0 < δ
  delta_lt_one : δ < 1
  epsilon_pos : 0 < ε
  epsilon_le_delta : ε ≤ δ
  lower : (q : ℝ) * α = (p : ℝ) + δ
  upper : (Q : ℝ) * α = (P : ℝ) - ε
  determinant : P * (q : ℤ) - p * (Q : ℤ) = 1

private theorem family_scalar_eventually (N C : ℕ) :
    ∃ K : ℕ, ∀ j ≥ K,
      24 * (3 * (N : ℝ) + 3 * (C + 1) * j + 1) * (6561 : ℝ) ^ j < 8192 ^ j := by
  let c : ℝ := 6561 / 8192
  have hc : |c| < 1 := by norm_num [c]
  have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 hc
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hc
  have hlim : Filter.Tendsto
      (fun j : ℕ => 24 * (3 * (N : ℝ) + 3 * (C + 1) * j + 1) * c ^ j)
      Filter.atTop (nhds 0) := by
    convert (h0.const_mul (24 * (3 * (N : ℝ) + 1))).add
      (h1.const_mul (72 * ((C : ℝ) + 1))) using 1
    · funext j
      simp only [pow_zero, one_mul, pow_one]
      ring
    · simp
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨K, fun j hj => ?_⟩
  have h := hK j hj
  dsimp [c] at h
  rw [div_pow, ← mul_div_assoc] at h
  simpa using (div_lt_iff₀ (by positivity : (0 : ℝ) < 8192 ^ j)).mp h

private theorem family_size {α : ℝ} (hα : α ≤ 1)
    (L : SturmianNeighborLevel α) (N C : ℕ)
    (hQ : 6 * L.q ≤ L.Q) (hC : L.Q ≤ C * L.q)
    (hscalar : 24 * (3 * (N : ℝ) + 3 * (C + 1) * L.q + 1) *
      (6561 : ℝ) ^ L.q < 8192 ^ L.q) :
    (3 : ℝ) ^ (((L.q + (L.q + L.Q) : ℕ) : ℝ) * α + 1) *
      (3 * N + 3 * ((L.q + L.Q : ℕ) : ℝ) + 1) <
        (2 : ℝ) ^ (L.Q - 3 + (L.q + L.Q)) := by
  let a : ℝ := (3 : ℝ) ^ α
  let d : ℕ := L.Q - 6 * L.q
  let G : ℕ := L.q + L.Q
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha3 : a ≤ 3 := by
    simpa [a] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα
  have ha8 : a ^ 8 ≤ 6561 := by
    convert pow_le_pow_left₀ ha ha3 8 using 1
    norm_num
  have ha4 : a ≤ 4 := by linarith
  have hd : L.Q = 6 * L.q + d := by dsimp [d]; omega
  have hQ3 : 3 ≤ L.Q := by have := L.q_pos; omega
  have hpowa : a ^ (L.q + G) = (a ^ 8) ^ L.q * a ^ d := by
    rw [← pow_mul, ← pow_add]
    congr 1
    dsimp [G]
    omega
  have hpow2 : (2 : ℝ) ^ (L.Q + G) = 8192 ^ L.q * 4 ^ d := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, show (4 : ℝ) = 2 ^ 2 by norm_num,
      ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    dsimp [G]
    omega
  have hGR : (G : ℝ) ≤ (C + 1) * (L.q : ℝ) := by
    have : G ≤ (C + 1) * L.q := by dsimp [G]; nlinarith
    exact_mod_cast this
  have hs : 24 * (3 * (N : ℝ) + 3 * G + 1) * (a ^ 8) ^ L.q < 8192 ^ L.q := by
    apply lt_of_le_of_lt _ hscalar
    apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) ha8 L.q) (by positivity)
      (by positivity)
    nlinarith
  have hpowd : a ^ d ≤ (4 : ℝ) ^ d := pow_le_pow_left₀ ha ha4 d
  have hm : 24 * (3 * (N : ℝ) + 3 * G + 1) * (a ^ 8) ^ L.q * a ^ d <
      8192 ^ L.q * 4 ^ d := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpowd (by positivity))
      (mul_lt_mul_of_pos_right hs (by positivity))
  have hform : (3 : ℝ) ^ (((L.q + G : ℕ) : ℝ) * α + 1) = 3 * a ^ (L.q + G) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
    dsimp [a]
    rw [mul_comm (((L.q + G : ℕ) : ℝ)) α, Real.rpow_mul_natCast (by norm_num)]
    ring
  have he : (2 : ℝ) ^ (L.Q + G) = 8 * 2 ^ (L.Q - 3 + G) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  change (3 : ℝ) ^ (((L.q + G : ℕ) : ℝ) * α + 1) *
      (3 * N + 3 * G + 1) < 2 ^ (L.Q - 3 + G)
  rw [hform, hpowa]
  rw [← hpow2, he] at hm
  nlinarith

/-- Uniformly bounded denominator ratios at least six, at arbitrarily large
lower denominators, exclude a supercritical mechanical itinerary. -/
theorem no_itinerary_of_unbounded_neighbors {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hcrit : (2 : ℝ) ≤ (3 : ℝ) ^ α)
    (C : ℕ)
    (hlevels : ∀ K : ℕ, ∃ L : SturmianNeighborLevel α,
      K ≤ L.q ∧ 6 * L.q ≤ L.Q ∧ L.Q ≤ C * L.q)
    (N : ℕ) (ρ : ℝ) : ¬ HasItin α ρ N := by
  obtain ⟨K, hK⟩ := family_scalar_eventually N C
  obtain ⟨L, hq, hQ, hC⟩ := hlevels K
  apply sturmian_level_endpoint (q := L.q) (Q := L.Q) (G := L.q + L.Q)
    (p := L.p) (δ := L.δ) hα0 hcrit L.lower L.delta_pos L.delta_lt_one
    (by have := L.q_pos; omega)
  · exact sturmian_separation_of_neighbors L.q_pos L.Q_pos L.delta_pos
      L.epsilon_pos L.lower L.upper L.determinant
  · exact rotation_window_of_neighbors L.q_pos L.Q_pos L.delta_pos
      L.epsilon_pos L.epsilon_le_delta L.lower L.upper ρ
  · exact family_size hα1 L N C hQ hC (hK L.q hq)

end Collatz
