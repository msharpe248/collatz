import Collatz.SturmianApprox
import Collatz.SturmianEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The quadratic slope `1 / sqrt 2`. Integer Pell recurrences supply the
approximation certificates; no external continued-fraction axioms are used. -/

namespace Collatz.Silver

noncomputable def alpha : ℝ := Real.sqrt 2 / 2

theorem alpha_sq : alpha ^ 2 = 1 / 2 := by
  unfold alpha
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem alpha_bounds : (2 : ℝ) / 3 < alpha ∧ alpha < 5 / 7 := by
  have ha : 0 ≤ alpha := by unfold alpha; positivity
  constructor <;> nlinarith [alpha_sq]

def pair : ℕ → ℕ × ℕ
  | 0 => (3, 2)
  | k + 1 => (3 * (pair k).1 + 4 * (pair k).2, 2 * (pair k).1 + 3 * (pair k).2)

def q (k : ℕ) : ℕ := (pair k).1
def p (k : ℕ) : ℕ := (pair k).2

@[simp] theorem q_zero : q 0 = 3 := rfl
@[simp] theorem p_zero : p 0 = 2 := rfl
@[simp] theorem q_succ (k : ℕ) : q (k + 1) = 3 * q k + 4 * p k := rfl
@[simp] theorem p_succ (k : ℕ) : p (k + 1) = 2 * q k + 3 * p k := rfl

theorem pell (k : ℕ) :
    3 ≤ q k ∧ 1 ≤ p k ∧ q k ≤ 2 * p k ∧ p k ≤ q k ∧ q k ^ 2 = 2 * p k ^ 2 + 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases ih with ⟨hq, hp, hqp, hpq, he⟩
    rw [q_succ, p_succ]
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    nlinarith

theorem q_large (k : ℕ) : k + 3 ≤ q k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [q_succ]; nlinarith [(pell k).1]

noncomputable def delta (k : ℕ) : ℝ := (q k : ℝ) * alpha - p k

theorem delta_product (k : ℕ) :
    delta k * ((q k : ℝ) * alpha + p k) = 1 / 2 := by
  have he : (q k : ℝ) ^ 2 = 2 * (p k : ℝ) ^ 2 + 1 := by
    exact_mod_cast (pell k).2.2.2.2
  unfold delta
  linear_combination (q k : ℝ) ^ 2 * alpha_sq + he / 2

theorem delta_bounds (k : ℕ) : 0 < delta k ∧ delta k < 1 := by
  have ha : 0 < alpha := by linarith [alpha_bounds.1]
  have hq : (0 : ℝ) ≤ q k := by positivity
  have hp : (1 : ℝ) ≤ p k := by exact_mod_cast (pell k).2.1
  have hsum : (1 : ℝ) ≤ (q k : ℝ) * alpha + p k := by nlinarith
  have he := delta_product k
  constructor <;> nlinarith

theorem delta_succ (k : ℕ) : delta (k + 1) = (3 - 4 * alpha) * delta k := by
  unfold delta
  rw [q_succ, p_succ]
  push_cast
  linear_combination 4 * (q k : ℝ) * alpha_sq

/-- The larger grid `q_(k+1)` has enough coverage for the interval of
    width `delta k`; it replaces the shorter three-distance grid. -/
theorem grid_width (k : ℕ) :
    1 + (q (k + 1) : ℝ) * delta (k + 1) ≤ (q (k + 1) : ℝ) * delta k := by
  have ha : (2 : ℝ) / 3 ≤ alpha := le_of_lt alpha_bounds.1
  have hd := (delta_bounds k).1
  have hq : (0 : ℝ) ≤ q k := by positivity
  have hp : (0 : ℝ) ≤ p k := by positivity
  have hc1 : 0 ≤ 10 * alpha - 6 := by linarith
  have hc2 : 0 ≤ 16 * alpha - 10 := by linarith
  have hnonneg := mul_nonneg (le_of_lt hd)
    (add_nonneg (mul_nonneg hq hc1) (mul_nonneg hp hc2))
  have he := delta_product k
  rw [delta_succ, q_succ]
  push_cast
  nlinarith

theorem separation (k : ℕ) :
    ∀ m : ℕ, 0 < m → m < q k + 2 * p k → ∀ r : ℤ,
      delta k ≤ |(m : ℝ) * alpha - r| := by
  have ha := alpha_bounds
  have hd := delta_bounds k
  apply sturmian_separation_of_neighbors (q := q k) (Q := q k + 2 * p k)
    (p := (p k : ℤ)) (P := (q k + p k : ℕ))
    (ε := (2 * alpha - 1) * delta k)
    (by have := (pell k).1; omega) (by have := (pell k).1; omega) hd.1
    (mul_pos (by linarith) hd.1)
  · unfold delta
    push_cast
    ring
  · unfold delta
    push_cast
    linear_combination 2 * (q k : ℝ) * alpha_sq
  · have he : (q k : ℤ) ^ 2 = 2 * (p k : ℤ) ^ 2 + 1 := by
      exact_mod_cast (pell k).2.2.2.2
    push_cast
    nlinarith

theorem coverage (k : ℕ) (ρ : ℝ) :
    ∀ a : ℕ, ∃ n, a ≤ n ∧ n < a + q (k + 1) ∧ visit alpha ρ (delta k) n := by
  apply rotation_window_of_grid (P := (p (k + 1) : ℤ))
    (U := -((q k : ℤ) + 2 * p k)) (V := (q k : ℤ) + p k)
    (by have := (pell (k + 1)).1; omega)
    (delta_bounds k).2 (le_of_lt (delta_bounds (k + 1)).1)
  · have he : (q k : ℤ) ^ 2 = 2 * (p k : ℤ) ^ 2 + 1 := by
      exact_mod_cast (pell k).2.2.2.2
    rw [p_succ, q_succ]
    push_cast
    nlinarith
  · unfold delta
    push_cast
    ring
  · exact grid_width k

theorem critical : (2 : ℝ) ≤ (3 : ℝ) ^ alpha := by
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
  rw [← Real.rpow_mul_natCast (by norm_num)]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    (show (2 : ℝ) ≤ alpha * 3 by linarith [alpha_bounds.1])
  norm_num at h ⊢
  linarith

theorem multiplier_lt : (3 : ℝ) ^ alpha < 20 / 9 := by
  apply lt_of_pow_lt_pow_left₀ 7 (by norm_num)
  rw [← Real.rpow_mul_natCast (by norm_num)]
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3)
    (show alpha * 7 < (5 : ℝ) by linarith [alpha_bounds.2])
  norm_num at h
  exact h.trans (by norm_num)

private theorem scalar_eventually (N : ℕ) :
    ∃ K : ℕ, ∀ j ≥ K,
      24 * (3 * (N : ℝ) + 21 * j + 1) * (((3 : ℝ) ^ alpha) ^ 6) ^ j < 128 ^ j := by
  let a : ℝ := (3 : ℝ) ^ alpha
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha6 : a ^ 6 < 128 :=
    (pow_lt_pow_left₀ multiplier_lt ha (by decide : 6 ≠ 0)).trans (by norm_num)
  let c : ℝ := a ^ 6 / 128
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : |c| < 1 := by rw [abs_of_nonneg hc0]; dsimp [c]; linarith
  have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 hc1
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hc1
  have hlim : Filter.Tendsto (fun j : ℕ => 24 * (3 * (N : ℝ) + 21 * j + 1) * c ^ j)
      Filter.atTop (nhds 0) := by
    convert (h0.const_mul (24 * (3 * (N : ℝ) + 1))).add (h1.const_mul 504) using 1
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
  have hpos : (0 : ℝ) < 128 ^ j := by positivity
  have := (div_lt_iff₀ hpos).mp h
  simpa [a] using this

private theorem size_of_scalar (k N : ℕ)
    (hscalar : 24 * (3 * (N : ℝ) + 21 * q k + 1) * (((3 : ℝ) ^ alpha) ^ 6) ^ q k <
      128 ^ q k) :
    (3 : ℝ) ^ (((q k + q (k + 1) : ℕ) : ℝ) * alpha + 1) *
        (3 * N + 3 * q (k + 1) + 1) <
      (2 : ℝ) ^ (q k + 2 * p k - 3 + q (k + 1)) := by
  let a : ℝ := (3 : ℝ) ^ alpha
  let Q : ℕ := q k + 2 * p k
  let G : ℕ := q (k + 1)
  let d : ℕ := Q - 2 * q k
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hQ : 2 * q k ≤ Q := by dsimp [Q]; have := (pell k).2.2.1; omega
  have hQ3 : 3 ≤ Q := by dsimp [Q]; have := (pell k).1; omega
  have hG : G = 2 * Q + q k := by dsimp [G, Q]; ring
  have hGle : G ≤ 7 * q k := by
    dsimp [G]; have := (pell k).2.2.2.1; omega
  have hd : Q = 2 * q k + d := by dsimp [d]; omega
  have ha2 : a ^ 2 ≤ 8 :=
    le_of_lt ((pow_lt_pow_left₀ multiplier_lt ha (by decide : 2 ≠ 0)).trans (by norm_num))
  have hpowa : a ^ (q k + G) = (a ^ 6) ^ q k * (a ^ 2) ^ d := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hpow2 : (2 : ℝ) ^ (Q + G) = 128 ^ q k * 8 ^ d := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, show (8 : ℝ) = 2 ^ 3 by norm_num,
      ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hB : (3 * (N : ℝ) + 3 * G + 1) ≤ 3 * N + 21 * q k + 1 := by
    have : (G : ℝ) ≤ 7 * q k := by exact_mod_cast hGle
    linarith
  have hs : 24 * (3 * (N : ℝ) + 3 * G + 1) * (a ^ 6) ^ q k < 128 ^ q k := by
    apply lt_of_le_of_lt _ hscalar
    gcongr
  have hpowd : (a ^ 2) ^ d ≤ (8 : ℝ) ^ d := pow_le_pow_left₀ (by positivity) ha2 d
  have hm : 24 * (3 * (N : ℝ) + 3 * G + 1) * (a ^ 6) ^ q k * (a ^ 2) ^ d <
      128 ^ q k * 8 ^ d := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpowd (by positivity))
      (mul_lt_mul_of_pos_right hs (by positivity))
  have hform : (3 : ℝ) ^ (((q k + G : ℕ) : ℝ) * alpha + 1) = 3 * a ^ (q k + G) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
    dsimp [a]
    rw [mul_comm (((q k + G : ℕ) : ℝ)) alpha, Real.rpow_mul_natCast (by norm_num)]
    ring
  have he : (2 : ℝ) ^ (Q + G) = 8 * 2 ^ (Q - 3 + G) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  change (3 : ℝ) ^ (((q k + G : ℕ) : ℝ) * alpha + 1) *
      (3 * N + 3 * G + 1) < 2 ^ (Q - 3 + G)
  rw [hform, hpowa]
  rw [← hpow2, he] at hm
  nlinarith

/-- No natural number has the mechanical itinerary of slope `1/sqrt 2`,
    for any real intercept. Every approximation and size obligation is proved. -/
theorem no_itinerary (N : ℕ) (ρ : ℝ) : ¬ HasItin alpha ρ N := by
  obtain ⟨K, hK⟩ := scalar_eventually N
  have hsize := size_of_scalar K N (hK (q K) (by have := q_large K; omega))
  apply sturmian_level_endpoint (q := q K) (Q := q K + 2 * p K)
    (G := q (K + 1)) (p := (p K : ℤ)) (δ := delta K)
    (by linarith [alpha_bounds.1]) critical
  · unfold delta
    push_cast
    ring
  · exact (delta_bounds K).1
  · exact (delta_bounds K).2
  · have := (pell K).1; omega
  · exact separation K
  · exact coverage K ρ
  · exact hsize

/-- An orbit cannot acquire this itinerary after an arbitrary finite prefix. -/
theorem no_eventual_itinerary (N s : ℕ) (ρ : ℝ) :
    ¬ ∀ t, (terras_iter (s + t) N % 2 : ℤ) = mech alpha ρ t := by
  intro h
  apply no_itinerary (terras_iter s N) ρ
  intro t
  rw [terras_iter_add]
  exact h t

end Collatz.Silver
