import Collatz.SturmianFamily
import Mathlib.NumberTheory.Real.Irrational

/-! An infinite explicit family of excluded mechanical itineraries.
For every integer m ≥ 6, the slope is 1 / (1 + t), where t is the
positive root of t² + m t = 1. All recurrence certificates are proved. -/

namespace Collatz.Metallic

structure Bracket where
  q : ℕ
  Q : ℕ
  p : ℕ
  P : ℕ

def brackets (m : ℕ) : ℕ → Bracket
  | 0 => ⟨1, 1, 0, 1⟩
  | k + 1 =>
    let b := brackets m k
    ⟨b.q + m * b.Q, m * (b.q + m * b.Q) + b.Q,
      b.p + m * b.P, m * (b.p + m * b.P) + b.P⟩

theorem bracket_bounds (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    k + 1 ≤ (brackets m k).q ∧ 1 ≤ (brackets m k).Q ∧
      (brackets m k).Q ≤ (m + 1) * (brackets m k).q := by
  induction k with
  | zero => simp [brackets]
  | succ k ih =>
    rcases ih with ⟨hq, hQ, hbound⟩
    change k + 1 + 1 ≤ (brackets m k).q + m * (brackets m k).Q ∧
      1 ≤ m * ((brackets m k).q + m * (brackets m k).Q) + (brackets m k).Q ∧
      m * ((brackets m k).q + m * (brackets m k).Q) + (brackets m k).Q ≤
        (m + 1) * ((brackets m k).q + m * (brackets m k).Q)
    have hmQ : (brackets m k).Q ≤ m * (brackets m k).Q := by nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

theorem bracket_ratio (m k : ℕ) :
    m * (brackets m (k + 1)).q ≤ (brackets m (k + 1)).Q := by
  change m * ((brackets m k).q + m * (brackets m k).Q) ≤
    m * ((brackets m k).q + m * (brackets m k).Q) + (brackets m k).Q
  omega

theorem determinant (m k : ℕ) :
    ((brackets m k).P : ℤ) * (brackets m k).q -
      ((brackets m k).p : ℤ) * (brackets m k).Q = 1 := by
  induction k with
  | zero => norm_num [brackets]
  | succ k ih =>
    simp only [brackets]
    push_cast
    linear_combination ih

noncomputable def slope (t : ℝ) : ℝ := 1 / (1 + t)

theorem slope_identity {t : ℝ} (ht : 0 < t) : (1 + t) * slope t = 1 := by
  unfold slope
  field_simp

theorem slope_bounds {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    (2 : ℝ) / 3 ≤ slope t ∧ slope t < 1 := by
  have ha : 0 < slope t := by unfold slope; positivity
  have hid := slope_identity ht
  constructor <;> nlinarith

noncomputable def error (t : ℝ) (k : ℕ) : ℝ := (t ^ 2) ^ k * slope t

theorem error_succ (t : ℝ) (k : ℕ) : error t (k + 1) = t ^ 2 * error t k := by
  unfold error
  rw [pow_succ]
  ring

theorem error_bounds {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (k : ℕ) : 0 < error t k ∧ error t k < 1 := by
  have ha : 0 < slope t := by unfold slope; positivity
  have ha1 : slope t < 1 := by nlinarith [slope_identity ht0]
  induction k with
  | zero => simpa [error] using And.intro ha ha1
  | succ k ih =>
    rw [error_succ]
    rcases ih with ⟨hd0, hd1⟩
    constructor
    · exact mul_pos (sq_pos_of_pos ht0) hd0
    · have ht : t ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right ht (le_of_lt hd0)]

theorem approximations (m : ℕ) {t : ℝ} (ht0 : 0 < t)
    (he : t ^ 2 + m * t = 1) (k : ℕ) :
    ((brackets m k).q : ℝ) * slope t = (brackets m k).p + error t k ∧
    ((brackets m k).Q : ℝ) * slope t = (brackets m k).P - t * error t k := by
  induction k with
  | zero =>
    simp only [brackets, error, pow_zero, one_mul, Nat.cast_one, Nat.cast_zero, zero_add]
    constructor
    · trivial
    · nlinarith [slope_identity ht0]
  | succ k ih =>
    rcases ih with ⟨hlo, hhi⟩
    simp only [brackets, error_succ]
    push_cast
    constructor
    · linear_combination hlo + (m : ℝ) * hhi - error t k * he
    · linear_combination (m : ℝ) * hlo + ((m : ℝ) ^ 2 + 1) * hhi +
        (t - m) * error t k * he

noncomputable def level (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (he : t ^ 2 + m * t = 1)
    (k : ℕ) : SturmianNeighborLevel (slope t) where
  q := (brackets m k).q
  Q := (brackets m k).Q
  p := (brackets m k).p
  P := (brackets m k).P
  δ := error t k
  ε := t * error t k
  q_pos := by have := (bracket_bounds m hm k).1; omega
  Q_pos := (bracket_bounds m hm k).2.1
  delta_pos := (error_bounds ht0 ht1 k).1
  delta_lt_one := (error_bounds ht0 ht1 k).2
  epsilon_pos := mul_pos ht0 (error_bounds ht0 ht1 k).1
  epsilon_le_delta := by
    have := mul_le_mul_of_nonneg_right (le_of_lt ht1) (le_of_lt (error_bounds ht0 ht1 k).1)
    simpa using this
  lower := by exact_mod_cast (approximations m ht0 he k).1
  upper := by exact_mod_cast (approximations m ht0 he k).2
  determinant := determinant m k

theorem no_itinerary_of_root (m : ℕ) (hm : 6 ≤ m) {t : ℝ}
    (ht0 : 0 < t) (he : t ^ 2 + m * t = 1)
    (N : ℕ) (ρ : ℝ) : ¬ HasItin (slope t) ρ N := by
  have hmR : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have ht2 : t ≤ 1 / 2 := by nlinarith
  have ht1 : t < 1 := by linarith
  have ha := slope_bounds ht0 ht2
  have hcrit : (2 : ℝ) ≤ (3 : ℝ) ^ slope t := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
    rw [← Real.rpow_mul_natCast (by norm_num)]
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (show (2 : ℝ) ≤ slope t * 3 by linarith [ha.1])
    norm_num at h ⊢
    linarith
  apply no_itinerary_of_unbounded_neighbors (by linarith [ha.1]) (le_of_lt ha.2)
    hcrit (m + 1) _ N ρ
  intro K
  refine ⟨level m (by omega) t ht0 ht1 he (K + 1), ?_, ?_, ?_⟩
  · exact le_trans (by omega) (bracket_bounds m (by omega) (K + 1)).1
  · change 6 * (brackets m (K + 1)).q ≤ (brackets m (K + 1)).Q
    exact (Nat.mul_le_mul_right _ hm).trans (bracket_ratio m K)
  · exact (bracket_bounds m (by omega) (K + 1)).2.2

noncomputable def root (m : ℕ) : ℝ := (Real.sqrt ((m : ℝ) ^ 2 + 4) - m) / 2

theorem root_positive (m : ℕ) : 0 < root m := by
  have hs := Real.sq_sqrt (show 0 ≤ (m : ℝ) ^ 2 + 4 by positivity)
  have hn := Real.sqrt_nonneg ((m : ℝ) ^ 2 + 4)
  unfold root
  nlinarith

theorem root_equation (m : ℕ) : root m ^ 2 + m * root m = 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ (m : ℝ) ^ 2 + 4 by positivity)
  unfold root
  nlinarith

noncomputable def alpha (m : ℕ) : ℝ := slope (root m)

theorem alpha_irrational (m : ℕ) (hm : 2 ≤ m) : Irrational (alpha m) := by
  have hns : ¬ IsSquare (m ^ 2 + 4) := by
    rintro ⟨r, hr⟩
    have hrm : m < r := by nlinarith
    have : m + 1 ≤ r := by omega
    nlinarith
  have hs : Irrational (Real.sqrt ((m : ℝ) ^ 2 + 4)) := by
    exact_mod_cast irrational_sqrt_natCast_iff.mpr hns
  have ht : Irrational (root m) := by
    simpa [root] using (hs.sub_natCast m).div_natCast (by decide : (2 : ℕ) ≠ 0)
  simpa [alpha, slope, one_div] using (ht.natCast_add 1).inv

theorem alpha_strictMono : StrictMono alpha := by
  intro m n hmn
  have hm := root_positive m
  have hn := root_positive n
  have hem := root_equation m
  have hen := root_equation n
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have ht : root n < root m := by
    by_contra h
    have hle : root m ≤ root n := by linarith
    have hsq : root m ^ 2 ≤ root n ^ 2 := by nlinarith
    have hmul : (m : ℝ) * root m < n * root n :=
      mul_lt_mul_of_pos_right hmnR hm |>.trans_le
        (mul_le_mul_of_nonneg_left hle (by positivity))
    linarith
  have ham : 0 < slope (root m) := by unfold slope; positivity
  have han : 0 < slope (root n) := by unfold slope; positivity
  have hidm := slope_identity hm
  have hidn := slope_identity hn
  change slope (root m) < slope (root n)
  nlinarith [mul_pos (sub_pos.mpr ht) ham]

/-- Explicit closeness to one; in particular the excluded slopes accumulate
at one. This holds for every natural parameter, even below the exclusion range. -/
theorem alpha_close_to_one (m : ℕ) :
    0 < 1 - alpha m ∧ 1 - alpha m < 1 / ((m : ℝ) + 1) := by
  have ht := root_positive m
  have he := root_equation m
  have ha : 0 < slope (root m) := by unfold slope; positivity
  have hid := slope_identity ht
  have ha1 : slope (root m) < 1 := by nlinarith
  change 0 < 1 - slope (root m) ∧ 1 - slope (root m) < 1 / ((m : ℝ) + 1)
  constructor
  · linarith
  · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
    have hmt : (m : ℝ) * root m < 1 := by nlinarith [sq_pos_of_pos ht]
    have hprod := mul_lt_mul_of_pos_right hmt ha
    nlinarith

theorem excluded_slopes_arbitrarily_close_to_one {η : ℝ} (hη : 0 < η) :
    ∃ m : ℕ, 6 ≤ m ∧ 1 - η < alpha m ∧ alpha m < 1 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (6 + 1 / η)
  have h6 : 6 ≤ m := by
    have : (6 : ℝ) < m := by have := one_div_pos.mpr hη; linarith
    exact_mod_cast le_of_lt this
  have hinv : 1 / ((m : ℝ) + 1) < η := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
    have hprod := (div_lt_iff₀ hη).mp (show 1 / η < (m : ℝ) + 1 by linarith)
    nlinarith
  have ha := alpha_close_to_one m
  exact ⟨m, h6, by linarith [ha.2], by linarith [ha.1]⟩

/-- An unconditional all-intercepts family, for every integer parameter m ≥ 6. -/
theorem no_itinerary (m : ℕ) (hm : 6 ≤ m) (N : ℕ) (ρ : ℝ) :
    ¬ HasItin (alpha m) ρ N :=
  no_itinerary_of_root m hm (root_positive m) (root_equation m) N ρ

theorem no_eventual_itinerary (m : ℕ) (hm : 6 ≤ m) (N s : ℕ) (ρ : ℝ) :
    ¬ ∀ t, (terras_iter (s + t) N % 2 : ℤ) = mech (alpha m) ρ t := by
  intro h
  apply no_itinerary m hm (terras_iter s N) ρ
  intro t
  rw [terras_iter_add]
  exact h t

end Collatz.Metallic
