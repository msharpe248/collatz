import Collatz.Shadow

/-!
# Finite parity words and their affine corrections

These are identities and conditional obstructions, not a coverage claim about
arbitrary divergent itineraries. Adjacent swaps preserve the multiplier and
have an explicitly weighted correction cost.
-/

namespace Collatz.WordAffine

def ones : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) + ones w

def correction : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 3 ^ ones w else 0) + 2 * correction w

def Realizes : ℕ → List Bool → Prop
  | _, [] => True
  | n, b :: w => n % 2 = (if b then 1 else 0) ∧ Realizes (terras n) w

@[simp] theorem ones_append (u v : List Bool) : ones (u ++ v) = ones u + ones v := by
  induction u with
  | nil => simp [ones]
  | cons b u ih => simp only [List.cons_append, ones, ih]; omega

theorem correction_append (u v : List Bool) :
    correction (u ++ v) = 3 ^ ones v * correction u + 2 ^ u.length * correction v := by
  induction u with
  | nil => simp [correction]
  | cons b u ih =>
    cases b <;> simp only [List.cons_append, correction, Bool.false_eq_true,
      ↓reduceIte, ones_append, ih, List.length_cons, pow_add, pow_one] <;> ring

/-- Moving a one one position earlier changes the correction by an exact
    positive weight; this statement avoids truncated subtraction. -/
theorem adjacent_swap (u v : List Bool) :
    correction (u ++ false :: true :: v) =
      correction (u ++ true :: false :: v) + 2 ^ u.length * 3 ^ ones v := by
  simp only [correction_append, correction, ones, Bool.false_eq_true,
    ↓reduceIte, zero_add, pow_add, pow_one]
  ring

theorem realizes_ones {n : ℕ} {w : List Bool} (h : Realizes n w) :
    ones w = oddSteps w.length n := by
  induction w generalizing n with
  | nil => rfl
  | cons b w ih =>
    rcases h with ⟨hp, ht⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp
      simp only [ones, Bool.false_eq_true, ↓reduceIte, zero_add, List.length_cons]
      rw [oddSteps_succ_even _ _ hp, ih ht]
    · simp only [↓reduceIte] at hp
      simp only [ones, ↓reduceIte, List.length_cons]
      rw [oddSteps_succ_odd _ _ hp, ih ht]
      omega

theorem realizes_correction {n : ℕ} {w : List Bool} (h : Realizes n w) :
    correction w = dcoef w.length n := by
  induction w generalizing n with
  | nil => rfl
  | cons b w ih =>
    rcases h with ⟨hp, ht⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp
      simp only [correction, Bool.false_eq_true, ↓reduceIte, zero_add, List.length_cons]
      rw [dcoef_succ_even hp, ih ht]
    · simp only [↓reduceIte] at hp
      simp only [correction, ↓reduceIte, List.length_cons]
      rw [dcoef_succ_odd hp, realizes_ones ht, ih ht]

theorem exact_form {n : ℕ} {w : List Bool} (h : Realizes n w) :
    2 ^ w.length * terras_iter w.length n = 3 ^ ones w * n + correction w := by
  rw [realizes_ones h, realizes_correction h]
  exact terras_exact_form _ _

/-- Comparison of two realized words with equal length and equal odd count.
    The casts precede subtraction: all differences are in the integers. -/
theorem compare {x y : ℕ} {u v : List Bool}
    (hx : Realizes x u) (hy : Realizes y v)
    (hlen : u.length = v.length) (hones : ones u = ones v) :
    (2 : ℤ) ^ u.length * ((terras_iter u.length y : ℤ) - (terras_iter u.length x : ℤ)) =
      (3 : ℤ) ^ ones u * ((y : ℤ) - (x : ℤ)) + (correction v : ℤ) - (correction u : ℤ) := by
  have hX := exact_form hx
  have hY := exact_form hy
  rw [← hlen, ← hones] at hY
  have eX : (2 : ℤ) ^ u.length * (terras_iter u.length x : ℤ) =
      (3 : ℤ) ^ ones u * (x : ℤ) + (correction u : ℤ) := by exact_mod_cast hX
  have eY : (2 : ℤ) ^ u.length * (terras_iter u.length y : ℤ) =
      (3 : ℤ) ^ ones u * (y : ℤ) + (correction v : ℤ) := by exact_mod_cast hY
  linear_combination eY - eX

theorem compare_dvd {x y : ℕ} {u v : List Bool}
    (hx : Realizes x u) (hy : Realizes y v)
    (hlen : u.length = v.length) (hones : ones u = ones v) :
    (2 : ℤ) ^ u.length ∣
      (3 : ℤ) ^ ones u * ((y : ℤ) - (x : ℤ)) + (correction v : ℤ) - (correction u : ℤ) :=
  ⟨(terras_iter u.length y : ℤ) - (terras_iter u.length x : ℤ),
    (compare hx hy hlen hones).symm⟩

theorem compare_bound {x y : ℕ} {u v : List Bool}
    (hx : Realizes x u) (hy : Realizes y v)
    (hlen : u.length = v.length) (hones : ones u = ones v)
    (hne : terras_iter u.length y ≠ terras_iter u.length x) :
    (2 : ℤ) ^ u.length ≤
      |(3 : ℤ) ^ ones u * ((y : ℤ) - (x : ℤ)) + (correction v : ℤ) - (correction u : ℤ)| := by
  rw [← compare hx hy hlen hones, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ u.length)]
  have hd : (terras_iter u.length y : ℤ) - (terras_iter u.length x : ℤ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hne)
  have hpos := abs_pos.mpr hd
  have hone : (1 : ℤ) ≤ |(terras_iter u.length y : ℤ) - (terras_iter u.length x : ℤ)| := by omega
  nlinarith [show (0 : ℤ) ≤ 2 ^ u.length by positivity]

end Collatz.WordAffine
