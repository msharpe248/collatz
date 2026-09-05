import Collatz.WordAffine
import Collatz.Paradoxical

/-! Prefix pruning using the largest possible correction of a suffix.
This is a sound fixed-length exclusion, not an all-length termination proof. -/
namespace Collatz.WordAffine

theorem ones_le_length (w : List Bool) : ones w ≤ w.length := by
  induction w with
  | nil => simp [ones]
  | cons b w ih => cases b <;> simp_all [ones] <;> omega

/-- The largest correction occurs when the odd letters are at the end;
this scaled bound avoids division and truncated subtraction. -/
theorem correction_scaled_upper (w : List Bool) :
    2^ones w * (correction w + 2^w.length) ≤ 2^w.length * 3^ones w := by
  induction w with
  | nil => simp [ones, correction]
  | cons b w ih =>
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) (ones_le_length w)
    cases b <;> simp only [ones, correction, Bool.false_eq_true, ↓reduceIte,
      zero_add, List.length_cons, pow_add, pow_one]
    · nlinarith
    · nlinarith [Nat.mul_le_mul_right (3^ones w) hpow]

/-- Unscaled sharp upper bound on a suffix correction. -/
theorem correction_upper (w : List Bool) :
    correction w ≤ 2^(w.length-ones w)*(3^ones w-2^ones w) := by
  have h := correction_scaled_upper w
  have he : 2^(w.length-ones w)*2^ones w = 2^w.length := by
    rw [← pow_add, Nat.sub_add_cancel (ones_le_length w)]
  have hp : 0 < 2^ones w := by positivity
  have hthree : 2^ones w ≤ 3^ones w := Nat.pow_le_pow_left (by omega) _
  have hsub := Nat.sub_add_cancel hthree
  apply Nat.le_of_mul_le_mul_left (c := 2^ones w) _ hp
  have heq : 2^ones w * (2^(w.length-ones w)*(3^ones w-2^ones w)) +
      2^ones w * 2^w.length = 2^w.length * 3^ones w := by
    conv_rhs => rw [← hsub]
    rw [← he]
    ring
  nlinarith [heq]

/-- Upper correction envelope for every completion with a specified odd count. -/
theorem completion_correction_upper (u v : List Bool) :
    correction (u++v) ≤ 3^ones v * correction u +
      2^(u.length+v.length-ones v)*(3^ones v-2^ones v) := by
  rw [correction_append]
  have h := Nat.mul_le_mul_left (2^u.length) (correction_upper v)
  have hv := ones_le_length v
  have he : u.length+v.length-ones v = u.length+(v.length-ones v) := by omega
  rw [he, pow_add]
  nlinarith

/-- If even the maximal suffix correction cannot make the smallest possible
seed non-descending, no realized completion can be paradoxical. -/
theorem prune_paradoxical_completion {n m : ℕ} {u v : List Bool}
    (hr : Realizes n (u++v)) (hm : m ≤ n)
    (hc : 3^(ones u+ones v) < 2^(u.length+v.length))
    (hb : 3^ones v * correction u +
      2^(u.length+v.length-ones v)*(3^ones v-2^ones v) <
      (2^(u.length+v.length)-3^(ones u+ones v))*m) :
    ¬ IsParadoxical (u.length+v.length) n := by
  intro hp
  have he := exact_form hr
  have hbound := completion_correction_upper u v
  simp only [List.length_append, ones_append] at he
  have hsub := Nat.sub_add_cancel (Nat.le_of_lt hc)
  have hmul := Nat.mul_le_mul_left (2^(u.length+v.length)-3^(ones u+ones v)) hm
  have hnd := Nat.mul_le_mul_left (2^(u.length+v.length)) hp.2.1
  nlinarith

end Collatz.WordAffine
