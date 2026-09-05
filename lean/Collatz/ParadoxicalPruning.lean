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

/-- The suffix correction envelope increases with its allowed odd count.
This justifies testing only the largest admissible odd count in a search. -/
theorem completion_envelope_mono (L D : ℕ) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ L) :
    3^k*D + 2^(L-k)*(3^k-2^k) ≤
      3^l*D + 2^(L-l)*(3^l-2^l) := by
  have identity (j : ℕ) (hj : j ≤ L) :
      2^(L-j)*(3^j-2^j) + 2^L = 2^(L-j)*3^j := by
    have hsub := Nat.sub_add_cancel (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j)
    have he : 2^(L-j)*2^j = 2^L := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    nlinarith only [Nat.mul_le_mul_left (2^(L-j)) (le_of_eq hsub),
      Nat.mul_le_mul_left (2^(L-j)) (le_of_eq hsub.symm), he]
  have hpow : 2^(L-k)*3^k ≤ 2^(L-l)*3^l := by
    calc
      2^(L-k)*3^k = (2^(L-l)*2^(l-k))*3^k := by
        rw [← pow_add]
        congr 2
        omega
      _ ≤ (2^(L-l)*3^(l-k))*3^k :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _))
      _ = 2^(L-l)*3^l := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkl]
  have hmass : 3^k*D ≤ 3^l*D :=
    Nat.mul_le_mul_right D (Nat.pow_le_pow_right (by decide) hkl)
  have hk := identity k (hkl.trans hl)
  have hl' := identity l hl
  omega

/-- Passing the necessary envelope test at any odd count implies passing
at every larger count within the target length. -/
theorem completion_test_mono (L a D m : ℕ) {k l : ℕ}
    (hkl : k ≤ l) (hl : l ≤ L)
    (hk : (2^L-3^(a+k))*m ≤ 3^k*D + 2^(L-k)*(3^k-2^k)) :
    (2^L-3^(a+l))*m ≤ 3^l*D + 2^(L-l)*(3^l-2^l) := by
  have hp : 3^(a+k) ≤ 3^(a+l) :=
    Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left hkl a)
  exact (Nat.mul_le_mul_right m (Nat.sub_le_sub_left hp _)).trans
    (hk.trans (completion_envelope_mono L D hkl hl))

/-- One maximal admissible odd count suffices to prune all realized suffixes
whose odd counts are at most that maximum. -/
theorem prune_paradoxical_completion_max {n m k : ℕ} {u v : List Bool}
    (hr : Realizes n (u++v)) (hm : m ≤ n)
    (hk : ones v ≤ k) (hkL : k ≤ u.length+v.length)
    (hc : 3^(ones u+k) < 2^(u.length+v.length))
    (hb : 3^k * correction u +
      2^(u.length+v.length-k)*(3^k-2^k) <
      (2^(u.length+v.length)-3^(ones u+k))*m) :
    ¬ IsParadoxical (u.length+v.length) n := by
  have hp : 3^(ones u+ones v) ≤ 3^(ones u+k) :=
    Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left hk _)
  apply prune_paradoxical_completion hr hm (hp.trans_lt hc)
  have he := completion_envelope_mono (u.length+v.length) (correction u) hk hkL
  have hd := Nat.mul_le_mul_right m (Nat.sub_le_sub_left hp (2^(u.length+v.length)))
  exact (he.trans_lt hb).trans_le hd

/-- All seeds in a paradoxical completion satisfy the maximal-count bound.
This permits resolving a short residue-class quotient interval directly. -/
theorem paradoxical_completion_seed_bound {n k : ℕ} {u v : List Bool}
    (hr : Realizes n (u++v)) (hp : IsParadoxical (u.length+v.length) n)
    (hk : ones v ≤ k) (hkL : k ≤ u.length+v.length)
    (hc : 3^(ones u+k) < 2^(u.length+v.length)) :
    (2^(u.length+v.length)-3^(ones u+k))*n ≤
      3^k*correction u + 2^(u.length+v.length-k)*(3^k-2^k) := by
  by_contra hh
  exact (prune_paradoxical_completion_max hr (le_refl n) hk hkL hc (by omega)) hp

end Collatz.WordAffine
