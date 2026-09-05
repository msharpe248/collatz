import Collatz.WordAffine
import Collatz.Cycles

/-! The cancellation argument of Knight's high-cycle exclusion, expressed
for actual natural returns and arbitrary shared middle words. See the nested
Knight2026/NoHighCycles.lean for the related Christoffel-specific argument.
No Christoffel structure or custom axiom is imported here. -/
namespace Collatz.WordAffine

/-- Swapping the two endpoint letters gives a cancellation identity,
without any palindrome assumption on the shared middle word. -/
theorem endpoint_cancellation (u : List Bool) :
    3 * correction (true :: (u ++ [false])) + 2^(u.length+2) =
      correction (false :: (u ++ [true])) + 3^(ones u+1) + 2^(u.length+1) := by
  simp only [correction, ones_append, ones, correction_append,
    Bool.false_eq_true, ↓reduceIte, pow_zero, pow_one, add_zero, zero_add,
    mul_zero, mul_one, pow_add]
  ring

private theorem three_pow_mod_eight (j : ℕ) : 3^j % 8 = 1 ∨ 3^j % 8 = 3 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

/-- If both endpoint-swapped words are realized by returning natural seeds,
then the shared middle is empty and the seeds are exactly 1 and 2.
The two returns need not be assumed to belong to the same orbit. -/
theorem endpoint_returns_trivial {u : List Bool} {x y : ℕ}
    (hx : Realizes x (true :: (u ++ [false])))
    (hy : Realizes y (false :: (u ++ [true])))
    (hrx : terras_iter (u.length+2) x = x)
    (hry : terras_iter (u.length+2) y = y) :
    u = [] ∧ x = 1 ∧ y = 2 := by
  let A := 2^(u.length+2)
  let B := 3^(ones u+1)
  let D := A-B
  have hxp : 0 < x := by
    have hh := hx.1
    simp only [↓reduceIte] at hh
    omega
  have hxlen : (true :: (u ++ [false])).length = u.length+2 := by simp
  have hylen : (false :: (u ++ [true])).length = u.length+2 := by simp
  have hxones : ones (true :: (u ++ [false])) = ones u+1 := by simp [ones]; omega
  have hyones : ones (false :: (u ++ [true])) = ones u+1 := by simp [ones]
  have hp : B < A := by
    have hh := cycle_three_pow_lt (u.length+2) x (by omega) hxp hrx
    have ho := realizes_ones hx
    rw [hxlen, hxones] at ho
    simpa [A, B, ← ho] using hh
  have hd : D+B = A := Nat.sub_add_cancel hp.le
  have hex := exact_form hx
  have hey := exact_form hy
  rw [hxlen, hxones, hrx] at hex
  rw [hylen, hyones, hry] at hey
  have hcx : correction (true :: (u ++ [false])) = D*x := by
    change A*x = B*x + _ at hex
    nlinarith only [hex, hd]
  have hcy : correction (false :: (u ++ [true])) = D*y := by
    change A*y = B*y + _ at hey
    nlinarith only [hey, hd]
  have hc := endpoint_cancellation u
  change 3 * correction (true :: (u ++ [false])) + A =
    correction (false :: (u ++ [true])) + B + 2^(u.length+1) at hc
  rw [hcx, hcy] at hc
  have hcan : D*(3*x+1) = D*y + 2^(u.length+1) := by nlinarith only [hc, hd]
  have hdiv : D ∣ 2^(u.length+1) := by
    have hh : D ∣ D*y + 2^(u.length+1) := by rw [← hcan]; exact dvd_mul_right _ _
    exact (Nat.dvd_add_iff_right (dvd_mul_right D y)).mpr hh
  have hodd : D % 2 = 1 := by
    have ha : A % 2 = 0 := by simp [A, pow_add, Nat.mul_mod]
    have hb : B % 2 = 1 := by simp [B, Nat.pow_mod]
    have hm := congrArg (fun n => n % 2) hd
    dsimp only at hm
    rw [Nat.add_mod, ha, hb] at hm
    omega
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hk0 : k = 0 := by
    by_contra hn
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [hk, pow_succ] at hodd
  have hd1 : D = 1 := by simp [hk, hk0]
  have heq : 2^(u.length+2) = 3^(ones u+1)+1 := by
    change D+B=A at hd
    dsimp [A, B] at hd
    omega
  have hlen : u.length = 0 := by
    by_contra hn
    have hh : u.length+2 = 3+(u.length-1) := by omega
    have ha : 2^(u.length+2) % 8 = 0 := by rw [hh, pow_add]; omega
    have hm := congrArg (fun n => n % 8) heq
    dsimp only at hm
    rw [ha, Nat.add_mod] at hm
    rcases three_pow_mod_eight (ones u+1) with hb | hb <;> rw [hb] at hm <;> norm_num at hm
  have hu : u = [] := List.length_eq_zero_iff.mp hlen
  subst u
  norm_num [correction, ones] at hex hey
  exact ⟨rfl, by omega, by omega⟩

/-- A single cyclic orbit cannot contain these two return words unless
it is the trivial cycle, with an empty shared middle. -/
theorem endpoint_cycle_shift_trivial {u : List Bool} {N s : ℕ}
    (hx : Realizes N (true :: (u ++ [false])))
    (hy : Realizes (terras_iter s N) (false :: (u ++ [true])))
    (hr : terras_iter (u.length+2) N = N) :
    u = [] ∧ N = 1 ∧ terras_iter s N = 2 := by
  apply endpoint_returns_trivial hx hy hr
  rw [terras_iter_add, Nat.add_comm s, ← terras_iter_add, hr]

end Collatz.WordAffine
