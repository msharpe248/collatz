import Collatz.OddRunMerges
import Mathlib.Data.Nat.Factorization.Basic

/-! The affine transfer criterion can target reaching one, not just
boundedness. Its premise remains unproved and has the full strength of
the Collatz conjecture, including the nontrivial-cycle question. -/
namespace Collatz

def ReachesOne (n : ℕ) : Prop := ∃ t, terras_iter t n = 1

theorem ReachesOne.step_iff (n : ℕ) : ReachesOne (terras n) ↔ ReachesOne n := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t+1, ht⟩
  · rintro ⟨t, ht⟩
    cases t with
    | zero =>
      change n = 1 at ht
      rw [ht]
      exact ⟨1, rfl⟩
    | succ t => exact ⟨t, ht⟩

theorem ReachesOne.shift_iff (n k : ℕ) :
    ReachesOne (terras_iter k n) ↔ ReachesOne n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simpa only [terras_iter, ih] using step_iff n

/-- Exact restricted affine transfer is equivalent to the full conjecture.
The forward implication is trivial; the reverse is strong induction using
the two classical odd-run exit branches. No transfer premise is discharged. -/
theorem collatz_iff_restricted_affine_transfer :
    (∀ n, 0 < n → ReachesOne n) ↔
      (∀ z, z % 3 = 2 → ReachesOne z → ReachesOne (9*z+2)) := by
  constructor
  · intro h z _ _
    exact h (9*z+2) (by omega)
  · intro h n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · rw [hn1]
        exact ⟨0, rfl⟩
      have hnlarge : 1 < n := by omega
      rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
      · have ht := two_mul_terras_even n heven
        apply (ReachesOne.step_iff n).mp
        exact ih (terras n) (by omega) (by omega)
      · obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n+1 ≠ 0)
        have hm' : m % 2 = 1 := Nat.odd_iff.mp hm
        have ha : 0 < a := by
          by_contra hh
          have haz : a = 0 := by omega
          rw [haz] at he
          norm_num only [pow_zero, one_mul] at he
          omega
        by_cases ha1 : a = 1
        · have hdecomp := he
          rw [ha1] at hdecomp
          norm_num only [pow_one] at hdecomp
          have ht := two_mul_terras_odd n hodd
          have hpar : terras n % 2 = 0 := by omega
          have ht' := two_mul_terras_even (terras n) hpar
          have hsmall : terras_iter 2 n < n := by
            change terras (terras n) < n
            omega
          exact (ReachesOne.shift_iff n 2).mp
            (ih (terras_iter 2 n) hsmall (terras_iter_pos 2 n hn))
        · have ha2 : 2 ≤ a := by omega
          have hprev : ReachesOne (n-1) := ih (n-1) (by omega) (by omega)
          have hz : ReachesOne (terras_iter (a+2) (n-1)) :=
            (ReachesOne.shift_iff (n-1) (a+2)).mpr hprev
          apply (ReachesOne.shift_iff n (a+2)).mp
          by_cases hmod : (3^a*m) % 4 = 1
          · rw [← WordAffine.garner_merge_of_odd_run ha he hmod]
            exact hz
          · have hp : (3^a*m) % 2 = 1 := by simp [Nat.mul_mod, Nat.pow_mod, hm']
            have hmod' : (3^a*m) % 4 = 3 := by omega
            rw [WordAffine.single_even_exit_pair ha he hmod']
            exact h _ (WordAffine.single_even_exit_predecessor_mod_three ha2 he hmod') hz

end Collatz
