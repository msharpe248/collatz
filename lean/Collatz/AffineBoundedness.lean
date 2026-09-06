import Collatz.OddRunMerges
import Collatz.ResidueCorrection
import Mathlib.Data.Nat.Factorization.Basic

/-! The proposed boundedness transfer z -> 9z+2 has the full strength of
nondivergence. This equivalence is a scope check, not a proof of either side. -/
namespace Collatz

def OrbitBounded (n : ℕ) : Prop := ∃ B, ∀ t, terras_iter t n ≤ B

theorem OrbitBounded.shift {n : ℕ} (hn : OrbitBounded n) (k : ℕ) :
    OrbitBounded (terras_iter k n) := by
  obtain ⟨B, hB⟩ := hn
  exact ⟨B, fun t => by simpa only [terras_iter_add] using hB (k+t)⟩

private theorem unbounded_of_not_bounded {n : ℕ} (hn : ¬ OrbitBounded n) :
    ∀ B, ∃ t, B < terras_iter t n := by
  simpa only [OrbitBounded, not_exists, not_forall, not_le] using hn

private theorem zero_bounded : OrbitBounded 0 := by
  refine ⟨0, ?_⟩
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simpa [terras_iter, terras] using ih

/-- Failure of nondivergence produces an actual bounded/unbounded pair
z,9z+2. Its construction uses a least unbounded seed and the classical
odd-run endpoint dichotomy, not assumed affine stability. -/
theorem exists_affine_boundedness_failure
    (h : ¬ ∀ n, OrbitBounded n) :
    ∃ z, z % 3 = 2 ∧ OrbitBounded z ∧ ¬ OrbitBounded (9*z+2) := by
  classical
  have hex : ∃ n, ¬ OrbitBounded n := by simpa only [not_forall] using h
  let n := Nat.find hex
  have hn : ¬ OrbitBounded n := Nat.find_spec hex
  have hu := unbounded_of_not_bounded hn
  have hmin : ∀ x, x < n → OrbitBounded x := by
    intro x hx
    exact not_not.mp (Nat.find_min hex hx)
  have hn0 : n ≠ 0 := by intro he; rw [he] at hn; exact hn zero_bounded
  have hn1 : n ≠ 1 := by
    have hh := unbounded_orbit_ne_one hu 0
    exact hh
  have hodd : n % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one n with he | he
    · exfalso
      have ht := two_mul_terras_even n he
      have hsmall : terras n < n := by omega
      obtain ⟨B, hB⟩ := hmin (terras n) hsmall
      obtain ⟨t, hlt⟩ := unbounded_tail hu 1 B
      exact (Nat.not_lt_of_ge (hB t)) hlt
    · exact he
  obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n+1 ≠ 0)
  have hm' : m % 2 = 1 := Nat.odd_iff.mp hm
  have ha : 0 < a := by
    by_contra hh
    have haz : a = 0 := by omega
    rw [haz] at he
    norm_num only [pow_zero, one_mul] at he
    omega
  have ha2 : 2 ≤ a := by
    by_contra hh
    have ha1 : a = 1 := by omega
    have hdecomp := he
    rw [ha1] at hdecomp
    norm_num only [pow_one] at hdecomp
    have ht := two_mul_terras_odd n hodd
    have hpar : terras n % 2 = 0 := by omega
    have ht' := two_mul_terras_even (terras n) hpar
    have hsmall : terras_iter 2 n < n := by
      change terras (terras n) < n
      omega
    obtain ⟨B, hB⟩ := hmin (terras_iter 2 n) hsmall
    obtain ⟨t, hlt⟩ := unbounded_tail hu 2 B
    exact (Nat.not_lt_of_ge (hB t)) hlt
  have hmod := least_unbounded_odd_run_exit ha he hm' (by omega : 1 < n)
    (fun x _ hx => hmin x hx) hu
  have hp := WordAffine.single_even_exit_pair ha he hmod
  let z := terras_iter (a+2) (n-1)
  have hz : OrbitBounded z := (hmin (n-1) (by omega)).shift (a+2)
  have hz3 : z % 3 = 2 :=
    WordAffine.single_even_exit_predecessor_mod_three ha2 he hmod
  refine ⟨z, hz3, hz, ?_⟩
  intro hb
  obtain ⟨B, hB⟩ := hb
  obtain ⟨t, hlt⟩ := unbounded_tail hu (a+2) B
  rw [hp] at hlt
  exact (Nat.not_lt_of_ge (hB t)) hlt

/-- Universal boundedness transfer through this affine map is equivalent
to nondivergence. Neither assertion is proved by this equivalence, and
boundedness does not by itself exclude nontrivial cycles. -/
theorem all_bounded_iff_affine_transfer :
    (∀ n, OrbitBounded n) ↔
      (∀ z, OrbitBounded z → OrbitBounded (9*z+2)) := by
  constructor
  · intro h z _
    exact h (9*z+2)
  · intro h
    by_contra hh
    obtain ⟨z, _, hz, hf⟩ := exists_affine_boundedness_failure hh
    exact hf (h z hz)

/-- Even transfer only on z=2 modulo three has the full strength of
nondivergence. A restriction to this progression does not remove the gap. -/
theorem all_bounded_iff_restricted_affine_transfer :
    (∀ n, OrbitBounded n) ↔
      (∀ z, z % 3 = 2 → OrbitBounded z → OrbitBounded (9*z+2)) := by
  constructor
  · intro h z _ _
    exact h (9*z+2)
  · intro h
    by_contra hh
    obtain ⟨z, hr, hz, hf⟩ := exists_affine_boundedness_failure hh
    exact hf (h z hr hz)

end Collatz
