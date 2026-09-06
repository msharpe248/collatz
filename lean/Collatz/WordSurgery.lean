import Collatz.WordCongruence
import Collatz.NoncontractingTail

/-! Exact merging certificates. The parameterized stem is the classical
Garner family; no claim that these stems cover all orbits is made. -/
namespace Collatz.WordAffine

/-- Equal-length, equal-count word replacement is exactly an affine equality.
The reverse direction proves actual parity realization, not only integrality. -/
theorem replacement_iff {n x : ℕ} {u v : List Bool}
    (hu : Realizes n u) (hlen : u.length = v.length) (hj : ones u = ones v) :
    (Realizes x v ∧ terras_iter v.length x = terras_iter u.length n) ↔
      3^ones u*x + correction v = 3^ones u*n + correction u := by
  constructor
  · rintro ⟨hv, he⟩
    have hx := exact_form hv
    rw [← hj, he, ← hlen] at hx
    exact hx.symm.trans (exact_form hu)
  · intro he
    have hd : 2^v.length ∣ 3^ones v*x + correction v := by
      rw [← hlen, ← hj, he]
      exact (realizes_iff_dvd n u).mp hu
    have hv := (realizes_iff_dvd x v).mpr hd
    refine ⟨hv, ?_⟩
    have hx := exact_form hv
    rw [← hj, he, ← (exact_form hu), ← hlen] at hx
    rw [← hlen]
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^u.length) hx

/-- A correction increase by a ternary multiple certifies a merging predecessor.
The seed bound is explicit; positivity requires the strict bound delta < n. -/
theorem replacement_of_correction_shift {n delta : ℕ} {u v : List Bool}
    (hu : Realizes n u) (hlen : u.length = v.length) (hj : ones u = ones v)
    (hd : delta ≤ n) (hc : correction v = correction u + 3^ones u*delta) :
    Realizes (n-delta) v ∧ terras_iter v.length (n-delta) = terras_iter u.length n := by
  apply (replacement_iff hu hlen hj).mpr
  rw [hc]
  have h := Nat.sub_add_cancel hd
  calc
    3^ones u*(n-delta) + (correction u + 3^ones u*delta) =
        3^ones u*((n-delta)+delta) + correction u := by ring
    _ = 3^ones u*n + correction u := by rw [h]

private theorem ones_replicate (a : ℕ) : ones (List.replicate a true) = a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, ones, ih, Nat.add_comm]

private theorem correction_replicate (a : ℕ) :
    correction (List.replicate a true) + 2^a = 3^a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [List.replicate_succ, correction, ones_replicate, ↓reduceIte, pow_succ]
    omega

/-- Garner's stems: an initial positive run of odd steps followed by two
even steps merges with the immediately smaller seed. -/
theorem garner_stem_merge {n : ℕ} (a : ℕ) (hn : 1 ≤ n)
    (hu : Realizes n (List.replicate (a+1) true ++ [false, false])) :
    Realizes (n-1) (false :: (List.replicate a true ++ [false, true])) ∧
      terras_iter (a+3) (n-1) = terras_iter (a+3) n := by
  have hc : correction (false :: (List.replicate a true ++ [false, true])) =
      correction (List.replicate (a+1) true ++ [false, false]) +
        3^ones (List.replicate (a+1) true ++ [false, false])*1 := by
    have ha := correction_replicate a
    have hb := correction_replicate (a+1)
    simp only [correction, ones, Bool.false_eq_true, ↓reduceIte, zero_add,
      correction_append, ones_append, ones_replicate, List.length_replicate,
      pow_zero, one_mul, mul_zero, add_zero, mul_one, pow_succ] at *
    omega
  have hh := replacement_of_correction_shift hu
    (v := false :: (List.replicate a true ++ [false, true]))
    (by simp)
    (by simp [ones, ones_replicate]) hn hc
  simpa using hh

end Collatz.WordAffine

namespace Collatz

private theorem cycle_odd_counts (k : ℕ) :
    oddSteps k 2 ≤ oddSteps k 1 ∧ oddSteps k 1 ≤ oddSteps k 2 + 1 := by
  induction k with
  | zero => simp [oddSteps]
  | succ k ih =>
    simp only [oddSteps, show 1 % 2 = 1 from rfl, show 2 % 2 = 0 from rfl,
      show terras 1 = 2 from rfl, show terras 2 = 1 from rfl,
      ite_true, show ¬ (0 = 1) from by decide, ite_false]
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem surgery_27_table :
    terras_iter 70 27 = 1 ∧ oddSteps 70 27 = 41 ∧
    (∀ x : Fin 27, 0 < x.val →
      (terras_iter 70 x.val = 1 ∨ terras_iter 70 x.val = 2) ∧
      oddSteps 70 x.val ≤ 35) ∧
    (∀ x : Fin 27, ∀ t : Fin 71, 0 < x.val →
      ¬ (terras_iter t.val x.val = terras_iter t.val 27 ∧
        oddSteps t.val x.val = oddSteps t.val 27)) := by decide

/-- The convergent seed 27 has no smaller positive merging predecessor
at the same time with the same odd count, at any time. Thus unrestricted
universal coverage by equal-length/equal-count surgery is false. -/
theorem no_equal_count_smaller_merge_27 (x t : ℕ) (hx : 0 < x) (hxn : x < 27) :
    ¬ (terras_iter t x = terras_iter t 27 ∧ oddSteps t x = oddSteps t 27) := by
  obtain ⟨hn, hj, hsmall, hshort⟩ := surgery_27_table
  by_cases ht : t < 71
  · exact hshort ⟨x, hxn⟩ ⟨t, ht⟩ hx
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 70 ≤ t by omega)
    obtain ⟨he, hb⟩ := hsmall ⟨x, hxn⟩ hx
    change (terras_iter 70 x = 1 ∨ terras_iter 70 x = 2) at he
    change oddSteps 70 x ≤ 35 at hb
    have ho := cycle_odd_counts k
    intro hh
    have hc := hh.2
    rw [oddSteps_add 70 k x, oddSteps_add 70 k 27, hn, hj] at hc
    rcases he with he | he <;> rw [he] at hc <;> omega

/-- Any smaller positive merging predecessor excludes least-unboundedness.
No noncontraction hypothesis is required along the replacement word. -/
theorem smaller_merge_excludes_least_unbounded {n x s t : ℕ}
    (hx : 0 < x) (hxn : x < n)
    (he : terras_iter s x = terras_iter t n)
    (hmin : ∀ m, 0 < m → m < n → ∃ B, ∀ k, terras_iter k m ≤ B)
    (hu : ∀ B, ∃ k, B < terras_iter k n) : False := by
  obtain ⟨B, hB⟩ := hmin x hx hxn
  have hs := supercritical_shift (unbounded_orbit_supercritical (by omega) hu) t
  have htail := (supercritical_iff_unbounded_orbit (terras_iter_pos t n (by omega))).mp hs
  obtain ⟨k, hk⟩ := htail B
  rw [← he, terras_iter_add] at hk
  exact (Nat.not_lt_of_ge (hB (s+k))) hk

end Collatz
