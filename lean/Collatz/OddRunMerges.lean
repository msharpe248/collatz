import Collatz.WordSurgery

/-! Arithmetic applicability of the classical Garner stem at an arbitrarily
long initial odd run. Ordinary merging is sufficient for least-unboundedness;
the smaller replacement is not claimed to be noncontracting. -/
/- The endpoint identities also appear in LaDue (2017), Lemma 3.1 and
Theorem 4.1: https://arxiv.org/abs/1709.02979. No novelty claim. -/
namespace Collatz.WordAffine

theorem realizes_append_iff (n : ℕ) (u v : List Bool) :
    Realizes n (u ++ v) ↔
      Realizes n u ∧ Realizes (terras_iter u.length n) v := by
  induction u generalizing n with
  | nil => simp [Realizes, terras_iter]
  | cons b u ih =>
    simp only [List.cons_append, Realizes, List.length_cons, terras_iter, ih]
    tauto

/-- The divisibility of n+1 gives an actual initial odd run and its endpoint. -/
theorem realizes_odd_run (a : ℕ) {n m : ℕ} (hn : n+1 = 2^a*m) :
    Realizes n (List.replicate a true) ∧ terras_iter a n+1 = 3^a*m := by
  induction a generalizing n m with
  | zero => simpa [Realizes, terras_iter] using hn
  | succ a ih =>
    have hp : n % 2 = 1 := by
      have he : n+1 = 2*(2^a*m) := by rw [hn, pow_succ]; ring
      omega
    have ht := two_mul_terras_odd n hp
    have hnext : terras n+1 = 2^a*(3*m) := by
      rw [pow_succ] at hn
      nlinarith only [hn, ht]
    obtain ⟨hr, he⟩ := ih hnext
    constructor
    · simpa only [List.replicate_succ, Realizes, Bool.true_eq, ↓reduceIte] using
        And.intro hp hr
    · simp only [terras_iter, pow_succ]
      nlinarith only [he]

/-- A double-even exit from any nonempty odd run gives the classical
Garner merge with n-1. The run length is unrestricted. -/
theorem garner_merge_of_odd_run {a n m : ℕ} (ha : 0 < a)
    (hn : n+1 = 2^a*m) (hm : (3^a*m) % 4 = 1) :
    terras_iter (a+2) (n-1) = terras_iter (a+2) n := by
  obtain ⟨hr, he⟩ := realizes_odd_run a hn
  have hfour : terras_iter a n % 4 = 0 := by omega
  have hp : terras_iter a n % 2 = 0 := by omega
  have ht := two_mul_terras_even (terras_iter a n) hp
  have hp' : terras (terras_iter a n) % 2 = 0 := by omega
  have htail : Realizes (terras_iter a n) [false, false] := by
    simpa [Realizes] using And.intro hp hp'
  have hw : Realizes n (List.replicate a true ++ [false, false]) :=
    (realizes_append_iff n _ _).mpr (by simpa using And.intro hr htail)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have hnpos : 1 ≤ n := by
    have hh : n+1 = 2*(2^b*m) := by rw [hn, pow_succ]; ring
    omega
  exact (garner_stem_merge b hnpos hw).2

/-- The two consecutive seeds have endpoints in ratio three with offset
two after the initial odd run (LaDue, Lemma 3.1). -/
theorem odd_run_pair_endpoint {a n m : ℕ} (ha : 0 < a)
    (hn : n+1 = 2^a*m) :
    terras_iter a n = 3*terras_iter a (n-1)+2 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have hh : n+1 = 2*(2^b*m) := by rw [hn, pow_succ]; ring
  have hp : (n-1) % 2 = 0 := by omega
  have ht := two_mul_terras_even (n-1) hp
  have hprev : terras (n-1)+1 = 2^b*m := by omega
  have he := (realizes_odd_run b hprev).2
  have he' := (realizes_odd_run (b+1) hn).2
  change terras_iter b (terras n) = 3*terras_iter b (terras (n-1))+2
  simp only [terras_iter, pow_succ] at he'
  nlinarith only [he, he']

private theorem two_step_pair {x y : ℕ} (he : x = 3*y+2) (hx : x % 4 = 2) :
    terras_iter 2 x = 9*terras_iter 2 y+2 := by
  have hy : y % 4 = 0 := by omega
  have hxe : x % 2 = 0 := by omega
  have hye : y % 2 = 0 := by omega
  have hxt := two_mul_terras_even x hxe
  have hyt := two_mul_terras_even y hye
  have hxo : terras x % 2 = 1 := by omega
  have hye' : terras y % 2 = 0 := by omega
  have hxt' := two_mul_terras_odd (terras x) hxo
  have hyt' := two_mul_terras_even (terras y) hye'
  change terras (terras x) = 9*terras (terras y)+2
  omega

/-- In the nonmerging branch the same-time endpoints are exactly 9z+2
and z (the second case of LaDue, Theorem 4.1). No boundedness transfer
from z to 9z+2 is assumed or proved here. -/
theorem single_even_exit_pair {a n m : ℕ} (ha : 0 < a)
    (hn : n+1 = 2^a*m) (hm : (3^a*m) % 4 = 3) :
    terras_iter (a+2) n = 9*terras_iter (a+2) (n-1)+2 := by
  have he := (realizes_odd_run a hn).2
  have hx : terras_iter a n % 4 = 2 := by omega
  have hh := two_step_pair (odd_run_pair_endpoint ha hn) hx
  simpa only [terras_iter_add] using hh

/-- Exact early meeting criterion for an odd seed, with the odd part of
n+1 explicit. This is the classical criterion, not full eventual merging. -/
theorem garner_merge_iff {a n m : ℕ} (ha : 0 < a)
    (hn : n+1 = 2^a*m) (hm : m % 2 = 1) :
    terras_iter (a+2) (n-1) = terras_iter (a+2) n ↔ (3^a*m) % 4 = 1 := by
  constructor
  · intro he
    have hodd : (3^a*m) % 2 = 1 := by simp [Nat.mul_mod, Nat.pow_mod, hm]
    by_contra hh
    have hmod : (3^a*m) % 4 = 3 := by omega
    have hp := single_even_exit_pair ha hn hmod
    omega
  · exact garner_merge_of_odd_run ha hn

/-- The remaining pair's smaller endpoint is two modulo three once
there are at least two initial odd steps. -/
theorem single_even_exit_predecessor_mod_three {a n m : ℕ} (ha2 : 2 ≤ a)
    (he : n+1 = 2^a*m) (hmod : (3^a*m) % 4 = 3) :
    terras_iter (a+2) (n-1) % 3 = 2 := by
  have ha : 0 < a := by omega
  let z := terras_iter (a+2) (n-1)
  have hrun := (WordAffine.realizes_odd_run a he).2
  have hpair := WordAffine.odd_run_pair_endpoint ha he
  have hx4 : terras_iter a n % 4 = 2 := by omega
  have hy4 : terras_iter a (n-1) % 4 = 0 := by omega
  have hye : terras_iter a (n-1) % 2 = 0 := by omega
  have ht := two_mul_terras_even (terras_iter a (n-1)) hye
  have hye' : terras (terras_iter a (n-1)) % 2 = 0 := by omega
  have ht' := two_mul_terras_even (terras (terras_iter a (n-1))) hye'
  have hz4 : 4*z = terras_iter a (n-1) := by
    dsimp [z]
    rw [← terras_iter_add]
    change 4*terras (terras (terras_iter a (n-1))) = terras_iter a (n-1)
    omega
  obtain ⟨b, hab⟩ := Nat.exists_eq_add_of_le ha2
  have hpow : 3^a*m = 9*(3^b*m) := by rw [hab, pow_add]; ring
  rw [hpow] at hrun
  omega

end Collatz.WordAffine

namespace Collatz

/-- A least positive unbounded seed cannot have a double-even exit from
its initial odd run. This follows from ordinary merging, without assuming
noncontraction of the smaller replacement. -/
theorem least_unbounded_odd_run_exit {a n m : ℕ} (ha : 0 < a)
    (hn : n+1 = 2^a*m) (hm : m % 2 = 1) (hn1 : 1 < n)
    (hmin : ∀ x, 0 < x → x < n → ∃ B, ∀ k, terras_iter k x ≤ B)
    (hu : ∀ B, ∃ k, B < terras_iter k n) : (3^a*m) % 4 = 3 := by
  have hodd : (3^a*m) % 2 = 1 := by simp [Nat.mul_mod, Nat.pow_mod, hm]
  by_contra hh
  have hmod : (3^a*m) % 4 = 1 := by omega
  have he := WordAffine.garner_merge_of_odd_run ha hn hmod
  exact smaller_merge_excludes_least_unbounded (by omega : 0 < n-1)
    (by omega : n-1 < n) he hmin hu

end Collatz
