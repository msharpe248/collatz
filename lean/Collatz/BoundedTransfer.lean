import Collatz.AffinePairReturn

namespace Collatz

/-- A dyadic seed bound controls the ternary size of its initial odd run. -/
theorem odd_run_size_bound {a b m : ℕ} (hm : 0 < m)
    (h : 2^a*m ≤ 2^b) : 3^a*m ≤ 3^b := by
  have ha : a ≤ b := by
    have hp : 2^a ≤ 2^b := by nlinarith [Nat.one_le_pow a 2 (by decide)]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp hp
  have he : 2^b = 2^a*2^(b-a) := by rw [← pow_add, Nat.add_sub_of_le ha]
  rw [he] at h
  have hm' : m ≤ 2^(b-a) := Nat.le_of_mul_le_mul_left h (by positivity : 0 < 2^a)
  calc
    3^a*m ≤ 3^a*2^(b-a) := Nat.mul_le_mul_left _ hm'
    _ ≤ 3^a*3^(b-a) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = 3^b := by rw [← pow_add, Nat.add_sub_of_le ha]

/-- Exact parameter size in the single-even odd-run exit. -/
theorem odd_run_transfer_size {a n m : ℕ} (ha : 0 < a)
    (he : n+1 = 2^a*m) (hmod : (3^a*m)%4 = 3) :
    12*terras_iter (a+2) (n-1)+3 = 3^a*m := by
  have hrun := (WordAffine.realizes_odd_run a he).2
  have hpair := WordAffine.odd_run_pair_endpoint ha he
  have hy4 : terras_iter a (n-1)%4 = 0 := by omega
  have h1 := two_mul_terras_even (terras_iter a (n-1)) (by omega)
  have h2 := two_mul_terras_even (terras (terras_iter a (n-1))) (by omega)
  rw [← terras_iter_add]
  change 12*terras (terras (terras_iter a (n-1)))+3 = 3^a*m
  omega

/-- Only transfer requests actually arising from odd runs below N are needed. -/
theorem reachesOne_below_of_odd_run_requests (N : ℕ)
    (h : ∀ a m v : ℕ, 2 ≤ a → 0 < m → m%2 = 1 →
      2^a*m ≤ N → 36*v+27 = 3^a*m → AffineTransfer v) :
    ∀ n : ℕ, 0 < n → n < N → ReachesOne n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnb
    by_cases hn1 : n = 1
    · rw [hn1]
      exact ⟨0, rfl⟩
    have hnlarge : 1 < n := by omega
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · have ht := two_mul_terras_even n heven
      apply (ReachesOne.step_iff n).mp
      exact ih (terras n) (by omega) (by omega) (by omega)
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
          (ih (terras_iter 2 n) hsmall (terras_iter_pos 2 n hn) (by omega))
      · have ha2 : 2 ≤ a := by omega
        have hprev : ReachesOne (n-1) := ih (n-1) (by omega) (by omega) (by omega)
        have hz : ReachesOne (terras_iter (a+2) (n-1)) :=
          (ReachesOne.shift_iff (n-1) (a+2)).mpr hprev
        apply (ReachesOne.shift_iff n (a+2)).mp
        by_cases hmod : (3^a*m) % 4 = 1
        · rw [← WordAffine.garner_merge_of_odd_run ha he hmod]
          exact hz
        · have hp : (3^a*m) % 2 = 1 := by simp [Nat.mul_mod, Nat.pow_mod, hm']
          have hmod' : (3^a*m) % 4 = 3 := by omega
          rw [WordAffine.single_even_exit_pair ha he hmod']
          have hzmod := WordAffine.single_even_exit_predecessor_mod_three ha2 he hmod'
          let z := terras_iter (a+2) (n-1)
          obtain ⟨v, hv⟩ : ∃ v : ℕ, z = 3*v+2 := by
            refine ⟨z/3, ?_⟩
            have hd := Nat.mod_add_div z 3
            change z%3 = 2 at hzmod
            omega
          have hmpos : 0 < m := by
            by_contra hh
            have : m = 0 := by omega
            simp [this] at he
          have hsize := odd_run_transfer_size ha he hmod'
          change 12*z+3 = 3^a*m at hsize
          have hvsize : 36*v+27 = 3^a*m := by rw [hv] at hsize; omega
          have hrec := h a m v ha2 hmpos hm' (by omega) hvsize
          change ReachesOne z at hz
          rw [hv] at hz
          have hout := hrec hz
          change ReachesOne (9*z+2)
          have htarg : 9*z+2 = 27*v+20 := by rw [hv]; ring
          rw [htarg]
          exact hout

/-- A finite transfer cutoff suffices for convergence below a dyadic bound.
The transfer hypotheses remain explicit. -/
theorem reachesOne_below_pow_two (b : ℕ)
    (h : ∀ v : ℕ, 36*v+27 ≤ 3^b → AffineTransfer v) :
    ∀ n : ℕ, 0 < n → n < 2^b → ReachesOne n := by
  apply reachesOne_below_of_odd_run_requests (2^b)
  intro a m v _ hm _ hn hv
  apply h v
  rw [hv]
  exact odd_run_size_bound hm hn

/-- Smaller transfer instances give convergence below a justified dyadic cutoff. -/
theorem reachesOne_of_smaller_transfers {U b n : ℕ}
    (hrec : ∀ v : ℕ, v < U → AffineTransfer v)
    (hscale : 3^b ≤ 36*U) (hn : 0 < n) (hbound : n < 2^b) :
    ReachesOne n := by
  apply reachesOne_below_pow_two b _ n hn hbound
  intro v hv
  exact hrec v (by omega)

/-- Descent below the justified cutoff closes a transfer instance without
assuming convergence of arbitrary integers below its parameter. -/
theorem AffineTransfer.of_dyadic_descent {u b t : ℕ}
    (hrec : ∀ v : ℕ, v < u → AffineTransfer v)
    (hscale : 3^b ≤ 36*u)
    (hdescent : terras_iter t (27*u+20) < 2^b) : AffineTransfer u := by
  intro _
  apply (ReachesOne.shift_iff (27*u+20) t).mp
  exact reachesOne_of_smaller_transfers hrec hscale
    (terras_iter_pos t (27*u+20) (by omega)) hdescent

end Collatz
