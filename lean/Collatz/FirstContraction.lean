import Collatz.Paradoxical
import Collatz.Cycles

/-! Sharper correction control up to the first contraction of the
multiplicative coefficient. No universal contraction time is assumed. -/
namespace Collatz

/-- If all earlier coefficients are at least one, the correction in
scaled integer form is at most one third of the odd count. -/
theorem first_contraction_correction_bound (T N : ℕ)
    (hpre : ∀ s < T, 2^s ≤ 3^oddSteps s N) :
    3*dcoef T N ≤ oddSteps T N * 3^oddSteps T N := by
  induction T with
  | zero => simp [dcoef, oddSteps]
  | succ T ih =>
    have hi := ih (fun s hs => hpre s (by omega))
    have hb := hpre T (by omega)
    have hd := dcoef_add T 1 N
    have ho := oddSteps_add T 1 N
    rcases Nat.mod_two_eq_zero_or_one (terras_iter T N) with hp | hp
    · have hn : ¬ terras_iter T N % 2 = 1 := by omega
      have hd1 : dcoef 1 (terras_iter T N) = 0 := by simp [dcoef, hn]
      have ho1 : oddSteps 1 (terras_iter T N) = 0 := by simp [oddSteps, hn]
      rw [hd1, ho1] at hd
      rw [ho1] at ho
      simp only [pow_zero, one_mul, mul_zero, add_zero] at hd ho
      rw [hd, ho]
      exact hi
    · have hd1 : dcoef 1 (terras_iter T N) = 1 := by simp [dcoef, hp]
      have ho1 : oddSteps 1 (terras_iter T N) = 1 := by simp [oddSteps, hp]
      rw [hd1, ho1] at hd
      rw [ho1] at ho
      simp only [pow_one, mul_one] at hd
      rw [hd, ho, pow_succ]
      nlinarith only [hi, hb]

/-- A non-descending endpoint at the first coefficient contraction has a
finite seed bound substantially smaller than the unrestricted envelope. -/
theorem first_contraction_seed_bound {T N : ℕ}
    (hpre : ∀ s < T, 2^s ≤ 3^oddSteps s N)
    (hc : 3^oddSteps T N < 2^T) (hnd : N ≤ terras_iter T N) :
    3*(2^T-3^oddSteps T N)*N ≤ oddSteps T N * 3^oddSteps T N := by
  have hd := first_contraction_correction_bound T N hpre
  have he := terras_exact_form T N
  have hm := Nat.mul_le_mul_left (2^T) hnd
  have hs := Nat.sub_add_cancel (Nat.le_of_lt hc)
  nlinarith only [hd, he, hm, hs]

/-- A seed larger than the first-contraction bound must already descend
at that endpoint. This is a conditional certificate, not an all-time bound. -/
theorem descent_at_first_contraction {T N : ℕ}
    (hpre : ∀ s < T, 2^s ≤ 3^oddSteps s N)
    (hc : 3^oddSteps T N < 2^T)
    (hlarge : oddSteps T N * 3^oddSteps T N <
      3*(2^T-3^oddSteps T N)*N) : terras_iter T N < N := by
  by_contra h
  have hb := first_contraction_seed_bound hpre hc (by omega)
  omega

/-- A finite checker that stops successfully at descent and otherwise
requires noncontraction at each visited time. -/
def contractionCheck (N x A B : ℕ) : ℕ → Bool
  | 0 => decide (x < N ∨ B ≤ A)
  | fuel+1 => if x < N then true else
      decide (B ≤ A) && contractionCheck N (terras x)
        (if x % 2 = 1 then 3*A else A) (2*B) fuel

/-- Soundness of the executable certificate at arbitrary starting state
and coefficient numerator/denominator. -/
theorem contractionCheck_sound {N x A B fuel : ℕ}
    (h : contractionCheck N x A B fuel = true) :
    ∀ t ≤ fuel, A*3^oddSteps t x < B*2^t →
      ∃ s ≤ t, terras_iter s x < N := by
  induction fuel generalizing x A B with
  | zero =>
    intro t ht hc
    have ht0 : t = 0 := by omega
    subst t
    simp only [oddSteps_zero, pow_zero, mul_one] at hc
    simp only [contractionCheck, decide_eq_true_eq] at h
    exact ⟨0, le_refl 0, by simpa using (by omega : x < N)⟩
  | succ fuel ih =>
    by_cases hx : x < N
    · intro t _ _
      exact ⟨0, Nat.zero_le t, by simpa using hx⟩
    · simp only [contractionCheck, hx, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq] at h
      intro t ht hc
      cases t with
      | zero => simp only [oddSteps_zero, pow_zero, mul_one] at hc; omega
      | succ t =>
        have ht' : t ≤ fuel := by omega
        have hc' : (if x % 2 = 1 then 3*A else A)*3^oddSteps t (terras x) <
            (2*B)*2^t := by
          rcases Nat.mod_two_eq_zero_or_one x with hp | hp
          · have hn : ¬ x % 2 = 1 := by omega
            rw [oddSteps_succ_even t x hp, pow_succ] at hc
            simp only [hn, ↓reduceIte]
            nlinarith only [hc]
          · rw [oddSteps_succ_odd t x hp, pow_succ, pow_succ] at hc
            simp only [hp, ↓reduceIte]
            nlinarith only [hc]
        obtain ⟨s, hs, hd⟩ := ih h.2 t ht' hc'
        exact ⟨s+1, by omega, hd⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem contraction_bound_65_table : ∀ T j : Fin 66,
    3^(j:ℕ) < 2^(T:ℕ) → (j:ℕ)*3^(j:ℕ) <
      3*(2^(T:ℕ)-3^(j:ℕ))*1186 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_contraction_65_table : ∀ N : Fin 1186,
    1 < (N:ℕ) → contractionCheck N N 1 1 65 = true := by
  decide

/-- Every seed above one descends by its first coefficient contraction
if that contraction occurs within 65 steps. Both finite tables are checked
by ordinary kernel reduction, with no native-decide axiom. -/
theorem descent_by_first_contraction_65 {T N : ℕ} (hN : 1 < N) (hT : T ≤ 65)
    (hpre : ∀ s < T, 2^s ≤ 3^oddSteps s N)
    (hc : 3^oddSteps T N < 2^T) : ∃ s ≤ T, terras_iter s N < N := by
  by_cases hn : N < 1186
  · have hh := small_contraction_65_table ⟨N, hn⟩ hN
    have hs := contractionCheck_sound hh T hT
    exact hs (by simpa using hc)
  · have hj : oddSteps T N < 66 := lt_of_le_of_lt (oddSteps_le T N) (by omega)
    have hb := contraction_bound_65_table ⟨T, by omega⟩ ⟨oddSteps T N, hj⟩ hc
    have hm := Nat.mul_le_mul_left (3*(2^T-3^oddSteps T N)) (show 1186 ≤ N by omega)
    exact ⟨T, le_refl T, descent_at_first_contraction hpre hc (lt_of_lt_of_le hb hm)⟩

/-- Any coefficient contraction within the first 65 steps forces an actual
prior or simultaneous descent, for every natural seed above one. -/
theorem descent_of_contraction_le65 {T N : ℕ} (hN : 1 < N) (hT : T ≤ 65)
    (hc : 3^oddSteps T N < 2^T) : ∃ s ≤ T, terras_iter s N < N := by
  have hex : ∃ t, 3^oddSteps t N < 2^t := ⟨T, hc⟩
  have ht : Nat.find hex ≤ T := Nat.find_min' hex hc
  have hpre : ∀ s < Nat.find hex, 2^s ≤ 3^oddSteps s N := by
    intro s hs
    have hh := Nat.find_min hex hs
    omega
  obtain ⟨s, hs, hd⟩ := descent_by_first_contraction_65 hN (ht.trans hT)
    hpre (Nat.find_spec hex)
  exact ⟨s, hs.trans ht, hd⟩

/-- Every positive natural return of length at most 65 reaches one.
This is a small finite-horizon exclusion, not a general cycle theorem. -/
theorem return_le65_reaches_one (N : ℕ) : ∀ T, 0 < N → 0 < T → T ≤ 65 →
    terras_iter T N = N → ∃ s, terras_iter s N = 1 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro T hN hT h65 hr
    by_cases hn : N = 1
    · exact ⟨0, by simpa using hn⟩
    have hc := cycle_three_pow_lt T N (by omega) (by omega) hr
    obtain ⟨s, _, hs⟩ := descent_of_contraction_le65 (by omega : 1 < N) h65 hc
    have hreturn : terras_iter T (terras_iter s N) = terras_iter s N := by
      rw [terras_iter_add, Nat.add_comm s T, ← terras_iter_add, hr]
    obtain ⟨r, hr'⟩ := ih (terras_iter s N) hs T (terras_iter_pos s N hN) hT h65 hreturn
    exact ⟨s+r, by rw [← terras_iter_add, hr']⟩

end Collatz
