import Collatz.Ideal

/-! A precise sufficient condition for bounded ideal correction.
This geometric ratio hypothesis is stronger than the critical density floor.
It is never asserted here for every divergent orbit. -/

namespace Collatz

theorem idealC_one_le_one (n : ℕ) : idealC 1 n ≤ 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hd := dcoef_succ_even (T := 0) hn
    have ho := oddSteps_succ_even 0 n hn
    norm_num [idealC, hd, ho, oddSteps, hn]
  · have hd := dcoef_succ_odd (T := 0) hn
    have ho := oddSteps_succ_odd 0 n hn
    norm_num [idealC, hd, ho, oddSteps, hn]

/-- A summable geometric bound on the inverse drift gives an explicit
    bound on every finite correction. -/
theorem idealC_le_of_geometric {n : ℕ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hgeom : ∀ t : ℕ, (2 : ℝ) ^ t ≤ C * r ^ t * (3 : ℝ) ^ oddSteps t n) :
    ∀ t, idealC t n ≤ C / (1 - r) := by
  have hden : 0 < 1 - r := by linarith
  have hledger : ∀ t, (1 - r) * idealC t n ≤ C * (1 - r ^ t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep := idealC_add t 1 n
      have hcorr := idealC_one_le_one (terras_iter t n)
      have hpos : (0 : ℝ) < (3 : ℝ) ^ oddSteps t n := by positivity
      have hratio : (2 : ℝ) ^ t / (3 : ℝ) ^ oddSteps t n ≤ C * r ^ t :=
        (div_le_iff₀ hpos).mpr (hgeom t)
      have hmul := mul_le_mul_of_nonneg_left hcorr
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ t / (3 : ℝ) ^ oddSteps t n)
      have hinc : idealC (t + 1) n ≤ idealC t n + C * r ^ t := by
        linarith
      have := mul_le_mul_of_nonneg_left hinc (le_of_lt hden)
      rw [pow_succ]
      nlinarith
  intro t
  apply (le_div_iff₀ hden).mpr
  have hnonneg : 0 ≤ C * r ^ t := by positivity
  nlinarith [hledger t]

theorem supercritical_of_geometric {n : ℕ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hgeom : ∀ t : ℕ, (2 : ℝ) ^ t ≤ C * r ^ t * (3 : ℝ) ^ oddSteps t n) :
    Supercritical n := by
  refine ⟨C / (1 - r), ?_⟩
  rintro _ ⟨t, rfl⟩
  exact idealC_le_of_geometric hC hr0 hr1 hgeom t

end Collatz
