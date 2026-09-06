import Collatz.Shadow

/-! A cycle-based cylinder construction cannot bootstrap Mersenne parameters
from proper smaller canonical base residues. This is not an orbit exclusion. -/
namespace Collatz.CycleCylinderBoundary

theorem seed_le_scaled_endpoint (t n : ℕ) : n ≤ 2^t*terras_iter t n := by
  have h := terras_exact_form t n
  have hp : 1 ≤ 3^oddSteps t n := Nat.one_le_pow _ _ (by decide)
  nlinarith

/-- Reaching the target cycle within the cylinder depth forces a small base. -/
theorem target_cycle_size_bound {r d : ℕ}
    (h : terras_iter d (27*r+20) ≤ 2) : 27*r+20 ≤ 2^(d+1) := by
  have hb := seed_le_scaled_endpoint d (27*r+20)
  have hs := Nat.mul_le_mul_left (2^d) h
  rw [pow_succ]
  omega

/-- The largest canonical parameter residue cannot reach the target cycle
within that same binary depth. -/
theorem top_residue_not_in_target_cycle (d : ℕ) :
    2 < terras_iter d (27*(2^d-1)+20) := by
  by_contra h
  have hb := target_cycle_size_bound (by omega : terras_iter d (27*(2^d-1)+20) ≤ 2)
  have hp : 0 < 2^d := by positivity
  rw [pow_succ] at hb
  omega

/-- Every proper-prefix residue of a Mersenne parameter is a top residue. -/
theorem mersenne_residue {k d r : ℕ} (hd : d ≤ k)
    (hr : r < 2^d) (hm : (2^k-1) % 2^d = r) : r = 2^d-1 := by
  have hp : 0 < 2^k := by positivity
  have hp' : 0 < 2^d := by positivity
  have he : 2^k-1+1 = 2^k := by omega
  have hv : 2^d ∣ 2^k := pow_dvd_pow 2 hd
  have hz : (2^k-1+1) % 2^d = 0 := by rw [he]; exact Nat.mod_eq_zero_of_dvd hv
  have hh : (r+1) % 2^d = 0 := by
    simpa only [Nat.add_mod, hm, Nat.mod_mod] using hz
  have hdiv : 2^d ∣ r+1 := Nat.dvd_of_mod_eq_zero hh
  have hb := Nat.le_of_dvd (by omega : 0<r+1) hdiv
  omega

/-- No smaller canonical base can bootstrap this parameter using a target
that has already reached the cycle by the chosen binary-cylinder depth. -/
theorem no_smaller_cycle_base {k d r : ℕ}
    (hr : r < 2^d) (hm : (2^k-1) % 2^d = r) (hsmall : r < 2^k-1) :
    ¬ terras_iter d (27*r+20) ≤ 2 := by
  have hd : d ≤ k := by
    by_contra hh
    have hk : k ≤ d := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0<2) hk
    have hpos : 0<2^k := by positivity
    have hlt : 2^k-1 < 2^d := by omega
    rw [Nat.mod_eq_of_lt hlt] at hm
    omega
  have he := mersenne_residue hd hr hm
  rw [he]
  have hb := top_residue_not_in_target_cycle d
  omega

end Collatz.CycleCylinderBoundary
