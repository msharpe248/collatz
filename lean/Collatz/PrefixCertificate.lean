import Collatz.PrefixPower

/-! Exact initial-height bounds for repetitions at a later orbit position.
Unlike a drift-only score, this includes the affine correction at the shift. -/

namespace Collatz

theorem prefix_power_initial_bound (n : ℕ) (hdiv : ∀ B, ∃ t, B < terras_iter t n)
    (s ℓ M : ℕ) (hℓ : 1 ≤ ℓ) (hM : ℓ ≤ M)
    (h : ∀ t, t + ℓ < M →
      terras_iter (s + t) n % 2 = terras_iter (s + (t + ℓ)) n % 2) :
    2 ^ (M + s) ≤
      (2 ^ ℓ + 3 ^ oddSteps ℓ (terras_iter s n)) *
        (3 ^ oddSteps s n * n + dcoef s n) +
      3 ^ oddSteps ℓ (terras_iter s n) * 2 ^ (ℓ + s) := by
  have hpp := prefix_power_divergent n hdiv s ℓ M hℓ hM h
  have hscaled := Nat.mul_le_mul_right (2 ^ s) hpp
  have he := terras_exact_form s n
  calc 2 ^ (M + s) = 2 ^ M * 2 ^ s := pow_add _ _ _
    _ ≤ (2 ^ ℓ * terras_iter s n +
        3 ^ oddSteps ℓ (terras_iter s n) * (terras_iter s n + 2 ^ ℓ)) * 2 ^ s := hscaled
    _ = (2 ^ ℓ + 3 ^ oddSteps ℓ (terras_iter s n)) *
        (2 ^ s * terras_iter s n) +
        3 ^ oddSteps ℓ (terras_iter s n) * 2 ^ (ℓ + s) := by rw [pow_add]; ring
    _ = _ := by rw [he]

end Collatz
