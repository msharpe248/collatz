import Collatz.Cylinder

namespace Collatz

/-- Independence of powers of two and three, used to compare cylinder slopes. -/
theorem two_three_slope_injective {a b s t : ℕ}
    (h : 3^a * 2^s = 3^b * 2^t) : a = b ∧ s = t := by
  have hs : 2^s ∣ 2^t := by
    have hc : Nat.Coprime (2^s) (3^b) := Nat.Coprime.pow _ _ (by norm_num)
    apply hc.dvd_of_dvd_mul_left
    rw [← h]
    exact dvd_mul_left _ _
  have ht : 2^t ∣ 2^s := by
    have hc : Nat.Coprime (2^t) (3^a) := Nat.Coprime.pow _ _ (by norm_num)
    apply hc.dvd_of_dvd_mul_left
    rw [h]
    exact dvd_mul_left _ _
  have hst : s = t := by
    have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2:ℕ))).mp hs
    have hge := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2:ℕ))).mp ht
    omega
  subst t
  have hab : 3^a = 3^b := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2^s) h
  exact ⟨(Nat.pow_right_injective (by norm_num : 2 ≤ (3:ℕ))) hab, rfl⟩

/-- Equal affine endpoints on a shared binary cylinder cannot hide different
orbit clocks when their initial slopes differ only by powers of three. -/
theorem uniform_cylinder_clock_rigidity {D s t a b c d : ℕ}
    (hs : s ≤ D) (ht : t ≤ D)
    (h : ∀ Q : ℕ, 3^a * 2^(D-s) * Q + c = 3^b * 2^(D-t) * Q + d) :
    s = t ∧ a = b ∧ c = d := by
  have h0 := h 0
  have h1 := h 1
  simp only [mul_zero, zero_add] at h0
  simp only [mul_one] at h1
  have he : 3^a * 2^(D-s) = 3^b * 2^(D-t) := by omega
  obtain ⟨hab, hst⟩ := two_three_slope_injective he
  exact ⟨by omega, hab, h0⟩

/-- Orbit-level form: a uniform merge of two cylinders with power-of-three
initial slopes forces equal clocks and equal total power-of-three exponents. -/
theorem uniform_orbit_clock_rigidity {D s t a b r v : ℕ}
    (hs : s ≤ D) (ht : t ≤ D)
    (h : ∀ Q : ℕ,
      terras_iter s (r + 2^D*(3^a*Q)) = terras_iter t (v + 2^D*(3^b*Q))) :
    s = t ∧ oddSteps s r + a = oddSteps t v + b := by
  have he : ∀ Q : ℕ,
      3^(oddSteps s r+a)*2^(D-s)*Q + terras_iter s r =
      3^(oddSteps t v+b)*2^(D-t)*Q + terras_iter t v := by
    intro Q
    have hx := Cylinder.prefix_transport D r (3^a*Q) s hs
    have hy := Cylinder.prefix_transport D v (3^b*Q) t ht
    calc
      _ = terras_iter s (r+2^D*(3^a*Q)) := by rw [hx, pow_add]; ring
      _ = terras_iter t (v+2^D*(3^b*Q)) := h Q
      _ = _ := by rw [hy, pow_add]; ring
  obtain ⟨hst, hab, _⟩ := uniform_cylinder_clock_rigidity hs ht he
  exact ⟨hst, hab⟩

end Collatz
