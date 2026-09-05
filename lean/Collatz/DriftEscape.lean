import Collatz.CorrectionGrowth

/-! A quantitative escape condition for the multiplicative drift.
This excludes uniformly bounded critical drift, not all unbounded orbits. -/
namespace Collatz

/-- Among T+1 distinct positive integers, at least one is at least T+1. -/
theorem prefix_has_large_value {f : ℕ → ℕ} (hp : ∀ t, 0 < f t)
    (hi : Function.Injective f) (T : ℕ) : ∃ t ≤ T, T+1 ≤ f t := by
  by_contra hn
  push_neg at hn
  have hs : (Finset.range (T+1)).image f ⊆ Finset.Icc 1 T := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr ⟨hp t, by have := hn t (by have := Finset.mem_range.mp ht; omega); omega⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hi, Finset.card_range] at hc
  simp at hc

/-- On every prefix of an unbounded orbit, some multiplicative drift has
sixth power at least (T+1)^5/N^6, expressed entirely with integers. -/
theorem unbounded_prefix_drift_escape {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    ∃ t ≤ T, (2^t)^6 * (T+1)^5 ≤ (3^oddSteps t N * N)^6 := by
  obtain ⟨t, ht, hv⟩ := prefix_has_large_value (fun t => terras_iter_pos t N hN)
    (unbounded_orbit_injective h) T
  refine ⟨t, ht, ?_⟩
  have hb := unbounded_sixth_drift_bound hN h t
  have hj : oddSteps t N + 1 ≤ T+1 := by
    have := oddSteps_le t N
    omega
  have hleft : (2^t * (T+1))^6 ≤ (2^t * terras_iter t N)^6 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hv) 6
  have hright := Nat.mul_le_mul_left ((3^oddSteps t N * N)^6) hj
  have hall := (hleft.trans hb).trans hright
  rw [mul_pow] at hall
  have hp : 0 < T+1 := by omega
  apply Nat.le_of_mul_le_mul_right (c := T+1) _ hp
  convert hall using 1; ring

/-- Every polynomial drift envelope with rational exponent below 5/6
forces boundedness. The exponent is b/(6*a), with b < 5*a. -/
theorem finite_drift_certificate_bounds_orbit {N C a b T : ℕ} (hN : 0 < N)
    (hab : b < 5*a) (hT : C*(N^6)^a < T+1)
    (hc : ∀ t, t ≤ T → ((3^oddSteps t N)^6)^a ≤
      C * (t+1)^b * ((2^t)^6)^a) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  by_contra hn
  push_neg at hn
  obtain ⟨t, ht, he⟩ := unbounded_prefix_drift_escape hN hn T
  have he' := Nat.pow_le_pow_left he a
  rw [mul_pow, mul_pow, mul_pow] at he'
  have hc' := Nat.mul_le_mul_right ((N^6)^a) (hc t ht)
  have hall := he'.trans hc'
  have hp : 0 < ((2^t)^6)^a := by positivity
  have hsmall : ((T+1)^5)^a ≤ C*(t+1)^b*(N^6)^a := by
    apply Nat.le_of_mul_le_mul_left (c := ((2^t)^6)^a) _ hp
    convert hall using 1; ring
  have htPow : (t+1)^b ≤ (T+1)^b := Nat.pow_le_pow_left (by omega) b
  have hsmall' : (T+1)^(5*a) ≤ C*(N^6)^a*(T+1)^b := by
    rw [← pow_mul] at hsmall
    nlinarith [Nat.mul_le_mul_left (C*(N^6)^a) htPow]
  have hbig : (T+1)^(b+1) ≤ (T+1)^(5*a) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hcanc : T+1 ≤ C*(N^6)^a := by
    apply Nat.le_of_mul_le_mul_right (c := (T+1)^b) _ (by positivity)
    have := hbig.trans hsmall'
    rw [pow_succ] at this
    nlinarith
  exact (not_le_of_gt hT) hcanc

/-- A global polynomial envelope below exponent 5/6 supplies the finite
certificate. No such envelope is asserted for arbitrary Collatz orbits. -/
theorem bounded_orbit_of_subcritical_polynomial_drift {N C a b : ℕ} (hN : 0 < N)
    (hab : b < 5*a)
    (hc : ∀ t, ((3^oddSteps t N)^6)^a ≤
      C * (t+1)^b * ((2^t)^6)^a) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  apply finite_drift_certificate_bounds_orbit (C := C) (T := C*(N^6)^a) hN hab (by omega)
  exact fun t _ => hc t

/-- A uniform bound on the sixth power of the drift forces a bounded orbit. -/
theorem bounded_orbit_of_bounded_drift {N C : ℕ} (hN : 0 < N)
    (hc : ∀ t, (3^oddSteps t N)^6 ≤ C * (2^t)^6) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  apply bounded_orbit_of_subcritical_polynomial_drift (a := 1) (b := 0) hN (by omega)
  simpa using hc

end Collatz
