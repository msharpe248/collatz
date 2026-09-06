import Collatz.EarlyInverseBridge
set_option maxRecDepth 2048

/-! Two smaller transfer premises combine after an early inverse segment. -/
namespace Collatz

theorem two_early_bridge_geometry (Q : ℕ) :
    13+8*2^40*Q < 15+9*2^40*Q ∧
    2+3^16*2^15*Q < 15+9*2^40*Q ∧
    terras_iter 3 (3*(13+8*2^40*Q)+2) = 3*(15+9*2^40*Q)+2 ∧
    terras_iter 28 (27*(13+8*2^40*Q)+20) = 3*(2+3^16*2^15*Q)+2 ∧
    terras_iter 15 (27*(2+3^16*2^15*Q)+20) =
      terras_iter 40 (27*(15+9*2^40*Q)+20) := by
  have h1 := Cylinder.transport 3 41 (3*2^40*Q)
  have h2 := Cylinder.transport 28 371 (27*2^15*Q)
  have h3 := Cylinder.transport 15 74 (3^19*Q)
  have h4 := Cylinder.transport 40 425 (243*Q)
  simp only [show terras_iter 3 41 = 47 from rfl,
    show oddSteps 3 41 = 2 from rfl] at h1
  simp only [show terras_iter 28 371 = 8 from rfl,
    show oddSteps 28 371 = 14 from rfl] at h2
  simp only [show terras_iter 15 74 = 2 from rfl,
    show oddSteps 15 74 = 6 from rfl] at h3
  simp only [show terras_iter 40 425 = 2 from rfl,
    show oddSteps 40 425 = 20 from rfl] at h4
  have e1 : 3*(13+8*2^40*Q)+2 = 41+2^3*(3*2^40*Q) := by ring
  have e2 : 27*(13+8*2^40*Q)+20 = 371+2^28*(27*2^15*Q) := by ring
  have e3 : 27*(2+3^16*2^15*Q)+20 = 74+2^15*(3^19*Q) := by ring
  have e4 : 27*(15+9*2^40*Q)+20 = 425+2^40*(243*Q) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num; omega
  · norm_num; omega
  · rw [e1,h1]; ring
  · rw [e2,h2]; ring
  · rw [e3,e4,h3,h4]; ring

/-- Both recursive parameters decrease uniformly. Neither target-convergence
premise is assumed; the two smaller transfer implications remain explicit. -/
theorem AffineTransfer.two_early_15 (Q : ℕ)
    (hA : AffineTransfer (13+8*2^40*Q))
    (hB : AffineTransfer (2+3^16*2^15*Q)) :
    AffineTransfer (15+9*2^40*Q) := by
  intro hu
  obtain ⟨_,_,h1,h2,h3⟩ := two_early_bridge_geometry Q
  rw [← h1] at hu
  have hv := (ReachesOne.shift_iff (3*(13+8*2^40*Q)+2) 3).mp hu
  have hw := (ReachesOne.shift_iff (27*(13+8*2^40*Q)+20) 28).mpr (hA hv)
  rw [h2] at hw
  have hz := (ReachesOne.shift_iff (27*(2+3^16*2^15*Q)+20) 15).mpr (hB hw)
  rw [h3] at hz
  exact (ReachesOne.shift_iff (27*(15+9*2^40*Q)+20) 40).mp hz

end Collatz
