import Collatz.AffineBridge

/-! A signed orbit excursion lowers the cycle charge by seven. The smaller
transfer premise remains explicit; no global coverage is asserted. -/
set_option maxRecDepth 2048

namespace Collatz

theorem inverse_cycle_geometry :
    terras_iter 65 47 = 2 ∧ oddSteps 65 47 = 38 ∧
    terras_iter 38 425 = 2 ∧ oddSteps 38 425 = 19 := by decide

/-- Exact lifts for the inverse 47 excursion and subsequent transfer bridge. -/
theorem inverse_cycle_transport (Q : ℕ) :
    terras_iter 65 (3*(15+2^65*Q)+2) = 2+3^39*Q ∧
    terras_iter 38 (27*(15+2^65*Q)+20) = 2+3^22*2^27*Q := by
  have hx := Cylinder.transport 65 47 (3*Q)
  have hy := Cylinder.transport 38 425 (27*2^27*Q)
  simp only [show terras_iter 65 47 = 2 from rfl,
    show oddSteps 65 47 = 38 from rfl] at hx
  simp only [show terras_iter 38 425 = 2 from rfl,
    show oddSteps 38 425 = 19 from rfl] at hy
  have ex : 3*(15+2^65*Q)+2 = 47+2^65*(3*Q) := by ring
  have ey : 27*(15+2^65*Q)+20 = 425+2^38*(27*2^27*Q) := by ring
  constructor
  · rw [ex, hx]; ring
  · rw [ey, hy]; ring

/-- Convergence transfers through a backward ordinary segment, a recursive
bridge, and a forward segment. Strict recursive decrease is a caller obligation. -/
theorem inverse_cycle_transfer (Q : ℕ) (hrec : AffineTransfer (15+2^65*Q)) :
    ReachesOne (2+3^39*Q) → ReachesOne (2+3^22*2^27*Q) := by
  intro hs
  obtain ⟨hx, hy⟩ := inverse_cycle_transport Q
  rw [← hx] at hs
  have hv := (ReachesOne.shift_iff (3*(15+2^65*Q)+2) 65).mp hs
  have hw := (ReachesOne.shift_iff (27*(15+2^65*Q)+20) 38).mpr (hrec hv)
  rwa [hy] at hw

end Collatz
