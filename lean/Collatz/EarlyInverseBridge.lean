import Collatz.AffineBridge

/-! An inverse bridge usable before assuming target cycle entry. -/
namespace Collatz

/-- One odd predecessor exposes a smaller transfer parameter on u=3w+2. -/
theorem early_inverse_predecessor (w : ℕ) :
    2*w+1 < 3*w+2 ∧ terras (3*(2*w+1)+2) = 3*(3*w+2)+2 ∧
    terras (27*(2*w+1)+20) = 81*w+71 := by
  have h1 := two_mul_terras_odd (3*(2*w+1)+2) (by omega)
  have h2 := two_mul_terras_odd (27*(2*w+1)+20) (by omega)
  omega

/-- Uniform early bridge geometry; the larger target is never assumed to converge. -/
theorem early_inverse_bridge_59 (Q : ℕ) :
    39+128*Q < 59+192*Q ∧
    terras (3*(39+128*Q)+2) = 3*(59+192*Q)+2 ∧
    terras_iter 7 (27*(39+128*Q)+20) =
      terras_iter 6 (27*(59+192*Q)+20) := by
  have hx := Cylinder.transport 7 1073 (27*Q)
  have hy := Cylinder.transport 6 1613 (81*Q)
  simp only [show terras_iter 7 1073 = 227 from rfl,
    show oddSteps 7 1073 = 3 from rfl] at hx
  simp only [show terras_iter 6 1613 = 227 from rfl,
    show oddSteps 6 1613 = 2 from rfl] at hy
  have ex : 27*(39+128*Q)+20 = 1073+2^7*(27*Q) := by ring
  have ey : 27*(59+192*Q)+20 = 1613+2^6*(81*Q) := by ring
  refine ⟨by omega, ?_, ?_⟩
  · have hs := two_mul_terras_odd (3*(39+128*Q)+2) (by omega)
    omega
  · rw [ex, ey, hx, hy]; ring

/-- A strictly smaller recursive transfer proves this progression, without
requiring convergence of the base target to construct the bridge. -/
theorem AffineTransfer.early_inverse_59 (Q : ℕ)
    (hrec : AffineTransfer (39+128*Q)) : AffineTransfer (59+192*Q) := by
  intro hu
  obtain ⟨_, hx, hy⟩ := early_inverse_bridge_59 Q
  rw [← hx] at hu
  have hv := (ReachesOne.step_iff (3*(39+128*Q)+2)).mp hu
  have hw := (ReachesOne.shift_iff (27*(39+128*Q)+20) 7).mpr (hrec hv)
  rw [hy] at hw
  exact (ReachesOne.shift_iff (27*(59+192*Q)+20) 6).mp hw

end Collatz
