import Collatz.AffinePairReturn

/-! Smaller transfer instances can supply auxiliary convergent orbits.
The endpoint clocks need not form a simultaneous return of the pair. -/
namespace Collatz

/-- Soundness of a single auxiliary transfer bridge. For strong induction,
strict decrease of v must additionally be established by the caller. -/
theorem AffineTransfer.of_bridge {u v s t r : ℕ}
    (hx : terras_iter s (3*u+2) = 3*v+2)
    (hy : terras_iter t (27*u+20) = terras_iter r (27*v+20))
    (hrec : AffineTransfer v) : AffineTransfer u := by
  intro hu
  have hv := (ReachesOne.shift_iff (3*u+2) s).mpr hu
  rw [hx] at hv
  have hw := (ReachesOne.shift_iff (27*v+20) r).mpr (hrec hv)
  rw [← hy] at hw
  exact (ReachesOne.shift_iff (27*u+20) t).mp hw

/-- An auxiliary bridge on an entire parameter progression. -/
theorem affine_bridge_28 (Q : ℕ) :
    21+3072*Q < 28+4096*Q ∧
    terras_iter 2 (3*(28+4096*Q)+2) = 3*(21+3072*Q)+2 ∧
    terras_iter 12 (27*(28+4096*Q)+20) =
      terras_iter 10 (27*(21+3072*Q)+20) := by
  have hx := Cylinder.transport 2 86 (3072*Q)
  have hy := Cylinder.transport 12 776 (27*Q)
  have hz := Cylinder.transport 10 587 (81*Q)
  norm_num only [show terras_iter 2 86 = 65 from rfl,
    show oddSteps 2 86 = 1 from rfl, Nat.reducePow] at hx
  norm_num only [show terras_iter 12 776 = 47 from rfl,
    show oddSteps 12 776 = 5 from rfl, Nat.reducePow] at hy
  norm_num only [show terras_iter 10 587 = 47 from rfl,
    show oddSteps 10 587 = 4 from rfl, Nat.reducePow] at hz
  have ex : 3*(28+4096*Q)+2 = 86+4*(3072*Q) := by ring
  have ey : 27*(28+4096*Q)+20 = 776+4096*(27*Q) := by ring
  have ez : 27*(21+3072*Q)+20 = 587+1024*(81*Q) := by ring
  refine ⟨by omega, ?_, ?_⟩
  · rw [ex, hx]; ring
  · rw [ey, ez, hy, hz]; ring

/-- The smaller transfer premise is explicit; this is not global coverage. -/
theorem AffineTransfer.bridge_28 (Q : ℕ)
    (hrec : AffineTransfer (21+3072*Q)) : AffineTransfer (28+4096*Q) := by
  obtain ⟨_, hx, hy⟩ := affine_bridge_28 Q
  exact of_bridge hx hy hrec

end Collatz
