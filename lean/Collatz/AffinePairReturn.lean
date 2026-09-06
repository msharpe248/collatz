import Collatz.AffineConvergence

/-! Direct merging and contracting returns for the affine transfer problem.
These certificates apply on entire progressions, but no coverage theorem
or proof of the universal transfer is asserted. -/
namespace Collatz

def AffineTransfer (u : ℕ) : Prop := ReachesOne (3*u+2) → ReachesOne (27*u+20)

/-- Both affine partners transport exactly on a binary parameter cylinder. -/
theorem affine_pair_transport (t u Q : ℕ) :
    terras_iter t (3*(u+2^t*Q)+2) = terras_iter t (3*u+2) +
      3^(oddSteps t (3*u+2)+1)*Q ∧
    terras_iter t (27*(u+2^t*Q)+20) = terras_iter t (27*u+20) +
      3^(oddSteps t (27*u+20)+3)*Q := by
  constructor
  · have h := Cylinder.transport t (3*u+2) (3*Q)
    have he : 3*u+2+2^t*(3*Q) = 3*(u+2^t*Q)+2 := by ring
    rw [he] at h
    rw [h, pow_succ]
    ring
  · have h := Cylinder.transport t (27*u+20) (27*Q)
    have he : 27*u+20+2^t*(27*Q) = 27*(u+2^t*Q)+20 := by ring
    rw [he] at h
    rw [h, pow_add]
    norm_num
    ring

/-- Transport transfer through an actual return. Strong induction additionally
requires v<u. Transfer at the returned parameter is an explicit premise. -/
theorem AffineTransfer.of_return {u v t : ℕ}
    (hx : terras_iter t (3*u+2) = 3*v+2)
    (hy : terras_iter t (27*u+20) = 27*v+20)
    (hrec : AffineTransfer v) : AffineTransfer u := by
  intro hu
  have hv := (ReachesOne.shift_iff (3*u+2) t).mpr hu
  rw [hx] at hv
  have hw := hrec hv
  rw [← hy] at hw
  exact (ReachesOne.shift_iff (27*u+20) t).mp hw

/-- The first direct cylinder found by the paired search. -/
theorem AffineTransfer.merge_36 (Q : ℕ) : AffineTransfer (36+64*Q) := by
  obtain ⟨hx, hy⟩ := affine_pair_transport 6 36 Q
  norm_num only [show terras_iter 6 (3*36+2) = 47 from rfl,
    show terras_iter 6 (27*36+20) = 47 from rfl,
    show oddSteps 6 (3*36+2) = 3 from rfl,
    show oddSteps 6 (27*36+20) = 1 from rfl, Nat.reduceAdd, Nat.reducePow] at hx hy
  intro hu
  have hh := (ReachesOne.shift_iff (3*(36+64*Q)+2) 6).mpr hu
  rw [hx, ← hy] at hh
  exact (ReachesOne.shift_iff (27*(36+64*Q)+20) 6).mp hh

/-- A twelve-step return of the affine pair to a strictly smaller
parameter, uniformly over every natural quotient. -/
theorem affine_pair_return_2308 (Q : ℕ) :
    45+81*Q < 2308+4096*Q ∧
    terras_iter 12 (3*(2308+4096*Q)+2) = 3*(45+81*Q)+2 ∧
    terras_iter 12 (27*(2308+4096*Q)+20) = 27*(45+81*Q)+20 := by
  obtain ⟨hx, hy⟩ := affine_pair_transport 12 2308 Q
  norm_num only [show terras_iter 12 (3*2308+2) = 137 from rfl,
    show terras_iter 12 (27*2308+20) = 1235 from rfl,
    show oddSteps 12 (3*2308+2) = 4 from rfl,
    show oddSteps 12 (27*2308+20) = 4 from rfl, Nat.reduceAdd, Nat.reducePow] at hx hy
  refine ⟨by omega, ?_, ?_⟩
  · rw [hx]; ring
  · rw [hy]; ring

/-- A conditional induction step, not an unconditional transfer theorem
for this progression. -/
theorem AffineTransfer.return_2308 (Q : ℕ) (hrec : AffineTransfer (45+81*Q)) :
    AffineTransfer (2308+4096*Q) := by
  obtain ⟨_, hx, hy⟩ := affine_pair_return_2308 Q
  exact of_return hx hy hrec

private def zeroPairStates : List (ℕ × ℕ) :=
  [(2,20), (1,10), (2,5), (1,8), (2,4), (1,2), (2,1)]

private theorem zeroPairChecked : zeroPairStates.all (fun p => decide
    (p.1 ≠ p.2 ∧ (terras p.1, terras p.2) ∈ zeroPairStates)) = true := by decide

/-- Both partners for parameter zero reach one, but they never coalesce
at equal times. This limits certificates based solely on aligned merging. -/
theorem zero_pair_never_coalesces :
    ReachesOne 2 ∧ ReachesOne 20 ∧ ∀ t, terras_iter t 2 ≠ terras_iter t 20 := by
  refine ⟨⟨1, rfl⟩, ⟨6, rfl⟩, ?_⟩
  have hstates : ∀ t, (terras_iter t 2, terras_iter t 20) ∈ zeroPairStates := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      have hh := of_decide_eq_true ((List.all_eq_true.mp zeroPairChecked) _ ih)
      simpa only [terras_iter_succ'] using hh.2
  intro t
  exact (of_decide_eq_true ((List.all_eq_true.mp zeroPairChecked) _ (hstates t))).1

end Collatz
