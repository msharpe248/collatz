import Collatz.DominatingMerge

/-! Finite data certify an entire arithmetic progression of smaller
noncontracting merging predecessors. Coverage is a separate obligation. -/
namespace Collatz

structure MergeRule where
  seed : ℕ
  predecessor : ℕ
  forwardTime : ℕ
  inverseTime : ℕ
  seedQuotientStep : ℕ
  predecessorQuotientStep : ℕ
  deriving DecidableEq, Repr

namespace MergeRule

def original (r : MergeRule) (Q : ℕ) : ℕ :=
  r.seed + 2^r.forwardTime*(r.seedQuotientStep*Q)

def replacement (r : MergeRule) (Q : ℕ) : ℕ :=
  r.predecessor + 2^r.inverseTime*(r.predecessorQuotientStep*Q)

/-- All obligations are finite arithmetic, including actual parity paths. -/
def Valid (r : MergeRule) : Prop :=
  0 < r.predecessor ∧ r.predecessor < r.seed ∧
  terras_iter r.inverseTime r.predecessor = terras_iter r.forwardTime r.seed ∧
  (∀ i : Fin (r.inverseTime+1), 2^i.val ≤ 3^oddSteps i.val r.predecessor) ∧
  2^r.inverseTime*3^oddSteps r.forwardTime r.seed ≤
    2^r.forwardTime*3^oddSteps r.inverseTime r.predecessor ∧
  3^oddSteps r.forwardTime r.seed*r.seedQuotientStep =
    3^oddSteps r.inverseTime r.predecessor*r.predecessorQuotientStep ∧
  2^r.inverseTime*r.predecessorQuotientStep ≤
    2^r.forwardTime*r.seedQuotientStep

instance (r : MergeRule) : Decidable (Valid r) := by
  unfold Valid
  infer_instance

/-- One valid finite rule proves conditional descent in the noncontracting
set for every natural quotient, with no bound on the resulting seed. -/
theorem sound {r : MergeRule} (h : Valid r) (Q : ℕ)
    (hn : NeverContracts (r.original Q)) :
    0 < r.replacement Q ∧ r.replacement Q < r.original Q ∧
      NeverContracts (r.replacement Q) := by
  rcases h with ⟨hp, hlt, he, hpre, hc, hbal, hstep⟩
  have hmN : r.original Q ≡ r.seed [MOD 2^r.forwardTime] := by
    simp [original, Nat.ModEq]
  have hmX : r.replacement Q ≡ r.predecessor [MOD 2^r.inverseTime] := by
    simp [replacement, Nat.ModEq]
  have he' : terras_iter r.inverseTime (r.replacement Q) =
      terras_iter r.forwardTime (r.original Q) := by
    rw [replacement, original, Cylinder.transport, Cylinder.transport, he]
    have hb := congrArg (fun z => z*Q) hbal
    simpa only [Nat.mul_assoc] using congrArg
      (fun z => terras_iter r.forwardTime r.seed+z) hb.symm
  have hpre' : ∀ i ≤ r.inverseTime, 2^i ≤ 3^oddSteps i (r.replacement Q) := by
    intro i hi
    rw [oddSteps_modEq i (Nat.ModEq.of_dvd (Nat.pow_dvd_pow 2 hi) hmX)]
    exact hpre ⟨i, by omega⟩
  have hc' : 2^r.inverseTime*3^oddSteps r.forwardTime (r.original Q) ≤
      2^r.forwardTime*3^oddSteps r.inverseTime (r.replacement Q) := by
    rw [oddSteps_modEq _ hmN, oddSteps_modEq _ hmX]
    exact hc
  have hs := Nat.mul_le_mul_right Q hstep
  simp only [Nat.mul_assoc] at hs
  refine ⟨?_, ?_, neverContracts_of_dominating_merge hn hpre' he' hc'⟩
  · dsimp [replacement]
    omega
  · dsimp [replacement, original]
    omega

end MergeRule
end Collatz
