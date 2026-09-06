import Collatz.DominatingMerge

/-! Quantitative transport through shifted merging paths. The natural pair
`a,b` represents the lower coefficient bound a/b when b is positive.
No applicability of a merge or existence of a noncontracting seed is assumed. -/
namespace Collatz

/-- Every orbit coefficient is at least a/b (for positive b). -/
def CoefficientBound (a b n : ℕ) : Prop :=
  ∀ i, a * 2^i ≤ b * 3^oddSteps i n

/-- Shifting a fully noncontracting orbit retains an explicit coefficient
bound, even though the shifted seed need not be fully noncontracting. -/
theorem NeverContracts.shift_bound {n : ℕ} (hn : NeverContracts n) (k : ℕ) :
    CoefficientBound (2^k) (3^oddSteps k n) (terras_iter k n) := by
  intro i
  have h := hn (k+i)
  simpa only [oddSteps_add, pow_add] using h

/-- A dominating replacement prefix transports a rational coefficient
bound. For deficits D=b/a and D'=b'/a', the last hypothesis says
D' >= D/rho, where rho is the ratio of the two merging coefficients.
The prefix condition also requires D' >= 1. -/
theorem CoefficientBound.merge {a b a' b' n x s t : ℕ}
    (hn : CoefficientBound a b n) (hb : 0 < b)
    (hp : ∀ i ≤ s, 2^i ≤ 3^oddSteps i x)
    (hab : a' ≤ b')
    (he : terras_iter s x = terras_iter t n)
    (hc : a' * b * 2^s * 3^oddSteps t n ≤
      b' * a * 2^t * 3^oddSteps s x) : CoefficientBound a' b' x := by
  intro i
  by_cases hi : i ≤ s
  · exact Nat.mul_le_mul hab (hp i hi)
  · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (show s ≤ i by omega)
    have hh := hn (t+v)
    rw [oddSteps_add, pow_add, pow_add] at hh
    rw [oddSteps_add, pow_add, pow_add, he]
    apply Nat.le_of_mul_le_mul_left (c := b * 3^oddSteps t n) ?_ (by positivity)
    calc
      b * 3^oddSteps t n * (a' * (2^s * 2^v)) =
          (a' * b * 2^s * 3^oddSteps t n) * 2^v := by ring
      _ ≤ (b' * a * 2^t * 3^oddSteps s x) * 2^v :=
        Nat.mul_le_mul_right _ hc
      _ = (b' * 3^oddSteps s x) * (a * (2^t * 2^v)) := by ring
      _ ≤ (b' * 3^oddSteps s x) *
          (b * (3^oddSteps t n * 3^oddSteps v (terras_iter t n))) :=
        Nat.mul_le_mul_left _ hh
      _ = b * 3^oddSteps t n *
          (b' * (3^oddSteps s x * 3^oddSteps v (terras_iter t n))) := by ring

/-- Restoring a bound of at least one restores full noncontraction. -/
theorem CoefficientBound.neverContracts {a b n : ℕ}
    (hn : CoefficientBound a b n) (ha : 0 < a) (hba : b ≤ a) :
    NeverContracts n := by
  intro i
  apply Nat.le_of_mul_le_mul_left (c := a) ?_ ha
  exact (hn i).trans (Nat.mul_le_mul_right _ hba)

/-- Cylinder transport retains the finite hypotheses of the quantitative
merge theorem. This permits chains with different quotient scales. -/
theorem CoefficientBound.merge_cylinder {a b a' b' n x s t q r : ℕ}
    (hn : CoefficientBound a b (n + 2^t*q)) (hb : 0 < b)
    (hp : ∀ i ≤ s, 2^i ≤ 3^oddSteps i x) (hab : a' ≤ b')
    (he : terras_iter s x = terras_iter t n)
    (hbal : 3^oddSteps t n*q = 3^oddSteps s x*r)
    (hc : a' * b * 2^s * 3^oddSteps t n ≤
      b' * a * 2^t * 3^oddSteps s x) :
    CoefficientBound a' b' (x + 2^s*r) := by
  have hmn : n + 2^t*q ≡ n [MOD 2^t] := by simp [Nat.ModEq]
  have hmx : x + 2^s*r ≡ x [MOD 2^s] := by simp [Nat.ModEq]
  apply hn.merge hb (s := s) (t := t) ?_ hab ?_ ?_
  · intro i hi
    rw [oddSteps_modEq i (Nat.ModEq.of_dvd (Nat.pow_dvd_pow 2 hi) hmx)]
    exact hp i hi
  · rw [Cylinder.transport, Cylinder.transport, he, hbal]
  · simpa only [oddSteps_modEq t hmn, oddSteps_modEq s hmx] using hc

set_option maxRecDepth 100000 in
/-- A three-rule chain restores noncontraction after a 23-step shift,
for an entire arithmetic progression. It excludes this progression from
being the least positive noncontracting seed; it is not global coverage. -/
theorem NeverContracts.smaller_merge_chain_447 {Q : ℕ}
    (hn : NeverContracts (447 + 549755813888*Q)) :
    0 < 307 + 376572715308*Q ∧
    307 + 376572715308*Q < 447 + 549755813888*Q ∧
    NeverContracts (307 + 376572715308*Q) := by
  have hm : 447 + 549755813888*Q ≡ 447 [MOD 2^23] := by
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  have hc := oddSteps_modEq 23 hm
  have he := Cylinder.transport 23 447 (65536*Q)
  have harg : 447 + 2^23*(65536*Q) = 447 + 549755813888*Q := by ring
  rw [harg] at he
  norm_num only [show terras_iter 23 447 = 767 from rfl,
    show oddSteps 23 447 = 15 from rfl, Nat.reducePow] at he hc
  have h0 := hn.shift_bound 23
  rw [hc, he] at h0
  norm_num only [Nat.reducePow] at h0
  have h0' : CoefficientBound 8388608 14348907 (767 + 940369969152*Q) := by
    simpa only [Nat.reducePow, ← Nat.mul_assoc, Nat.reduceMul] using h0
  have p511 : ∀ i ≤ 1, 2^i ≤ 3^oddSteps i 511 := by
    intro i hi
    interval_cases i <;> decide
  have p461 : ∀ i ≤ 1, 2^i ≤ 3^oddSteps i 461 := by
    intro i hi
    interval_cases i <;> decide
  have p307 : ∀ i ≤ 1, 2^i ≤ 3^oddSteps i 307 := by
    intro i hi
    interval_cases i <;> decide
  have h1 : CoefficientBound 4194304 4782969 (511 + 626913312768*Q) := by
    have h0'' : CoefficientBound 8388608 14348907
        (767 + 2^0*(940369969152*Q)) := by simpa using h0'
    have hh := h0''.merge_cylinder (x := 511) (s := 1)
      (r := 313456656384*Q) (a' := 4194304) (b' := 4782969)
      (by decide) p511 (by decide) (by rfl) (by
        norm_num only [show oddSteps 0 767 = 0 from rfl,
          show oddSteps 1 511 = 1 from rfl, Nat.reducePow]
        ring) (by decide)
    simpa only [Nat.reducePow, ← Nat.mul_assoc, Nat.reduceMul] using hh
  have h2 : CoefficientBound 274877906944 282429536481
      (461 + 564859072962*Q) := by
    have h1' : CoefficientBound 4194304 4782969
        (511 + 2^17*(4782969*Q)) := by
      simpa only [Nat.reducePow, ← Nat.mul_assoc, Nat.reduceMul] using h1
    have hh := h1'.merge_cylinder (x := 461) (s := 1)
      (r := 282429536481*Q) (a' := 274877906944) (b' := 282429536481)
      (by decide) p461 (by decide) (by rfl) (by
        norm_num only [show oddSteps 17 511 = 11 from rfl,
          show oddSteps 1 461 = 1 from rfl, Nat.reducePow]
        ring) (by decide)
    simpa only [Nat.reducePow, ← Nat.mul_assoc, Nat.reduceMul] using hh
  have h3 : CoefficientBound 1 1 (307 + 376572715308*Q) := by
    have h2' : CoefficientBound 274877906944 282429536481
        (461 + 2^0*(564859072962*Q)) := by simpa using h2
    have hh := h2'.merge_cylinder (x := 307) (s := 1)
      (r := 188286357654*Q) (a' := 1) (b' := 1)
      (by decide) p307 (by decide) (by rfl) (by
        norm_num only [show oddSteps 0 461 = 0 from rfl,
          show oddSteps 1 307 = 1 from rfl, Nat.reducePow]
        ring) (by decide)
    simpa only [Nat.reducePow, ← Nat.mul_assoc, Nat.reduceMul] using hh
  exact ⟨by omega, by omega, h3.neverContracts (by decide) (by decide)⟩

end Collatz
