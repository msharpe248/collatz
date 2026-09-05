import Collatz.OrbitSummability

/-! Every unbounded positive orbit has a tail with no coefficient
contraction. This is a reduction of nondivergence, not an exclusion. -/
namespace Collatz

/-- Every finite multiplicative coefficient is at least one. -/
def NeverContracts (N : ℕ) : Prop := ∀ t, 2^t ≤ 3^oddSteps t N

private theorem inverse_drift_add (s t N : ℕ) :
    (2:ℝ)^(s+t)/(3:ℝ)^oddSteps (s+t) N =
      ((2:ℝ)^s/(3:ℝ)^oddSteps s N) *
      ((2:ℝ)^t/(3:ℝ)^oddSteps t (terras_iter s N)) := by
  rw [oddSteps_add, pow_add, pow_add]
  field_simp

/-- A positive sequence converging to zero attains a global maximum. -/
private theorem inverse_drift_attains_max {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) :
    ∃ s, ∀ t, (2:ℝ)^t/(3:ℝ)^oddSteps t N ≤
      (2:ℝ)^s/(3:ℝ)^oddSteps s N := by
  classical
  let f := fun t => (2:ℝ)^t/(3:ℝ)^oddSteps t N
  have hz := unbounded_inverse_drift_tendsto_zero hN h
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (hz.eventually_lt_const (by norm_num : (0:ℝ) < 1))
  obtain ⟨s, hs, hmax⟩ := (Finset.range (K+1)).exists_max_image f
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  refine ⟨s, ?_⟩
  intro t
  by_cases ht : t < K+1
  · exact hmax t (Finset.mem_range.mpr ht)
  · have h0 := hmax 0 (Finset.mem_range.mpr (by omega))
    have hsmall := hK t (by omega)
    have hf0 : f 0 = 1 := by simp [f]
    rw [hf0] at h0
    exact hsmall.le.trans h0

/-- Every unbounded positive orbit contains a seed with no future
coefficient contraction. The index maximizes the original inverse drift. -/
theorem unbounded_has_noncontracting_tail {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) :
    ∃ s, NeverContracts (terras_iter s N) := by
  obtain ⟨s, hs⟩ := inverse_drift_attains_max hN h
  refine ⟨s, ?_⟩
  intro t
  have hh := hs (s+t)
  rw [inverse_drift_add] at hh
  have hp : (0:ℝ) < (2:ℝ)^s/(3:ℝ)^oddSteps s N := by positivity
  have hr : (2:ℝ)^t/(3:ℝ)^oddSteps t (terras_iter s N) ≤ 1 := by
    nlinarith only [hh, hp]
  have he := (div_le_one (by positivity : (0:ℝ) < (3:ℝ)^oddSteps t (terras_iter s N))).mp hr
  exact_mod_cast he

/-- A positive seed whose coefficient never contracts has an unbounded
natural orbit. Boundedness would bound its ideal correction and force escape. -/
theorem NeverContracts.unbounded {N : ℕ} (h : NeverContracts N) (hN : 0 < N) :
    ∀ B, ∃ t, B < terras_iter t N := by
  by_contra hh
  push_neg at hh
  obtain ⟨B, hB⟩ := hh
  have hs : Supercritical N := by
    refine ⟨(B:ℝ), ?_⟩
    rintro _ ⟨t, rfl⟩
    have he := terras_exact_form t N
    have hd : dcoef t N ≤ 3^oddSteps t N * B := by
      calc dcoef t N ≤ 2^t*terras_iter t N := by omega
           _ ≤ 3^oddSteps t N * B := Nat.mul_le_mul (h t) (hB t)
    unfold idealC
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (3:ℝ)^oddSteps t N)).mpr
    have hdR : (dcoef t N:ℝ) ≤ (3:ℝ)^oddSteps t N * B := by exact_mod_cast hd
    nlinarith only [hdR]
  obtain ⟨t, ht⟩ := (supercritical_iff_unbounded_orbit hN).mp hs B
  have := hB t
  omega

/-- Exact orbit-level equivalence: unboundedness is equivalent to having
a tail with no coefficient contraction. -/
theorem unbounded_iff_noncontracting_tail {N : ℕ} (hN : 0 < N) :
    (∀ B, ∃ t, B < terras_iter t N) ↔ ∃ s, NeverContracts (terras_iter s N) := by
  constructor
  · exact unbounded_has_noncontracting_tail hN
  · rintro ⟨s, hs⟩ B
    obtain ⟨t, ht⟩ := hs.unbounded (terras_iter_pos s N hN) B
    exact ⟨s+t, by simpa only [terras_iter_add] using ht⟩

/-- Such tails occur beyond every prescribed time on an unbounded orbit. -/
theorem unbounded_has_arbitrarily_late_noncontracting_tail {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) (K : ℕ) :
    ∃ s, K ≤ s ∧ NeverContracts (terras_iter s N) := by
  have hs := supercritical_shift (unbounded_orbit_supercritical hN h) K
  have hp := terras_iter_pos K N hN
  have hu := (supercritical_iff_unbounded_orbit hp).mp hs
  obtain ⟨t, ht⟩ := unbounded_has_noncontracting_tail hp hu
  exact ⟨K+t, by omega, by simpa only [terras_iter_add] using ht⟩

/-- Nondivergence is exactly the universal existence of a coefficient
contraction. Neither side is proved here, and neither excludes cycles. -/
theorem all_orbits_bounded_iff_all_contract :
    (∀ N, 0 < N → ∃ B, ∀ t, terras_iter t N ≤ B) ↔
    (∀ N, 0 < N → ∃ t, 3^oddSteps t N < 2^t) := by
  constructor
  · intro hb N hN
    by_contra hh
    have hn : NeverContracts N := by
      intro t
      have ht : ¬ 3^oddSteps t N < 2^t := fun ht => hh ⟨t, ht⟩
      omega
    obtain ⟨B, hB⟩ := hb N hN
    obtain ⟨t, ht⟩ := hn.unbounded hN B
    have := hB t
    omega
  · intro hc N hN
    by_contra hh
    push_neg at hh
    obtain ⟨s, hs⟩ := unbounded_has_noncontracting_tail hN hh
    obtain ⟨t, ht⟩ := hc (terras_iter s N) (terras_iter_pos s N hN)
    have := hs t
    omega

/-- A noncontracting seed must be odd. -/
theorem NeverContracts.odd {N : ℕ} (h : NeverContracts N) : N % 2 = 1 := by
  have hh := h 1
  by_contra hn
  norm_num [oddSteps, hn] at hh

/-- Odd predecessor steps preserve the absence of coefficient contraction. -/
theorem neverContracts_of_odd_step {N : ℕ} (ho : N % 2 = 1)
    (h : NeverContracts (terras N)) : NeverContracts N := by
  intro t
  cases t with
  | zero => simp
  | succ t =>
    rw [oddSteps_succ_odd t N ho, pow_succ, pow_succ]
    have hh := h t
    omega

/-- A noncontracting seed congruent to two modulo three has a smaller
positive noncontracting predecessor. This excludes that residue only for
a least such seed, not for arbitrary noncontracting orbits. -/
theorem NeverContracts.smaller_predecessor {N : ℕ} (h : NeverContracts N)
    (h3 : N % 3 = 2) : ∃ M, 0 < M ∧ M < N ∧ NeverContracts M := by
  have ho := h.odd
  let M := (2*N-1)/3
  have hM : 0 < M ∧ M < N ∧ M % 2 = 1 ∧ 3*M+1 = 2*N := by
    dsimp [M]
    omega
  have he : terras M = N := by
    have hh := two_mul_terras_odd M hM.2.2.1
    omega
  refine ⟨M, hM.1, hM.2.1, neverContracts_of_odd_step hM.2.2.1 ?_⟩
  simpa only [he] using h

/-- A finite noncontracting prefix followed by a noncontracting tail is
noncontracting at every time. This supports exact backward constructions. -/
theorem neverContracts_of_prefix {N k : ℕ}
    (hp : ∀ t ≤ k, 2^t ≤ 3^oddSteps t N)
    (ht : NeverContracts (terras_iter k N)) : NeverContracts N := by
  intro t
  by_cases hk : t ≤ k
  · exact hp t hk
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k ≤ t)
    rw [oddSteps_add, pow_add, pow_add]
    exact Nat.mul_le_mul (hp k (le_refl k)) (ht r)

/-- A least positive noncontracting seed cannot be two modulo three.
This leaves other residues and does not assert existence of such a seed. -/
theorem least_noncontracting_not_two_mod_three {N : ℕ} (h : NeverContracts N)
    (hmin : ∀ M, 0 < M → M < N → ¬ NeverContracts M) : N % 3 ≠ 2 := by
  intro h3
  obtain ⟨M, hM, hlt, hh⟩ := h.smaller_predecessor h3
  exact hmin M hM hlt hh

end Collatz
