import Collatz.ResidueCoverage
import Collatz.NoncontractingTail

/-! Exact coverage by noncontracting sampled returns. This is a reduction
of nondivergence, not a proof of it or of convergence. -/
namespace Collatz

/-- Coefficients do not contract at any visit to two modulo nine. -/
def SampledNeverContracts (n : ℕ) : Prop :=
  n % 9 = 2 ∧ ∀ t, terras_iter t n % 9 = 2 → 2^t ≤ 3^oddSteps t n

/-- Between sampled visits, at most six even steps give a uniform deficit
factor of sixty-four. This is weaker than `NeverContracts`. -/
theorem SampledNeverContracts.deficit {n : ℕ} (h : SampledNeverContracts n) (t : ℕ) :
    2^t ≤ 64 * 3^oddSteps t n := by
  let P := fun k => terras_iter k n % 9 = 2
  let k := Nat.findGreatest P t
  have hk : k ≤ t := Nat.findGreatest_le t
  have hp : P k := Nat.findGreatest_spec (Nat.zero_le t) h.1
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk
  have ha : ∀ s, 0 < s → s < r → terras_iter s (terras_iter k n) % 9 ≠ 2 := by
    intro s hs hsr
    have hh := Nat.findGreatest_is_greatest (P := P) (n := t)
      (show k < k+s by omega) (show k+s ≤ t by omega)
    simpa only [P, terras_iter_add] using hh
  have he := even_steps_between_two_mod_nine hp ha
  have hb : 2^r ≤ 64 * 3^oddSteps r (terras_iter k n) := by
    have hpow := Nat.pow_le_pow_right (n := 2) (by omega) he
    have hbase : 2^oddSteps r (terras_iter k n) ≤ 3^oddSteps r (terras_iter k n) :=
      Nat.pow_le_pow_left (by omega) _
    rw [pow_add] at hpow
    norm_num at hpow
    omega
  have hstart := h.2 k hp
  rw [hr, pow_add, oddSteps_add, pow_add]
  nlinarith [Nat.mul_le_mul hstart hb]

/-- Failure of sampled contraction forces escape for a positive seed. -/
theorem SampledNeverContracts.unbounded {n : ℕ} (h : SampledNeverContracts n)
    (hn : 0 < n) : ∀ B, ∃ t, B < terras_iter t n := by
  by_contra hh
  push_neg at hh
  obtain ⟨B, hB⟩ := hh
  have hs : Supercritical n := by
    refine ⟨(64*B : ℝ), ?_⟩
    rintro _ ⟨t, rfl⟩
    have he := terras_exact_form t n
    have hb := Nat.mul_le_mul (h.deficit t) (hB t)
    have hd : dcoef t n ≤ (64*B) * 3^oddSteps t n := by
      calc dcoef t n ≤ 2^t * terras_iter t n := by omega
           _ ≤ 64 * 3^oddSteps t n * B := hb
           _ = (64*B) * 3^oddSteps t n := by ring
    unfold idealC
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (3:ℝ)^oddSteps t n)).mpr
    exact_mod_cast hd
  obtain ⟨t, ht⟩ := (supercritical_iff_unbounded_orbit hn).mp hs B
  have := hB t
  omega

private theorem sampled_maximum {n : ℕ} (hn : 0 < n) (hr : n % 9 = 2)
    (hu : ∀ B, ∃ t, B < terras_iter t n) :
    ∃ s, terras_iter s n % 9 = 2 ∧
      ∀ t, terras_iter t n % 9 = 2 →
        (2:ℝ)^t/(3:ℝ)^oddSteps t n ≤ (2:ℝ)^s/(3:ℝ)^oddSteps s n := by
  classical
  let f := fun t => (2:ℝ)^t/(3:ℝ)^oddSteps t n
  have hz := unbounded_inverse_drift_tendsto_zero hn hu
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (hz.eventually_lt_const (by norm_num : (0:ℝ) < 1))
  let S := (Finset.range (K+1)).filter (fun t => terras_iter t n % 9 = 2)
  have h0 : 0 ∈ S := by simp [S, hr, terras_iter]
  obtain ⟨s, hs, hm⟩ := S.exists_max_image f ⟨0, h0⟩
  refine ⟨s, (Finset.mem_filter.mp hs).2, ?_⟩
  intro t ht
  by_cases hlt : t < K+1
  · exact hm t (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ht⟩)
  · have hb := hm 0 h0
    have hh := hK t (by omega)
    have hf : f 0 = 1 := by simp [f]
    rw [hf] at hb
    exact hh.le.trans hb

/-- Every unbounded positive orbit has a residue-two tail with no sampled
coefficient contraction. This does not assert full noncontraction. -/
theorem unbounded_has_sampled_noncontracting_tail {n : ℕ} (hn : 0 < n)
    (hu : ∀ B, ∃ t, B < terras_iter t n) :
    ∃ s, SampledNeverContracts (terras_iter s n) := by
  obtain ⟨q, hq⟩ := exists_two_mod_nine n hn
  have hp := terras_iter_pos q n hn
  have hsu := (supercritical_iff_unbounded_orbit hp).mp
    (supercritical_shift (unbounded_orbit_supercritical hn hu) q)
  obtain ⟨s, hs, hm⟩ := sampled_maximum hp hq hsu
  have hsample : SampledNeverContracts (terras_iter s (terras_iter q n)) := by
    refine ⟨hs, ?_⟩
    intro t ht
    have hv : terras_iter (s+t) (terras_iter q n) % 9 = 2 := by
      simpa only [terras_iter_add, Nat.add_assoc] using ht
    have hb := hm (s+t) hv
    rw [oddSteps_add, pow_add, pow_add] at hb
    have he :
        (2:ℝ)^s * 2^t / ((3:ℝ)^oddSteps s (terras_iter q n) *
          3^oddSteps t (terras_iter s (terras_iter q n))) =
        ((2:ℝ)^s / 3^oddSteps s (terras_iter q n)) *
          ((2:ℝ)^t / 3^oddSteps t (terras_iter s (terras_iter q n))) := by field_simp
    rw [he] at hb
    have hf : (0:ℝ) < (2:ℝ)^s / 3^oddSteps s (terras_iter q n) := by positivity
    have hratio : (2:ℝ)^t / 3^oddSteps t (terras_iter s (terras_iter q n)) ≤ 1 := by
      nlinarith only [hb, hf]
    have hh := (div_le_one (by positivity : (0:ℝ) <
      3^oddSteps t (terras_iter s (terras_iter q n)))).mp hratio
    exact_mod_cast hh
  exact ⟨q+s, by simpa only [terras_iter_add] using hsample⟩

/-- Sampled contraction existence is exactly nondivergence. Neither side
is proved, and neither side excludes nontrivial cycles. -/
theorem all_bounded_iff_sampled_contraction :
    (∀ n, 0 < n → ∃ B, ∀ t, terras_iter t n ≤ B) ↔
    (∀ n, 0 < n → n % 9 = 2 →
      ∃ t, terras_iter t n % 9 = 2 ∧ 3^oddSteps t n < 2^t) := by
  constructor
  · intro hb n hn hr
    by_contra hh
    have hs : SampledNeverContracts n := by
      refine ⟨hr, ?_⟩
      intro t ht
      have hc : ¬ 3^oddSteps t n < 2^t := fun hc => hh ⟨t, ht, hc⟩
      omega
    obtain ⟨B, hB⟩ := hb n hn
    obtain ⟨t, ht⟩ := hs.unbounded hn B
    have := hB t
    omega
  · intro hc n hn
    by_contra hh
    push_neg at hh
    obtain ⟨s, hs⟩ := unbounded_has_sampled_noncontracting_tail hn hh
    obtain ⟨t, ht, hcontract⟩ := hc (terras_iter s n) (terras_iter_pos s n hn) hs.1
    have := hs.2 t ht
    omega

end Collatz
