import Collatz.OrbitPacking

/-! Every unbounded natural Collatz orbit has summable reciprocals.
No external density theorem is assumed: finite packing supplies a geometric
shell majorant. This establishes correction coverage, not nondivergence. -/
namespace Collatz

private noncomputable def shellBudget (m : ℕ) : ℝ :=
  54*(27/32 : ℝ)^m + (243/8 : ℝ)*(243/256 : ℝ)^m

private theorem shellBudget_nonneg (m : ℕ) : 0 ≤ shellBudget m := by
  unfold shellBudget
  positivity

private theorem shellBudget_summable : Summable shellBudget :=
  ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 27/32)
    (by norm_num : (27/32:ℝ) < 1)).mul_left 54).add
  ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 243/256)
    (by norm_num : (243/256:ℝ) < 1)).mul_left (243/8))

private theorem shellBudget_identity (m : ℕ) :
    shellBudget m * ((8:ℝ)^(m+1)*32^m) = 2*216^(m+1)+243^(m+1) := by
  unfold shellBudget
  rw [div_pow, div_pow, pow_succ, pow_succ, pow_succ]
  have h216 : (216:ℝ)^m = 8^m*27^m := by rw [← mul_pow]; norm_num
  have h256 : (256:ℝ)^m = 8^m*32^m := by rw [← mul_pow]; norm_num
  rw [h216, h256]
  field_simp
  ring

private theorem reciprocal_shell_bound {N m : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) {S : Finset ℕ}
    (hS : S ⊆ Finset.range (32^(m+1)))
    (hlo : ∀ n ∈ S, 32^m ≤ n)
    (horb : ∀ n ∈ S, ∃ t, terras_iter t N = n) :
    ∑ n ∈ S, (1/(n:ℝ)) ≤ shellBudget m := by
  have hc := unbounded_orbit_packing h hS horb
  have hcR : (8:ℝ)^(m+1)*S.card ≤ 2*216^(m+1)+243^(m+1) := by exact_mod_cast hc
  have h32 : (0:ℝ) < 32^m := by positivity
  have h8 : (0:ℝ) < 8^(m+1) := by positivity
  have hcard : (S.card : ℝ)/32^m ≤ shellBudget m := by
    apply (div_le_iff₀ h32).mpr
    have he := shellBudget_identity m
    nlinarith only [hcR, he, h8]
  calc
    ∑ n ∈ S, (1/(n:ℝ)) ≤ ∑ _n ∈ S, (1/(32:ℝ)^m) := by
      apply Finset.sum_le_sum
      intro n hn
      apply one_div_le_one_div_of_le h32
      exact_mod_cast hlo n hn
    _ = (S.card : ℝ)/32^m := by simp [div_eq_mul_inv]
    _ ≤ shellBudget m := hcard

private theorem reciprocal_packing_sum {N : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) (m : ℕ) {S : Finset ℕ}
    (hS : S ⊆ Finset.range (32^m)) (hpos : ∀ n ∈ S, 0 < n)
    (horb : ∀ n ∈ S, ∃ t, terras_iter t N = n) :
    ∑ n ∈ S, (1/(n:ℝ)) ≤ ∑ k ∈ Finset.range m, shellBudget k := by
  classical
  induction m generalizing S with
  | zero =>
    have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hh := hS hn
      simp at hh
      have := hpos n hn
      omega
    simp [he]
  | succ m ih =>
    let lo := S.filter (fun n => n < 32^m)
    let high := S.filter (fun n => ¬ n < 32^m)
    have hlS : lo ⊆ Finset.range (32^m) := by
      intro n hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    have hl := ih hlS (fun n hn => hpos n ((Finset.mem_filter.mp hn).1))
      (fun n hn => horb n ((Finset.mem_filter.mp hn).1))
    have hhS : high ⊆ Finset.range (32^(m+1)) := fun n hn => hS ((Finset.mem_filter.mp hn).1)
    have hh := reciprocal_shell_bound h hhS
      (fun n hn => by have := (Finset.mem_filter.mp hn).2; omega)
      (fun n hn => horb n ((Finset.mem_filter.mp hn).1))
    have he : (∑ n ∈ lo, (1/(n:ℝ))) + (∑ n ∈ high, (1/(n:ℝ))) = ∑ n ∈ S, (1/(n:ℝ)) := by
      exact Finset.sum_filter_add_sum_filter_not S (fun n => n < 32^m) (fun n => 1/(n:ℝ))
    rw [Finset.sum_range_succ]
    linarith only [hl, hh, he]

/-- Every unbounded positive natural orbit has a convergent reciprocal
series. The proof covers all such orbits, not only a density-one set. -/
theorem unbounded_orbit_reciprocal_summable {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) : Summable (orbitReciprocal N) := by
  classical
  apply summable_of_sum_range_le (orbitReciprocal_nonneg N) (c := ∑' m, shellBudget m)
  intro T
  let S := (Finset.range T).image (fun t => terras_iter t N)
  let m := S.sup id + 1
  have hS : S ⊆ Finset.range (32^m) := by
    intro n hn
    apply Finset.mem_range.mpr
    have hnle : n ≤ S.sup id := Finset.le_sup (f := id) hn
    have hm : n < 2^m := by
      have hh := (Nat.lt_two_pow_self : m < 2^m)
      dsimp [m] at *
      omega
    exact hm.trans_le (Nat.pow_le_pow_left (by decide) _)
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hn
    exact terras_iter_pos t N hN
  have horb : ∀ n ∈ S, ∃ t, terras_iter t N = n := by
    intro n hn
    obtain ⟨t, _, he⟩ := Finset.mem_image.mp hn
    exact ⟨t, he⟩
  have hh := reciprocal_packing_sum h m hS hpos horb
  have hsum : (∑ t ∈ Finset.range T, orbitReciprocal N t) = ∑ n ∈ S, (1/(n:ℝ)) := by
    dsimp [S, orbitReciprocal]
    rw [Finset.sum_image]
    intro a _ b _ he
    exact unbounded_orbit_injective h he
  rw [hsum]
  exact hh.trans (shellBudget_summable.sum_le_tsum _ (fun k _ => shellBudget_nonneg k))

/-- The previously open correction-coverage implication follows from
packing: every unbounded positive natural orbit has bounded ideal correction. -/
theorem unbounded_orbit_supercritical {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) : Supercritical N :=
  supercritical_of_summable_reciprocal hN (unbounded_orbit_reciprocal_summable hN h)

/-- For positive seeds, bounded ideal correction is exactly unboundedness
of the natural orbit. This does not assert that either condition occurs. -/
theorem supercritical_iff_unbounded_orbit {N : ℕ} (hN : 0 < N) :
    Supercritical N ↔ (∀ B, ∃ t, B < terras_iter t N) := by
  constructor
  · intro hs B
    obtain ⟨t, _, ht⟩ := Filter.exists_lt_of_tendsto_atTop
      (supercritical_orbit_tendsto_atTop hN hs) 0 B
    exact ⟨t, ht⟩
  · exact unbounded_orbit_supercritical hN

/-- The inverse multiplicative drift tends to zero on every unbounded
positive orbit. This is additive discrepancy escape, not a strict density gap. -/
theorem unbounded_inverse_drift_tendsto_zero {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) :
    Filter.Tendsto (fun t => (2:ℝ)^t/(3:ℝ)^oddSteps t N)
      Filter.atTop (nhds 0) := by
  have hs := unbounded_orbit_reciprocal_summable hN h
  have hc := tendsto_idealC (unbounded_orbit_supercritical hN h)
  have hh := (hc.const_add (N:ℝ)).mul hs.tendsto_atTop_zero
  simp only [mul_zero] at hh
  simpa only [inverse_drift_eq_reciprocal hN] using hh

end Collatz
