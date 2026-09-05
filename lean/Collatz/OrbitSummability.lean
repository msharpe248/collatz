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

/-- Explicit reciprocal budget above the value threshold `32^K`. -/
noncomputable def orbitTailBudget (K : ℕ) : ℝ :=
  (1728/5 : ℝ)*(27/32 : ℝ)^K + (7776/13 : ℝ)*(243/256 : ℝ)^K

theorem orbitTailBudget_nonneg (K : ℕ) : 0 ≤ orbitTailBudget K := by
  unfold orbitTailBudget
  positivity

private theorem orbitTailBudget_step (K : ℕ) :
    orbitTailBudget K = shellBudget K + orbitTailBudget (K+1) := by
  unfold orbitTailBudget shellBudget
  rw [pow_succ, pow_succ]
  ring

private theorem reciprocal_finite_tail {N K : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) (d : ℕ) {S : Finset ℕ}
    (hS : S ⊆ Finset.range (32^(K+d)))
    (hlo : ∀ n ∈ S, 32^K ≤ n)
    (horb : ∀ n ∈ S, ∃ t, terras_iter t N = n) :
    ∑ n ∈ S, (1/(n:ℝ)) ≤ orbitTailBudget K - orbitTailBudget (K+d) := by
  classical
  induction d generalizing S with
  | zero =>
    have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hh := Finset.mem_range.mp (hS hn)
      have hl := hlo n hn
      simp only [Nat.add_zero] at hh
      omega
    simp [he]
  | succ d ih =>
    let low := S.filter (fun n => n < 32^(K+d))
    let high := S.filter (fun n => ¬ n < 32^(K+d))
    have hlS : low ⊆ Finset.range (32^(K+d)) := by
      intro n hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    have hl := ih hlS (fun n hn => hlo n ((Finset.mem_filter.mp hn).1))
      (fun n hn => horb n ((Finset.mem_filter.mp hn).1))
    have hhS : high ⊆ Finset.range (32^((K+d)+1)) := by
      intro n hn
      simpa only [Nat.add_assoc] using hS ((Finset.mem_filter.mp hn).1)
    have hh := reciprocal_shell_bound h hhS
      (fun n hn => by have := (Finset.mem_filter.mp hn).2; omega)
      (fun n hn => horb n ((Finset.mem_filter.mp hn).1))
    have he : (∑ n ∈ low, (1/(n:ℝ))) + (∑ n ∈ high, (1/(n:ℝ))) =
        ∑ n ∈ S, (1/(n:ℝ)) :=
      Finset.sum_filter_add_sum_filter_not S (fun n => n < 32^(K+d)) (fun n => 1/(n:ℝ))
    have hb := orbitTailBudget_step (K+d)
    simp only [Nat.add_assoc] at hb
    linarith only [hl, hh, he, hb]

/-- A uniform value-tail estimate, independent of how late values occur. -/
theorem unbounded_reciprocal_value_tail {N K : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) {S : Finset ℕ}
    (hlo : ∀ n ∈ S, 32^K ≤ n)
    (horb : ∀ n ∈ S, ∃ t, terras_iter t N = n) :
    ∑ n ∈ S, (1/(n:ℝ)) ≤ orbitTailBudget K := by
  let d := S.sup id + 1
  have hS : S ⊆ Finset.range (32^(K+d)) := by
    intro n hn
    apply Finset.mem_range.mpr
    have hnle : n ≤ S.sup id := Finset.le_sup (f := id) hn
    have hh := (Nat.lt_two_pow_self : d < 2^d)
    have hd : n < 2^d := by dsimp [d] at *; omega
    exact hd.trans_le ((Nat.pow_le_pow_left (by decide : 2 ≤ 32) d).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left d K)))
  have hh := reciprocal_finite_tail h d hS hlo horb
  linarith [orbitTailBudget_nonneg (K+d)]

/-- If an unbounded orbit stays above `32^K`, its entire reciprocal series
is at most the explicit geometric tail budget. -/
theorem unbounded_reciprocal_tsum_le {N K : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N)
    (hlo : ∀ t, 32^K ≤ terras_iter t N) :
    ∑' t, orbitReciprocal N t ≤ orbitTailBudget K := by
  classical
  apply Real.tsum_le_of_sum_range_le (orbitReciprocal_nonneg N)
  intro T
  let S := (Finset.range T).image (fun t => terras_iter t N)
  have hh := unbounded_reciprocal_value_tail h (S := S)
    (fun n hn => by obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hn; exact hlo t)
    (fun n hn => by obtain ⟨t, _, he⟩ := Finset.mem_image.mp hn; exact ⟨t, he⟩)
  have he : (∑ t ∈ Finset.range T, orbitReciprocal N t) = ∑ n ∈ S, (1/(n:ℝ)) := by
    dsimp [S, orbitReciprocal]
    rw [Finset.sum_image]
    intro a _ b _ he
    exact unbounded_orbit_injective h he
  rw [he]
  exact hh

/-- The explicit value-tail budget tends to zero with the threshold. -/
theorem orbitTailBudget_tendsto_zero : Filter.Tendsto orbitTailBudget
    Filter.atTop (nhds 0) := by
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ) ≤ 27/32) (by norm_num : (27/32:ℝ) < 1)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ) ≤ 243/256) (by norm_num : (243/256:ℝ) < 1)
  simpa [orbitTailBudget] using (h1.const_mul (1728/5:ℝ)).add (h2.const_mul (7776/13:ℝ))

/-- Explicit correction control for an unbounded orbit that never falls
below `32^K`. At future minima this gives a threshold-dependent envelope. -/
theorem unbounded_idealLimit_le_tailBudget {N K : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N)
    (hlo : ∀ t, 32^K ≤ terras_iter t N) :
    idealLimit N ≤ (N:ℝ) * (Real.exp (orbitTailBudget K) - 1) := by
  apply ciSup_le
  intro T
  have hsum := unbounded_orbit_reciprocal_summable hN h
  have hp := hsum.sum_le_tsum (Finset.range T) (fun t _ => orbitReciprocal_nonneg N t)
  have hb := unbounded_reciprocal_tsum_le h hlo
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hp.trans hb))
    (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hc := idealC_exp_reciprocal_bound hN T
  nlinarith only [he, hc]

/-- The upper envelope itself grows even at the smallest allowed seed.
Thus this estimate cannot supply an absolute rounding bound below one. -/
theorem tail_correction_envelope_lower (K : ℕ) :
    (1728/5:ℝ)*27^K ≤ (32:ℝ)^K * (Real.exp (orbitTailBudget K) - 1) := by
  have he := Real.add_one_le_exp (orbitTailBudget K)
  have hh : (0:ℝ) ≤ (7776/13:ℝ)*(243/256:ℝ)^K := by positivity
  have hb : (1728/5:ℝ)*(27/32:ℝ)^K ≤ orbitTailBudget K := by
    unfold orbitTailBudget
    linarith
  have hm := mul_le_mul_of_nonneg_left (show orbitTailBudget K ≤
      Real.exp (orbitTailBudget K) - 1 by linarith) (by positivity : (0:ℝ) ≤ 32^K)
  have hl := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ 32^K)
  have hid : (32:ℝ)^K * ((1728/5:ℝ)*(27/32:ℝ)^K) = (1728/5:ℝ)*27^K := by
    rw [div_pow]
    field_simp
  rw [hid] at hl
  exact hl.trans hm

end Collatz
