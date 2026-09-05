import Collatz.Reciprocal
import Collatz.ParityDefects

/-! Distinct odd orbit values give a polynomial bound on ideal correction.
The hypotheses below are necessary for unbounded orbits, not established
for arbitrary positive seeds. -/
namespace Collatz

/-- A finite set of distinct positive integers cannot have more reciprocal
product mass than the initial segment of the same cardinality. -/
theorem reciprocal_product_le_card (s : Finset ℕ) (hs : ∀ k ∈ s, 0 < k) :
    (∏ k ∈ s, ((k : ℝ) + 1) / k) ≤ (s.card : ℝ) + 1 := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s = ∅
    · simp [he]
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s id (Finset.nonempty_iff_ne_empty.mpr he)
    have hmpos := hs m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hsub : s ⊆ Finset.Icc 1 m := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨hs k hk, hmax k hk⟩
    have hcard : s.card ≤ m := by
      have := Finset.card_le_card hsub
      simpa using this
    have hc : (s.card : ℝ) ≤ m := by exact_mod_cast hcard
    have hcErase : ((s.erase m).card : ℝ) + 1 = s.card := by
      exact_mod_cast Finset.card_erase_add_one hm
    have hp := ih (s.erase m) (Finset.erase_ssubset hm)
      (fun k hk => hs k (Finset.mem_of_mem_erase hk))
    rw [← Finset.mul_prod_erase s (fun k => ((k : ℝ) + 1) / k) hm]
    have hprod := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ ((m : ℝ) + 1) / m)
    rw [hcErase] at hprod
    apply hprod.trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmR).mpr
    nlinarith

/-- The sixth power is controlled by a ratio that telescopes across odd values. -/
theorem odd_correction_sixth_le {x : ℝ} (hx : 1 < x) :
    (1 + 1 / (3 * x))^6 ≤ (x + 1) / (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  apply (le_div_iff₀ hxm).mpr
  field_simp
  have hpoly : 0 ≤ 1 + 17*x + 117*x^2 + 405*x^3 + 675*x^4 + 243*x^5 := by positivity
  nlinarith [hpoly]

/-- Unbounded deterministic trajectories cannot repeat a value. -/
theorem unbounded_orbit_injective {N : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) : Function.Injective (fun t => terras_iter t N) := by
  intro a b hab
  by_contra hne
  wlog hablt : a < b generalizing a b
  · exact this (a := b) (b := a) hab.symm (Ne.symm hne) (by omega)
  have hret : terras_iter (a + (b-a)) N = terras_iter a N := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hablt)] using hab.symm
  obtain ⟨B, hB⟩ := return_bounds_orbit (by omega : 0 < b-a) hret
  obtain ⟨t, ht⟩ := h B
  exact (not_lt_of_ge (hB t)) ht

theorem idealC_one_even {n : ℕ} (hn : n % 2 = 0) : idealC 1 n = 0 := by
  have hd := dcoef_succ_even (T := 0) hn
  have ho := oddSteps_succ_even 0 n hn
  norm_num [idealC, hd, ho, oddSteps, hn]

/-- Exact multiplicative formula over the odd positions of a finite prefix. -/
theorem idealC_odd_product {N : ℕ} (hN : 0 < N) (T : ℕ) :
    (N : ℝ) + idealC T N = N * ∏ t ∈ parities T N,
      (1 + 1 / (3 * (terras_iter t N : ℝ))) := by
  induction T with
  | zero => simp [parities]
  | succ T ih =>
    have hs := idealC_add T 1 N
    rw [inverse_drift_eq_reciprocal hN T] at hs
    rcases Nat.mod_two_eq_zero_or_one (terras_iter T N) with he | ho
    · rw [idealC_one_even he] at hs
      have hp : parities (T+1) N = parities T N := by
        simp [parities, Finset.range_add_one, Finset.filter_insert, he]
      rw [hp]
      simpa [hs] using ih
    · rw [idealC_one_odd ho] at hs
      have hp : parities (T+1) N = insert T (parities T N) := by
        simp [parities, Finset.range_add_one, Finset.filter_insert, ho]
      have hnot : T ∉ parities T N := by simp [parities]
      rw [hp, Finset.prod_insert hnot, ← mul_left_comm, ← ih, hs]
      unfold orbitReciprocal
      ring

/-- No repetition and avoidance of one force a sixth-power correction bound. -/
theorem idealC_sixth_bound_of_prefix {N : ℕ} (hN : 0 < N) (T : ℕ)
    (hinj : Set.InjOn (fun t => terras_iter t N) (Finset.range T))
    (hone : ∀ t, t < T → terras_iter t N ≠ 1) :
    ((N : ℝ) + idealC T N)^6 ≤ (N : ℝ)^6 * ((oddSteps T N : ℝ) + 1) := by
  let f : ℕ → ℕ := fun t => (terras_iter t N - 1) / 2
  have hodd (t : ℕ) (ht : t ∈ parities T N) : terras_iter t N % 2 = 1 :=
    (Finset.mem_filter.mp ht).2
  have hf (t : ℕ) (ht : t ∈ parities T N) : terras_iter t N = 2 * f t + 1 := by
    have := hodd t ht
    dsimp [f]
    omega
  have hfpos (t : ℕ) (ht : t ∈ parities T N) : 0 < f t := by
    have := hf t ht
    have := hone t (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)
    omega
  have hfinj : Set.InjOn f (parities T N) := by
    intro a ha b hb hab
    have haR : a ∈ Finset.range T := (Finset.mem_filter.mp ha).1
    have hbR : b ∈ Finset.range T := (Finset.mem_filter.mp hb).1
    apply hinj haR hbR
    change terras_iter a N = terras_iter b N
    rw [hf a ha, hf b hb, hab]
  have hp := reciprocal_product_le_card ((parities T N).image f) (by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    exact hfpos t ht)
  rw [Finset.prod_image hfinj, Finset.card_image_of_injOn hfinj, ← oddSteps_eq_card] at hp
  rw [idealC_odd_product hN T, mul_pow, ← Finset.prod_pow]
  apply mul_le_mul_of_nonneg_left (le_trans ?_ hp) (by positivity)
  apply Finset.prod_le_prod
  · intro t ht
    positivity
  · intro t ht
    have hft := hf t ht
    have hfr : (terras_iter t N : ℝ) = 2 * (f t : ℝ) + 1 := by exact_mod_cast hft
    have hfp : (0 : ℝ) < f t := by exact_mod_cast hfpos t ht
    have hx : (1 : ℝ) < terras_iter t N := by linarith
    have hb := odd_correction_sixth_le hx
    have heq : ((terras_iter t N : ℝ) + 1) / ((terras_iter t N : ℝ) - 1) =
        ((f t : ℝ) + 1) / f t := by
      rw [hfr]
      field_simp
      ring
    rwa [heq] at hb

theorem unbounded_orbit_ne_one {N : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) (t : ℕ) : terras_iter t N ≠ 1 := by
  intro ht
  have he : terras_iter (t+2) N = terras_iter t N := by
    rw [← terras_iter_add, ht]
    norm_num [terras_iter, terras]
  have := unbounded_orbit_injective h he
  omega

/-- Every unbounded positive orbit obeys the polynomial correction bound,
without a summability or density-gap assumption. -/
theorem unbounded_idealC_sixth_bound {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    ((N : ℝ) + idealC T N)^6 ≤ (N : ℝ)^6 * ((oddSteps T N : ℝ) + 1) :=
  idealC_sixth_bound_of_prefix hN T (unbounded_orbit_injective h).injOn
    (fun t _ => unbounded_orbit_ne_one h t)

/-- A division-free integer drift restriction on every unbounded orbit. -/
theorem unbounded_sixth_drift_bound {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    (2^T * terras_iter T N)^6 ≤ (3^oddSteps T N * N)^6 * (oddSteps T N + 1) := by
  have hc := unbounded_idealC_sixth_bound hN h T
  have he : (2 : ℝ)^T * (terras_iter T N : ℝ) =
      (3 : ℝ)^oddSteps T N * ((N : ℝ) + idealC T N) := by
    have := terras_iter_eq_ideal T N
    have hp : (0 : ℝ) < (2 : ℝ)^T := by positivity
    apply (eq_div_iff (ne_of_gt hp)).mp at this
    nlinarith
  have hb : ((2 : ℝ)^T * (terras_iter T N : ℝ))^6 ≤
      ((3 : ℝ)^oddSteps T N * N)^6 * ((oddSteps T N : ℝ) + 1) := by
    rw [he, mul_pow, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hc
      (by positivity : (0 : ℝ) ≤ ((3 : ℝ)^oddSteps T N)^6)]
  exact_mod_cast hb

/-- At a non-descent time, the necessary drift bound is independent of the seed. -/
theorem unbounded_nondescent_drift {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ)
    (hT : N ≤ terras_iter T N) :
    (2^T)^6 ≤ (3^oddSteps T N)^6 * (oddSteps T N + 1) := by
  have hb := unbounded_sixth_drift_bound hN h T
  have hp : 0 < N^6 := by positivity
  have hm : (2^T * N)^6 ≤ (2^T * terras_iter T N)^6 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hT) 6
  have hall := hm.trans hb
  rw [mul_pow, mul_pow] at hall
  nlinarith [hall]

end Collatz
