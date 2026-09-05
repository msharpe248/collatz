import Collatz.DriftEscape

/-! Residue information strengthens correction control on injective orbits.
Every positive orbit eventually avoids multiples of three. This is not an
exclusion of every unbounded orbit or of nontrivial cycles. -/
namespace Collatz

theorem terras_mod_three_ne_zero {n : ℕ} (hn : n % 3 ≠ 0) :
    terras n % 3 ≠ 0 := by
  intro hz
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have := two_mul_terras_even n he
    omega
  · have := two_mul_terras_odd n ho
    omega

theorem orbit_mod_three_ne_zero {n : ℕ} (hn : n % 3 ≠ 0) (t : ℕ) :
    terras_iter t n % 3 ≠ 0 := by
  induction t with
  | zero => exact hn
  | succ t ih => rw [terras_iter_succ']; exact terras_mod_three_ne_zero ih

/-- Every positive seed has a tail avoiding multiples of three. -/
theorem exists_tail_mod_three_ne_zero (n : ℕ) (hn : 0 < n) :
    ∃ t, terras_iter t n % 3 ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n % 3 = 0
    · rcases Nat.mod_two_eq_zero_or_one n with he | ho
      · have hs := two_mul_terras_even n he
        have hp := terras_iter_pos 1 n hn
        change 0 < terras n at hp
        obtain ⟨t, ht⟩ := ih (terras n) (by omega) hp
        exact ⟨t+1, ht⟩
      · refine ⟨1, ?_⟩
        change terras n % 3 ≠ 0
        have hs := two_mul_terras_odd n ho
        omega
    · exact ⟨0, hz⟩

/-- The telescoping product on positive integer ranks, with half-unit offset. -/
theorem half_rank_product_le_card (s : Finset ℕ) (hs : ∀ k ∈ s, 0 < k) :
    (∏ k ∈ s, (2*(k : ℝ)+1)/(2*k-1)) ≤ 2*(s.card : ℝ)+1 := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s = ∅
    · simp [he]
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s id (Finset.nonempty_iff_ne_empty.mpr he)
    have hmpos := hs m hm
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    have hsub : s ⊆ Finset.Icc 1 m := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨hs k hk, hmax k hk⟩
    have hcard : s.card ≤ m := by simpa using Finset.card_le_card hsub
    have hc : (s.card : ℝ) ≤ m := by exact_mod_cast hcard
    have hErase : ((s.erase m).card : ℝ)+1 = s.card := by
      exact_mod_cast Finset.card_erase_add_one hm
    have hp := ih (s.erase m) (Finset.erase_ssubset hm)
      (fun k hk => hs k (Finset.mem_of_mem_erase hk))
    rw [← Finset.mul_prod_erase s (fun k => (2*(k : ℝ)+1)/(2*k-1)) hm]
    have hmden : 0 < 2*(m : ℝ)-1 := by linarith
    have hb := mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ (2*(m : ℝ)+1)/(2*m-1))
    apply hb.trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmden).mpr
    nlinarith

/-- A ninth-power factor is dominated by a telescoping rank ratio. -/
theorem rank_correction_ninth_le {r : ℝ} (hr : 1 ≤ r) :
    (1+1/(9*r))^9 ≤ (2*r+1)/(2*r-1) := by
  have hr0 : 0 < r := by linarith
  have hd : 0 < 2*r-1 := by linarith
  apply (le_div_iff₀ hd).mpr
  field_simp
  have hp : 0 ≤ 1+79*r+2754*r^2+55404*r^3+704214*r^4+
      5786802*r^5+29760696*r^6+82904796*r^7+43046721*r^8 := by positivity
  nlinarith [hp]

/-- Excluding multiples of three compresses the ranks of distinct odd values. -/
theorem idealC_ninth_bound_of_prefix {N : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0) (T : ℕ)
    (hinj : Set.InjOn (fun t => terras_iter t N) (Finset.range T))
    (hone : ∀ t, t < T → terras_iter t N ≠ 1) :
    ((N : ℝ)+idealC T N)^9 ≤ (N : ℝ)^9*(2*(oddSteps T N : ℝ)+1) := by
  let f : ℕ → ℕ := fun t => (terras_iter t N-1)/3
  have hodd (t : ℕ) (ht : t ∈ parities T N) : terras_iter t N % 2 = 1 :=
    (Finset.mem_filter.mp ht).2
  have hfpos (t : ℕ) (ht : t ∈ parities T N) : 0 < f t := by
    have ho := hodd t ht
    have hne := hone t (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)
    have hm := orbit_mod_three_ne_zero h3 t
    have hge : 5 ≤ terras_iter t N := by omega
    dsimp [f]
    omega
  have hfinj : Set.InjOn f (parities T N) := by
    intro a ha b hb hab
    have haR : a ∈ Finset.range T := (Finset.mem_filter.mp ha).1
    have hbR : b ∈ Finset.range T := (Finset.mem_filter.mp hb).1
    apply hinj haR hbR
    change terras_iter a N = terras_iter b N
    have := hodd a ha
    have := hodd b hb
    have := orbit_mod_three_ne_zero h3 a
    have := orbit_mod_three_ne_zero h3 b
    dsimp [f] at hab
    have had : (terras_iter a N-1)/3 = terras_iter a N/3 := by omega
    have hbd : (terras_iter b N-1)/3 = terras_iter b N/3 := by omega
    rw [had, hbd] at hab
    omega
  have hp := half_rank_product_le_card ((parities T N).image f) (by
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
    have hfp : (1 : ℝ) ≤ f t := by exact_mod_cast hfpos t ht
    have hfn : 3*f t ≤ terras_iter t N := by dsimp [f]; omega
    have hfr : 3*(f t : ℝ) ≤ terras_iter t N := by exact_mod_cast hfn
    have hx : 0 < (terras_iter t N : ℝ) := by linarith
    apply le_trans ?_ (rank_correction_ninth_le hfp)
    have hrec : 1/(3*(terras_iter t N : ℝ)) ≤ 1/(9*(f t : ℝ)) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    simpa [add_comm] using pow_le_pow_left₀ (by positivity) (add_le_add_left hrec 1) 9

theorem unbounded_idealC_ninth_bound {N : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    ((N : ℝ)+idealC T N)^9 ≤ (N : ℝ)^9*(2*(oddSteps T N : ℝ)+1) :=
  idealC_ninth_bound_of_prefix hN h3 T (unbounded_orbit_injective h).injOn
    (fun t _ => unbounded_orbit_ne_one h t)

theorem unbounded_tail {N : ℕ} (h : ∀ B, ∃ t, B < terras_iter t N) (K : ℕ) :
    ∀ B, ∃ t, B < terras_iter t (terras_iter K N) := by
  intro B
  obtain ⟨t, ht⟩ := h (max B ((Finset.range K).sup (fun t => terras_iter t N)))
  have hKt : K ≤ t := by
    by_contra hn
    have hh := Finset.le_sup (f := fun t => terras_iter t N)
      (Finset.mem_range.mpr (show t < K by omega))
    dsimp only at hh
    omega
  refine ⟨t-K, ?_⟩
  rw [terras_iter_add, Nat.add_sub_of_le hKt]
  omega

/-- Every unbounded positive orbit has a tail satisfying the ninth bound at
all lengths, including seeds initially divisible by three. -/
theorem unbounded_eventual_ninth_bound {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) :
    ∃ K, ∀ T, let M := terras_iter K N
      ((M : ℝ)+idealC T M)^9 ≤ (M : ℝ)^9*(2*(oddSteps T M : ℝ)+1) := by
  obtain ⟨K, hK⟩ := exists_tail_mod_three_ne_zero N hN
  exact ⟨K, fun T => unbounded_idealC_ninth_bound (terras_iter_pos K N hN)
    hK (unbounded_tail h K) T⟩

/-- Division-free drift restriction on an unbounded orbit avoiding multiples of three. -/
theorem unbounded_ninth_drift_bound {N : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    (2^T * terras_iter T N)^9 ≤ (3^oddSteps T N * N)^9*(2*oddSteps T N+1) := by
  have hc := unbounded_idealC_ninth_bound hN h3 h T
  have he : (2 : ℝ)^T*(terras_iter T N : ℝ) =
      (3 : ℝ)^oddSteps T N*((N : ℝ)+idealC T N) := by
    have hh := terras_iter_eq_ideal T N
    apply (eq_div_iff (by positivity : (2 : ℝ)^T ≠ 0)).mp at hh
    nlinarith
  have hb : ((2 : ℝ)^T*(terras_iter T N : ℝ))^9 ≤
      ((3 : ℝ)^oddSteps T N*N)^9*(2*(oddSteps T N : ℝ)+1) := by
    rw [he, mul_pow, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hc
      (by positivity : (0 : ℝ) ≤ ((3 : ℝ)^oddSteps T N)^9)]
  exact_mod_cast hb

/-- Every prefix has a drift excursion at the improved exponent 8/9. -/
theorem unbounded_prefix_ninth_escape {N : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    ∃ t ≤ T, (2^t)^9*(T+1)^8 ≤ 2*(3^oddSteps t N*N)^9 := by
  obtain ⟨t, ht, hv⟩ := prefix_has_large_value (fun t => terras_iter_pos t N hN)
    (unbounded_orbit_injective h) T
  refine ⟨t, ht, ?_⟩
  have hb := unbounded_ninth_drift_bound hN h3 h t
  have hj : 2*oddSteps t N+1 ≤ 2*(T+1) := by
    have := oddSteps_le t N
    omega
  have hleft : (2^t*(T+1))^9 ≤ (2^t*terras_iter t N)^9 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hv) 9
  have hall := (hleft.trans hb).trans (Nat.mul_le_mul_left ((3^oddSteps t N*N)^9) hj)
  rw [mul_pow] at hall
  apply Nat.le_of_mul_le_mul_right (c := T+1) _ (by omega)
  convert hall using 1 <;> ring

/-- Every unbounded positive orbit has a tail with the improved drift escape. -/
theorem unbounded_eventual_ninth_escape {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) :
    ∃ K, ∀ T, let M := terras_iter K N
      ∃ t ≤ T, (2^t)^9*(T+1)^8 ≤ 2*(3^oddSteps t M*M)^9 := by
  obtain ⟨K, hK⟩ := exists_tail_mod_three_ne_zero N hN
  exact ⟨K, fun T => unbounded_prefix_ninth_escape (terras_iter_pos K N hN)
    hK (unbounded_tail h K) T⟩

/-- A finite rational polynomial drift certificate below exponent 8/9
forces boundedness for a seed outside the multiples of three. -/
theorem finite_ninth_drift_certificate {N C a b T : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (hab : b < 8*a) (hT : 2^a*C*(N^9)^a < T+1)
    (hc : ∀ t, t ≤ T → ((3^oddSteps t N)^9)^a ≤
      C * (t+1)^b * ((2^t)^9)^a) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  by_contra hn
  push_neg at hn
  obtain ⟨t, ht, he⟩ := unbounded_prefix_ninth_escape hN h3 hn T
  have he' := Nat.pow_le_pow_left he a
  simp only [mul_pow] at he'
  have hc' := Nat.mul_le_mul_left (2^a)
    (Nat.mul_le_mul_right ((N^9)^a) (hc t ht))
  have hall : ((2^t)^9)^a*((T+1)^8)^a ≤
      2^a*C*(t+1)^b*((2^t)^9)^a*(N^9)^a := by
    nlinarith [he', hc']
  have hp : 0 < ((2^t)^9)^a := by positivity
  have hsmall : ((T+1)^8)^a ≤ 2^a*C*(t+1)^b*(N^9)^a := by
    apply Nat.le_of_mul_le_mul_left (c := ((2^t)^9)^a) _ hp
    convert hall using 1; ring
  have htPow : (t+1)^b ≤ (T+1)^b := Nat.pow_le_pow_left (by omega) b
  have hsmall' : (T+1)^(8*a) ≤ 2^a*C*(N^9)^a*(T+1)^b := by
    rw [← pow_mul] at hsmall
    nlinarith [Nat.mul_le_mul_left (2^a*C*(N^9)^a) htPow]
  have hbig : (T+1)^(b+1) ≤ (T+1)^(8*a) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hcanc : T+1 ≤ 2^a*C*(N^9)^a := by
    apply Nat.le_of_mul_le_mul_right (c := (T+1)^b) _ (by positivity)
    have := hbig.trans hsmall'
    rw [pow_succ] at this
    nlinarith
  exact (not_le_of_gt hT) hcanc

/-- A global polynomial envelope below exponent 8/9 supplies the finite
certificate. No such envelope is asserted for arbitrary Collatz orbits. -/
theorem bounded_orbit_of_ninth_polynomial_drift {N C a b : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (hab : b < 8*a)
    (hc : ∀ t, ((3^oddSteps t N)^9)^a ≤
      C * (t+1)^b * ((2^t)^9)^a) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  apply finite_ninth_drift_certificate (C := C) (T := 2^a*C*(N^9)^a) hN h3 hab (by omega)
  exact fun t _ => hc t

end Collatz
