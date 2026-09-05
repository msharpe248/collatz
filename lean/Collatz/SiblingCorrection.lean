import Collatz.OddPrehistory

/-! Pair exclusions yield a thinner comparison set for correction products.
The compressed values need not be orbit values; their weights dominate the
original weights. No universal slow-drift envelope is asserted. -/
namespace Collatz.SiblingCorrection

def compress (x : ℕ) : ℕ := if x % 24 = 5 then (x-1)/4 else x

def Good (x : ℕ) : Prop := 1 < x ∧ x % 2 = 1 ∧ x % 3 ≠ 0 ∧ x % 24 ≠ 5

def rank (x : ℕ) : ℕ := 7*(x/24) +
  if x % 24 < 7 then 0 else if x % 24 < 11 then 1 else
  if x % 24 < 13 then 2 else if x % 24 < 17 then 3 else
  if x % 24 < 19 then 4 else if x % 24 < 23 then 5 else 6

private theorem good_residues {x : ℕ} (hx : Good x) :
    x % 24 = 1 ∨ x % 24 = 7 ∨ x % 24 = 11 ∨ x % 24 = 13 ∨
    x % 24 = 17 ∨ x % 24 = 19 ∨ x % 24 = 23 := by
  rcases hx with ⟨_, ho, h3, h5⟩
  omega

theorem rank_pos {x : ℕ} (hx : Good x) : 0 < rank x := by
  have hp := hx.1
  rcases good_residues hx with h | h | h | h | h | h | h <;>
    simp [rank, h]
  omega

theorem rank_weight {x : ℕ} (hx : Good x) : 10*rank x ≤ 3*x := by
  rcases good_residues hx with h | h | h | h | h | h | h <;>
    simp [rank, h] <;> omega

theorem rank_injective {x y : ℕ} (hx : Good x) (hy : Good y)
    (hxy : rank x = rank y) : x = y := by
  rcases good_residues hx with h | h | h | h | h | h | h <;>
    rcases good_residues hy with g | g | g | g | g | g | g <;>
    simp [rank, h, g] at hxy <;> omega

theorem compress_good {x : ℕ} (hx : 5 < x) (ho : x % 2 = 1) (h3 : x % 3 ≠ 0) :
    Good (compress x) ∧ compress x ≤ x := by
  by_cases hh : x % 24 = 5
  · have he : (x-1)/4 = 6*(x/24)+1 := by omega
    simp only [compress, hh, ↓reduceIte, he, Good]
    omega
  · simp only [compress, hh, ↓reduceIte, Good]
    omega

/-- Compression is injective on a set not containing both siblings. -/
theorem compress_injective {S : Set ℕ}
    (hodd : ∀ x ∈ S, x % 2 = 1)
    (hpair : ∀ n, n % 2 = 1 → ¬ (n ∈ S ∧ 4*n+1 ∈ S)) : Set.InjOn compress S := by
  intro x hx y hy hxy
  by_cases hhx : x % 24 = 5 <;> by_cases hhy : y % 24 = 5
  · simp only [compress, hhx, hhy, ↓reduceIte] at hxy
    omega
  · simp only [compress, hhx, hhy, ↓reduceIte] at hxy
    have he : x = 4*y+1 := by omega
    exact False.elim (hpair y (hodd y hy) ⟨hy, he ▸ hx⟩)
  · simp only [compress, hhx, hhy, ↓reduceIte] at hxy
    have he : y = 4*x+1 := by omega
    exact False.elim (hpair x (hodd x hx) ⟨hx, he ▸ hy⟩)
  · simpa only [compress, hhx, hhy, ↓reduceIte] using hxy

theorem rank_correction_tenth_le {r : ℝ} (hr : 1 ≤ r) :
    (1+1/(10*r))^10 ≤ (2*r+1)/(2*r-1) := by
  have hr0 : 0 < r := by linarith
  have hd : 0 < 2*r-1 := by linarith
  apply (le_div_iff₀ hd).mpr
  field_simp
  have hp : 0 ≤ 1+98*r+4300*r^2+111000*r^3+1860000*r^4+21000000*r^5+
      159600000*r^6+780000000*r^7+2100000000*r^8+1000000000*r^9 := by positivity
  nlinarith [hp]

/-- A weighted product bound for distinct allowed odd values with no sibling pair. -/
theorem pair_free_product_bound (s : Finset ℕ)
    (hs : ∀ x ∈ s, 5 < x ∧ x % 2 = 1 ∧ x % 3 ≠ 0)
    (hpair : ∀ n, n % 2 = 1 → ¬ (n ∈ s ∧ 4*n+1 ∈ s)) :
    (∏ x ∈ s, (1+1/(3*(x : ℝ))))^10 ≤ 2*(s.card : ℝ)+1 := by
  let f : ℕ → ℕ := fun x => rank (compress x)
  have hg (x : ℕ) (hx : x ∈ s) : Good (compress x) ∧ compress x ≤ x :=
    compress_good (hs x hx).1 (hs x hx).2.1 (hs x hx).2.2
  have hci := compress_injective (S := (s : Set ℕ))
    (fun x hx => (hs x hx).2.1) hpair
  have hfi : Set.InjOn f (s : Set ℕ) := by
    intro x hx y hy he
    exact hci hx hy (rank_injective (hg x hx).1 (hg y hy).1 he)
  have hp := half_rank_product_le_card (s.image f) (by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact rank_pos (hg x hx).1)
  rw [Finset.prod_image hfi, Finset.card_image_of_injOn hfi] at hp
  rw [← Finset.prod_pow]
  apply le_trans ?_ hp
  apply Finset.prod_le_prod
  · intro x hx
    positivity
  · intro x hx
    have hfp : (1 : ℝ) ≤ f x := by exact_mod_cast rank_pos (hg x hx).1
    have hfn : 10*f x ≤ 3*x :=
      (rank_weight (hg x hx).1).trans (Nat.mul_le_mul_left 3 (hg x hx).2)
    have hfr : 10*(f x : ℝ) ≤ 3*(x : ℝ) := by exact_mod_cast hfn
    have hxp : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by have := (hs x hx).1; omega)
    apply le_trans ?_ (rank_correction_tenth_le hfp)
    have hrec : 1/(3*(x : ℝ)) ≤ 1/(10*(f x : ℝ)) :=
      one_div_le_one_div_of_le (by linarith) hfr
    simpa [add_comm] using pow_le_pow_left₀ (by positivity) (add_le_add_left hrec 1) 10

end Collatz.SiblingCorrection

namespace Collatz

private theorem unbounded_ne_five {N : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) (t : ℕ) : terras_iter t N ≠ 5 := by
  intro ht
  apply unbounded_orbit_ne_one h (t+4)
  rw [← terras_iter_add, ht]
  norm_num [terras_iter, terras]

/-- Sibling exclusion strengthens the ninth bound to a tenth-power bound. -/
theorem unbounded_idealC_tenth_bound {N : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    ((N : ℝ)+idealC T N)^10 ≤ (N : ℝ)^10*(2*(oddSteps T N : ℝ)+1) := by
  let s := (parities T N).image (fun t => terras_iter t N)
  have hs (x : ℕ) (hx : x ∈ s) : 5 < x ∧ x % 2 = 1 ∧ x % 3 ≠ 0 := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have ho := (Finset.mem_filter.mp ht).2
    have hne := unbounded_orbit_ne_one h t
    have hf := unbounded_ne_five h t
    have hm := orbit_mod_three_ne_zero h3 t
    exact ⟨by omega, ho, hm⟩
  have hp := SiblingCorrection.pair_free_product_bound s hs (by
    intro n ho hh
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh.1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hh.2
    exact unbounded_excludes_odd_siblings h ho ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)
  dsimp [s] at hp
  rw [Finset.prod_image (unbounded_orbit_injective h).injOn,
    Finset.card_image_of_injOn (unbounded_orbit_injective h).injOn, ← oddSteps_eq_card] at hp
  rw [idealC_odd_product hN T, mul_pow]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

/-- Every unbounded positive orbit has a tail satisfying the tenth bound at
all lengths, including seeds initially divisible by three. -/
theorem unbounded_eventual_tenth_bound {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) :
    ∃ K, ∀ T, let M := terras_iter K N
      ((M : ℝ)+idealC T M)^10 ≤ (M : ℝ)^10*(2*(oddSteps T M : ℝ)+1) := by
  obtain ⟨K, hK⟩ := exists_tail_mod_three_ne_zero N hN
  exact ⟨K, fun T => unbounded_idealC_tenth_bound (terras_iter_pos K N hN)
    hK (unbounded_tail h K) T⟩

/-- Division-free drift restriction on an unbounded orbit avoiding multiples of three. -/
theorem unbounded_tenth_drift_bound {N : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    (2^T * terras_iter T N)^10 ≤ (3^oddSteps T N * N)^10*(2*oddSteps T N+1) := by
  have hc := unbounded_idealC_tenth_bound hN h3 h T
  have he : (2 : ℝ)^T*(terras_iter T N : ℝ) =
      (3 : ℝ)^oddSteps T N*((N : ℝ)+idealC T N) := by
    have hh := terras_iter_eq_ideal T N
    apply (eq_div_iff (by positivity : (2 : ℝ)^T ≠ 0)).mp at hh
    nlinarith
  have hb : ((2 : ℝ)^T*(terras_iter T N : ℝ))^10 ≤
      ((3 : ℝ)^oddSteps T N*N)^10*(2*(oddSteps T N : ℝ)+1) := by
    rw [he, mul_pow, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hc
      (by positivity : (0 : ℝ) ≤ ((3 : ℝ)^oddSteps T N)^10)]
  exact_mod_cast hb

/-- Every prefix has a drift excursion at the improved exponent 9/10. -/
theorem unbounded_prefix_tenth_escape {N : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (h : ∀ B, ∃ t, B < terras_iter t N) (T : ℕ) :
    ∃ t ≤ T, (2^t)^10*(T+1)^9 ≤ 2*(3^oddSteps t N*N)^10 := by
  obtain ⟨t, ht, hv⟩ := prefix_has_large_value (fun t => terras_iter_pos t N hN)
    (unbounded_orbit_injective h) T
  refine ⟨t, ht, ?_⟩
  have hb := unbounded_tenth_drift_bound hN h3 h t
  have hj : 2*oddSteps t N+1 ≤ 2*(T+1) := by
    have := oddSteps_le t N
    omega
  have hleft : (2^t*(T+1))^10 ≤ (2^t*terras_iter t N)^10 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hv) 10
  have hall := (hleft.trans hb).trans (Nat.mul_le_mul_left ((3^oddSteps t N*N)^10) hj)
  rw [mul_pow] at hall
  apply Nat.le_of_mul_le_mul_right (c := T+1) _ (by omega)
  convert hall using 1 <;> ring

/-- Every unbounded positive orbit has a tail with the improved drift escape. -/
theorem unbounded_eventual_tenth_escape {N : ℕ} (hN : 0 < N)
    (h : ∀ B, ∃ t, B < terras_iter t N) :
    ∃ K, ∀ T, let M := terras_iter K N
      ∃ t ≤ T, (2^t)^10*(T+1)^9 ≤ 2*(3^oddSteps t M*M)^10 := by
  obtain ⟨K, hK⟩ := exists_tail_mod_three_ne_zero N hN
  exact ⟨K, fun T => unbounded_prefix_tenth_escape (terras_iter_pos K N hN)
    hK (unbounded_tail h K) T⟩

/-- A finite rational polynomial drift certificate below exponent 9/10
forces boundedness for a seed outside the multiples of three. -/
theorem finite_tenth_drift_certificate {N C a b T : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (hab : b < 9*a) (hT : 2^a*C*(N^10)^a < T+1)
    (hc : ∀ t, t ≤ T → ((3^oddSteps t N)^10)^a ≤
      C * (t+1)^b * ((2^t)^10)^a) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  by_contra hn
  push_neg at hn
  obtain ⟨t, ht, he⟩ := unbounded_prefix_tenth_escape hN h3 hn T
  have he' := Nat.pow_le_pow_left he a
  simp only [mul_pow] at he'
  have hc' := Nat.mul_le_mul_left (2^a)
    (Nat.mul_le_mul_right ((N^10)^a) (hc t ht))
  have hall : ((2^t)^10)^a*((T+1)^9)^a ≤
      2^a*C*(t+1)^b*((2^t)^10)^a*(N^10)^a := by
    nlinarith [he', hc']
  have hp : 0 < ((2^t)^10)^a := by positivity
  have hsmall : ((T+1)^9)^a ≤ 2^a*C*(t+1)^b*(N^10)^a := by
    apply Nat.le_of_mul_le_mul_left (c := ((2^t)^10)^a) _ hp
    convert hall using 1; ring
  have htPow : (t+1)^b ≤ (T+1)^b := Nat.pow_le_pow_left (by omega) b
  have hsmall' : (T+1)^(9*a) ≤ 2^a*C*(N^10)^a*(T+1)^b := by
    rw [← pow_mul] at hsmall
    nlinarith [Nat.mul_le_mul_left (2^a*C*(N^10)^a) htPow]
  have hbig : (T+1)^(b+1) ≤ (T+1)^(9*a) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hcanc : T+1 ≤ 2^a*C*(N^10)^a := by
    apply Nat.le_of_mul_le_mul_right (c := (T+1)^b) _ (by positivity)
    have := hbig.trans hsmall'
    rw [pow_succ] at this
    nlinarith
  exact (not_le_of_gt hT) hcanc

/-- A global polynomial envelope below exponent 9/10 supplies the finite
certificate. No such envelope is asserted for arbitrary Collatz orbits. -/
theorem bounded_orbit_of_tenth_polynomial_drift {N C a b : ℕ} (hN : 0 < N) (h3 : N % 3 ≠ 0)
    (hab : b < 9*a)
    (hc : ∀ t, ((3^oddSteps t N)^10)^a ≤
      C * (t+1)^b * ((2^t)^10)^a) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  apply finite_tenth_drift_certificate (C := C) (T := 2^a*C*(N^10)^a) hN h3 hab (by omega)
  exact fun t _ => hc t

end Collatz
