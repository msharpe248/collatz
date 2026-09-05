import Collatz.RationalGrid

/-! Transport real intercepts to finite rational phases. -/
namespace Collatz

private theorem floor_rational_phase {p q r : ℕ} {β : ℝ} (hq : 0 < q)
    (hr0 : (r : ℝ) ≤ q*β) (hr1 : (q : ℝ)*β < r+1) (t : ℕ) :
    ⌊(t : ℝ)*((p : ℝ)/q)+β⌋ = (((t*p+r)/q : ℕ) : ℤ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he : (q : ℝ)*((t : ℝ)*((p : ℝ)/q)+β) = (t : ℝ)*p+q*β := by
    field_simp
  have hd : (q : ℝ)*((t*p+r)/q : ℕ) + ((t*p+r)%q : ℕ) = (t : ℝ)*p+r := by
    exact_mod_cast Nat.div_add_mod (t*p+r) q
  have hm : (0 : ℝ) ≤ ((t*p+r)%q : ℕ) := by positivity
  have hm1 : (((t*p+r)%q : ℕ) : ℝ)+1 ≤ q := by
    exact_mod_cast (show (t*p+r)%q+1 ≤ q by have := Nat.mod_lt (t*p+r) hq; omega)
  rw [Int.floor_eq_iff]
  simp only [Int.cast_natCast]
  constructor <;> nlinarith only [he, hd, hm, hm1, hr0, hr1, hqR]

private theorem mech_eq_grid {p q r : ℕ} {β : ℝ} (hpq : p < q)
    (hr0 : (r : ℝ) ≤ q*β) (hr1 : (q : ℝ)*β < r+1) (t : ℕ) :
    mech ((p : ℝ)/q) β t = if RationalGrid.bit p q r t then 1 else 0 := by
  have hq : 0 < q := by omega
  unfold mech
  rw [show (t : ℝ)+1 = ((t+1 : ℕ) : ℝ) by push_cast; rfl,
    floor_rational_phase hq hr0 hr1, floor_rational_phase hq hr0 hr1]
  have he : ((t+1)*p+r)/q = (t*p+r)/q +
      (if RationalGrid.bit p q r t then 1 else 0) := by
    rw [show (t+1)*p+r = (t*p+r)+p by ring, Nat.add_div hq]
    simp [RationalGrid.bit, Nat.div_eq_of_lt hpq, Nat.mod_eq_of_lt hpq]
  rw [he]
  split <;> simp_all

/-- Every real intercept of a rational slope has an exact finite grid
phase. This is equality of infinite itineraries, not finite approximation. -/
theorem rational_itinerary_grid {p q N : ℕ} {ρ : ℝ} (hpq : p < q)
    (h : HasItin ((p : ℝ)/q) ρ N) : ∃ r, RationalGrid.HasGrid p q r N := by
  let β := Int.fract ρ
  let r := ⌊(q : ℝ)*β⌋₊
  have hb : 0 ≤ β := Int.fract_nonneg ρ
  have hr0 : (r : ℝ) ≤ q*β := Nat.floor_le (by positivity)
  have hr1 : (q : ℝ)*β < r+1 := Nat.lt_floor_add_one _
  have hs := h.shift 0
  simp only [Nat.cast_zero, zero_mul, zero_add, terras_iter] at hs
  refine ⟨r, ?_⟩
  intro t
  have hh := hs t
  rw [mech_eq_grid hpq hr0 hr1] at hh
  cases he : RationalGrid.bit p q r t <;> simp [he] at hh ⊢ <;> omega

/-- All reduced rational mechanical slopes strictly between zero and one,
with arbitrary real intercept, force reaching 1. -/
theorem reduced_rational_mechanical_reaches_one {p q N : ℕ} {ρ : ℝ}
    (hp : 0 < p) (hpq : p < q) (hc : Nat.Coprime q p)
    (h : HasItin ((p : ℝ)/q) ρ N) : ∃ t, terras_iter t N = 1 := by
  obtain ⟨r, hr⟩ := rational_itinerary_grid hpq h
  exact RationalGrid.grid_reaches_one hp hpq hc hr

private theorem mechanical_reaches_one_of_return {α ρ : ℝ} {N q : ℕ}
    (hN : 0 < N) (hq : 0 < q) (h : HasItin α ρ N)
    (hr : terras_iter q N = N) : ∃ t, terras_iter t N = 1 := by
  let p := oddSteps q N
  have hp : 0 < p := cycle_has_odd_step q N hq hN hr
  have hpq : p < q := by
    have hh := cycle_three_pow_lt q N hq hN hr
    have hpqle := oddSteps_le q N
    by_contra hn
    have he : p = q := by dsimp [p] at *; omega
    change 3^p < 2^q at hh
    rw [he] at hh
    exact (not_lt_of_ge (Nat.pow_le_pow_left (by decide : 2 ≤ 3) q)) hh
  obtain ⟨a, b, hc, ha, hb⟩ := Nat.exists_coprime p q
  have ha0 : 0 < a := by
    by_contra hn
    have he : a = 0 := by omega
    rw [he, Nat.zero_mul] at ha
    omega
  have hab : a < b := by
    have hh : a * p.gcd q < b * p.gcd q := by rwa [← ha, ← hb]
    exact Nat.lt_of_mul_lt_mul_right hh
  have hg : (0 : ℝ) < p.gcd q := by exact_mod_cast Nat.gcd_pos_of_pos_left q hp
  have hs := mechanical_return_slope h hr
  have haR : (p : ℝ) = (a : ℝ)*(p.gcd q : ℕ) := by exact_mod_cast ha
  have hbR : (q : ℝ) = (b : ℝ)*(p.gcd q : ℕ) := by exact_mod_cast hb
  have hs' : (b : ℝ)*α = a := by
    change (q : ℝ)*α = p at hs
    rw [haR, hbR] at hs
    nlinarith only [hs, hg]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have he : α = (a : ℝ)/b := (eq_div_iff hb0).mpr (by nlinarith only [hs'])
  rw [he] at h
  exact reduced_rational_mechanical_reaches_one ha0 hab hc.symm h

/-- Every mechanical parity itinerary of a positive natural seed reaches
one, with no rationality or slope-range assumption. -/
theorem mechanical_reaches_one {α ρ : ℝ} {N : ℕ} (hN : 0 < N)
    (hit : HasItin α ρ N) : ∃ t, terras_iter t N = 1 := by
  obtain ⟨B, hB⟩ := bounded_of_mechanical hit
  have hm : Set.MapsTo (fun t => terras_iter t N) (Finset.range (B+2)) (Finset.range (B+1)) := by
    intro t _
    apply Finset.mem_range.mpr
    change terras_iter t N < B+1
    have := hB t
    omega
  obtain ⟨a, _, b, _, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simp : (Finset.range (B+1)).card < (Finset.range (B+2)).card) hm
  have finish (a b : ℕ) (hab : a < b) (he : terras_iter a N = terras_iter b N) :
      ∃ t, terras_iter t N = 1 := by
    have hr : terras_iter (b-a) (terras_iter a N) = terras_iter a N := by
      rw [terras_iter_add, Nat.add_sub_of_le (by omega)]
      exact he.symm
    obtain ⟨t, ht⟩ := mechanical_reaches_one_of_return (terras_iter_pos a N hN)
      (by omega : 0 < b-a) (hit.shift a) hr
    exact ⟨a+t, by rwa [← terras_iter_add]⟩
  rcases lt_or_gt_of_ne hne with hab | hab
  · exact finish a b hab he
  · exact finish b a hab he.symm

/-- The only positive natural seeds with a globally mechanical itinerary
are 1 and 2, and their slope is necessarily one half. -/
theorem mechanical_classification {α ρ : ℝ} {N : ℕ} (hN : 0 < N)
    (hit : HasItin α ρ N) : α = 1/2 ∧ (N = 1 ∨ N = 2) := by
  obtain ⟨t, ht⟩ := mechanical_reaches_one hN hit
  have hh := hit.shift t
  rw [ht] at hh
  have hs := mechanical_return_slope hh (show terras_iter 2 1 = 1 by decide)
  norm_num [oddSteps, terras] at hs
  have ha : α = 1/2 := by linarith
  refine ⟨ha, ?_⟩
  have hr := mechanical_period_return hit (q := 2) (p := 1) (by rw [ha]; norm_num)
  exact ParityDefects.two_step_return_trivial hN hr

/-- Any positive orbit with a mechanical tail reaches one. -/
theorem eventual_mechanical_reaches_one {α ρ : ℝ} {N s : ℕ} (hN : 0 < N)
    (h : HasItin α ρ (terras_iter s N)) : ∃ t, terras_iter t N = 1 := by
  obtain ⟨t, ht⟩ := mechanical_reaches_one (terras_iter_pos s N hN) h
  exact ⟨s+t, by rwa [← terras_iter_add]⟩

end Collatz
