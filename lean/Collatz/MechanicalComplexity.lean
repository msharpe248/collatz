import Collatz.ParityComplexity
import Collatz.Sturmian
import Mathlib.NumberTheory.Real.Irrational

/-! Mechanical factors are determined by L ordered floor thresholds. -/
namespace Collatz
open scoped BigOperators
open Classical

private noncomputable def floorRank (α β : ℝ) (L : ℕ) : ℤ :=
  ∑ i : Fin L, (⌊((i.val : ℝ)+1)*α+β⌋ - ⌊((i.val : ℝ)+1)*α⌋)

private theorem floorRank_bounds (α : ℝ) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (L : ℕ) :
    0 ≤ floorRank α β L ∧ floorRank α β L ≤ L := by
  have hb (i : Fin L) : 0 ≤ ⌊((i.val : ℝ)+1)*α+β⌋ - ⌊((i.val : ℝ)+1)*α⌋ ∧
      ⌊((i.val : ℝ)+1)*α+β⌋ - ⌊((i.val : ℝ)+1)*α⌋ ≤ 1 := by
    have ha := Int.floor_mono (show ((i.val : ℝ)+1)*α ≤ ((i.val : ℝ)+1)*α+β by linarith)
    have hc := Int.floor_mono (show ((i.val : ℝ)+1)*α+β ≤ ((i.val : ℝ)+1)*α+1 by linarith)
    rw [Int.floor_add_one] at hc
    omega
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hb i).1)
  · calc
      floorRank α β L ≤ ∑ _i : Fin L, (1 : ℤ) := Finset.sum_le_sum (fun i _ => (hb i).2)
      _ = L := by simp

private theorem floors_eq_of_rank {α β γ : ℝ} {L : ℕ}
    (h : floorRank α β L = floorRank α γ L) (i : Fin L) :
    ⌊((i.val : ℝ)+1)*α+β⌋ = ⌊((i.val : ℝ)+1)*α+γ⌋ := by
  have ordered {β γ : ℝ} (hle : β ≤ γ) (he : floorRank α β L = floorRank α γ L) :
      ⌊((i.val : ℝ)+1)*α+β⌋ = ⌊((i.val : ℝ)+1)*α+γ⌋ := by
    have hm (j : Fin L) (_ : j ∈ Finset.univ) :
        ⌊((j.val : ℝ)+1)*α+β⌋ - ⌊((j.val : ℝ)+1)*α⌋ ≤
        ⌊((j.val : ℝ)+1)*α+γ⌋ - ⌊((j.val : ℝ)+1)*α⌋ :=
      sub_le_sub_right (Int.floor_mono (by linarith)) _
    have hh := (Finset.sum_eq_sum_iff_of_le hm).mp he i (Finset.mem_univ i)
    omega
  rcases le_total β γ with hle | hle
  · exact ordered hle h
  · exact (ordered hle h.symm).symm

private theorem mech_normalize (α ρ : ℝ) (t i : ℕ) :
    mech α ρ (t+i) = mech α (Int.fract ((t : ℝ)*α+ρ)) i := by
  have he (j : ℝ) : ((t : ℝ)+j)*α+ρ =
      (j*α+Int.fract ((t : ℝ)*α+ρ)) + (⌊(t : ℝ)*α+ρ⌋ : ℤ) := by
    rw [Int.fract]
    ring
  unfold mech
  push_cast
  rw [show ((t : ℝ)+(i : ℝ)+1)*α+ρ = ((t : ℝ)+((i : ℝ)+1))*α+ρ by ring,
    he, he, Int.floor_add_intCast, Int.floor_add_intCast]
  ring

/-- Every mechanical parity itinerary has at most L+1 distinct length-L factors.
No restriction on the slope or intercept is needed for this implication. -/
theorem mechanical_complexity_le {α ρ : ℝ} {N : ℕ} (hit : HasItin α ρ N) (L : ℕ) :
    ParityComplexity.complexity N L ≤ L+1 := by
  classical
  let β (t : ℕ) := Int.fract ((t : ℝ)*α+ρ)
  have same {s t : ℕ} (hr : floorRank α (β s) L = floorRank α (β t) L) :
      ParityComplexity.block N L s = ParityComplexity.block N L t := by
    have hf (j : ℕ) (hj : j ≤ L) : ⌊(j : ℝ)*α+β s⌋ = ⌊(j : ℝ)*α+β t⌋ := by
      cases j with
      | zero => simp [β, Int.floor_fract]
      | succ j =>
        have hh := floors_eq_of_rank hr ⟨j, by omega⟩
        simpa only [Nat.cast_add, Nat.cast_one] using hh
    funext i
    apply Fin.ext
    have hs := hit (s+i.val)
    have ht := hit (t+i.val)
    rw [mech_normalize] at hs ht
    have he : mech α (β s) i.val = mech α (β t) i.val := by
      unfold mech
      rw [show ((i.val : ℝ)+1) = ((i.val+1 : ℕ) : ℝ) by push_cast; rfl,
        hf (i.val+1) (by omega), hf i.val (by omega)]
    change terras_iter (s+i.val) N % 2 = terras_iter (t+i.val) N % 2
    exact_mod_cast hs.trans (he.trans ht.symm)
  let rep (w : Fin L → Fin 2) : ℕ := if h : ∃ t, ParityComplexity.block N L t = w then h.choose else 0
  have hrep (w : Fin L → Fin 2) (hw : w ∈ ParityComplexity.factors N L) :
      ParityComplexity.block N L (rep w) = w := by
    have hh : ∃ t, ParityComplexity.block N L t = w := (Finset.mem_filter.mp hw).2
    simp only [rep, dif_pos hh]
    exact hh.choose_spec
  let code (w : Fin L → Fin 2) := (floorRank α (β (rep w)) L).toNat
  have hbound (w : Fin L → Fin 2) := floorRank_bounds α (Int.fract_nonneg ((rep w : ℝ)*α+ρ)) (Int.fract_lt_one _) L
  have hm : Set.MapsTo code (ParityComplexity.factors N L) (Finset.range (L+1)) := by
    intro w _
    apply Finset.mem_range.mpr
    have hb := (hbound w).2
    dsimp [code, β]
    omega
  have hi : Set.InjOn code (ParityComplexity.factors N L) := by
    intro w hw v hv he
    have h0 := (hbound w).1
    have h1 := (hbound v).1
    have hr : floorRank α (β (rep w)) L = floorRank α (β (rep v)) L := by
      dsimp [code, β] at he
      dsimp [β]
      omega
    have hh := same hr
    rwa [hrep w hw, hrep v hv] at hh
  simpa [ParityComplexity.complexity] using Finset.card_le_card_of_injOn code hm hi

/-- A mechanical parity itinerary forces a bounded natural orbit. -/
theorem bounded_of_mechanical {α ρ : ℝ} {N : ℕ} (h : HasItin α ρ N) :
    ∃ B, ∀ t, terras_iter t N ≤ B :=
  ParityComplexity.bounded_of_additive_linear_complexity (mechanical_complexity_le h)

/-- Shifting an itinerary shifts its intercept. -/
theorem HasItin.shift {α ρ : ℝ} {N : ℕ} (h : HasItin α ρ N) (s : ℕ) :
    HasItin α (Int.fract ((s : ℝ)*α+ρ)) (terras_iter s N) := by
  intro t
  rw [terras_iter_add, h (s+t), mech_normalize]

/-- A return in a mechanical itinerary forces an integral period times slope. -/
theorem mechanical_return_slope {α ρ : ℝ} {N q : ℕ} (h : HasItin α ρ N)
    (hret : terras_iter q N = N) : (q : ℝ)*α = oddSteps q N := by
  have rep (k : ℕ) : terras_iter (k*q) N = N ∧ oddSteps (k*q) N = k*oddSteps q N := by
    induction k with
    | zero => simp [terras_iter]
    | succ k ih =>
      rw [Nat.succ_mul, ← terras_iter_add, oddSteps_add, ih.1, hret, ih.2]
      constructor
      · rfl
      · ring
  have hb (k : ℕ) : -1 < (k : ℝ)*((q : ℝ)*α-oddSteps q N) ∧
      (k : ℝ)*((q : ℝ)*α-oddSteps q N) < 1 := by
    have he := oddSteps_of_itin h (k*q)
    rw [mech_sum, (rep k).2] at he
    have heR := congrArg (fun z : ℤ => (z : ℝ)) he
    push_cast at heR
    have h0 := Int.floor_le ((k*q : ℕ)*α+ρ)
    have h1 := Int.lt_floor_add_one ((k*q : ℕ)*α+ρ)
    have h2 := Int.floor_le ρ
    have h3 := Int.lt_floor_add_one ρ
    push_cast at h0 h1
    constructor <;> nlinarith
  by_contra he
  have hn : (q : ℝ)*α-oddSteps q N ≠ 0 := sub_ne_zero.mpr he
  rcases lt_or_gt_of_ne hn with hn | hn
  · obtain ⟨k, hk⟩ := exists_nat_gt (1 / (-(q : ℝ)*α+oddSteps q N))
    have hp : 0 < -(q : ℝ)*α+oddSteps q N := by linarith
    have hm := (div_lt_iff₀ hp).mp hk
    have hh := (hb k).1
    nlinarith
  · obtain ⟨k, hk⟩ := exists_nat_gt (1 / ((q : ℝ)*α-oddSteps q N))
    have hm := (div_lt_iff₀ hn).mp hk
    have hh := (hb k).2
    nlinarith

/-- No natural Collatz seed has a mechanical itinerary of irrational slope,
for any real intercept. -/
theorem no_irrational_mechanical {α : ℝ} (hα : Irrational α) (ρ : ℝ) (N : ℕ) :
    ¬ HasItin α ρ N := by
  intro hit
  obtain ⟨B, hB⟩ := bounded_of_mechanical hit
  have hm : Set.MapsTo (fun t => terras_iter t N) (Finset.range (B+2)) (Finset.range (B+1)) := by
    intro t _
    apply Finset.mem_range.mpr
    change terras_iter t N < B+1
    have := hB t
    omega
  obtain ⟨a, _, b, _, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simp : (Finset.range (B+1)).card < (Finset.range (B+2)).card) hm
  have contradiction (a b : ℕ) (hab : a < b) (he : terras_iter a N = terras_iter b N) : False := by
    have hr : terras_iter (b-a) (terras_iter a N) = terras_iter a N := by
      rw [terras_iter_add, Nat.add_sub_of_le (by omega)]
      exact he.symm
    have hs := mechanical_return_slope (hit.shift a) hr
    exact (hα.natCast_mul (show b-a ≠ 0 by omega)).ne_int (oddSteps (b-a) (terras_iter a N))
      (by exact_mod_cast hs)
  rcases lt_or_gt_of_ne hne with hab | hab
  · exact contradiction a b hab he
  · exact contradiction b a hab he.symm

/-- The same exclusion applies to every tail. -/
theorem no_eventual_irrational_mechanical {α : ℝ} (hα : Irrational α)
    (ρ : ℝ) (N s : ℕ) : ¬ HasItin α ρ (terras_iter s N) :=
  no_irrational_mechanical hα ρ (terras_iter s N)

end Collatz
