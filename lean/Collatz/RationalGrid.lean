import Collatz.MechanicalPeriod

/-! Finite modular coding for rational mechanical words. -/
namespace Collatz.RationalGrid

/-- The carry bit for adding p at phase r modulo q. -/
def bit (p q r t : ℕ) : Bool := decide (q ≤ (t*p+r)%q+p)

/-- A coprime rational rotation visits every residue, from any initial phase. -/
theorem phase_surjective {p q : ℕ} (hq : 0 < q) (hc : Nat.Coprime q p)
    (r z : ℕ) (hz : z < q) : ∃ s, s < q ∧ (s*p+r)%q = z := by
  let f : Fin q → Fin q := fun s => ⟨(s.val*p+r)%q, Nat.mod_lt _ hq⟩
  have hi : Function.Injective f := by
    intro a b he
    have hm : a.val*p+r ≡ b.val*p+r [MOD q] := congrArg Fin.val he
    have hm' : a.val*p ≡ b.val*p [MOD q] := Nat.ModEq.add_right_cancel (Nat.ModEq.refl r) hm
    have hab : a.val ≡ b.val [MOD q] := hm'.cancel_right_of_coprime hc
    apply Fin.ext
    simpa [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hab
  obtain ⟨s, hs⟩ := (Finite.surjective_of_injective hi) ⟨z, hz⟩
  exact ⟨s.val, s.isLt, congrArg Fin.val hs⟩

theorem bit_shift (p q r s t : ℕ) :
    bit p q r (s+t) = bit p q ((s*p+r)%q) t := by
  unfold bit
  congr 2
  rw [show (s+t)*p+r = t*p+(s*p+r) by ring]
  simp [Nat.add_mod]

theorem bit_period (p q r t : ℕ) : bit p q r (q+t) = bit p q r t := by
  unfold bit
  simp [Nat.add_mul, Nat.add_mod, Nat.mul_mod]

private theorem residue_nonzero {p q i : ℕ} (hc : Nat.Coprime q p)
    (hi : 0 < i) (hiq : i < q) : (i*p)%q ≠ 0 := by
  intro he
  have hd : q ∣ i*p := Nat.dvd_of_mod_eq_zero he
  have hdi : q ∣ i := hc.dvd_of_dvd_mul_right hd
  have hh := Nat.le_of_dvd hi hdi
  omega

private theorem upper_residue {q a : ℕ} (h0 : 0 < a) (h1 : a < q) :
    (a+(q-1))%q = a-1 := by
  have he : a+(q-1) = q+(a-1) := by omega
  rw [he, Nat.add_mod]
  simp [Nat.mod_eq_of_lt (show a-1 < q by omega)]

/-- The two extreme phases give equal interior letters. -/
theorem extreme_interior {p q i : ℕ} (hpq : p < q)
    (hc : Nat.Coprime q p) (hi : 0 < i) (hiq : i+1 < q) :
    bit p q (q-1) i = bit p q 0 i := by
  have hq : 0 < q := by omega
  let a := (i*p)%q
  have ha0 : 0 < a := by have := residue_nonzero hc hi (by omega : i < q); omega
  have haq : a < q := Nat.mod_lt _ hq
  have hn := residue_nonzero hc (by omega : 0 < i+1) hiq
  have hne : a+p ≠ q := by
    intro he
    apply hn
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mod]
    change (a+p%q)%q = 0
    rw [Nat.mod_eq_of_lt hpq, he, Nat.mod_self]
  unfold bit
  have hh : (i*p+(q-1))%q = a-1 := by
    rw [Nat.add_mod]
    change (a+(q-1)%q)%q = a-1
    rw [Nat.mod_eq_of_lt (by omega : q-1 < q), upper_residue ha0 haq]
  rw [hh, Nat.add_zero]
  change decide (q ≤ a-1+p) = decide (q ≤ a+p)
  apply decide_eq_decide.mpr
  omega

/-- The low extreme phase starts with zero; the high one starts with one. -/
theorem extreme_first {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    bit p q 0 0 = false ∧ bit p q (q-1) 0 = true := by
  simp only [bit, Nat.zero_mul, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (by omega : q-1 < q)]
  constructor <;> simp <;> omega

/-- At the last position of a period, the extreme endpoint letters swap. -/
theorem extreme_last {p q : ℕ} (hp : 0 < p) (hpq : p < q) :
    bit p q 0 (q-1) = true ∧ bit p q (q-1) (q-1) = false := by
  have hq : 0 < q := by omega
  let a := ((q-1)*p)%q
  have haq : a < q := Nat.mod_lt _ hq
  have he : (q-1)*p+p = q*p := by nlinarith only [Nat.sub_add_cancel (show 1 ≤ q by omega), hp]
  have hm := congrArg (fun n => n%q) he
  dsimp only at hm
  rw [Nat.add_mod, Nat.mod_eq_of_lt hpq, Nat.mul_mod_right] at hm
  change (a+p)%q=0 at hm
  have hl : q ≤ a+p := by
    by_contra hn
    rw [Nat.mod_eq_of_lt (by omega : a+p < q)] at hm
    omega
  have hhmod := Nat.mod_eq_sub_mod hl
  have hap : a+p = q := by
    rw [Nat.mod_eq_of_lt (by omega : a+p-q < q), hm] at hhmod
    omega
  have ha0 : 0 < a := by omega
  have hh : ((q-1)*p+(q-1))%q = a-1 := by
    rw [Nat.add_mod]
    change (a+(q-1)%q)%q = a-1
    rw [Nat.mod_eq_of_lt (by omega : q-1 < q), upper_residue ha0 haq]
  simp only [bit, Nat.add_zero, hh]
  change decide (q ≤ a+p) = true ∧ decide (q ≤ a-1+p) = false
  constructor <;> simp <;> omega

/-- One full period of the modular carry coding. -/
def word (p q r : ℕ) : List Bool := List.ofFn (fun i : Fin q => bit p q r i.val)

/-- The extreme phases have the endpoint-swapped form, uniformly in the
reduced numerator and denominator. -/
theorem extreme_words {p q : ℕ} (hp : 0 < p) (hpq : p < q) (hc : Nat.Coprime q p) :
    ∃ u, word p q (q-1) = true :: (u ++ [false]) ∧
      word p q 0 = false :: (u ++ [true]) := by
  obtain ⟨k, hk⟩ : ∃ k, q = k+2 := ⟨q-2, by omega⟩
  subst q
  let u := List.ofFn (fun i : Fin k => bit p (k+2) 0 (i.val+1))
  refine ⟨u, ?_, ?_⟩
  · unfold word
    rw [List.ofFn_succ, List.ofFn_succ']
    have hfirst := (extreme_first hp hpq).2
    have hlast := (extreme_last hp hpq).2
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_last, Fin.val_castSucc]
    rw [hfirst, show k+1 = k+2-1 by omega, hlast]
    congr 1
    rw [List.concat_eq_append]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact extreme_interior hpq hc (by omega) (by omega)
  · unfold word
    rw [List.ofFn_succ, List.ofFn_succ']
    have hfirst := (extreme_first hp hpq).1
    have hlast := (extreme_last hp hpq).1
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_last, Fin.val_castSucc]
    rw [hfirst, show k+1 = k+2-1 by omega, hlast]
    simp only [List.concat_eq_append]
    rfl

/-- An actual itinerary following the rational grid. -/
def HasGrid (p q r N : ℕ) : Prop :=
  ∀ t, terras_iter t N % 2 = if bit p q r t then 1 else 0

theorem HasGrid.shift {p q r N : ℕ} (h : HasGrid p q r N) (s : ℕ) :
    HasGrid p q ((s*p+r)%q) (terras_iter s N) := by
  intro t
  rw [terras_iter_add, h (s+t), bit_shift]

theorem HasGrid.returns {p q r N : ℕ} (h : HasGrid p q r N) : terras_iter q N = N := by
  apply eq_of_itinerary_eq
  intro t
  rw [terras_iter_add, h (q+t), h t, bit_period]

theorem HasGrid.realizes {p q r N : ℕ} (h : HasGrid p q r N) :
    WordAffine.Realizes N (word p q r) := by
  apply (WordAffine.realizes_iff_getElem _ _).mpr
  intro i hi
  simpa [word] using h i

/-- Every reduced rational grid itinerary reaches 1. This includes all
integer phases and supplies a uniform, rather than enumerated, exclusion. -/
theorem grid_reaches_one {p q r N : ℕ} (hp : 0 < p) (hpq : p < q)
    (hc : Nat.Coprime q p) (h : HasGrid p q r N) : ∃ t, terras_iter t N = 1 := by
  have hq : 0 < q := by omega
  obtain ⟨a, _, ha⟩ := phase_surjective hq hc r (q-1) (by omega)
  obtain ⟨b, _, hb⟩ := phase_surjective hq hc r 0 hq
  have hx := h.shift a
  have hy := h.shift b
  rw [ha] at hx
  rw [hb] at hy
  obtain ⟨u, hu, hv⟩ := extreme_words hp hpq hc
  have hxr := hx.realizes
  have hyr := hy.realizes
  rw [hu] at hxr
  rw [hv] at hyr
  have hlen : q = u.length+2 := by
    have hh := congrArg List.length hu
    simpa [word] using hh
  have hrx := hx.returns
  have hry := hy.returns
  rw [hlen] at hrx hry
  have hh := WordAffine.endpoint_returns_trivial hxr hyr hrx hry
  exact ⟨a, hh.2.1⟩

end Collatz.RationalGrid
