import Collatz.MechanicalComplexity
import Collatz.EndpointCycles
import Mathlib.Data.List.Rotate

/-! Exact transport from mechanical periods and word rotations to natural
orbit returns. Rational periods are actual returns, not merely bounds. -/
namespace Collatz

theorem mech_period_of_integral {α ρ : ℝ} {q : ℕ} {p : ℤ}
    (hp : (q : ℝ)*α = p) (t : ℕ) : mech α ρ (q+t) = mech α ρ t := by
  have he (z : ℝ) : ((q : ℝ)+z)*α+ρ = (z*α+ρ)+(p : ℝ) := by
    nlinarith only [hp]
  unfold mech
  push_cast
  rw [show ((q : ℝ)+(t : ℝ)+1)*α+ρ = ((q : ℝ)+((t : ℝ)+1))*α+ρ by ring,
    he, he, Int.floor_add_intCast, Int.floor_add_intCast]
  ring

/-- Every integral slope increment is an actual return period for a
natural mechanical itinerary, without a boundedness hypothesis. -/
theorem mechanical_period_return {α ρ : ℝ} {N q : ℕ} {p : ℤ}
    (h : HasItin α ρ N) (hp : (q : ℝ)*α = p) : terras_iter q N = N := by
  apply eq_of_itinerary_eq
  intro t
  rw [terras_iter_add]
  have hs := h (q+t)
  rw [mech_period_of_integral hp] at hs
  exact_mod_cast hs.trans (h t).symm

/-- The denominator of a rational mechanical itinerary is an actual return
period at its initial natural seed. -/
theorem rational_mechanical_return (p : ℤ) {q : ℕ} (hq : 0 < q)
    {ρ : ℝ} {N : ℕ} (h : HasItin ((p : ℝ)/q) ρ N) : terras_iter q N = N := by
  apply mechanical_period_return h (p := p)
  have hqR : (q : ℝ) ≠ 0 := by positivity
  field_simp

namespace WordAffine

theorem realizes_iff_getElem (n : ℕ) (w : List Bool) :
    Realizes n w ↔ ∀ i (hi : i < w.length), terras_iter i n % 2 = if w[i] then 1 else 0 := by
  induction w generalizing n with
  | nil => simp [Realizes]
  | cons b w ih =>
    constructor
    · rintro ⟨hb, hw⟩ i hi
      cases i with
      | zero => simpa [terras_iter] using hb
      | succ i =>
        have hh := (ih (terras n)).mp hw i (by simpa using hi)
        simpa [terras_iter] using hh
    · intro h
      refine ⟨?_, (ih (terras n)).mpr ?_⟩
      · simpa [terras_iter] using h 0 (by simp)
      · intro i hi
        simpa [terras_iter] using h (i+1) (by simpa using hi)

/-- A rotated return word is realized at the correspondingly shifted state. -/
theorem realizes_rotate_of_return {n : ℕ} {w : List Bool} (h : Realizes n w)
    (hr : terras_iter w.length n = n) (s : ℕ) :
    Realizes (terras_iter s n) (w.rotate s) := by
  apply (realizes_iff_getElem _ _).mpr
  intro i hi
  have hlen : i < w.length := by simpa using hi
  have hwpos : 0 < w.length := by omega
  have himod : (s+i) % w.length < w.length := Nat.mod_lt _ hwpos
  have hh := (realizes_iff_getElem n w).mp h ((s+i) % w.length) himod
  have hp : terras_iter (s+i) n = terras_iter ((s+i) % w.length) n := by
    have he := orbit_pump hr ((s+i)/w.length) ((s+i)%w.length)
    have hdiv := Nat.div_add_mod (s+i) w.length
    simpa only [Nat.mul_comm, hdiv] using he
  rw [terras_iter_add, hp, hh, List.getElem_rotate]
  simp [Nat.add_comm]

/-- Endpoint-swapped rotations form a structural certificate for the
trivial cycle, expressed directly in actual-orbit language. -/
theorem endpoint_rotations_trivial {n : ℕ} {w u : List Bool} {a b : ℕ}
    (h : Realizes n w) (hr : terras_iter w.length n = n)
    (ha : w.rotate a = true :: (u ++ [false]))
    (hb : w.rotate b = false :: (u ++ [true])) :
    u = [] ∧ terras_iter a n = 1 ∧ terras_iter b n = 2 := by
  have hx := realizes_rotate_of_return h hr a
  have hy := realizes_rotate_of_return h hr b
  rw [ha] at hx
  rw [hb] at hy
  have hl : w.length = u.length+2 := by
    have he := congrArg List.length ha
    simpa using he
  have hs (s : ℕ) : terras_iter (u.length+2) (terras_iter s n) = terras_iter s n := by
    rw [← hl, terras_iter_add, Nat.add_comm s, ← terras_iter_add, hr]
  exact endpoint_returns_trivial hx hy (hs a) (hs b)

end WordAffine
end Collatz
