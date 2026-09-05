import Collatz.WordAffine
import Collatz.Paradoxical

/-! Exact arithmetic compatibility for a finite parity word. These criteria
retain the correction and seed jointly; no uniform exhaustion is asserted. -/
namespace Collatz.WordAffine

/-- Integrality of the affine endpoint already forces every parity in the word. -/
theorem realizes_iff_dvd (n : ℕ) (w : List Bool) :
    Realizes n w ↔ 2^w.length ∣ 3^ones w*n + correction w := by
  constructor
  · intro h
    exact ⟨terras_iter w.length n, (exact_form h).symm⟩
  · induction w generalizing n with
    | nil => simp [Realizes]
    | cons b w ih =>
      intro h
      have htwo : 2 ∣ 3^ones (b::w)*n + correction (b::w) :=
        dvd_trans (by simp [List.length_cons, pow_succ]) h
      have hp := (Nat.dvd_iff_mod_eq_zero).mp htwo
      have h3 : 3^ones w % 2 = 1 := by simp [Nat.pow_mod]
      cases b
      · have hn : n % 2 = 0 := by
          simpa [ones, correction, Nat.add_mod, Nat.mul_mod, h3] using hp
        refine ⟨hn, ih (terras n) ?_⟩
        have he : n = 2 * terras n := by
          simp [terras, hn]
          omega
        simp only [ones, correction, Bool.false_eq_true, ↓reduceIte,
          zero_add, List.length_cons, pow_succ] at h
        rw [he] at h
        have heq : 3^ones w*(2*terras n)+2*correction w =
            (3^ones w*terras n+correction w)*2 := by ring
        rw [heq] at h
        exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 2)).mp h
      · have hn : n % 2 = 1 := by
          simp [ones, correction, pow_add, Nat.add_mod, Nat.mul_mod, h3] at hp
          omega
        refine ⟨hn, ih (terras n) ?_⟩
        have he : 3*n+1 = 2*terras n := by
          simp [terras, hn]
          omega
        simp only [ones, correction, ↓reduceIte, List.length_cons, pow_succ] at h
        have heq : 3^(1+ones w)*n+(3^ones w+2*correction w) =
            (3^ones w*terras n+correction w)*2 := by
          rw [pow_add]
          simp only [pow_one]
          nlinarith [congrArg (fun x => 3^ones w*x) he]
        rw [heq] at h
        exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 2)).mp h

/-- Exact joint test: the correction must be large enough and compatible
with the seed modulo the full power of two. -/
theorem realizes_paradoxical_iff (n : ℕ) (w : List Bool) :
    (Realizes n w ∧ IsParadoxical w.length n) ↔
      0 < n ∧ 3^ones w < 2^w.length ∧
      2^w.length ∣ 3^ones w*n + correction w ∧
      (2^w.length-3^ones w)*n ≤ correction w := by
  constructor
  · rintro ⟨hr, hp, he, hc⟩
    rw [← realizes_ones hr] at hc
    refine ⟨hp, hc, (realizes_iff_dvd n w).mp hr, ?_⟩
    have hx := exact_form hr
    have hs := Nat.sub_add_cancel (Nat.le_of_lt hc)
    nlinarith [Nat.mul_le_mul_left (2^w.length) he]
  · rintro ⟨hp, hc, hd, hb⟩
    have hr := (realizes_iff_dvd n w).mpr hd
    refine ⟨hr, hp, ?_, ?_⟩
    · have hx := exact_form hr
      have hs := Nat.sub_add_cancel (Nat.le_of_lt hc)
      have hpos : 0 < 2^w.length := by positivity
      nlinarith
    · rwa [← realizes_ones hr]

end Collatz.WordAffine
