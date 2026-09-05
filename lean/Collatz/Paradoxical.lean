import Collatz.Cylinder

/-! Exact finite-length paradoxical cylinders, following the definition in
Rozier and Terracol, arXiv:2502.00948. No finiteness across all lengths is
asserted, and no external computational records are assumed. -/
namespace Collatz

/-- A positive seed whose endpoint does not descend despite a contracting
multiplicative coefficient. Intermediate descent is allowed. -/
def IsParadoxical (T n : ℕ) : Prop :=
  0 < n ∧ n ≤ terras_iter T n ∧ 3^oddSteps T n < 2^T

instance (T n : ℕ) : Decidable (IsParadoxical T n) :=
  inferInstanceAs (Decidable (0 < n ∧ n ≤ terras_iter T n ∧ 3^oddSteps T n < 2^T))

/-- Exact quotient test for every natural lift of a contracting cylinder. -/
theorem paradoxical_lift_iff (T r q : ℕ) (hc : 3^oddSteps T r < 2^T) :
    IsParadoxical T (r+2^T*q) ↔
      0 < r+2^T*q ∧ r+(2^T-3^oddSteps T r)*q ≤ terras_iter T r := by
  have hm : r+2^T*q ≡ r [MOD 2^T] := by simp [Nat.ModEq]
  have ho := oddSteps_modEq T hm
  have hs : 2^T-3^oddSteps T r+3^oddSteps T r = 2^T := Nat.sub_add_cancel (by omega)
  rw [IsParadoxical, ho, Cylinder.transport]
  constructor
  · rintro ⟨hp, he, _⟩
    refine ⟨hp, ?_⟩
    nlinarith
  · rintro ⟨hp, he⟩
    refine ⟨hp, ?_, hc⟩
    nlinarith

/-- The full quotient interval has an explicit upper endpoint, without a
seed-height cutoff. The separate r≤endpoint condition prevents truncated
natural subtraction from introducing a spurious q=0 solution. -/
theorem paradoxical_quotient_interval (T r q : ℕ) (hc : 3^oddSteps T r < 2^T) :
    IsParadoxical T (r+2^T*q) ↔
      0 < r+2^T*q ∧ r ≤ terras_iter T r ∧
        q ≤ (terras_iter T r-r)/(2^T-3^oddSteps T r) := by
  rw [paradoxical_lift_iff T r q hc]
  have hd : 0 < 2^T-3^oddSteps T r := by omega
  rw [Nat.le_div_iff_mul_le hd]
  constructor
  · rintro ⟨hp, he⟩
    refine ⟨hp, by omega, ?_⟩
    nlinarith [Nat.sub_add_cancel (show r ≤ terras_iter T r by omega)]
  · rintro ⟨hp, hr, he⟩
    refine ⟨hp, ?_⟩
    nlinarith [Nat.sub_add_cancel hr]

/-- Every seed belongs to its unique canonical residue cylinder. -/
theorem paradoxical_residue_iff (T n : ℕ) :
    IsParadoxical T n ↔
      0 < n ∧ 3^oddSteps T (n % 2^T) < 2^T ∧
      n % 2^T + (2^T-3^oddSteps T (n % 2^T))*(n / 2^T) ≤
        terras_iter T (n % 2^T) := by
  have he : n % 2^T + 2^T*(n/2^T) = n := Nat.mod_add_div n (2^T)
  have hm : n ≡ n % 2^T [MOD 2^T] := by simp [Nat.ModEq]
  have ho := oddSteps_modEq T hm
  constructor
  · intro h
    have hc : 3^oddSteps T (n % 2^T) < 2^T := by simpa [ho] using h.2.2
    have hl := (paradoxical_lift_iff T (n % 2^T) (n/2^T) hc).mp (he.symm ▸ h)
    exact ⟨h.1, hc, hl.2⟩
  · rintro ⟨hp, hc, hl⟩
    rw [← he]
    exact (paradoxical_lift_iff T (n % 2^T) (n/2^T) hc).mpr ⟨by simpa [he], hl⟩

set_option maxRecDepth 4096 in
private theorem eight_residue_table : ∀ i : Fin 256, let r : ℕ := i.val;
    3^oddSteps 8 r < 256 → r ≤ terras_iter 8 r →
      terras_iter 8 r-r < 256-3^oddSteps 8 r ∧
      (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 7 ∨ r = 9 ∨ r = 18 ∨ r = 19 ∨ r = 25) := by
  decide

/-- Complete classification at length eight, for all seeds above two.
This reproduces a small known case; it is not an all-length finiteness result. -/
theorem paradoxical_eight_iff {n : ℕ} (hn : 2 < n) :
    IsParadoxical 8 n ↔ n = 7 ∨ n = 9 ∨ n = 18 ∨ n = 19 ∨ n = 25 := by
  constructor
  · intro hp
    have hr : n % 256 < 256 := Nat.mod_lt n (by omega)
    have he := (paradoxical_residue_iff 8 n).mp hp
    norm_num only [show (2 : ℕ)^8 = 256 from rfl] at he
    have hlow : n % 256 ≤ terras_iter 8 (n % 256) := by omega
    obtain ⟨hsmall, hcases⟩ := eight_residue_table ⟨n % 256, hr⟩ he.2.1 hlow
    dsimp at hsmall hcases
    have hd : 0 < 256-3^oddSteps 8 (n % 256) := by omega
    have hq : n / 256 = 0 := by
      have hsub := Nat.sub_add_cancel hlow
      have hmul : (256-3^oddSteps 8 (n % 256))*(n/256) <
          256-3^oddSteps 8 (n % 256) := by omega
      by_contra hq
      have hge : 1 ≤ n / 256 := by omega
      have := Nat.mul_le_mul_left (256-3^oddSteps 8 (n % 256)) hge
      omega
    have hnmod : n % 256 = n := by have := Nat.mod_add_div n 256; omega
    rw [hnmod] at hcases
    omega
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

example : IsParadoxical 8 7 := by decide
example : terras_iter 7 7 < 7 := by decide
example : ¬ IsParadoxical 0 7 := by decide

end Collatz
