import Collatz.Density

/-! Growth bounds for arbitrary interleavings of forward Collatz steps and
auxiliary x ↦ 9x+2 bridges. No convergence or bridge admissibility is assumed. -/
namespace Collatz.BridgeGrowth

/-- e is twice the total increment of the symbolic exponent p; t counts
ordinary steps. Bridge admissibility is relaxed, strengthening exclusions. -/
inductive Path : ℕ → ℕ → ℕ → ℕ → Prop
  | refl (n : ℕ) : Path n n 0 0
  | even {n x t e : ℕ} : Path n x t e → x % 2 = 0 →
      Path n (terras x) (t+1) e
  | odd {n x t e : ℕ} : Path n x t e → x % 2 = 1 →
      Path n (terras x) (t+1) (e+2)
  | bridge {n x t e : ℕ} : Path n x t e → Path n (9*x+2) t (e+4)

theorem Path.pos {n x t e : ℕ} (h : Path n x t e) (hn : 0<n) : 0<x := by
  induction h with
  | refl => exact hn
  | even h hp ih => exact terras_pos _ ih
  | odd h hp ih => exact terras_pos _ ih
  | bridge h ih => omega

/-- A universal upper size bound for the mixed path. -/
theorem Path.growth_bound {n x t e : ℕ} (h : Path n x t e) (hn : 0<n) :
    2^t*x ≤ 2^e*n := by
  induction h with
  | refl => simp
  | @even x t e h hp ih =>
    have hs := two_mul_terras_even x hp
    calc
      2^(t+1)*terras x = 2^t*(2*terras x) := by rw [pow_succ]; ring
      _ = 2^t*x := by rw [hs]
      _ ≤ 2^e*n := ih
  | @odd x t e h hp ih =>
    have hx := h.pos hn
    have hs := two_mul_terras_odd x hp
    have hb : 2*terras x ≤ 4*x := by omega
    calc
      2^(t+1)*terras x = 2^t*(2*terras x) := by rw [pow_succ]; ring
      _ ≤ 2^t*(4*x) := Nat.mul_le_mul_left _ hb
      _ = 4*(2^t*x) := by ring
      _ ≤ 4*(2^e*n) := Nat.mul_le_mul_left _ ih
      _ = 2^(e+2)*n := by rw [pow_add]; ring
  | @bridge x t e h ih =>
    have hx := h.pos hn
    have hb : 9*x+2 ≤ 16*x := by omega
    calc
      2^t*(9*x+2) ≤ 2^t*(16*x) := Nat.mul_le_mul_left _ hb
      _ = 16*(2^t*x) := by ring
      _ ≤ 16*(2^e*n) := Nat.mul_le_mul_left _ ih
      _ = 2^(e+4)*n := by rw [pow_add]; ring

/-- Arbitrarily interleaved bridges cannot lower cycle charge. -/
theorem Path.cycle_charge_nondecrease {n x t e : ℕ} (h : Path n x t e)
    (hn : n=1 ∨ n=2) (hx : x=1 ∨ x=2) :
    t+(if n=1 then 1 else 0) ≤ e+(if x=1 then 1 else 0) := by
  have hb := h.growth_bound (by omega : 0<n)
  rcases hn with rfl | rfl <;> rcases hx with rfl | rfl
  · simp only [mul_one] at hb
    have he := (Nat.pow_le_pow_iff_right (by norm_num : 1<2)).mp hb
    simpa using he
  · have hh : 2^(t+1) ≤ 2^e := by simpa only [pow_succ, mul_one] using hb
    have he := (Nat.pow_le_pow_iff_right (by norm_num : 1<2)).mp hh
    simpa using he
  · have hh : 2^t ≤ 2^(e+1) := by simpa only [pow_succ, mul_one] using hb
    have he := (Nat.pow_le_pow_iff_right (by norm_num : 1<2)).mp hh
    simpa using he
  · have hh : 2^t ≤ 2^e := by omega
    have he := (Nat.pow_le_pow_iff_right (by norm_num : 1<2)).mp hh
    simpa using he

end Collatz.BridgeGrowth
