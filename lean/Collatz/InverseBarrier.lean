import Collatz.NoncontractingTail
import Collatz.Cylinder
import Collatz.Cycles

/-! A three-adic obstruction to bounded-odd-count backward exclusions.
The result does not construct a noncontracting natural seed. -/
namespace Collatz

/-- The canonical residue endpoint lies strictly below its ternary scale. -/
theorem canonical_endpoint_lt_three_pow (t : ℕ) : ∀ n, n < 2^t →
    terras_iter t n < 3^oddSteps t n := by
  induction t with
  | zero => intro n hn; simp at hn; simp [hn, terras_iter, oddSteps]
  | succ t ih =>
    intro n hn
    let r := n % 2^t
    let q := n / 2^t
    have h2 : 0 < 2^t := by positivity
    have hr : r < 2^t := Nat.mod_lt _ h2
    have hq : q ≤ 1 := by
      dsimp [q]
      have := (Nat.div_lt_iff_lt_mul h2).mpr (show n < 2*2^t by simpa [pow_succ, Nat.mul_comm] using hn)
      omega
    have heq : n = r+2^t*q := (Nat.mod_add_div n (2^t)).symm
    have he := Cylinder.transport t r q
    rw [← heq] at he
    have hm : n ≡ r [MOD 2^t] := by
      dsimp [r]
      simp [Nat.ModEq]
    have ho := oddSteps_modEq t hm
    have hi := ih r hr
    have hv : terras_iter t n < 2*3^oddSteps t n := by
      rw [he, ho]
      have hh := Nat.mul_le_mul_left (3^oddSteps t r) hq
      omega
    have hadd := oddSteps_add t 1 n
    rw [terras_iter_succ']
    rcases Nat.mod_two_eq_zero_or_one (terras_iter t n) with hp | hp
    · have hb : oddSteps 1 (terras_iter t n) = 0 := by
        have hh : ¬ terras_iter t n % 2 = 1 := by omega
        simp [oddSteps, hh]
      rw [hb, Nat.add_zero] at hadd
      rw [hadd]
      simp only [Nat.add_zero]
      have hs := two_mul_terras_even (terras_iter t n) hp
      omega
    · have hb : oddSteps 1 (terras_iter t n) = 1 := by simp [oddSteps, hp]
      rw [hb] at hadd
      rw [hadd, pow_succ]
      have hs := two_mul_terras_odd (terras_iter t n) hp
      omega

/-- A segment with a noncontracting final coefficient cannot end in the
class one modulo its full ternary odd-count scale. -/
theorem noncontracting_endpoint_not_one_mod {t n : ℕ} (ht : 0 < t)
    (hc : 2^t ≤ 3^oddSteps t n) :
    ¬ terras_iter t n ≡ 1 [MOD 3^oddSteps t n] := by
  intro hend
  let r := n % 2^t
  have hr : r < 2^t := Nat.mod_lt _ (by positivity)
  have hm : n ≡ r [MOD 2^t] := by dsimp [r]; simp [Nat.ModEq]
  have ho := oddSteps_modEq t hm
  have hb := canonical_endpoint_lt_three_pow t r hr
  have hs := shadow_modEq hm
  have h2 : 2 ≤ 2^t := by
    calc 2 = 2^1 := rfl
         _ ≤ 2^t := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : 1 < 3^oddSteps t n := by omega
  have hemod := hs.symm.trans hend
  have he : terras_iter t r = 1 := by
    rw [ho] at hemod h3
    have heq := hemod.eq_of_lt_of_lt hb h3
    exact heq
  have hzero : ∀ k, terras_iter k 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simpa [terras_iter, terras] using ih
  have hrpos : 0 < r := by
    by_contra hh
    have hz : r = 0 := by omega
    rw [hz, hzero] at he
    omega
  have hex := terras_exact_form t r
  rw [he] at hex
  rw [ho] at hc
  have hm' := Nat.mul_le_mul_right r hc
  have hrle : r ≤ 1 := by nlinarith only [hex, hm', h2]
  have hr1 : r = 1 := by omega
  have hcycle := cycle_three_pow_lt t r (by omega) (by omega) (by simpa [hr1] using he)
  omega

/-- At any fixed odd-count budget K, the entire class one modulo 3^K
has no positive-length predecessor segment with a noncontracting final
coefficient and at most K odd steps. There is no bound on segment length. -/
theorem bounded_odd_inverse_obstruction {K t n y : ℕ} (hy : y ≡ 1 [MOD 3^K])
    (ht : 0 < t) (hj : oddSteps t n ≤ K) (he : terras_iter t n = y) :
    3^oddSteps t n < 2^t := by
  by_contra hc
  have hm : y ≡ 1 [MOD 3^oddSteps t n] :=
    Nat.ModEq.of_dvd (Nat.pow_dvd_pow 3 hj) hy
  exact noncontracting_endpoint_not_one_mod (n := n) ht (by omega) (by simpa [he] using hm)

/-- No noncontracting predecessor can reach this residue class within
K odd steps, regardless of the total number of steps. -/
theorem no_noncontracting_predecessor_of_one_mod {K t n y : ℕ}
    (hy : y ≡ 1 [MOD 3^K]) (ht : 0 < t) (hj : oddSteps t n ≤ K)
    (he : terras_iter t n = y) : ¬ NeverContracts n := by
  intro hh
  have hc := bounded_odd_inverse_obstruction hy ht hj he
  have := hh t
  omega

/-- The bounded-odd-count obstruction occurs at arbitrarily large targets
outside multiples of three. These targets are not asserted noncontracting. -/
theorem arbitrarily_large_inverse_obstructions (K B : ℕ) :
    ∃ y, B < y ∧ y % 3 = 1 ∧
      ∀ n t, 0 < t → oddSteps t n ≤ K → terras_iter t n = y → ¬ NeverContracts n := by
  let y := 1+3^(K+1)*(B+1)
  have hp : 0 < 3^(K+1) := by positivity
  have hB : B < y := by dsimp [y]; nlinarith only [hp]
  have h3 : y % 3 = 1 := by simp [y, pow_succ, Nat.add_mod, Nat.mul_mod]
  have hm : y ≡ 1 [MOD 3^K] := by
    dsimp [y]
    rw [pow_succ]
    simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  exact ⟨y, hB, h3, fun n t ht hj he => no_noncontracting_predecessor_of_one_mod hm ht hj he⟩

end Collatz
