import Collatz.WordSurgery

/-! Unequal-length merging can preserve full noncontraction when its
replacement prefix dominates the original coefficient. No global coverage
claim is made. -/
namespace Collatz

/-- Transfer full noncontraction across unequal-length merging paths.
The replacement prefix must be noncontracting and its final coefficient
must dominate that of the original prefix. The original shifted tail
itself need not be noncontracting. -/
theorem neverContracts_of_dominating_merge {n x s t : ℕ}
    (hn : NeverContracts n)
    (hp : ∀ i ≤ s, 2^i ≤ 3^oddSteps i x)
    (he : terras_iter s x = terras_iter t n)
    (hc : 2^s*3^oddSteps t n ≤ 2^t*3^oddSteps s x) : NeverContracts x := by
  intro i
  by_cases hi : i ≤ s
  · exact hp i hi
  · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (show s ≤ i by omega)
    have hh := hn (t+v)
    rw [oddSteps_add, pow_add, pow_add] at hh
    rw [oddSteps_add, pow_add, pow_add, he]
    apply Nat.le_of_mul_le_mul_left (c := 3^oddSteps t n) ?_ (by positivity)
    calc
      3^oddSteps t n*(2^s*2^v) = (2^s*3^oddSteps t n)*2^v := by ring
      _ ≤ (2^t*3^oddSteps s x)*2^v := Nat.mul_le_mul_right _ hc
      _ = 3^oddSteps s x*(2^t*2^v) := by ring
      _ ≤ 3^oddSteps s x*(3^oddSteps t n*3^oddSteps v (terras_iter t n)) :=
        Nat.mul_le_mul_left _ hh
      _ = 3^oddSteps t n*(3^oddSteps s x*3^oddSteps v (terras_iter t n)) := by ring

set_option maxRecDepth 100000 in
private theorem prefix_103 : ∀ i : Fin 13, 2^i.val ≤ 3^oddSteps i.val 103 := by decide

/-- A variable-length merging family with a dominating noncontracting
replacement prefix. Every starting seed in the displayed family is a
multiple of three; the meeting is after one forward step. -/
theorem dominating_merge_111_family (Q : ℕ) :
    0 < 103+4096*Q ∧ 103+4096*Q < 111+4374*Q ∧
    terras_iter 12 (103+4096*Q) = terras_iter 1 (111+4374*Q) ∧
    oddSteps 12 (103+4096*Q) = 8 ∧ oddSteps 1 (111+4374*Q) = 1 ∧
    (∀ i ≤ 12, 2^i ≤ 3^oddSteps i (103+4096*Q)) := by
  have hm : 103+4096*Q ≡ 103 [MOD 2^12] := by
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  have ho := oddSteps_modEq 12 hm
  have hx := Cylinder.transport 12 103 Q
  have hn := Cylinder.transport 1 111 (2187*Q)
  have hmn : 111+4374*Q ≡ 111 [MOD 2^1] := by
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  have hon := oddSteps_modEq 1 hmn
  norm_num only [show terras_iter 12 103 = 167 from rfl,
    show oddSteps 12 103 = 8 from rfl,
    show terras_iter 1 111 = 167 from rfl,
    show oddSteps 1 111 = 1 from rfl, Nat.reducePow] at hx hn ho hon
  have hn' : terras_iter 1 (111+4374*Q) = 167+6561*Q := by
    have harg : 111+2*(2187*Q) = 111+4374*Q := by ring
    rw [harg] at hn
    calc
      terras_iter 1 (111+4374*Q) = 167+3*(2187*Q) := hn
      _ = 167+6561*Q := by ring
  refine ⟨by omega, by omega, by omega, ho, hon, ?_⟩
  intro i hi
  have hmi := Nat.ModEq.of_dvd (Nat.pow_dvd_pow 2 hi) hm
  rw [oddSteps_modEq i hmi]
  exact prefix_103 ⟨i, by omega⟩

/-- Each member of this progression, if noncontracting, has a smaller
positive noncontracting merging predecessor. No such seed is constructed. -/
theorem NeverContracts.smaller_merge_111 {Q : ℕ}
    (hn : NeverContracts (111+4374*Q)) :
    0 < 103+4096*Q ∧ 103+4096*Q < 111+4374*Q ∧
      NeverContracts (103+4096*Q) := by
  obtain ⟨hp, hlt, he, hx, ht, hpre⟩ := dominating_merge_111_family Q
  refine ⟨hp, hlt, neverContracts_of_dominating_merge hn hpre he ?_⟩
  rw [hx, ht]
  norm_num

end Collatz
