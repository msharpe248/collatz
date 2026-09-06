import Collatz.Density

/-! Exact counterexamples to treating divided Collatz maps as same-precision
residue maps. These do not rule out maps with extra input precision. -/
namespace Collatz.ResidueMapAudit

/-- Two gap inputs congruent modulo 32 have different outputs modulo 32. -/
theorem gap_precision_witness :
    3 % 32 = 35 % 32 ∧ 3 % 4 = 3 ∧ 35 % 4 = 3 ∧
    terras 3 % 32 = 5 ∧ terras 35 % 32 = 21 := by decide

/-- There is no same-precision residue function representing every gap step. -/
theorem no_gap_map_mod32 :
    ¬ ∃ f : ℕ → ℕ, ∀ n, n % 4 = 3 → terras n % 32 = f (n % 32) := by
  rintro ⟨f, hf⟩
  have h3 := hf 3 (by decide)
  have h35 := hf 35 (by decide)
  norm_num [terras] at h3 h35
  omega

/-- Retaining the quotient explains the lost input bit explicitly. -/
theorem gap_lift_formula (q : ℕ) : terras (3+32*q) = 5+48*q := by
  have h := two_mul_terras_odd (3+32*q) (by omega)
  omega

/-- A burst residue modulo 32 does not fix its gap image modulo 8. -/
theorem burst_precision_witness :
    29 % 32 = 61 % 32 ∧ 29 % 4 = 1 ∧ 61 % 4 = 1 ∧
    syracuse 29 = 11 ∧ syracuse 61 = 23 ∧
    syracuse 29 % 8 = 3 ∧ syracuse 61 % 8 = 7 := by norm_num [syracuse, v2]

/-- Explicit canonical-representative counts at input depth five. -/
theorem canonical_burst_counts_32 :
    ((List.range 32).filter (fun n => n % 4 == 1 && syracuse n % 8 == 3)).length = 2 ∧
    ((List.range 32).filter (fun n => n % 4 == 1 && syracuse n % 8 == 7)).length = 1 := by
  have h1 : syracuse 1 = 1 := by norm_num [syracuse, v2]
  have h5 : syracuse 5 = 1 := by norm_num [syracuse, v2]
  have h9 : syracuse 9 = 7 := by norm_num [syracuse, v2]
  have h13 : syracuse 13 = 5 := by norm_num [syracuse, v2]
  have h17 : syracuse 17 = 13 := by norm_num [syracuse, v2]
  have h21 : syracuse 21 = 1 := by norm_num [syracuse, v2]
  have h25 : syracuse 25 = 19 := by norm_num [syracuse, v2]
  have h29 : syracuse 29 = 11 := by norm_num [syracuse, v2]
  norm_num [List.range_succ, List.filter_cons, h1, h5, h9, h13, h17, h21, h25, h29]

end Collatz.ResidueMapAudit
