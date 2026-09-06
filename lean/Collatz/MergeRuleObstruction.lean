import Collatz.MergeRuleTable

/-! Exact congruence gaps in the current finite table. These results are
about the listed rules, not about all possible noncontracting merges. -/
namespace Collatz.MergeRuleObstruction

def modulus : ℕ := 46438023168

/-- Binary residue -1 modulo 2^18, and ternary residues
3^k / 2^k - 1 modulo 3^11, for k=0,...,11. The last is stationary
for every larger k. Division here is modular inversion. -/
def classes : List ℕ := [42120773631, 16743137279, 25114705919,
  14453047295, 21679570943, 9300344831, 13950517247, 44144787455,
  42998169599, 41278242815, 15479341055, 46438023167]

def inverseOdd : MergeRule := ⟨2, 1, 0, 1, 3, 1⟩

def step (r : MergeRule) : ℕ := 2^r.forwardTime*r.seedQuotientStep

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked : MergeRuleTable.rules.all (fun r => decide
    (step r ∣ modulus ∧ ∀ c ∈ classes,
      r = inverseOdd ∨ c % step r ≠ r.seed % step r)) = true := by decide

/-- On any of the twelve entire congruence classes, the only listed rule
that can apply is the one-step inverse odd rule. -/
theorem only_inverse_odd {r : MergeRule} (hr : r ∈ MergeRuleTable.rules)
    {n c Q : ℕ} (hc : c ∈ classes) (hn : n ≡ c [MOD modulus])
    (he : n = r.original Q) : r = inverseOdd := by
  have hh := of_decide_eq_true ((List.all_eq_true.mp checked) r hr)
  obtain ⟨hd, hclasses⟩ := hh
  rcases hclasses c hc with h | h
  · exact h
  · exfalso
    have hmod := Nat.ModEq.of_dvd hd hn
    have hseed : r.original Q ≡ r.seed [MOD step r] := by
      simp [MergeRule.original, step, Nat.ModEq, ← Nat.mul_assoc]
    rw [he] at hmod
    exact h (hmod.symm.trans hseed)

/-- The initial class admits no listed rule, even at arbitrarily large
quotients. The other eleven classes can only undo an odd step. -/
theorem no_rule_on_initial_class {n : ℕ}
    (hn : n ≡ 42120773631 [MOD modulus]) :
    ∀ r ∈ MergeRuleTable.rules, ∀ Q, n ≠ r.original Q := by
  intro r hr Q he
  have hc : 42120773631 ∈ classes := by decide
  have hh := only_inverse_odd hr hc hn he
  rw [hh] at he
  have h3 : n ≡ 42120773631 [MOD 3] :=
    Nat.ModEq.of_dvd (by decide : 3 ∣ modulus) hn
  rw [he] at h3
  norm_num [Nat.ModEq, inverseOdd, MergeRule.original, Nat.add_mod, Nat.mul_mod] at h3

end Collatz.MergeRuleObstruction
