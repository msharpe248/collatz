import Collatz.ParadoxicalPruning

/-! Limitation of the current unconstrained-suffix pruning envelope.
Every fixed prefix eventually passes its necessary envelope test. This is
not a claim that it has any actual paradoxical completion. -/
namespace Collatz.WordAffine

private theorem enough_odd_budget (m : ℕ) :
    (m+1)*2^(2*m) ≤ 3^(2*m) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have he : 2*(m+1) = 2*m+2 := by ring
    rw [he, pow_add, pow_add]
    norm_num
    nlinarith [Nat.mul_le_mul_left 9 ih, Nat.zero_le (m*2^(2*m)), Nat.zero_le (2^(2*m))]

/-- For a fixed prefix and seed floor, sufficiently long target lengths
always admit an odd-count budget that the present envelope cannot prune.
The parameters need not arise from an actual orbit. -/
theorem completion_envelope_survives (s a D m L : ℕ)
    (hL : s+2*(a+2*m)+1 ≤ L) :
    ∃ k, k ≤ L-s ∧
      3^(a+k) < 2^L ∧
      (2^L-3^(a+k))*m ≤ 3^k*D + 2^(L-k)*(3^k-2^k) := by
  refine ⟨2*m, by omega, ?_, ?_⟩
  · have hpow : 3^(a+2*m) ≤ (2^2)^(a+2*m) :=
      Nat.pow_le_pow_left (by norm_num) _
    rw [← pow_mul] at hpow
    exact hpow.trans_lt (Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega))
  · have hbudget := enough_odd_budget m
    have hp : 2^(2*m) ≤ 3^(2*m) := Nat.pow_le_pow_left (by omega) _
    have hsub := Nat.sub_add_cancel hp
    have hmass : m*2^(2*m) ≤ 3^(2*m)-2^(2*m) := by nlinarith
    have hm := Nat.mul_le_mul_left (2^(L-2*m)) hmass
    have he : 2^(L-2*m)*2^(2*m) = 2^L := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : 2*m ≤ L)]
    have hmass' : 2^L*m ≤ 2^(L-2*m)*(3^(2*m)-2^(2*m)) := by
      calc 2^L*m = 2^(L-2*m)*(m*2^(2*m)) := by rw [← he]; ring
           _ ≤ _ := hm
    have hd : 2^L-3^(a+2*m) ≤ 2^L := Nat.sub_le _ _
    exact (Nat.mul_le_mul_right m hd).trans (hmass'.trans (Nat.le_add_left _ _))

/-- Existential form of the explicit eventual-survival threshold. -/
theorem completion_envelope_eventually_survives (s a D m : ℕ) :
    ∃ L₀, ∀ L, L₀ ≤ L → ∃ k, k ≤ L-s ∧
      3^(a+k) < 2^L ∧
      (2^L-3^(a+k))*m ≤ 3^k*D + 2^(L-k)*(3^k-2^k) :=
  ⟨s+2*(a+2*m)+1, fun L hL => completion_envelope_survives s a D m L hL⟩

/-- Any finite collection of fixed prefix envelopes simultaneously survives
all sufficiently large target lengths. This rules out closure by such a
fixed collection of relaxed tests, not by richer arithmetic tests. -/
theorem finite_envelopes_eventually_survive {ι : Type*} (S : Finset ι)
    (s a D m : ι → ℕ) :
    ∃ L₀, ∀ i ∈ S, ∀ L, L₀ ≤ L → ∃ k, k ≤ L-s i ∧
      3^(a i+k) < 2^L ∧
      (2^L-3^(a i+k))*m i ≤ 3^k*D i + 2^(L-k)*(3^k-2^k) := by
  refine ⟨S.sup (fun i => s i+2*(a i+2*m i)+1), ?_⟩
  intro i hi L hL
  exact completion_envelope_survives (s i) (a i) (D i) (m i) L
    ((Finset.le_sup (f := fun i => s i+2*(a i+2*m i)+1) hi).trans hL)

/-- Applied to a real finite word, the obstruction still concerns only the
relaxed envelope, not realizability of any suffix. -/
theorem prefix_envelope_eventually_survives (u : List Bool) (m : ℕ) :
    ∃ L₀, ∀ L, L₀ ≤ L → ∃ k, k ≤ L-u.length ∧
      3^(ones u+k) < 2^L ∧
      (2^L-3^(ones u+k))*m ≤
        3^k*correction u + 2^(L-k)*(3^k-2^k) :=
  completion_envelope_eventually_survives u.length (ones u) (correction u) m

end Collatz.WordAffine
