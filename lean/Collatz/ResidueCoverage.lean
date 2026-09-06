import Collatz.IdealBarrier
import Collatz.ResidueCorrection

/-! Forward coverage of 2 modulo 9 (Monks et al., arXiv:1204.3904,
Corollary 5.8). Coverage does not preserve coefficient noncontraction. -/
namespace Collatz

private theorem residue_edge (n : ℕ) :
    (n % 2 = 0 ∧ 2 * terras n = n) ∨
    (n % 2 = 1 ∧ 2 * terras n = 3*n+1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact Or.inl ⟨h, two_mul_terras_even n h⟩
  · exact Or.inr ⟨h, two_mul_terras_odd n h⟩

set_option maxHeartbeats 800000 in
private theorem residue_graph {n : ℕ} (hn : n % 3 ≠ 0) :
    (n % 9 = 1 ∧ (terras n % 9 = 5 ∨ terras n % 9 = 2)) ∨
    (n % 9 = 2 ∧ (terras n % 9 = 1 ∨ terras n % 9 = 8)) ∨
    (n % 9 = 4 ∧ terras n % 9 = 2) ∨
    (n % 9 = 5 ∧ (terras n % 9 = 7 ∨ terras n % 9 = 8)) ∨
    (n % 9 = 7 ∧ (terras n % 9 = 8 ∨ terras n % 9 = 2)) ∨
    (n % 9 = 8 ∧ (terras n % 9 = 4 ∨ terras n % 9 = 8)) := by
  have hb : n % 9 < 9 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 9 <;> rcases residue_edge n with he | he <;> omega

private theorem avoidance_forces_eight {n : ℕ} (hn : n % 3 ≠ 0)
    (h : ∀ t, terras_iter t n % 9 ≠ 2) :
    terras_iter 3 n % 9 = 8 := by
  have hg (t : ℕ) := residue_graph (orbit_mod_three_ne_zero hn t)
  have g0 := hg 0
  have g1 := hg 1
  have g2 := hg 2
  have g3 := hg 3
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp only [terras_iter] at g0 g1 g2 g3 h0 h1 h2 h3 h4 ⊢
  omega

/-- Every positive natural orbit visits the residue 2 modulo 9. -/
theorem exists_two_mod_nine (n : ℕ) (hn : 0 < n) :
    ∃ t, terras_iter t n % 9 = 2 := by
  obtain ⟨s, hs⟩ := exists_tail_mod_three_ne_zero n hn
  by_contra h
  push_neg at h
  have ha (k t : ℕ) : terras_iter t (terras_iter k n) % 9 ≠ 2 := by
    simpa only [terras_iter_add] using h (k+t)
  have he (k : ℕ) : terras_iter (s+k+3) n % 9 = 8 := by
    have hz := orbit_mod_three_ne_zero hs k
    rw [terras_iter_add] at hz
    simpa only [terras_iter_add] using avoidance_forces_eight hz (ha (s+k))
  obtain ⟨t, ht⟩ := exists_even_value (terras_iter (s+3) n)
  rw [terras_iter_add] at ht
  have h8 := he t
  have h8next := he (t+1)
  have hedge := two_mul_terras_even (terras_iter (s+3+t) n) ht
  have hnext : terras (terras_iter (s+3+t) n) = terras_iter (s+(t+1)+3) n := by
    rw [← terras_iter_succ']
    congr 1; omega
  rw [hnext] at hedge
  have hind : s+t+3 = s+3+t := by omega
  rw [hind] at h8
  omega

/-- Apply coverage to any tail, without assuming boundedness. -/
theorem arbitrarily_late_two_mod_nine (n : ℕ) (hn : 0 < n) (K : ℕ) :
    ∃ t, K ≤ t ∧ terras_iter t n % 9 = 2 := by
  obtain ⟨t, ht⟩ := exists_two_mod_nine (terras_iter K n) (terras_iter_pos K n hn)
  exact ⟨K+t, by omega, by simpa only [terras_iter_add] using ht⟩

/-- Convergence on this progression would suffice for the full conjecture.
The premise remains open. -/
theorem reaches_one_of_two_mod_nine
    (h : ∀ n, 0 < n → n % 9 = 2 → ∃ t, terras_iter t n = 1)
    (n : ℕ) (hn : 0 < n) : ∃ t, terras_iter t n = 1 := by
  obtain ⟨s, hs⟩ := exists_two_mod_nine n hn
  obtain ⟨t, ht⟩ := h (terras_iter s n) (terras_iter_pos s n hn) hs
  exact ⟨s+t, by simpa only [terras_iter_add] using ht⟩

end Collatz
