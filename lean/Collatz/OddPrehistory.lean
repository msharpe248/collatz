import Collatz.ResidueCorrection

/-! Finite odd histories do not delete further positive odd targets coprime
to three. This says nothing about which targets lie on an escaping orbit. -/
namespace Collatz

/-- Every positive odd value outside multiples of three has a larger odd
predecessor outside multiples of three, using three to six halving steps. -/
theorem larger_odd_predecessor {y : ℕ} (hy : 0 < y) (ho : y % 2 = 1)
    (h3 : y % 3 ≠ 0) :
    ∃ n a : ℕ, y < n ∧ n % 2 = 1 ∧ n % 3 ≠ 0 ∧
      3 ≤ a ∧ a ≤ 6 ∧ 3*n+1 = 2^a*y := by
  have hres : y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 4 ∨
      y % 9 = 5 ∨ y % 9 = 7 ∨ y % 9 = 8 := by omega
  rcases hres with h | h | h | h | h | h
  · refine ⟨(16*y-1)/3, 4, ?_⟩
    norm_num
    omega
  · refine ⟨(8*y-1)/3, 3, ?_⟩
    norm_num
    omega
  · refine ⟨(64*y-1)/3, 6, ?_⟩
    norm_num
    omega
  · refine ⟨(8*y-1)/3, 3, ?_⟩
    norm_num
    omega
  · refine ⟨(16*y-1)/3, 4, ?_⟩
    norm_num
    omega
  · refine ⟨(32*y-1)/3, 5, ?_⟩
    norm_num
    omega

private theorem even_block (k y : ℕ) :
    terras_iter k (2^k*y) = y ∧ oddSteps k (2^k*y) = 0 := by
  induction k with
  | zero => simp [terras_iter, oddSteps]
  | succ k ih =>
    have he : (2^(k+1)*y) % 2 = 0 := by simp [pow_succ, Nat.mul_mod]
    have hs : terras (2^(k+1)*y) = 2^k*y := by
      have hh := two_mul_terras_even (2^(k+1)*y) he
      rw [pow_succ] at hh ⊢
      nlinarith
    rw [terras_iter, oddSteps_succ_even _ _ he, hs]
    exact ih

/-- The predecessor equation gives one genuine accelerated odd step. -/
theorem odd_predecessor_segment {n y a : ℕ} (ho : n % 2 = 1)
    (ha : 0 < a) (he : 3*n+1 = 2^a*y) :
    terras_iter a n = y ∧ oddSteps a n = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have hs : terras n = 2^k*y := by
    have hh := two_mul_terras_odd n ho
    rw [he, pow_succ] at hh
    nlinarith
  rw [terras_iter, oddSteps_succ_odd _ _ ho, hs]
  have hh := even_block k y
  simp [hh.1, hh.2]

/-- Any allowed odd target has genuine histories of any prescribed odd-step
count, starting at larger positive seeds. The seed varies with the history. -/
theorem arbitrarily_long_odd_prehistory (K : ℕ) {y : ℕ} (hy : 0 < y)
    (ho : y % 2 = 1) (h3 : y % 3 ≠ 0) :
    ∃ n t : ℕ, y+K ≤ n ∧ n % 2 = 1 ∧ n % 3 ≠ 0 ∧
      3*K ≤ t ∧ t ≤ 6*K ∧ terras_iter t n = y ∧ oddSteps t n = K := by
  induction K generalizing y with
  | zero => exact ⟨y, 0, by omega, ho, h3, by omega, by omega, rfl, rfl⟩
  | succ K ih =>
    obtain ⟨p, a, hyp, hpo, hp3, ha, ha6, he⟩ := larger_odd_predecessor hy ho h3
    have hseg := odd_predecessor_segment hpo (by omega : 0 < a) he
    obtain ⟨n, t, hn, hno, hn3, ht, ht6, hend, hcount⟩ := ih (by omega : 0 < p) hpo hp3
    refine ⟨n, t+a, by omega, hno, hn3, by omega, by omega, ?_, ?_⟩
    · rw [← terras_iter_add, hend]
      exact hseg.1
    · rw [oddSteps_add, hend, hcount, hseg.2]

private theorem sibling_two_steps (n : ℕ) :
    terras_iter 2 (4*n+1) = 3*n+1 := by
  have hfirst : terras (4*n+1) = 6*n+2 := by
    have hh := two_mul_terras_odd (4*n+1) (by omega)
    omega
  have hsecond : terras (6*n+2) = 3*n+1 := by
    have hh := two_mul_terras_even (6*n+2) (by omega)
    omega
  simp only [terras_iter, hfirst, hsecond]

/-- Although every allowed odd target has long histories, an unbounded
orbit cannot contain both odd siblings whose forward paths merge. -/
theorem unbounded_excludes_odd_siblings {N n : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) (ho : n % 2 = 1) :
    ¬ ((∃ i, terras_iter i N = n) ∧ (∃ j, terras_iter j N = 4*n+1)) := by
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have heven : terras (3*n+1) = terras n := by
    have hh := two_mul_terras_even (3*n+1) (by omega)
    have hh' := two_mul_terras_odd n ho
    omega
  have hmerge : terras_iter (i+1) N = terras_iter (j+3) N := by
    rw [← terras_iter_add i 1, hi, ← terras_iter_add j 3, hj]
    rw [terras_iter_succ' 2, sibling_two_steps n, heven]
    rfl
  have ht := unbounded_orbit_injective h hmerge
  have hij : i = j+2 := by omega
  have hh : n = 3*n+1 := by
    rw [hij, ← terras_iter_add j 2, hj, sibling_two_steps n] at hi
    exact hi.symm
  omega

end Collatz
