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

/-- Remaining even-step allowance before reaching two modulo nine. -/
private def residueHeight (n : ℕ) : ℕ :=
  if n % 9 = 1 then 5 else if n % 9 = 5 then 4 else
  if n % 9 = 7 then 3 else if n % 9 = 8 then 2 else
  if n % 9 = 4 then 1 else 0

set_option maxHeartbeats 1600000 in
private theorem residueHeight_step {n : ℕ} (hn : n % 3 ≠ 0)
    (h2 : n % 9 ≠ 2) :
    (if n % 2 = 0 then 1 else 0) + residueHeight (terras n) ≤ residueHeight n := by
  have hr := Nat.mod_lt n (by omega : 0 < 9)
  have hs := Nat.mod_lt (terras n) (by omega : 0 < 9)
  interval_cases hnr : n % 9 <;> interval_cases hns : terras n % 9 <;>
    rcases residue_edge n with ⟨he, heq⟩ | ⟨he, heq⟩ <;>
    simp [residueHeight, hnr, hns, he] <;> omega

private theorem even_steps_before_hit (t : ℕ) : ∀ n, n % 3 ≠ 0 →
    (∀ s < t, terras_iter s n % 9 ≠ 2) →
    t + residueHeight (terras_iter t n) ≤ oddSteps t n + residueHeight n := by
  induction t with
  | zero => intro n hn ha; simp [terras_iter, oddSteps]
  | succ t ih =>
    intro n hn ha
    have h2 := ha 0 (by omega)
    change n % 9 ≠ 2 at h2
    have hedge := residueHeight_step hn h2
    have htail : ∀ s < t, terras_iter s (terras n) % 9 ≠ 2 := by
      intro s hs
      exact ha (s+1) (by omega)
    have hh := ih (terras n) (terras_mod_three_ne_zero hn) htail
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · rw [oddSteps_succ_even t n he]
      simp only [he, if_pos] at hedge
      change t+1 + residueHeight (terras_iter t (terras n)) ≤ _
      omega
    · rw [oddSteps_succ_odd t n ho]
      simp only [ho, Nat.one_ne_zero, if_false, zero_add] at hedge
      change t+1 + residueHeight (terras_iter t (terras n)) ≤ _
      omega

/-- At most six even steps occur before the next visit to two modulo nine.
The total length and number of odd steps need not be bounded. -/
theorem even_steps_between_two_mod_nine {n t : ℕ} (hn : n % 9 = 2)
    (ha : ∀ s, 0 < s → s < t → terras_iter s n % 9 ≠ 2) :
    t ≤ oddSteps t n + 6 := by
  cases t with
  | zero => omega
  | succ t =>
    have h3 : n % 3 ≠ 0 := by omega
    have htail : ∀ s < t, terras_iter s (terras n) % 9 ≠ 2 := by
      intro s hs
      exact ha (s+1) (by omega) (by omega)
    have hh := even_steps_before_hit t (terras n) (terras_mod_three_ne_zero h3) htail
    have hb : residueHeight (terras n) ≤ 5 := by
      unfold residueHeight
      split_ifs <;> omega
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · rw [oddSteps_succ_even t n he]; omega
    · rw [oddSteps_succ_odd t n ho]; omega

private theorem eleven_odds_dominate_six_evens (j : ℕ) (hj : 11 ≤ j) :
    64 * 2^j < 3^j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih => simp only [pow_succ]; omega

/-- A contracting segment before the next residue-two visit has length
at most sixteen. In particular this applies to a contracting first return. -/
theorem contracting_two_mod_nine_segment_le_sixteen {n t : ℕ}
    (hn : n % 9 = 2)
    (ha : ∀ s, 0 < s → s < t → terras_iter s n % 9 ≠ 2)
    (hc : 3^oddSteps t n < 2^t) : t ≤ 16 := by
  have hb := even_steps_between_two_mod_nine hn ha
  have hj : oddSteps t n < 11 := by
    by_contra hh
    have hg := eleven_odds_dominate_six_evens (oddSteps t n) (by omega)
    have hp : 2^t ≤ 2^(oddSteps t n + 6) := Nat.pow_le_pow_right (by omega) hb
    rw [pow_add] at hp
    norm_num at hp
    omega
  omega

/-- The sixteen-step upper bound is attained by an actual first return. -/
theorem contracting_return_sixteen_sharp :
    147440 % 9 = 2 ∧
    (∀ s : Fin 16, 0 < s.val → terras_iter s.val 147440 % 9 ≠ 2) ∧
    terras_iter 16 147440 = 132860 ∧ 132860 % 9 = 2 ∧
    oddSteps 16 147440 = 10 ∧ 3^10 < (2:ℕ)^16 := by decide

set_option maxRecDepth 100000 in
private theorem return_growth_table : ∀ t j : Fin 17, j.val ≤ t.val →
    3^j.val < (2:ℕ)^t.val →
    3^j.val * (573 + 2^(t.val-j.val)) < (2:ℕ)^t.val * 574 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_return_table : ∀ n : Fin 573, n.val % 9 = 2 → 2 < n.val →
    ∀ t : Fin 17,
    (∀ s : Fin 17, 0 < s.val → s.val < t.val → terras_iter s.val n.val % 9 ≠ 2) →
    3^oddSteps t.val n.val < (2:ℕ)^t.val → terras_iter t.val n.val < n.val := by decide

/-- Every coefficient-contracting segment before the next residue-two visit
strictly descends for seeds above two. This includes every contracting first
return and has no seed-height or time cutoff in its hypotheses. -/
theorem contracting_two_mod_nine_segment_descends {n t : ℕ}
    (hn : n % 9 = 2) (hn2 : 2 < n)
    (ha : ∀ s, 0 < s → s < t → terras_iter s n % 9 ≠ 2)
    (hc : 3^oddSteps t n < 2^t) : terras_iter t n < n := by
  have ht := contracting_two_mod_nine_segment_le_sixteen hn ha hc
  by_cases hsmall : n < 573
  · exact small_return_table ⟨n, hsmall⟩ hn hn2 ⟨t, by omega⟩
      (fun s hs hst => ha s.val hs hst) hc
  · have hj := oddSteps_le t n
    have hb := return_growth_table ⟨t, by omega⟩ ⟨oddSteps t n, by omega⟩ hj hc
    dsimp at hb
    have hg := terras_growth_bound t n
    by_contra hnd
    have hx : n ≤ terras_iter t n := by omega
    have hn573 : 573 ≤ n := by omega
    have hs := Nat.sub_add_cancel hn573
    have hm := Nat.mul_le_mul_left (n-573) hc.le
    have hxmul := Nat.mul_le_mul_left (2^t) hx
    nlinarith

end Collatz
