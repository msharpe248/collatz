import Collatz.PrefixPower

/-! Quantitative near-periodicity certificates. Few shift disagreements over
a sufficiently long finite interval force an exact return. The resulting
cycle need not be the trivial Collatz cycle. -/

namespace Collatz

theorem terras_iter_height (N s : ℕ) :
    terras_iter s N + 1 ≤ 2 ^ s * (N + 1) := by
  have step (n : ℕ) : terras n + 1 ≤ 2 * (n + 1) := by
    unfold terras
    split <;> omega
  induction s with
  | zero => simp [terras_iter]
  | succ s ih =>
    rw [terras_iter_succ', pow_succ]
    have h := step (terras_iter s N)
    nlinarith

/-- If a tail does not return after q steps, a q-shift parity disagreement
must occur within a window whose length is linear in its starting time. -/
theorem return_or_parity_defect (N s q K : ℕ) (hN : N + 1 ≤ 2 ^ K) :
    terras_iter (s + q) N = terras_iter s N ∨
    ∃ t, s ≤ t ∧ t < 2 * s + (q + K) ∧
      terras_iter t N % 2 ≠ terras_iter (t + q) N % 2 := by
  by_cases hret : terras_iter (s + q) N = terras_iter s N
  · exact Or.inl hret
  right
  by_contra h
  have hagree : ∀ t, t + q < q + (s + q + K) →
      terras_iter t (terras_iter s N) % 2 =
        terras_iter (t + q) (terras_iter s N) % 2 := by
    intro t ht
    have he : terras_iter (s + t) N % 2 = terras_iter (s + t + q) N % 2 := by
      by_contra hne
      exact h ⟨s + t, by omega, by omega, hne⟩
    rw [terras_iter_add, terras_iter_add]
    convert he using 2
    congr 1
    omega
  have hpow := prefix_power (terras_iter s N) q (q + (s + q + K))
    (by omega) hagree
  rcases hpow with hcycle | hlarge
  · apply hret
    rwa [terras_iter_add] at hcycle
  · have height (u : ℕ) : terras_iter u N < 2 ^ (u + K) := by
      have h1 := terras_iter_height N u
      have h2 := Nat.mul_le_mul_left (2 ^ u) hN
      rw [← pow_add] at h2
      omega
    have hleft : terras_iter s N < 2 ^ (s + q + K) := by
      exact (height s).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hright := height (s + q)
    rw [terras_iter_add] at hlarge
    have he : q + (s + q + K) - q = s + q + K := by omega
    rw [he] at hlarge
    exact (not_le_of_gt (max_lt hleft hright)) hlarge

/-- A positive-period return gives a finite bound for the entire orbit,
including the initial segment before the return. -/
theorem return_bounds_orbit {N s q : ℕ} (hq : 0 < q)
    (hret : terras_iter (s + q) N = terras_iter s N) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  refine ⟨(Finset.range (s + q)).sup (fun i => terras_iter i N), ?_⟩
  have hper (j : ℕ) : terras_iter (s + q + j) N = terras_iter (s + j) N := by
    rw [← terras_iter_add, hret, terras_iter_add]
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t < s + q
    · exact Finset.le_sup (f := fun i => terras_iter i N) (Finset.mem_range.mpr ht)
    · have he : terras_iter t N = terras_iter (t - q) N := by
        convert hper (t - (s + q)) using 1 <;> congr 1 <;> omega
      rw [he]
      exact ih (t - q) (by omega)

namespace ParityDefects

/-- Checkpoints with disjoint windows [checkpoint k, checkpoint (k+1)). -/
def checkpoint (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * checkpoint A k + A

theorem checkpoint_formula (A k : ℕ) :
    checkpoint A k + A = 2 ^ k * A := by
  induction k with
  | zero => simp [checkpoint]
  | succ k ih => simp only [checkpoint, pow_succ]; nlinarith

theorem checkpoint_mono (A : ℕ) : Monotone (checkpoint A) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [checkpoint]
  omega

def defectSet (N q L : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun t => terras_iter t N % 2 ≠ terras_iter (t + q) N % 2)

def count (N q L : ℕ) : ℕ := (defectSet N q L).card

theorem count_mono (N q : ℕ) : Monotone (count N q) := by
  intro L M hLM
  apply Finset.card_le_card
  intro t ht
  simp only [defectSet, Finset.mem_filter, Finset.mem_range] at ht ⊢
  exact ⟨lt_of_lt_of_le ht.1 hLM, ht.2⟩

/-- Each checkpoint that fails to return contributes a different defect. -/
theorem count_ge_of_no_checkpoint_return (N q K D : ℕ) (hN : N + 1 ≤ 2 ^ K)
    (hret : ∀ k < D,
      terras_iter (checkpoint (q + K) k + q) N ≠ terras_iter (checkpoint (q + K) k) N) :
    D ≤ count N q (checkpoint (q + K) D) := by
  induction D with
  | zero => omega
  | succ D ih =>
    have hprev := ih (fun k hk => hret k (by omega))
    obtain ⟨t, htlo, hthi, hdef⟩ :=
      (return_or_parity_defect N (checkpoint (q + K) D) q K hN).resolve_left
        (hret D (by omega))
    have htnew : t ∉ defectSet N q (checkpoint (q + K) D) := by
      simp only [defectSet, Finset.mem_filter, Finset.mem_range]
      omega
    have hsub : insert t (defectSet N q (checkpoint (q + K) D)) ⊆
        defectSet N q (checkpoint (q + K) (D + 1)) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hthi, hdef⟩
      · simp only [defectSet, Finset.mem_filter, Finset.mem_range] at hx ⊢
        exact ⟨lt_of_lt_of_le hx.1 (checkpoint_mono _ (by omega)), hx.2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem htnew] at hc
    change D ≤ (defectSet N q (checkpoint (q + K) D)).card at hprev
    change D + 1 ≤ (defectSet N q (checkpoint (q + K) (D + 1))).card
    omega

/-- A finite certificate of an exact return: at most D disagreements over
(2^(D+1)-1)(q+K) comparisons force a q-step return at one of D+1 checkpoints.
The theorem does not identify the resulting cycle as the trivial one. -/
theorem few_defects_force_return (N q K D L : ℕ) (hN : N + 1 ≤ 2 ^ K)
    (hL : checkpoint (q + K) (D + 1) ≤ L) (hD : count N q L ≤ D) :
    ∃ k, k ≤ D ∧ terras_iter (checkpoint (q + K) k + q) N =
      terras_iter (checkpoint (q + K) k) N := by
  by_contra h
  have hn : ∀ k < D + 1,
      terras_iter (checkpoint (q + K) k + q) N ≠ terras_iter (checkpoint (q + K) k) N := by
    intro k hk he
    exact h ⟨k, by omega, he⟩
  have hlarge := count_ge_of_no_checkpoint_return N q K (D + 1) hN hn
  have hmono := count_mono N q hL
  omega

theorem few_defects_bound_orbit (N q K D L : ℕ) (hq : 0 < q)
    (hN : N + 1 ≤ 2 ^ K) (hL : checkpoint (q + K) (D + 1) ≤ L)
    (hD : count N q L ≤ D) : ∃ B, ∀ t, terras_iter t N ≤ B := by
  obtain ⟨k, _, hret⟩ := few_defects_force_return N q K D L hN hL hD
  exact return_bounds_orbit hq hret

def templateErrors (N : ℕ) (w : ℕ → ℕ) (M : ℕ) : Finset ℕ :=
  (Finset.range M).filter (fun t => terras_iter t N % 2 ≠ w t)

/-- Each edited letter can cause at most two shift disagreements. The
template need only be q-periodic on the finite interval being checked. -/
theorem count_le_twice_template_errors (N q L : ℕ) (w : ℕ → ℕ)
    (hper : ∀ t < L, w (t + q) = w t) :
    count N q L ≤ 2 * (templateErrors N w (L + q)).card := by
  let E := templateErrors N w (L + q)
  have hsub : defectSet N q L ⊆ E ∪ E.image (fun t => t - q) := by
    intro t ht
    obtain ⟨htL, hdef⟩ := Finset.mem_filter.mp ht
    have htlt : t < L := Finset.mem_range.mp htL
    by_cases hbad : terras_iter t N % 2 ≠ w t
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbad⟩)
    · have heq : terras_iter t N % 2 = w t := by omega
      have hbad' : terras_iter (t + q) N % 2 ≠ w (t + q) := by
        rw [hper t htlt, ← heq]
        exact Ne.symm hdef
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨t + q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbad'⟩,
        by omega⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le E (E.image (fun t => t - q))
  have h3 := Finset.card_image_le (s := E) (f := fun t => t - q)
  change (defectSet N q L).card ≤ 2 * E.card
  omega

/-- A finite parity prefix within e letter edits of a q-periodic template
forces a return if it is long enough. No edit positions or density assumptions
are imposed. This is a cycle certificate, not a universal Collatz proof. -/
theorem near_power_force_return (N q K e L : ℕ) (w : ℕ → ℕ)
    (hN : N + 1 ≤ 2 ^ K)
    (hL : checkpoint (q + K) (2 * e + 1) ≤ L)
    (hper : ∀ t < L, w (t + q) = w t)
    (herr : (templateErrors N w (L + q)).card ≤ e) :
    ∃ k, k ≤ 2 * e ∧ terras_iter (checkpoint (q + K) k + q) N =
      terras_iter (checkpoint (q + K) k) N := by
  apply few_defects_force_return N q K (2 * e) L hN hL
  exact (count_le_twice_template_errors N q L w hper).trans (by omega)

theorem near_power_bound_orbit (N q K e L : ℕ) (w : ℕ → ℕ) (hq : 0 < q)
    (hN : N + 1 ≤ 2 ^ K)
    (hL : checkpoint (q + K) (2 * e + 1) ≤ L)
    (hper : ∀ t < L, w (t + q) = w t)
    (herr : (templateErrors N w (L + q)).card ≤ e) :
    ∃ B, ∀ t, terras_iter t N ≤ B := by
  obtain ⟨k, _, hret⟩ := near_power_force_return N q K e L w hN hL hper herr
  exact return_bounds_orbit hq hret

theorem unbounded_forces_defects (N q K D : ℕ) (hq : 0 < q)
    (hN : N + 1 ≤ 2 ^ K) (hunb : ∀ B, ∃ t, B < terras_iter t N) :
    D < count N q (checkpoint (q + K) (D + 1)) := by
  by_contra h
  obtain ⟨B, hB⟩ := few_defects_bound_orbit N q K D
    (checkpoint (q + K) (D + 1)) hq hN (le_refl _) (by omega)
  obtain ⟨t, ht⟩ := hunb B
  have := hB t
  omega

theorem two_step_return_trivial {n : ℕ} (hn : 0 < n)
    (hret : terras_iter 2 n = n) : n = 1 ∨ n = 2 := by
  simp only [terras_iter, terras] at hret
  split_ifs at hret <;> omega

/-- For period two the cycle ambiguity disappears: a positive orbit with
the finite defect certificate actually reaches one. -/
theorem few_defects_two_reaches_one (N K D L : ℕ) (hpos : 0 < N)
    (hN : N + 1 ≤ 2 ^ K) (hL : checkpoint (2 + K) (D + 1) ≤ L)
    (hD : count N 2 L ≤ D) : ∃ t, terras_iter t N = 1 := by
  obtain ⟨k, _, hret⟩ := few_defects_force_return N 2 K D L hN hL hD
  let s := checkpoint (2 + K) k
  have hper : terras_iter 2 (terras_iter s N) = terras_iter s N := by
    rwa [terras_iter_add]
  have hp := terras_iter_pos s N hpos
  rcases two_step_return_trivial hp hper with h1 | h2
  · exact ⟨s, h1⟩
  · refine ⟨s + 1, ?_⟩
    rw [terras_iter_succ', h2]
    rfl

theorem near_two_power_reaches_one (N K e L : ℕ) (w : ℕ → ℕ) (hpos : 0 < N)
    (hN : N + 1 ≤ 2 ^ K) (hL : checkpoint (2 + K) (2 * e + 1) ≤ L)
    (hper : ∀ t < L, w (t + 2) = w t)
    (herr : (templateErrors N w (L + 2)).card ≤ e) :
    ∃ t, terras_iter t N = 1 := by
  apply few_defects_two_reaches_one N K (2 * e) L hpos hN hL
  exact (count_le_twice_template_errors N 2 L w hper).trans (by omega)

end ParityDefects
end Collatz
