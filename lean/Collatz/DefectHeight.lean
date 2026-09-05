import Collatz.ParityDefects

/-! Height-sensitive defect windows and a universal 3/5-bit growth bound.
These shorten finite certificates; no universal sparsity claim is made. -/

namespace Collatz

/-- The shifted shortcut map grows by at most 3/2 at each step. -/
theorem terras_iter_three_halves (N u : ℕ) :
    2 ^ u * (terras_iter u N + 1) ≤ 3 ^ u * (N + 1) := by
  have step (n : ℕ) : 2 * (terras n + 1) ≤ 3 * (n + 1) := by
    unfold terras
    split <;> omega
  induction u with
  | zero => simp [terras_iter]
  | succ u ih =>
    rw [terras_iter_succ', pow_succ, pow_succ]
    have h1 := Nat.mul_le_mul_left (2 ^ u) (step (terras_iter u N))
    have h2 := Nat.mul_le_mul_left 3 ih
    nlinarith

namespace ParityDefects

def growthBits (u : ℕ) : ℕ := (3 * u + 4) / 5

theorem growthBits_mono : Monotone growthBits := by
  intro i j hij
  unfold growthBits
  omega

theorem growthBits_le (u : ℕ) : growthBits u ≤ u := by
  unfold growthBits
  omega

theorem three_pow_le_growthBits (u : ℕ) : (3 : ℕ) ^ u ≤ 2 ^ (u + growthBits u) := by
  have hdiv : u = 5 * (u / 5) + u % 5 := by omega
  have hr : u % 5 < 5 := Nat.mod_lt _ (by decide)
  have hsmall : ∀ r : ℕ, r < 5 → (3 : ℕ) ^ r ≤ 2 ^ (r + growthBits r) := by
    intro r hr
    interval_cases r <;> norm_num [growthBits]
  have hbits : growthBits u = 3 * (u / 5) + growthBits (u % 5) := by
    unfold growthBits
    omega
  calc (3 : ℕ) ^ u = (3 ^ 5) ^ (u / 5) * 3 ^ (u % 5) := by
        rw [← pow_mul, ← pow_add, ← hdiv]
    _ ≤ (2 ^ 8) ^ (u / 5) * 2 ^ (u % 5 + growthBits (u % 5)) := by
        exact Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) _) (hsmall _ hr)
    _ = 2 ^ (u + growthBits u) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega

theorem height_from_growthBits (N K : ℕ) (hN : N + 1 ≤ 2 ^ K) (u : ℕ) :
    terras_iter u N < 2 ^ (growthBits u + K) := by
  have h1 := terras_iter_three_halves N u
  have h2 := Nat.mul_le_mul (three_pow_le_growthBits u) hN
  have h3 : 2 ^ u * (terras_iter u N + 1) ≤ 2 ^ u * 2 ^ (growthBits u + K) := by
    calc 2 ^ u * (terras_iter u N + 1) ≤ 2 ^ (u + growthBits u) * 2 ^ K := h1.trans h2
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have := Nat.le_of_mul_le_mul_left h3 (Nat.two_pow_pos u)
  omega

/-- Any monotone certified bit-height envelope supplies a defect window. -/
theorem return_or_defect_of_height (N s q : ℕ) (H : ℕ → ℕ)
    (hmono : Monotone H) (hheight : ∀ u, terras_iter u N < 2 ^ H u) :
    terras_iter (s + q) N = terras_iter s N ∨
    ∃ t, s ≤ t ∧ t < s + H (s + q) ∧
      terras_iter t N % 2 ≠ terras_iter (t + q) N % 2 := by
  by_cases hret : terras_iter (s + q) N = terras_iter s N
  · exact Or.inl hret
  right
  by_contra h
  have hagree : ∀ t, t + q < q + H (s + q) →
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
  rcases prefix_power (terras_iter s N) q (q + H (s + q)) (by omega) hagree with
    hcycle | hlarge
  · apply hret
    rwa [terras_iter_add] at hcycle
  · have hleft : terras_iter s N < 2 ^ H (s + q) :=
      (hheight s).trans_le (Nat.pow_le_pow_right (by decide) (hmono (by omega)))
    have hright := hheight (s + q)
    rw [terras_iter_add, Nat.add_sub_cancel_left] at hlarge
    exact (not_le_of_gt (max_lt hleft hright)) hlarge

def heightCheckpoint (H : ℕ → ℕ) (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => heightCheckpoint H q k + H (heightCheckpoint H q k + q)

theorem heightCheckpoint_mono (H : ℕ → ℕ) (q : ℕ) :
    Monotone (heightCheckpoint H q) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [heightCheckpoint]
  omega

theorem count_ge_of_height (N q D : ℕ) (H : ℕ → ℕ)
    (hmono : Monotone H) (hheight : ∀ u, terras_iter u N < 2 ^ H u)
    (hret : ∀ k < D, terras_iter (heightCheckpoint H q k + q) N ≠
      terras_iter (heightCheckpoint H q k) N) :
    D ≤ count N q (heightCheckpoint H q D) := by
  induction D with
  | zero => omega
  | succ D ih =>
    have hprev := ih (fun k hk => hret k (by omega))
    obtain ⟨t, htlo, hthi, hdef⟩ :=
      (return_or_defect_of_height N (heightCheckpoint H q D) q H hmono hheight).resolve_left
        (hret D (by omega))
    have htnew : t ∉ defectSet N q (heightCheckpoint H q D) := by
      simp only [defectSet, Finset.mem_filter, Finset.mem_range]
      omega
    have hsub : insert t (defectSet N q (heightCheckpoint H q D)) ⊆
        defectSet N q (heightCheckpoint H q (D + 1)) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hthi, hdef⟩
      · simp only [defectSet, Finset.mem_filter, Finset.mem_range] at hx ⊢
        exact ⟨lt_of_lt_of_le hx.1 (heightCheckpoint_mono H q (by omega)), hx.2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem htnew] at hc
    change D ≤ (defectSet N q (heightCheckpoint H q D)).card at hprev
    change D + 1 ≤ (defectSet N q (heightCheckpoint H q (D + 1))).card
    omega

theorem few_defects_return_of_height (N q D L : ℕ) (H : ℕ → ℕ)
    (hmono : Monotone H) (hheight : ∀ u, terras_iter u N < 2 ^ H u)
    (hL : heightCheckpoint H q (D + 1) ≤ L) (hD : count N q L ≤ D) :
    ∃ k, k ≤ D ∧ terras_iter (heightCheckpoint H q k + q) N =
      terras_iter (heightCheckpoint H q k) N := by
  by_contra h
  have hn : ∀ k < D + 1, terras_iter (heightCheckpoint H q k + q) N ≠
      terras_iter (heightCheckpoint H q k) N := by
    intro k hk he
    exact h ⟨k, by omega, he⟩
  have hlarge := count_ge_of_height N q (D + 1) H hmono hheight hn
  have hle := count_mono N q hL
  omega

def sharpCheckpoint (q K : ℕ) : ℕ → ℕ :=
  heightCheckpoint (fun u => growthBits u + K) q

theorem sharp_few_defects_force_return (N q K D L : ℕ) (hN : N + 1 ≤ 2 ^ K)
    (hL : sharpCheckpoint q K (D + 1) ≤ L) (hD : count N q L ≤ D) :
    ∃ k, k ≤ D ∧ terras_iter (sharpCheckpoint q K k + q) N =
      terras_iter (sharpCheckpoint q K k) N := by
  exact few_defects_return_of_height N q D L (fun u => growthBits u + K)
    (fun i j hij => Nat.add_le_add_right (growthBits_mono hij) K)
    (height_from_growthBits N K hN) hL hD

theorem sharpCheckpoint_le_old (q K k : ℕ) :
    sharpCheckpoint q K k ≤ checkpoint (q + K) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change sharpCheckpoint q K k + (growthBits (sharpCheckpoint q K k + q) + K) ≤
      2 * checkpoint (q + K) k + (q + K)
    have := growthBits_le (sharpCheckpoint q K k + q)
    omega

/-- Division-free geometric upper bound: the window growth base is 8/5.
The additive constant accounts for the integer ceiling. -/
theorem sharpCheckpoint_growth (q K k : ℕ) :
    5 ^ k * (3 * sharpCheckpoint q K k + (3 * q + 5 * K + 4)) ≤
      8 ^ k * (3 * q + 5 * K + 4) := by
  induction k with
  | zero => simp [sharpCheckpoint, heightCheckpoint]
  | succ k ih =>
    have hbits : 5 * growthBits (sharpCheckpoint q K k + q) ≤
        3 * (sharpCheckpoint q K k + q) + 4 := by unfold growthBits; omega
    have hstep : 5 * (3 * sharpCheckpoint q K (k + 1) + (3 * q + 5 * K + 4)) ≤
        8 * (3 * sharpCheckpoint q K k + (3 * q + 5 * K + 4)) := by
      change 5 * (3 * (sharpCheckpoint q K k +
        (growthBits (sharpCheckpoint q K k + q) + K)) + (3 * q + 5 * K + 4)) ≤ _
      omega
    have h1 := Nat.mul_le_mul_left (5 ^ k) hstep
    have h2 := Nat.mul_le_mul_left 8 ih
    rw [pow_succ, pow_succ]
    nlinarith

theorem sharp_few_defects_bound_orbit (N q K D L : ℕ) (hq : 0 < q)
    (hN : N + 1 ≤ 2 ^ K) (hL : sharpCheckpoint q K (D + 1) ≤ L)
    (hD : count N q L ≤ D) : ∃ B, ∀ t, terras_iter t N ≤ B := by
  obtain ⟨k, _, hret⟩ := sharp_few_defects_force_return N q K D L hN hL hD
  exact return_bounds_orbit hq hret

theorem sharp_near_power_force_return (N q K e L : ℕ) (w : ℕ → ℕ)
    (hN : N + 1 ≤ 2 ^ K) (hL : sharpCheckpoint q K (2 * e + 1) ≤ L)
    (hper : ∀ t < L, w (t + q) = w t)
    (herr : (templateErrors N w (L + q)).card ≤ e) :
    ∃ k, k ≤ 2 * e ∧ terras_iter (sharpCheckpoint q K k + q) N =
      terras_iter (sharpCheckpoint q K k) N := by
  apply sharp_few_defects_force_return N q K (2 * e) L hN hL
  exact (count_le_twice_template_errors N q L w hper).trans (by omega)

theorem sharp_few_defects_two_reaches_one (N K D L : ℕ) (hpos : 0 < N)
    (hN : N + 1 ≤ 2 ^ K) (hL : sharpCheckpoint 2 K (D + 1) ≤ L)
    (hD : count N 2 L ≤ D) : ∃ t, terras_iter t N = 1 := by
  obtain ⟨k, _, hret⟩ := sharp_few_defects_force_return N 2 K D L hN hL hD
  let s := sharpCheckpoint 2 K k
  have hper : terras_iter 2 (terras_iter s N) = terras_iter s N := by
    rwa [terras_iter_add]
  rcases two_step_return_trivial (terras_iter_pos s N hpos) hper with h1 | h2
  · exact ⟨s, h1⟩
  · refine ⟨s + 1, ?_⟩
    rw [terras_iter_succ', h2]
    rfl

theorem sharp_unbounded_forces_defects (N q K D : ℕ) (hq : 0 < q)
    (hN : N + 1 ≤ 2 ^ K) (hunb : ∀ B, ∃ t, B < terras_iter t N) :
    D < count N q (sharpCheckpoint q K (D + 1)) := by
  by_contra h
  obtain ⟨B, hB⟩ := sharp_few_defects_bound_orbit N q K D
    (sharpCheckpoint q K (D + 1)) hq hN (le_refl _) (by omega)
  obtain ⟨t, ht⟩ := hunb B
  have := hB t
  omega

end ParityDefects
end Collatz
