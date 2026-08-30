/-
  Collatz — The 1/50 cap grid and the Krasikov difference inequalities on it

  This file contains NO axioms and NO claim to prove the conjecture.

  HISTORY. This file is the definitional core of the former Krasikov50.lean,
  whose k = 8 instance (`K8.density_bound`, x^0.63201 — the first verified
  exponent above the critical constant, June 2026) was retired once
  KLGrid.lean / KL13.lean surpassed it; see git history.

  FORMER STATEMENT (retired): for every y, the number of integers
  n ≤ 80000·2^y whose Terras orbit reaches 1 satisfies

      c₈ · 1261^(50y) · 1250^100 ≤ count · (Cmax · 1250^(50y) · 1261^100),

  i.e. count = Ω(x^γ) with γ = 50·log₂(1261/1250) = 0.63201… — a
  machine-verified density exponent EXCEEDING the critical odd-step
  density log 2/log 3 = 0.63093…, and exceeding every published lower
  bound before Applegate–Lagarias 1995.

  ## Method: the 1/50-grid refinement of Krasikov.lean

  Krasikov.lean retards both odd-branch terms of Krasikov's difference
  inequalities to one full doubling (integer caps 2^y·a), costing
  exponent. Here the caps follow the interleaved-geometric sequence

      cap(t) = 2^(t/50) · r[t % 50],

  with a fixed 50-entry integer table r ≈ 10⁴·2^(i/50): fifty geometric
  ladders, each exactly doubling every 50 grid steps (cap_quad), and
  growing fast enough between rungs that the (D1) branch retards by
  only 21/50 of a doubling and the (D3) branch by 1/50 (cap_shift21,
  cap_shift1 — kernel-checked table conditions; the 21-step condition
  works because 2^(21/50) = 1.3382 > 4/3, with 0.4% to spare). The
  growth rate per grid step is the RATIONAL μ = 1261/1250, so every
  certificate condition is a pure integer inequality — no roots, no
  reals — verified by `decide` over the 2187 classes mod 3^8.
-/

import Collatz.Krasikov

namespace Collatz
namespace G50

/-! ## The interleaved-geometric cap sequence -/

/-- r[i] = round(10⁴·2^(i/50)): fifty interleaved geometric ladders. -/
def rtab : List ℕ :=
  [10000, 10140, 10281, 10425, 10570, 10718, 10867, 11019, 11173, 11329,
   11487, 11647, 11810, 11975, 12142, 12311, 12483, 12658, 12834, 13013,
   13195, 13379, 13566, 13755, 13947, 14142, 14340, 14540, 14743, 14948,
   15157, 15369, 15583, 15801, 16021, 16245, 16472, 16702, 16935, 17171,
   17411, 17654, 17901, 18150, 18404, 18661, 18921, 19185, 19453, 19725]

def rt (i : ℕ) : ℕ := if i < 50 then rtab.getD i 10000 else 10000

def cap (t : ℕ) : ℕ := 2 ^ (t / 50) * rt (t % 50)

theorem rt_ge (i : ℕ) : 10000 ≤ rt i := by
  unfold rt
  split
  · have h50 : ∀ j, j < 50 → 10000 ≤ rtab.getD j 10000 := by decide
    exact h50 i (by assumption)
  · exact le_refl _

theorem cap_pos (t : ℕ) : 1 ≤ cap t := by
  unfold cap
  have h1 : 1 ≤ 2 ^ (t / 50) := Nat.one_le_two_pow
  have h2 := rt_ge (t % 50)
  nlinarith

theorem cap_ge_four (t : ℕ) : 4 ≤ cap t := by
  unfold cap
  have h1 : 1 ≤ 2 ^ (t / 50) := Nat.one_le_two_pow
  have h2 := rt_ge (t % 50)
  nlinarith

/-- Fifty grid steps double the cap — exactly. -/
theorem cap_quad (t : ℕ) : cap (t + 100) = 4 * cap t := by
  unfold cap
  have h1 : (t + 100) / 50 = t / 50 + 2 := by omega
  have h2 : (t + 100) % 50 = t % 50 := by omega
  rw [h1, h2, pow_add]
  ring

/-- One grid step loses at most a factor 3/2 (the (D3) retardation). -/
theorem cap_shift1 (t : ℕ) : 2 * cap t ≤ 3 * cap (t + 1) := by
  unfold cap
  rcases lt_or_ge (t % 50) 49 with h | h
  · have h1 : (t + 1) / 50 = t / 50 := by omega
    have h2 : (t + 1) % 50 = t % 50 + 1 := by omega
    rw [h1, h2]
    have htab : ∀ j, j < 49 → 2 * rt j ≤ 3 * rt (j + 1) := by decide
    have hj := htab (t % 50) h
    calc 2 * (2 ^ (t / 50) * rt (t % 50))
        = 2 ^ (t / 50) * (2 * rt (t % 50)) := by ring
      _ ≤ 2 ^ (t / 50) * (3 * rt (t % 50 + 1)) :=
          Nat.mul_le_mul_left _ hj
      _ = 3 * (2 ^ (t / 50) * rt (t % 50 + 1)) := by ring
  · have h49 : t % 50 = 49 := by omega
    have h1 : (t + 1) / 50 = t / 50 + 1 := by omega
    have h2 : (t + 1) % 50 = 0 := by omega
    rw [h1, h2, h49, pow_add]
    have htab : 2 * rt 49 ≤ 3 * (2 * rt 0) := by decide
    calc 2 * (2 ^ (t / 50) * rt 49)
        = 2 ^ (t / 50) * (2 * rt 49) := by ring
      _ ≤ 2 ^ (t / 50) * (3 * (2 * rt 0)) := Nat.mul_le_mul_left _ htab
      _ = 3 * (2 ^ (t / 50) * 2 ^ 1 * rt 0) := by ring

/-- Twenty-one grid steps lose at most a factor 3/4 (the (D1)
    retardation): here 2^(21/50) > 4/3 does the work. -/
theorem cap_shift21 (t : ℕ) : 4 * cap t ≤ 3 * cap (t + 21) := by
  unfold cap
  rcases lt_or_ge (t % 50) 29 with h | h
  · have h1 : (t + 21) / 50 = t / 50 := by omega
    have h2 : (t + 21) % 50 = t % 50 + 21 := by omega
    rw [h1, h2]
    have htab : ∀ j, j < 29 → 4 * rt j ≤ 3 * rt (j + 21) := by decide
    have hj := htab (t % 50) h
    calc 4 * (2 ^ (t / 50) * rt (t % 50))
        = 2 ^ (t / 50) * (4 * rt (t % 50)) := by ring
      _ ≤ 2 ^ (t / 50) * (3 * rt (t % 50 + 21)) :=
          Nat.mul_le_mul_left _ hj
      _ = 3 * (2 ^ (t / 50) * rt (t % 50 + 21)) := by ring
  · have hlt : t % 50 < 50 := Nat.mod_lt _ (by norm_num)
    have h1 : (t + 21) / 50 = t / 50 + 1 := by omega
    have h2 : (t + 21) % 50 = t % 50 - 29 := by omega
    rw [h1, h2, pow_add]
    have htab : ∀ j, 29 ≤ j → j < 50 → 4 * rt j ≤ 3 * (2 * rt (j - 29)) := by
      decide
    have hj := htab (t % 50) h hlt
    calc 4 * (2 ^ (t / 50) * rt (t % 50))
        = 2 ^ (t / 50) * (4 * rt (t % 50)) := by ring
      _ ≤ 2 ^ (t / 50) * (3 * (2 * rt (t % 50 - 29))) :=
          Nat.mul_le_mul_left _ hj
      _ = 3 * (2 ^ (t / 50) * 2 ^ 1 * rt (t % 50 - 29)) := by ring

/-! ## The grid class-infimum and its difference inequalities -/

noncomputable def phi50 (k m t : ℕ) : ℕ :=
  sInf ((fun a => cnt a (cap t * a)) '' Roots k m)

theorem phi50_le {k m t a : ℕ} (ha : a ∈ Roots k m) :
    phi50 k m t ≤ cnt a (cap t * a) :=
  Nat.sInf_le ⟨a, ha, rfl⟩

theorem phi50_attained {k m t : ℕ} (hne : (Roots k m).Nonempty) :
    ∃ a ∈ Roots k m, phi50 k m t = cnt a (cap t * a) := by
  obtain ⟨a, ha, hval⟩ := Nat.sInf_mem (hne.image _)
  exact ⟨a, ha, hval.symm⟩

theorem phi50_ge_one {k m t : ℕ} (hne : (Roots k m).Nonempty) :
    1 ≤ phi50 k m t := by
  obtain ⟨a, ha, hval⟩ := phi50_attained (t := t) hne
  rw [hval]
  exact cnt_pos (Nat.le_mul_of_pos_left a (cap_pos t))

noncomputable def phiMin50 (k w t : ℕ) : ℕ :=
  min (phi50 k w t) (min (phi50 k (w + 3 ^ (k - 1)) t)
    (phi50 k (w + 2 * 3 ^ (k - 1)) t))

theorem phiMin50_le_of_lift {k w t b : ℕ} (hk : 1 ≤ k)
    (hw : w < 3 ^ (k - 1)) (hcong : b % 3 ^ (k - 1) = w)
    (hb : b ∈ Roots k (b % 3 ^ k)) :
    phiMin50 k w t ≤ cnt b (cap t * b) := by
  rcases mem_lifts hk hw hcong with hl | hl | hl
  · exact le_trans (min_le_left _ _) (phi50_le (hl ▸ hb))
  · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
      (phi50_le (hl ▸ hb))
  · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (phi50_le (hl ▸ hb))

theorem phi50_rec_five {k m t : ℕ} (hne : (Roots k m).Nonempty) :
    phi50 k (4 * m % 3 ^ k) t ≤ phi50 k m (t + 100) := by
  obtain ⟨a, ha, hval⟩ := phi50_attained (t := t + 100) hne
  rw [hval]
  have hq := cap_quad t
  have hX : cap (t + 100) * a = cap t * (4 * a) := by rw [hq]; ring
  calc phi50 k (4 * m % 3 ^ k) t ≤ cnt (4 * a) (cap t * (4 * a)) :=
        phi50_le (roots_double ha)
    _ = cnt (4 * a) (cap (t + 100) * a) := by rw [hX]
    _ ≤ cnt a (cap (t + 100) * a) := by
        apply cnt_le_of_chain iter_two_four_mul
        apply chain_four
        have h4 := cap_ge_four (t + 100)
        nlinarith

theorem phi50_rec_eight {k m t : ℕ} (hk : 1 ≤ k) (hm9 : m % 9 = 8)
    (hne : (Roots k m).Nonempty) :
    phi50 k (4 * m % 3 ^ k) t +
      phiMin50 k ((2 * m - 1) % 3 ^ k / 3) (t + 99) ≤
      phi50 k m (t + 100) := by
  obtain ⟨a, ha, hval⟩ := phi50_attained (t := t + 100) hne
  obtain ⟨h3a, hamod, h8⟩ := ha
  have hm8 : 8 ≤ m := by omega
  have ha3 : a % 3 = 2 := by
    have hdvd : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    have e := Nat.mod_mod_of_dvd a hdvd
    omega
  obtain ⟨b, hb3, hbodd, hbt, hb3le, hblt⟩ := odd_branch h3a ha3
  set X := cap (t + 100) * a with hXdef
  have hcap1 : 1 ≤ cap (t + 100) := cap_pos _
  have haX : a ≤ X := Nat.le_mul_of_pos_left a (cap_pos _)
  have h4aX : 4 * a ≤ X := by
    have h4 := cap_ge_four (t + 100)
    rw [hXdef]
    nlinarith
  have hnp := not_periodic_of_reaches_eight h3a h8
  have hsplit : cnt (4 * a) X + cnt b X ≤ cnt a X := by
    apply cnt_split (du := 2) (dv := 1) (by omega) (by omega)
      iter_two_four_mul (by show terras b = a; exact hbt) hnp
    · intro s hs
      have hs1 : s = 1 := by omega
      subst hs1
      show terras_iter 1 (4 * a) ≠ b
      show terras (4 * a) ≠ b
      have e : terras (4 * a) = 2 * a := by
        have e2 : 4 * a = 2 * (2 * a) := by ring
        rw [e2, terras_double]
      rw [e]
      omega
    · intro s hs
      omega
    · exact chain_four h4aX
    · intro i h1 h2
      have hi1 : i = 1 := by omega
      subst hi1
      show terras b ≤ X
      rw [hbt]
      exact haX
  have hcnt4 : phi50 k (4 * m % 3 ^ k) t ≤ cnt (4 * a) X := by
    have e : X = cap t * (4 * a) := by rw [hXdef, cap_quad]; ring
    rw [e]
    exact phi50_le (roots_double ⟨h3a, hamod, h8⟩)
  have hcntb : phiMin50 k ((2 * m - 1) % 3 ^ k / 3) (t + 99) ≤ cnt b X := by
    have hb8 : reaches b 8 :=
      reaches_trans ⟨1, by show terras b = a; exact hbt⟩ h8
    have hbmem : b ∈ Roots k (b % 3 ^ k) := ⟨hb3le, rfl, hb8⟩
    have hcap : cap (t + 99) * b ≤ X := by
      have hc1 : 2 * cap (t + 99) ≤ 3 * cap (t + 100) := by
        have := cap_shift1 (t + 99)
        rwa [show t + 99 + 1 = t + 100 by omega] at this
      have key : 3 * (cap (t + 99) * b) ≤ 3 * (cap (t + 100) * a) := by
        calc 3 * (cap (t + 99) * b) = cap (t + 99) * (3 * b) := by ring
          _ = cap (t + 99) * (2 * a - 1) := by rw [hb3]
          _ ≤ cap (t + 99) * (2 * a) := Nat.mul_le_mul_left _ (by omega)
          _ = (2 * cap (t + 99)) * a := by ring
          _ ≤ (3 * cap (t + 100)) * a := Nat.mul_le_mul_right _ hc1
          _ = 3 * (cap (t + 100) * a) := by ring
      exact Nat.le_of_mul_le_mul_left key (by norm_num)
    have hsplitP : (3 : ℕ) ^ k = 3 * 3 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hWmod : (3 * b) % 3 ^ k = (2 * m - 1) % 3 ^ k := by
      have e1 : 3 * b = 2 * a - 1 := by omega
      rw [e1]
      exact sub_mod_transfer hamod (by omega)
    have hcong : b % 3 ^ (k - 1) = (2 * m - 1) % 3 ^ k / 3 := by
      apply third_mod
      rw [← hsplitP]
      exact hWmod
    have hwlt : (2 * m - 1) % 3 ^ k / 3 < 3 ^ (k - 1) := by
      have h1 : (2 * m - 1) % 3 ^ k < 3 ^ k := Nat.mod_lt _ (by positivity)
      omega
    calc phiMin50 k ((2 * m - 1) % 3 ^ k / 3) (t + 99)
        ≤ cnt b (cap (t + 99) * b) :=
          phiMin50_le_of_lift hk hwlt hcong hbmem
      _ ≤ cnt b X := cnt_mono hcap
  rw [hval]
  calc phi50 k (4 * m % 3 ^ k) t +
        phiMin50 k ((2 * m - 1) % 3 ^ k / 3) (t + 99)
      ≤ cnt (4 * a) X + cnt b X := Nat.add_le_add hcnt4 hcntb
    _ ≤ cnt a X := hsplit

theorem phi50_rec_two {k m t : ℕ} (hk : 1 ≤ k) (hm9 : m % 9 = 2)
    (hne : (Roots k m).Nonempty) :
    phi50 k (4 * m % 3 ^ k) t +
      phiMin50 k ((4 * m - 2) % 3 ^ k / 3) (t + 79) ≤
      phi50 k m (t + 100) := by
  obtain ⟨a, ha, hval⟩ := phi50_attained (t := t + 100) hne
  obtain ⟨h3a, hamod, h8⟩ := ha
  have hm2 : 2 ≤ m := by omega
  have ha3 : a % 3 = 2 := by
    have hdvd : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    have e := Nat.mod_mod_of_dvd a hdvd
    omega
  obtain ⟨b, hb3, hbodd, hbt, hb3le, hblt⟩ := odd_branch h3a ha3
  set X := cap (t + 100) * a with hXdef
  have haX : a ≤ X := Nat.le_mul_of_pos_left a (cap_pos _)
  have h4aX : 4 * a ≤ X := by
    have h4 := cap_ge_four (t + 100)
    rw [hXdef]
    nlinarith
  have hnp := not_periodic_of_reaches_eight h3a h8
  have hb'2 : terras_iter 2 (2 * b) = a := by
    show terras_iter 1 (terras (2 * b)) = a
    rw [terras_double]
    show terras b = a
    exact hbt
  have hsplit : cnt (4 * a) X + cnt (2 * b) X ≤ cnt a X := by
    apply cnt_split (du := 2) (dv := 2) (by omega) (by omega)
      iter_two_four_mul hb'2 hnp
    · intro s hs
      have hs0 : s = 0 := by omega
      subst hs0
      show 4 * a ≠ 2 * b
      intro hcon
      have hba : b = 2 * a := by omega
      omega
    · intro s hs
      have hs0 : s = 0 := by omega
      subst hs0
      show 2 * b ≠ 4 * a
      intro hcon
      have hba : b = 2 * a := by omega
      omega
    · exact chain_four h4aX
    · intro i h1 h2
      interval_cases i
      · show terras (2 * b) ≤ X
        rw [terras_double]
        omega
      · show terras_iter 1 (terras (2 * b)) ≤ X
        rw [terras_double]
        show terras b ≤ X
        rw [hbt]
        exact haX
  have hcnt4 : phi50 k (4 * m % 3 ^ k) t ≤ cnt (4 * a) X := by
    have e : X = cap t * (4 * a) := by rw [hXdef, cap_quad]; ring
    rw [e]
    exact phi50_le (roots_double ⟨h3a, hamod, h8⟩)
  have hcntb : phiMin50 k ((4 * m - 2) % 3 ^ k / 3) (t + 79) ≤
      cnt (2 * b) X := by
    have hb'8 : reaches (2 * b) 8 := reaches_trans ⟨2, hb'2⟩ h8
    have hb'mem : 2 * b ∈ Roots k (2 * b % 3 ^ k) := ⟨by omega, rfl, hb'8⟩
    have hcap : cap (t + 79) * (2 * b) ≤ X := by
      have hc21 : 4 * cap (t + 79) ≤ 3 * cap (t + 100) := by
        have := cap_shift21 (t + 79)
        rwa [show t + 79 + 21 = t + 100 by omega] at this
      have key : 3 * (cap (t + 79) * (2 * b)) ≤ 3 * (cap (t + 100) * a) := by
        calc 3 * (cap (t + 79) * (2 * b))
            = cap (t + 79) * (2 * (3 * b)) := by ring
          _ = cap (t + 79) * (2 * (2 * a - 1)) := by rw [hb3]
          _ ≤ cap (t + 79) * (4 * a) := by
              apply Nat.mul_le_mul_left
              omega
          _ = (4 * cap (t + 79)) * a := by ring
          _ ≤ (3 * cap (t + 100)) * a := Nat.mul_le_mul_right _ hc21
          _ = 3 * (cap (t + 100) * a) := by ring
      exact Nat.le_of_mul_le_mul_left key (by norm_num)
    have hsplitP : (3 : ℕ) ^ k = 3 * 3 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hWmod : (3 * (2 * b)) % 3 ^ k = (4 * m - 2) % 3 ^ k := by
      have e1 : 3 * (2 * b) = 4 * a - 2 := by omega
      rw [e1]
      exact sub_mod_transfer hamod (by omega)
    have hcong : (2 * b) % 3 ^ (k - 1) = (4 * m - 2) % 3 ^ k / 3 := by
      apply third_mod
      rw [← hsplitP]
      exact hWmod
    have hwlt : (4 * m - 2) % 3 ^ k / 3 < 3 ^ (k - 1) := by
      have h1 : (4 * m - 2) % 3 ^ k < 3 ^ k := Nat.mod_lt _ (by positivity)
      omega
    calc phiMin50 k ((4 * m - 2) % 3 ^ k / 3) (t + 79)
        ≤ cnt (2 * b) (cap (t + 79) * (2 * b)) :=
          phiMin50_le_of_lift hk hwlt hcong hb'mem
      _ ≤ cnt (2 * b) X := cnt_mono hcap
  rw [hval]
  calc phi50 k (4 * m % 3 ^ k) t +
        phiMin50 k ((4 * m - 2) % 3 ^ k / 3) (t + 79)
      ≤ cnt (4 * a) X + cnt (2 * b) X := Nat.add_le_add hcnt4 hcntb
    _ ≤ cnt a X := hsplit

end G50
end Collatz
