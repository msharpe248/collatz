/-
  Collatz — The Krasikov–Lagarias inequality system on the 1/50 grid,
  with the ADVANCED term, generic in the level k and the rate μ = p/q.

  This file contains NO axioms and NO claim to prove the conjecture.

  Krasikov–Lagarias (Acta Arith. 109 (2003)) bound the number of
  integers whose orbit reaches a fixed root by a system of difference
  inequalities on class infima φ_m(y) = inf_a cnt(a, 2^y a):

      (D1) m ≡ 2 (9):  φ_m(y) ≥ φ_{4m}(y−2) + φ̄_{(4m−2)/3}(y + α − 2)
      (D2) m ≡ 5 (9):  φ_m(y) ≥ φ_{4m}(y−2)
      (D3) m ≡ 8 (9):  φ_m(y) ≥ φ_{4m}(y−2) + φ̄_{(2m−1)/3}(y + α − 1)

  with α = log₂3. The term in (D3) is ADVANCED (its argument exceeds
  y): the child (2a−1)/3 is smaller than a, so its relative scale is
  larger. A feasible vector c of the linear program with coefficients
  λ^{−2}, λ^{α−2}, λ^{α−1} gives φ_m(y) ≥ Δ c_m λ^y (their Thm 2.2),
  but a plain induction on y cannot use an advanced term, and KL prove
  Thm 2.2 by a back-substitution/elimination procedure (their §3–5,
  termination via Kőnig's lemma). Truncating the advanced term instead
  (Applegate–Lagarias 1995, Krasikov50.lean) caps the exponent near
  0.66; the advanced term is worth ≈ 0.19 in the exponent.

  THIS FILE proves the growth bound WITHOUT elimination, by a strong
  induction over actual roots rather than classes, on the measure

      M(t, a) = 10·t + ⌊log₂(a^498)⌋

  (t the grid time, 50 grid steps per doubling). Along the three
  branches the measure drops by 4, 3 and 1 respectively:

      4a          : t ↦ t − 100,  log₂ a ↦ log₂ a + 2       (−1000 + 996)
      (4a−2)/3    : t ↦ t −  21,  log₂ a ↦ ≤ log₂ a + 0.415 (−210 + 207)
      (2a−1)/3    : t ↦ t +  29,  log₂ a ↦ ≤ log₂ a − 0.585 (+290 − 291)

  because 498·log₂(3/2) = 291.3 > 291, i.e. 3^498 > 2^789 — the only
  numeric input. The exact KL shift α − 1 = log₂(3/2) would make this
  measure degenerate (that is why they needed elimination); the grid
  offset 29 < 50·log₂(3/2) = 29.25 leaves exactly the slack a
  well-founded induction needs, at a cost of 1/50 of a doubling.
  Using roots instead of classes also removes the min over lifts from
  the induction (the child's class is known) and the need for
  nonemptiness witnesses.

  THE GROWTH THEOREM (`growth_root`): for any level k ≥ 2, rate μ = p/q
  ≥ 1, bound Cmax, and certificate c : ℕ → ℕ with, on all classes
  m ≡ 2 (3) of modulus 3^k,

      (5)  c_m p^100        ≤ c_{4m} q^100
      (2)  c_m p^100        ≤ c_{4m} q^100 + cbar p^79 q^21
      (8)  c_m p^100 q^29   ≤ c_{4m} q^129 + cbar p^129,

  every root a ≡ 2 (3) reaching 8 satisfies

      c_{a mod 3^k} p^t q^100 ≤ cnt(a, cap(t)·a) · (Cmax q^t p^100),

  i.e. the tree of a grows like μ^t = (p/q)^t: density exponent
  γ = 50·log₂(p/q). KL12.lean instantiates this at k = 12.
-/

import Collatz.Krasikov50

set_option exponentiation.threshold 2000

namespace Collatz
namespace G50

/-- 2^(29/50) = 1.4946 < 3/2: the exact (D3) offset. -/
theorem cap_shift29 (t : ℕ) : 2 * cap (t + 29) ≤ 3 * cap t := by
  unfold cap
  rcases lt_or_ge (t % 50) 21 with h | h
  · have h1 : (t + 29) / 50 = t / 50 := by omega
    have h2 : (t + 29) % 50 = t % 50 + 29 := by omega
    rw [h1, h2]
    have htab : ∀ j, j < 21 → 2 * rt (j + 29) ≤ 3 * rt j := by decide
    have hj := htab (t % 50) h
    calc 2 * (2 ^ (t / 50) * rt (t % 50 + 29))
        = 2 ^ (t / 50) * (2 * rt (t % 50 + 29)) := by ring
      _ ≤ 2 ^ (t / 50) * (3 * rt (t % 50)) := Nat.mul_le_mul_left _ hj
      _ = 3 * (2 ^ (t / 50) * rt (t % 50)) := by ring
  · have hlt : t % 50 < 50 := Nat.mod_lt _ (by norm_num)
    have h1 : (t + 29) / 50 = t / 50 + 1 := by omega
    have h2 : (t + 29) % 50 = t % 50 - 21 := by omega
    rw [h1, h2, pow_add]
    have htab : ∀ j, 21 ≤ j → j < 50 → 2 * (2 * rt (j - 21)) ≤ 3 * rt j := by
      decide
    have hj := htab (t % 50) h hlt
    calc 2 * (2 ^ (t / 50) * 2 ^ 1 * rt (t % 50 - 21))
        = 2 ^ (t / 50) * (2 * (2 * rt (t % 50 - 21))) := by ring
      _ ≤ 2 ^ (t / 50) * (3 * rt (t % 50)) := Nat.mul_le_mul_left _ hj
      _ = 3 * (2 ^ (t / 50) * rt (t % 50)) := by ring

/-! ## The three difference inequalities, per root -/

/-- Doubling branch: the tree of 4a inside the tree of a, at the same cap. -/
theorem cnt_rec_five (a t : ℕ) :
    cnt (4 * a) (cap t * (4 * a)) ≤ cnt a (cap (t + 100) * a) := by
  have hX : cap (t + 100) * a = cap t * (4 * a) := by rw [cap_quad]; ring
  rw [hX]
  apply cnt_le_of_chain iter_two_four_mul
  apply chain_four
  have h4 := cap_ge_four t
  nlinarith

/-- (D1) per root: a ≡ 2 (3), b = (2a−1)/3, child 2b at offset 79. -/
theorem cnt_rec_two {a b t : ℕ} (h3a : 3 ≤ a) (hb3 : 3 * b = 2 * a - 1)
    (hbt : terras b = a) (hb3le : 3 ≤ b) (h8 : reaches a 8) :
    cnt (4 * a) (cap t * (4 * a)) + cnt (2 * b) (cap (t + 79) * (2 * b)) ≤
      cnt a (cap (t + 100) * a) := by
  set X := cap (t + 100) * a with hXdef
  have haX : a ≤ X := Nat.le_mul_of_pos_left a (cap_pos _)
  have h4aX : 4 * a ≤ X := by
    have h4 := cap_ge_four (t + 100)
    rw [hXdef]; nlinarith
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
      omega
    · intro s hs
      have hs0 : s = 0 := by omega
      subst hs0
      show 2 * b ≠ 4 * a
      intro hcon
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
  have hX4 : cap t * (4 * a) = X := by rw [hXdef, cap_quad]; ring
  have hcap : cap (t + 79) * (2 * b) ≤ X := by
    have hc21 : 4 * cap (t + 79) ≤ 3 * cap (t + 100) := by
      have := cap_shift21 (t + 79)
      rwa [show t + 79 + 21 = t + 100 by omega] at this
    have key : 3 * (cap (t + 79) * (2 * b)) ≤ 3 * (cap (t + 100) * a) := by
      calc 3 * (cap (t + 79) * (2 * b))
          = cap (t + 79) * (2 * (3 * b)) := by ring
        _ = cap (t + 79) * (2 * (2 * a - 1)) := by rw [hb3]
        _ ≤ cap (t + 79) * (4 * a) := by
            apply Nat.mul_le_mul_left; omega
        _ = (4 * cap (t + 79)) * a := by ring
        _ ≤ (3 * cap (t + 100)) * a := Nat.mul_le_mul_right _ hc21
        _ = 3 * (cap (t + 100) * a) := by ring
    exact Nat.le_of_mul_le_mul_left key (by norm_num)
  rw [hX4]
  calc cnt (4 * a) X + cnt (2 * b) (cap (t + 79) * (2 * b))
      ≤ cnt (4 * a) X + cnt (2 * b) X := Nat.add_le_add_left (cnt_mono hcap) _
    _ ≤ cnt a X := hsplit

/-- (D3) per root, exact offset 129: a ≡ 2 (3), b = (2a−1)/3, child b. -/
theorem cnt_rec_eight {a b t : ℕ} (h3a : 3 ≤ a) (hb3 : 3 * b = 2 * a - 1)
    (hbt : terras b = a) (hb3le : 3 ≤ b) (h8 : reaches a 8) :
    cnt (4 * a) (cap t * (4 * a)) + cnt b (cap (t + 129) * b) ≤
      cnt a (cap (t + 100) * a) := by
  set X := cap (t + 100) * a with hXdef
  have haX : a ≤ X := Nat.le_mul_of_pos_left a (cap_pos _)
  have h4aX : 4 * a ≤ X := by
    have h4 := cap_ge_four (t + 100)
    rw [hXdef]; nlinarith
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
  have hX4 : cap t * (4 * a) = X := by rw [hXdef, cap_quad]; ring
  have hcap : cap (t + 129) * b ≤ X := by
    have hc1 : 2 * cap (t + 129) ≤ 3 * cap (t + 100) := by
      have := cap_shift29 (t + 100)
      rwa [show t + 100 + 29 = t + 129 by omega] at this
    have key : 3 * (cap (t + 129) * b) ≤ 3 * (cap (t + 100) * a) := by
      calc 3 * (cap (t + 129) * b) = cap (t + 129) * (3 * b) := by ring
        _ = cap (t + 129) * (2 * a - 1) := by rw [hb3]
        _ ≤ cap (t + 129) * (2 * a) := Nat.mul_le_mul_left _ (by omega)
        _ = (2 * cap (t + 129)) * a := by ring
        _ ≤ (3 * cap (t + 100)) * a := Nat.mul_le_mul_right _ hc1
        _ = 3 * (cap (t + 100) * a) := by ring
    exact Nat.le_of_mul_le_mul_left key (by norm_num)
  rw [hX4]
  calc cnt (4 * a) X + cnt b (cap (t + 129) * b)
      ≤ cnt (4 * a) X + cnt b X := Nat.add_le_add_left (cnt_mono hcap) _
    _ ≤ cnt a X := hsplit

/-! ## The measure -/

/-- L(a) = ⌊498·log₂ a⌋, as ⌊log₂(a^498)⌋. -/
def L (a : ℕ) : ℕ := Nat.log 2 (a ^ 498)

theorem three_pow_gt : (2 : ℕ) ^ 789 < 3 ^ 498 := by norm_num

theorem four_pow_498 : (4 : ℕ) ^ 498 = 2 ^ 996 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

theorem L_four {a : ℕ} (ha : 1 ≤ a) : L (4 * a) ≤ L a + 996 := by
  unfold L
  have hne : (4 * a) ^ 498 ≠ 0 := by positivity
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (a ^ 498)
  have key : (4 * a) ^ 498 < 2 ^ (Nat.log 2 (a ^ 498) + 996 + 1) := by
    calc (4 * a) ^ 498 = 2 ^ 996 * a ^ 498 := by rw [mul_pow, four_pow_498]
      _ < 2 ^ 996 * 2 ^ (Nat.log 2 (a ^ 498) + 1) := by
          apply Nat.mul_lt_mul_of_pos_left h (by positivity)
      _ = 2 ^ (Nat.log 2 (a ^ 498) + 996 + 1) := by rw [← pow_add]; congr 1; ring
  have := (Nat.log_lt_iff_lt_pow (by norm_num) hne).mpr key
  omega

theorem L_child_two {a b : ℕ} (hb3 : 3 * b = 2 * a - 1) (hb : 1 ≤ b) :
    L (2 * b) ≤ L a + 207 := by
  unfold L
  have ha : 1 ≤ a := by omega
  have hne : (2 * b) ^ 498 ≠ 0 := by positivity
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (a ^ 498)
  have h1 : 3 * (2 * b) ≤ 4 * a := by omega
  have h2 : (3 * (2 * b)) ^ 498 ≤ (4 * a) ^ 498 := Nat.pow_le_pow_left h1 _
  have h3 : 3 ^ 498 * (2 * b) ^ 498 ≤ 2 ^ 996 * a ^ 498 := by
    calc 3 ^ 498 * (2 * b) ^ 498 = (3 * (2 * b)) ^ 498 := by rw [← mul_pow]
      _ ≤ (4 * a) ^ 498 := h2
      _ = 2 ^ 996 * a ^ 498 := by rw [mul_pow, four_pow_498]
  have h4 : 2 ^ 789 * (2 * b) ^ 498 < 2 ^ 996 * a ^ 498 := by
    calc 2 ^ 789 * (2 * b) ^ 498 < 3 ^ 498 * (2 * b) ^ 498 :=
          Nat.mul_lt_mul_of_pos_right three_pow_gt (by positivity)
      _ ≤ 2 ^ 996 * a ^ 498 := h3
  have h5 : (2 * b) ^ 498 < 2 ^ 207 * a ^ 498 := by
    have e : (2 : ℕ) ^ 996 = 2 ^ 789 * 2 ^ 207 := by rw [← pow_add]
    rw [e, mul_assoc] at h4
    exact Nat.lt_of_mul_lt_mul_left h4
  have key : (2 * b) ^ 498 < 2 ^ (Nat.log 2 (a ^ 498) + 207 + 1) := by
    calc (2 * b) ^ 498 < 2 ^ 207 * a ^ 498 := h5
      _ < 2 ^ 207 * 2 ^ (Nat.log 2 (a ^ 498) + 1) :=
          Nat.mul_lt_mul_of_pos_left h (by positivity)
      _ = 2 ^ (Nat.log 2 (a ^ 498) + 207 + 1) := by rw [← pow_add]; congr 1; ring
  have := (Nat.log_lt_iff_lt_pow (by norm_num) hne).mpr key
  omega

theorem L_child_eight {a b : ℕ} (hb3 : 3 * b = 2 * a - 1) (hb : 1 ≤ b) :
    L b + 291 ≤ L a := by
  unfold L
  have ha : 1 ≤ a := by omega
  have hne : a ^ 498 ≠ 0 := by positivity
  have h1 : 3 * b ≤ 2 * a := by omega
  have h2 : (3 * b) ^ 498 ≤ (2 * a) ^ 498 := Nat.pow_le_pow_left h1 _
  have h3 : 3 ^ 498 * b ^ 498 ≤ 2 ^ 498 * a ^ 498 := by
    rw [← mul_pow, ← mul_pow]; exact h2
  have h4 : 2 ^ 789 * b ^ 498 < 2 ^ 498 * a ^ 498 := by
    calc 2 ^ 789 * b ^ 498 < 3 ^ 498 * b ^ 498 :=
          Nat.mul_lt_mul_of_pos_right three_pow_gt (by positivity)
      _ ≤ 2 ^ 498 * a ^ 498 := h3
  have h5 : 2 ^ 291 * b ^ 498 < a ^ 498 := by
    have e : (2 : ℕ) ^ 789 = 2 ^ 498 * 2 ^ 291 := by rw [← pow_add]
    rw [e, mul_assoc] at h4
    exact Nat.lt_of_mul_lt_mul_left h4
  have h6 : 2 ^ Nat.log 2 (b ^ 498) ≤ b ^ 498 :=
    Nat.pow_log_le_self 2 (by positivity)
  have key : 2 ^ (Nat.log 2 (b ^ 498) + 291) ≤ a ^ 498 := by
    calc 2 ^ (Nat.log 2 (b ^ 498) + 291) = 2 ^ 291 * 2 ^ Nat.log 2 (b ^ 498) := by
          rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ 291 * b ^ 498 := Nat.mul_le_mul_left _ h6
      _ ≤ a ^ 498 := le_of_lt h5
  exact (Nat.le_log_iff_pow_le (by norm_num) hne).mpr key

/-! ## The certificate and the growth theorem -/

/-- The minimum of the certificate over the three lifts of a class of
    modulus 3^(k−1). -/
def cbarG (k : ℕ) (c : ℕ → ℕ) (w : ℕ) : ℕ :=
  min (c w) (min (c (w + 3 ^ (k - 1))) (c (w + 2 * 3 ^ (k - 1))))

/-- The certificate conditions at level k with rate p/q. -/
def CertOK (k p q : ℕ) (c : ℕ → ℕ) : Prop :=
  ∀ m, m < 3 ^ k → m % 3 = 2 →
    (m % 9 = 5 → c m * p ^ 100 ≤ c (4 * m % 3 ^ k) * q ^ 100) ∧
    (m % 9 = 2 → c m * p ^ 100 ≤ c (4 * m % 3 ^ k) * q ^ 100 +
      cbarG k c ((4 * m - 2) % 3 ^ k / 3) * (p ^ 79 * q ^ 21)) ∧
    (m % 9 = 8 → c m * p ^ 100 * q ^ 29 ≤ c (4 * m % 3 ^ k) * q ^ 129 +
      cbarG k c ((2 * m - 1) % 3 ^ k / 3) * p ^ 129)

theorem cbarG_le_of_lift {k : ℕ} (c : ℕ → ℕ) (hk : 1 ≤ k) {w b : ℕ}
    (hw : w < 3 ^ (k - 1)) (hcong : b % 3 ^ (k - 1) = w) :
    cbarG k c w ≤ c (b % 3 ^ k) := by
  unfold cbarG
  rcases mem_lifts hk hw hcong with h | h | h <;> rw [h]
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- Base-case power swap: (p/q)^t ≤ (p/q)^100 for t ≤ 100. -/
theorem pow_swap' {p q t : ℕ} (hpq : q ≤ p) (ht : t ≤ 100) :
    p ^ t * q ^ 100 ≤ q ^ t * p ^ 100 := by
  have e1 : p ^ 100 = p ^ t * p ^ (100 - t) := by rw [← pow_add]; congr 1; omega
  have e2 : q ^ 100 = q ^ t * q ^ (100 - t) := by rw [← pow_add]; congr 1; omega
  rw [e1, e2]
  have h := Nat.pow_le_pow_left hpq (100 - t)
  calc p ^ t * (q ^ t * q ^ (100 - t)) = (p ^ t * q ^ t) * q ^ (100 - t) := by ring
    _ ≤ (p ^ t * q ^ t) * p ^ (100 - t) := Nat.mul_le_mul_left _ h
    _ = q ^ t * (p ^ t * p ^ (100 - t)) := by ring

/-- THE GROWTH THEOREM (root form). -/
theorem growth_root (k : ℕ) (hk : 2 ≤ k) (p q Cmax : ℕ) (hpq : q ≤ p) (hq : 1 ≤ q)
    (c : ℕ → ℕ)
    (hbounds : ∀ m, m < 3 ^ k → m % 3 = 2 → 1 ≤ c m ∧ c m ≤ Cmax)
    (hcert : CertOK k p q c) :
    ∀ n t a, 10 * t + L a = n → 3 ≤ a → a % 3 = 2 → reaches a 8 →
      c (a % 3 ^ k) * p ^ t * q ^ 100 ≤
        cnt a (cap t * a) * (Cmax * q ^ t * p ^ 100) := by
  have hk1 : 1 ≤ k := by omega
  have hP : 0 < 3 ^ k := by positivity
  have h9 : (9 : ℕ) ≤ 3 ^ k := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h9dvd : (9 : ℕ) ∣ 3 ^ k := by
    have : (3 : ℕ) ^ k = 3 ^ 2 * 3 ^ (k - 2) := by rw [← pow_add]; congr 1; omega
    rw [this]; exact Dvd.intro _ rfl
  have h3dvd : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hH : (3 : ℕ) ^ k = 3 * 3 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t a hn h3a ha3 h8
    set m := a % 3 ^ k with hmdef
    have hm : m < 3 ^ k := Nat.mod_lt _ hP
    have hm3 : m % 3 = 2 := by
      rw [hmdef, Nat.mod_mod_of_dvd _ h3dvd]; exact ha3
    have hb := hbounds m hm hm3
    have hcnt1 : 1 ≤ cnt a (cap t * a) :=
      cnt_pos (Nat.le_mul_of_pos_left a (cap_pos _))
    rcases lt_or_ge t 100 with ht | ht
    · -- base: t < 100
      calc c m * p ^ t * q ^ 100 = c m * (p ^ t * q ^ 100) := by ring
        _ ≤ Cmax * (p ^ t * q ^ 100) := Nat.mul_le_mul_right _ hb.2
        _ ≤ Cmax * (q ^ t * p ^ 100) := Nat.mul_le_mul_left _ (pow_swap' hpq (by omega))
        _ = 1 * (Cmax * q ^ t * p ^ 100) := by ring
        _ ≤ cnt a (cap t * a) * (Cmax * q ^ t * p ^ 100) := Nat.mul_le_mul_right _ hcnt1
    · -- step
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 100 := ⟨t - 100, by omega⟩
      have ha1 : 1 ≤ a := by omega
      -- the doubling child
      have h4mod : 4 * a % 3 ^ k = 4 * m % 3 ^ k := by
        rw [hmdef, Nat.mul_mod, Nat.mod_eq_of_lt (show 4 < 3 ^ k by omega)]
      have h4a8 : reaches (4 * a) 8 := reaches_trans ⟨2, iter_two_four_mul⟩ h8
      have hL4 := L_four ha1
      have ih4 := ih (10 * t' + L (4 * a)) (by omega) t' (4 * a) rfl (by omega)
        (by omega) h4a8
      rw [h4mod] at ih4
      have h9a : a % 9 = m % 9 := by rw [hmdef, Nat.mod_mod_of_dvd _ h9dvd]
      have hcm := hcert m hm hm3
      have hcase : m % 9 = 2 ∨ m % 9 = 5 ∨ m % 9 = 8 := by omega
      rcases hcase with hc9 | hc9 | hc9
      · -- (D1): child 2b at offset 79
        obtain ⟨b, hb3, hbodd, hbt, hb3le, hblt⟩ := odd_branch h3a ha3
        have hrec := cnt_rec_two (t := t') h3a hb3 hbt hb3le h8
        have h2b8 : reaches (2 * b) 8 := by
          refine reaches_trans ⟨2, ?_⟩ h8
          show terras_iter 1 (terras (2 * b)) = a
          rw [terras_double]; exact hbt
        have h2b3 : (2 * b) % 3 = 2 := by omega
        have hL2 := L_child_two hb3 (by omega)
        have ih2 := ih (10 * (t' + 79) + L (2 * b)) (by omega) (t' + 79) (2 * b) rfl
          (by omega) h2b3 h2b8
        -- the class of 2b is a lift of w = (4m−2) % 3^k / 3
        set w := (4 * m - 2) % 3 ^ k / 3 with hwdef
        have hw : w < 3 ^ (k - 1) := by
          have : (4 * m - 2) % 3 ^ k < 3 ^ k := Nat.mod_lt _ hP
          omega
        have hWmod : (3 * (2 * b)) % 3 ^ k = (4 * m - 2) % 3 ^ k := by
          have e1 : 3 * (2 * b) = 4 * a - 2 := by omega
          rw [e1]
          exact sub_mod_transfer hmdef.symm (by omega)
        have hcong : (2 * b) % 3 ^ (k - 1) = w := by
          apply third_mod
          rw [← hH]; exact hWmod
        have hcb := cbarG_le_of_lift c hk1 hw hcong
        have hcmm := hcm.2.1 hc9
        calc c m * p ^ (t' + 100) * q ^ 100
            = (c m * p ^ 100) * (p ^ t' * q ^ 100) := by ring
          _ ≤ (c (4 * m % 3 ^ k) * q ^ 100 + cbarG k c w * (p ^ 79 * q ^ 21)) *
              (p ^ t' * q ^ 100) := Nat.mul_le_mul_right _ hcmm
          _ ≤ (c (4 * m % 3 ^ k) * q ^ 100 + c (2 * b % 3 ^ k) * (p ^ 79 * q ^ 21)) *
              (p ^ t' * q ^ 100) := by
              apply Nat.mul_le_mul_right
              apply Nat.add_le_add_left
              exact Nat.mul_le_mul_right _ hcb
          _ = (c (4 * m % 3 ^ k) * p ^ t' * q ^ 100) * q ^ 100 +
              (c (2 * b % 3 ^ k) * p ^ (t' + 79) * q ^ 100) * q ^ 21 := by ring
          _ ≤ (cnt (4 * a) (cap t' * (4 * a)) * (Cmax * q ^ t' * p ^ 100)) * q ^ 100 +
              (cnt (2 * b) (cap (t' + 79) * (2 * b)) *
                (Cmax * q ^ (t' + 79) * p ^ 100)) * q ^ 21 :=
              Nat.add_le_add (Nat.mul_le_mul_right _ ih4) (Nat.mul_le_mul_right _ ih2)
          _ = (cnt (4 * a) (cap t' * (4 * a)) + cnt (2 * b) (cap (t' + 79) * (2 * b))) *
              (Cmax * q ^ (t' + 100) * p ^ 100) := by ring
          _ ≤ cnt a (cap (t' + 100) * a) * (Cmax * q ^ (t' + 100) * p ^ 100) :=
              Nat.mul_le_mul_right _ hrec
      · -- (D2): doubling only
        have hrec := cnt_rec_five a t'
        have hcmm := hcm.1 hc9
        calc c m * p ^ (t' + 100) * q ^ 100
            = (c m * p ^ 100) * (p ^ t' * q ^ 100) := by ring
          _ ≤ (c (4 * m % 3 ^ k) * q ^ 100) * (p ^ t' * q ^ 100) :=
              Nat.mul_le_mul_right _ hcmm
          _ = (c (4 * m % 3 ^ k) * p ^ t' * q ^ 100) * q ^ 100 := by ring
          _ ≤ (cnt (4 * a) (cap t' * (4 * a)) * (Cmax * q ^ t' * p ^ 100)) * q ^ 100 :=
              Nat.mul_le_mul_right _ ih4
          _ = cnt (4 * a) (cap t' * (4 * a)) * (Cmax * q ^ (t' + 100) * p ^ 100) := by ring
          _ ≤ cnt a (cap (t' + 100) * a) * (Cmax * q ^ (t' + 100) * p ^ 100) :=
              Nat.mul_le_mul_right _ hrec
      · -- (D3): child b at the ADVANCED offset 129
        obtain ⟨b, hb3, hbodd, hbt, hb3le, hblt⟩ := odd_branch h3a ha3
        have hrec := cnt_rec_eight (t := t') h3a hb3 hbt hb3le h8
        have hb8 : reaches b 8 := reaches_trans ⟨1, by show terras b = a; exact hbt⟩ h8
        have hbb3 : b % 3 = 2 := by omega
        have hLb := L_child_eight hb3 (by omega)
        have ihb := ih (10 * (t' + 129) + L b) (by omega) (t' + 129) b rfl
          hb3le hbb3 hb8
        set w := (2 * m - 1) % 3 ^ k / 3 with hwdef
        have hw : w < 3 ^ (k - 1) := by
          have : (2 * m - 1) % 3 ^ k < 3 ^ k := Nat.mod_lt _ hP
          omega
        have hWmod : (3 * b) % 3 ^ k = (2 * m - 1) % 3 ^ k := by
          rw [hb3]
          exact sub_mod_transfer hmdef.symm (by omega)
        have hcong : b % 3 ^ (k - 1) = w := by
          apply third_mod
          rw [← hH]; exact hWmod
        have hcb := cbarG_le_of_lift c hk1 hw hcong
        have hcmm := hcm.2.2 hc9
        have hq29 : 0 < q ^ 29 := by positivity
        have key : (c m * p ^ (t' + 100) * q ^ 100) * q ^ 29 ≤
            (cnt a (cap (t' + 100) * a) * (Cmax * q ^ (t' + 100) * p ^ 100)) * q ^ 29 := by
          calc (c m * p ^ (t' + 100) * q ^ 100) * q ^ 29
              = (c m * p ^ 100 * q ^ 29) * (p ^ t' * q ^ 100) := by ring
            _ ≤ (c (4 * m % 3 ^ k) * q ^ 129 + cbarG k c w * p ^ 129) *
                (p ^ t' * q ^ 100) := Nat.mul_le_mul_right _ hcmm
            _ ≤ (c (4 * m % 3 ^ k) * q ^ 129 + c (b % 3 ^ k) * p ^ 129) *
                (p ^ t' * q ^ 100) := by
                apply Nat.mul_le_mul_right
                apply Nat.add_le_add_left
                exact Nat.mul_le_mul_right _ hcb
            _ = (c (4 * m % 3 ^ k) * p ^ t' * q ^ 100) * q ^ 129 +
                (c (b % 3 ^ k) * p ^ (t' + 129) * q ^ 100) := by ring
            _ ≤ (cnt (4 * a) (cap t' * (4 * a)) * (Cmax * q ^ t' * p ^ 100)) * q ^ 129 +
                (cnt b (cap (t' + 129) * b) * (Cmax * q ^ (t' + 129) * p ^ 100)) :=
                Nat.add_le_add (Nat.mul_le_mul_right _ ih4) ihb
            _ = (cnt (4 * a) (cap t' * (4 * a)) + cnt b (cap (t' + 129) * b)) *
                (Cmax * q ^ (t' + 129) * p ^ 100) := by ring
            _ ≤ cnt a (cap (t' + 100) * a) * (Cmax * q ^ (t' + 129) * p ^ 100) :=
                Nat.mul_le_mul_right _ hrec
            _ = (cnt a (cap (t' + 100) * a) * (Cmax * q ^ (t' + 100) * p ^ 100)) * q ^ 29 := by
                ring
        exact Nat.le_of_mul_le_mul_right key hq29

end G50
end Collatz
