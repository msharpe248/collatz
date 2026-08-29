/-
  Collatz — The Word-Complexity Ladder, Rung One (the running example)

  This file contains NO axioms and NO claim to prove the conjecture.

  RUNG ONE (`no_shifted_sigWord_itinerary`): no natural number has a
  Terras parity itinerary equal to the fixed point of the substitution
  σ : 1 ↦ 110, 0 ↦ 011, or to any shift of it.  The fixed point

      w = 110 110 011 011 110 011 …

  has odd-step density 2/3 > log 2 / log 3, so it lies in the band
  where the density corridor allows a divergent orbit to live.  It
  cannot.

  METHOD.  RUNG1_ATTACK.md reduces the statement to the irrationality
  of the 2-adic Mahler value F₂(8/9), F(z) = Σ w_i z^i, and records
  that the naive truncation route provably fails (exponent 0.946 < 1).
  What closes it is Mahler's method with a degree-one auxiliary form,
  in a purely finite, integer form:

    * a Padé form  E(z) = p₀(z) + p₁(z)·F(z),  deg p_i ≤ 4,  with
      ord_z E = 9 and leading coefficient −1 (a finite check on the
      first ten letters of w);
    * the functional equation  F(z) = (z+z²)/(1−z³) + (1−z²)F(z³),
      here as an exact identity between prefix sums (`preS_three`);
    * iteration along α_k = (8/9)^{3^k}:  |α_k|₂ = 2^{−3^{k+1}} → 0,
      so the 2-adic size of E(α_k) is EXACTLY 2^{−9·3^{k+1}}, while a
      rational value of F₂(8/9) forces E(α_k) to be a rational whose
      height grows only like 9^{(13/2)·3^k}.  Since 2^{27} > 3^{13},
      the two bounds collide for large k.

  Everything is expressed with divisibility of integers by powers of 2
  and with integer size bounds; no p-adic analysis is used.
-/

import Collatz.Ladder

namespace Collatz

/-! ## The word -/

/-- The fixed point of σ : 1 ↦ 110, 0 ↦ 011, starting from 1. -/
def sigWord (q : ℕ) : ℕ :=
  if _h : q = 0 then 1
  else if q % 3 = 0 then sigWord (q / 3)
  else if q % 3 = 1 then 1
  else 1 - sigWord (q / 3)
decreasing_by all_goals omega

theorem sigWord_le_one (q : ℕ) : sigWord q ≤ 1 := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rw [sigWord]
    split_ifs with h0 h1 h2
    · exact le_refl 1
    · exact ih _ (by omega)
    · exact le_refl 1
    · omega

theorem sigWord_zero : sigWord 0 = 1 := by
  rw [sigWord]; simp

theorem sigWord_three (q : ℕ) : sigWord (3 * q) = sigWord q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · rw [sigWord]
    have h1 : ¬ 3 * q = 0 := by omega
    have h2 : 3 * q % 3 = 0 := by omega
    have h3 : 3 * q / 3 = q := by omega
    simp [h1, h2, h3]

theorem sigWord_three_one (q : ℕ) : sigWord (3 * q + 1) = 1 := by
  rw [sigWord]
  have h1 : ¬ 3 * q + 1 = 0 := by omega
  have h2 : ¬ (3 * q + 1) % 3 = 0 := by omega
  have h3 : (3 * q + 1) % 3 = 1 := by omega
  simp [h3]

theorem sigWord_three_two (q : ℕ) : sigWord (3 * q + 2) = 1 - sigWord q := by
  rw [sigWord]
  have h1 : ¬ 3 * q + 2 = 0 := by omega
  have h2 : ¬ (3 * q + 2) % 3 = 0 := by omega
  have h3 : ¬ (3 * q + 2) % 3 = 1 := by omega
  have h4 : (3 * q + 2) / 3 = q := by omega
  simp [h4]

/-- The first ten letters: 1 1 0 1 1 0 0 1 1 1. -/
theorem sigWord_first_ten :
    sigWord 0 = 1 ∧ sigWord 1 = 1 ∧ sigWord 2 = 0 ∧ sigWord 3 = 1 ∧
    sigWord 4 = 1 ∧ sigWord 5 = 0 ∧ sigWord 6 = 0 ∧ sigWord 7 = 1 ∧
    sigWord 8 = 1 ∧ sigWord 9 = 1 := by
  have h0 : sigWord 0 = 1 := sigWord_zero
  have h1 : sigWord 1 = 1 := sigWord_three_one 0
  have h2 : sigWord 2 = 1 - sigWord 0 := sigWord_three_two 0
  have h3 : sigWord 3 = sigWord 1 := sigWord_three 1
  have h4 : sigWord 4 = 1 := sigWord_three_one 1
  have h5 : sigWord 5 = 1 - sigWord 1 := sigWord_three_two 1
  have h6 : sigWord 6 = sigWord 2 := sigWord_three 2
  have h7 : sigWord 7 = 1 := sigWord_three_one 2
  have h8 : sigWord 8 = 1 - sigWord 2 := sigWord_three_two 2
  have h9 : sigWord 9 = sigWord 3 := sigWord_three 3
  omega

/-! ## Prefix sums of the generating function, homogenised -/

/-- `preS a b L = Σ_{q<L} w_q a^q b^(L-1-q)`, i.e. b^(L-1)·P_L(a/b) where
    P_L is the degree-<L prefix of F(z) = Σ w_i z^i. -/
def preS (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | L + 1 => b * preS a b L + (sigWord L : ℤ) * a ^ L

/-- The all-ones analogue: `geomS a b L = Σ_{q<L} a^q b^(L-1-q)`. -/
def geomS (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | L + 1 => b * geomS a b L + a ^ L

theorem geomS_mul (a b : ℤ) : ∀ L, (b - a) * geomS a b L = b ^ L - a ^ L := by
  intro L
  induction L with
  | zero => simp [geomS]
  | succ L ih =>
    simp only [geomS, pow_succ]
    linear_combination b * ih

/-- THE FUNCTIONAL EQUATION, in exact finite form:
    P_{3L}(z) = (z+z²)·Σ_{q<L} z^{3q} + (1−z²)·P_L(z³), homogenised. -/
theorem preS_three (a b : ℤ) : ∀ L,
    preS a b (3 * L) =
      (a * b + a ^ 2) * geomS (a ^ 3) (b ^ 3) L +
        (b ^ 2 - a ^ 2) * preS (a ^ 3) (b ^ 3) L := by
  intro L
  induction L with
  | zero => simp [preS, geomS]
  | succ L ih =>
    have e : 3 * (L + 1) = 3 * L + 2 + 1 := by ring
    rw [e]
    simp only [preS, geomS]
    rw [sigWord_three, sigWord_three_one, sigWord_three_two]
    have hw := sigWord_le_one L
    rw [Nat.cast_sub hw]
    rw [ih]
    push_cast
    ring

theorem preS_succ (a b : ℤ) (L : ℕ) :
    preS a b (L + 1) = b * preS a b L + (sigWord L : ℤ) * a ^ L := rfl

/-! ## The correction term as a function of the word alone -/

/-- `wordD u T = Σ_{i<T, u_i=1} 2^i 3^(#ones of u in (i,T))`, computed by
    appending letters at the back: d(w·x) = 3^x·d(w) + x·2^|w|. -/
def wordD (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | T + 1 => 3 ^ u T * wordD u T + 2 ^ T * u T

/-- Number of ones among the first `T` letters. -/
def wordJ (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | T + 1 => wordJ u T + u T

theorem oddSteps_one (m : ℕ) : oddSteps 1 m = m % 2 := by
  simp only [oddSteps]
  split_ifs with h <;> omega

theorem dcoef_one (m : ℕ) : dcoef 1 m = m % 2 := by
  simp only [dcoef, oddSteps, pow_zero, mul_zero, add_zero]
  split_ifs with h <;> omega

theorem dcoef_succ_back (T n : ℕ) :
    dcoef (T + 1) n =
      3 ^ (terras_iter T n % 2) * dcoef T n + 2 ^ T * (terras_iter T n % 2) := by
  rw [dcoef_add T 1 n, oddSteps_one, dcoef_one]

theorem oddSteps_succ_back (T n : ℕ) :
    oddSteps (T + 1) n = oddSteps T n + terras_iter T n % 2 := by
  rw [oddSteps_add T 1 n, oddSteps_one]

/-- On an orbit whose itinerary is the word `u`, the correction term and
    the odd-step count are the word-level quantities. -/
theorem dcoef_eq_wordD (u : ℕ → ℕ) (n : ℕ) : ∀ T,
    (∀ t, t < T → terras_iter t n % 2 = u t) →
    dcoef T n = wordD u T ∧ oddSteps T n = wordJ u T := by
  intro T
  induction T with
  | zero => intro _; simp [wordD, wordJ]
  | succ T ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih (fun t ht => h t (by omega))
    rw [dcoef_succ_back, oddSteps_succ_back, h T (by omega), h1, h2]
    simp [wordD, wordJ]

/-- The cocycle law at the word level. -/
theorem wordD_add (u : ℕ → ℕ) (s : ℕ) : ∀ T,
    wordD u (s + T) =
      3 ^ wordJ (fun t => u (s + t)) T * wordD u s +
        2 ^ s * wordD (fun t => u (s + t)) T ∧
    wordJ u (s + T) = wordJ u s + wordJ (fun t => u (s + t)) T := by
  intro T
  induction T with
  | zero => simp [wordD, wordJ]
  | succ T ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [show s + (T + 1) = (s + T) + 1 by omega]
    simp only [wordD, wordJ]
    rw [h1, h2]
    constructor
    · ring
    · ring

/-- THE BLOCK FORMULA: along the fixed point, prefixes of length 3L have
    exactly 2L ones and correction term 10·(9^L − 8^L) − 5·S_L. -/
theorem wordD_sigWord_three : ∀ L,
    (wordD sigWord (3 * L) : ℤ) = 10 * (9 ^ L - 2 ^ (3 * L)) - 5 * preS 8 9 L ∧
    wordJ sigWord (3 * L) = 2 * L := by
  intro L
  induction L with
  | zero => simp [wordD, wordJ, preS]
  | succ L ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [show 3 * (L + 1) = 3 * L + 1 + 1 + 1 by ring]
    simp only [wordD, wordJ, preS]
    rw [sigWord_three, sigWord_three_one, sigWord_three_two]
    have hw : sigWord L = 0 ∨ sigWord L = 1 := by
      have := sigWord_le_one L; omega
    rcases hw with h0 | h0
    · rw [h0]
      constructor
      · push_cast
        rw [h1, show (8 : ℤ) ^ L = 2 ^ (3 * L) by rw [pow_mul]; norm_num]
        ring
      · omega
    · rw [h0]
      constructor
      · push_cast
        rw [h1, show (8 : ℤ) ^ L = 2 ^ (3 * L) by rw [pow_mul]; norm_num]
        ring
      · omega

/-! ## From an itinerary to the level-0 hypothesis -/

/-- If the itinerary of `n` is the s-shift of the fixed point, then the
    2-adic number x(w) is the rational (2^s n − d_s)/3^{j_s}, in finite
    form: with p = 2^s n − d_s and q = 3^{j_s},
        2^{3L} ∣ 9^L (p + 10 q) − 5 q S_L   for all L with 3L ≥ s. -/
theorem link (n s : ℕ) (h : ∀ t, terras_iter t n % 2 = sigWord (s + t)) :
    ∀ L, s ≤ 3 * L →
    (2 : ℤ) ^ (3 * L) ∣
      9 ^ L * ((2 ^ s * n - wordD sigWord s) + 10 * 3 ^ wordJ sigWord s) -
        5 * 3 ^ wordJ sigWord s * preS 8 9 L := by
  intro L hL
  obtain ⟨T, hT⟩ : ∃ T, 3 * L = s + T := ⟨3 * L - s, by omega⟩
  obtain ⟨hD, hJ⟩ := wordD_add sigWord s T
  obtain ⟨hd, hj⟩ :=
    dcoef_eq_wordD (fun t => sigWord (s + t)) n T (fun t _ => h t)
  have hex := terras_exact_form T n
  obtain ⟨hB, hB2⟩ := wordD_sigWord_three L
  rw [hT] at hB hB2
  rw [hD] at hB
  rw [hJ] at hB2
  rw [← hd] at hB
  rw [← hj] at hB hB2
  -- exponent bookkeeping
  have h9 : (9 : ℤ) ^ L = 3 ^ wordJ sigWord s * 3 ^ oddSteps T n := by
    rw [← pow_add, hB2, pow_mul]; norm_num
  have h2 : (2 : ℤ) ^ (3 * L) = 2 ^ s * 2 ^ T := by
    rw [hT, pow_add]
  have hexZ : (2 : ℤ) ^ T * terras_iter T n =
      3 ^ oddSteps T n * n + dcoef T n := by exact_mod_cast hex
  refine ⟨3 ^ wordJ sigWord s * terras_iter T n + 10 * 3 ^ wordJ sigWord s, ?_⟩
  push_cast at hB
  rw [pow_add, h9] at hB
  rw [h9, h2]
  linear_combination (-(3 : ℤ) ^ wordJ sigWord s) * hB -
    (3 : ℤ) ^ wordJ sigWord s * 2 ^ s * hexZ

/-! ## The Mahler tower -/

/-- α_k = a_k / b_k with a_k = 8^{3^k} = 2^{3^{k+1}}, b_k = 9^{3^k}. -/
def lvA (k : ℕ) : ℤ := 8 ^ (3 ^ k)
def lvB (k : ℕ) : ℤ := 9 ^ (3 ^ k)

theorem lvA_succ (k : ℕ) : lvA (k + 1) = lvA k ^ 3 := by
  unfold lvA; rw [← pow_mul, pow_succ]

theorem lvB_succ (k : ℕ) : lvB (k + 1) = lvB k ^ 3 := by
  unfold lvB; rw [← pow_mul, pow_succ]

theorem lvA_eq_two_pow (k : ℕ) : lvA k = 2 ^ (3 ^ (k + 1)) := by
  unfold lvA
  rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_mul, pow_succ, mul_comm]

/-- Denominator and numerator of the rational value forced at level k
    (D_k, u_k): running the functional equation backwards. -/
def lvD (D0 : ℤ) : ℕ → ℤ
  | 0 => D0
  | k + 1 => lvD D0 k * (lvB k ^ 2 - lvA k ^ 2) * (lvB k ^ 3 - lvA k ^ 3)

def lvU (D0 u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | k + 1 => lvB k ^ 2 *
      ((lvB k ^ 3 - lvA k ^ 3) * lvU D0 u0 k -
        lvD D0 k * lvA k * (lvA k + lvB k) * lvB k)

/-- The level-k hypothesis: for every prefix length L+1 ≥ L0+1,
    u_k·b_k^L ≡ D_k·S_{L+1}(a_k, b_k)  (mod 2^{3^{k+1}(L+1)}). -/
def Hyp (D0 u0 : ℤ) (L0 k : ℕ) : Prop :=
  ∀ L, L0 ≤ L →
    (2 : ℤ) ^ (3 ^ (k + 1) * (L + 1)) ∣
      lvU D0 u0 k * lvB k ^ L - lvD D0 k * preS (lvA k) (lvB k) (L + 1)

/-- THE TRANSPORT: the functional equation carries the hypothesis one
    level up the tower. -/
theorem Hyp_succ (D0 u0 : ℤ) (L0 k : ℕ) (hk : Hyp D0 u0 L0 k) :
    Hyp D0 u0 L0 (k + 1) := by
  intro L hL
  obtain ⟨c, hc⟩ := hk (3 * L + 2) (by omega)
  rw [show 3 * L + 2 + 1 = 3 * (L + 1) by ring] at hc
  have hP := preS_three (lvA k) (lvB k) (L + 1)
  have hG := geomS_mul (lvA k ^ 3) (lvB k ^ 3) (L + 1)
  have hE : (2 : ℤ) ^ (3 ^ (k + 1) * (3 * (L + 1))) =
      2 ^ (3 ^ (k + 1 + 1) * (L + 1)) := by
    congr 1; ring
  have ha : (lvA k ^ 3) ^ (L + 1) = 2 ^ (3 ^ (k + 1 + 1) * (L + 1)) := by
    rw [lvA_eq_two_pow, ← pow_mul, ← pow_mul]
    exact hE
  rw [hE] at hc
  refine ⟨(lvB k ^ 3 - lvA k ^ 3) * c - lvD D0 k * (lvA k * lvB k + lvA k ^ 2), ?_⟩
  simp only [lvU, lvD, lvA_succ, lvB_succ]
  linear_combination (lvB k ^ 3 - lvA k ^ 3) * hc +
    lvD D0 k * (lvB k ^ 3 - lvA k ^ 3) * hP +
    lvD D0 k * (lvA k * lvB k + lvA k ^ 2) * hG -
    lvD D0 k * (lvA k * lvB k + lvA k ^ 2) * ha

theorem Hyp_all (D0 u0 : ℤ) (L0 : ℕ) (h0 : Hyp D0 u0 L0 0) : ∀ k, Hyp D0 u0 L0 k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => exact Hyp_succ D0 u0 L0 k ih

/-! ## The Padé form -/

/-- p₀(z) = 1 + z³ − z⁴, homogenised to degree 4: b⁴·p₀(a/b). -/
def P0 (a b : ℤ) : ℤ := b ^ 4 + a ^ 3 * b - a ^ 4
/-- p₁(z) = −1 + z − z² + z³, homogenised to degree 4: b⁴·p₁(a/b). -/
def P1 (a b : ℤ) : ℤ := -b ^ 4 + a * b ^ 3 - a ^ 2 * b ^ 2 + a ^ 3 * b

/-- THE CERTIFICATE: p₀ + p₁·F vanishes to order exactly 9 at z = 0 with
    leading coefficient −1 — a computation on the first ten letters. -/
theorem pade_base (a b : ℤ) :
    b ^ 9 * P0 a b + P1 a b * preS a b 10 =
      a ^ 9 * (-b ^ 4 + a * (b ^ 3 + a ^ 2 * b)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := sigWord_first_ten
  simp only [preS, P0, P1, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  push_cast
  ring

/-- The certificate propagates to every longer prefix: the extra terms
    are divisible by a^{10}. -/
theorem pade_gen (a b : ℤ) : ∀ M, ∃ R : ℤ,
    b ^ (9 + M) * P0 a b + P1 a b * preS a b (9 + M + 1) =
      a ^ 9 * (-b ^ (4 + M) + a * R) := by
  intro M
  induction M with
  | zero => exact ⟨b ^ 3 + a ^ 2 * b, by simpa using pade_base a b⟩
  | succ M ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨b * R + P1 a b * (sigWord (9 + M + 1) : ℤ) * a ^ M, ?_⟩
    rw [show 9 + (M + 1) + 1 = (9 + M + 1) + 1 by ring, preS_succ a b (9 + M + 1)]
    linear_combination b * hR

/-! ## The level contradiction -/

/-- At a level where a = 2^v, the hypothesis forces
    Z := P₀·D + P₁·u to be a nonzero multiple of 2^{9v}: the 2-adic size of
    the Padé form is exactly |a|₂^9, and the hypothesis says the form
    evaluates to the rational Z/(b^{…}·D). -/
theorem level_dvd (D u a b : ℤ) (v : ℕ) (hv : 1 ≤ v) (ha : a = 2 ^ v)
    (hb : Odd b) (hD : Odd D) (M : ℕ)
    (h : (2 : ℤ) ^ (v * (9 + M + 1)) ∣
      u * b ^ (9 + M) - D * preS a b (9 + M + 1)) :
    (2 : ℤ) ^ (9 * v) ∣ P0 a b * D + P1 a b * u ∧
      P0 a b * D + P1 a b * u ≠ 0 := by
  obtain ⟨R, hR⟩ := pade_gen a b M
  obtain ⟨t, ht⟩ := h
  subst ha
  set Z := P0 (2 ^ v) b * D + P1 (2 ^ v) b * u with hZ
  set O := D * (-b ^ (4 + M)) +
    (D * (2 ^ v * R) + P1 (2 ^ v) b * 2 ^ (v * (1 + M)) * t) with hO
  have key : b ^ (9 + M) * Z = 2 ^ (9 * v) * O := by
    rw [hZ, hO]
    linear_combination D * hR + P1 (2 ^ v) b * ht
  have hOodd : Odd O := by
    rw [hO]
    apply Odd.add_even (hD.mul hb.pow.neg)
    have e1 : Even ((2 : ℤ) ^ v) := Int.even_pow.mpr ⟨by decide, by omega⟩
    have e2 : Even ((2 : ℤ) ^ (v * (1 + M))) :=
      Int.even_pow.mpr ⟨by decide, by positivity⟩
    exact ((e1.mul_right R).mul_left D).add ((e2.mul_left _).mul_right _)
  have hZne : Z ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at key
    have h2 : (2 : ℤ) ^ (9 * v) ≠ 0 := pow_ne_zero _ (by norm_num)
    have : O = 0 := (mul_eq_zero.mp key.symm).resolve_left h2
    rw [this] at hOodd
    have := Int.odd_iff.mp hOodd
    norm_num at this
  refine ⟨?_, hZne⟩
  have h1 : (2 : ℤ) ^ (9 * v) ∣ b ^ (9 + M) * Z := ⟨O, key⟩
  have hnb : ¬ (2 : ℤ) ∣ b ^ (9 + M) := by
    intro h2
    exact (Int.not_even_iff_odd.mpr hb.pow) (even_iff_two_dvd.mpr h2)
  exact Int.prime_two.pow_dvd_of_dvd_mul_left _ hnb h1

/-- Size of the Padé value: |Z| ≤ 7·b⁴·max(|D|,|u|). -/
theorem abs_Z_le (D u a b : ℤ) (ha0 : 0 ≤ a) (hab : a ≤ b) (m : ℤ)
    (hD : |D| ≤ m) (hu : |u| ≤ m) :
    |P0 a b * D + P1 a b * u| ≤ 7 * b ^ 4 * m := by
  have hb0 : 0 ≤ b := le_trans ha0 hab
  have hb4 : 0 ≤ b ^ 4 := pow_nonneg hb0 4
  have h3 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha0 hab 3
  have h2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha0 hab 2
  have h4 : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha0 hab 4
  have ha2 : 0 ≤ a ^ 2 := pow_nonneg ha0 2
  have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha0 3
  have ha4 : 0 ≤ a ^ 4 := pow_nonneg ha0 4
  have hb2 : 0 ≤ b ^ 2 := pow_nonneg hb0 2
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb0 3
  have e1 : a ^ 3 * b ≤ b ^ 4 := by nlinarith
  have e2 : a * b ^ 3 ≤ b ^ 4 := by nlinarith
  have e3 : a ^ 2 * b ^ 2 ≤ b ^ 4 := by nlinarith
  have f1 : 0 ≤ a ^ 3 * b := mul_nonneg ha3 hb0
  have f2 : 0 ≤ a * b ^ 3 := mul_nonneg ha0 hb3
  have f3 : 0 ≤ a ^ 2 * b ^ 2 := mul_nonneg ha2 hb2
  have hP0 : |P0 a b| ≤ 3 * b ^ 4 := by
    unfold P0
    rw [abs_le]; constructor <;> linarith
  have hP1 : |P1 a b| ≤ 4 * b ^ 4 := by
    unfold P1
    rw [abs_le]; constructor <;> linarith
  calc |P0 a b * D + P1 a b * u|
      ≤ |P0 a b * D| + |P1 a b * u| := abs_add_le _ _
    _ = |P0 a b| * |D| + |P1 a b| * |u| := by rw [abs_mul, abs_mul]
    _ ≤ 3 * b ^ 4 * m + 4 * b ^ 4 * m :=
        add_le_add (mul_le_mul hP0 hD (abs_nonneg _) (by positivity))
          (mul_le_mul hP1 hu (abs_nonneg _) (by positivity))
    _ = 7 * b ^ 4 * m := by ring

/-! ## Facts about the tower -/

theorem lvA_nonneg (k : ℕ) : 0 ≤ lvA k := by unfold lvA; positivity
theorem lvB_pos (k : ℕ) : 0 < lvB k := by unfold lvB; positivity
theorem lvA_le_lvB (k : ℕ) : lvA k ≤ lvB k := by
  unfold lvA lvB; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
theorem lvB_odd (k : ℕ) : Odd (lvB k) := by
  unfold lvB; exact Odd.pow (Int.odd_iff.mpr (by norm_num))
theorem lvA_even (k : ℕ) : Even (lvA k) := by
  unfold lvA
  exact Int.even_pow.mpr ⟨Int.even_iff.mpr (by norm_num), by positivity⟩

theorem lvD_odd (D0 : ℤ) (hD : Odd D0) : ∀ k, Odd (lvD D0 k) := by
  intro k
  induction k with
  | zero => exact hD
  | succ k ih =>
    simp only [lvD]
    have h2 : Odd (lvB k ^ 2 - lvA k ^ 2) :=
      (lvB_odd k).pow.sub_even ((lvA_even k).pow_of_ne_zero (by norm_num))
    have h3 : Odd (lvB k ^ 3 - lvA k ^ 3) :=
      (lvB_odd k).pow.sub_even ((lvA_even k).pow_of_ne_zero (by norm_num))
    exact (ih.mul h2).mul h3

/-- The height budget at level k. -/
def lvE (m0 : ℤ) (k : ℕ) : ℤ := 3 ^ k * 9 ^ (3 * 3 ^ k) * m0

theorem lvE_succ (m0 : ℤ) (k : ℕ) : lvE m0 (k + 1) = 3 * lvB k ^ 6 * lvE m0 k := by
  unfold lvE lvB
  have e : (9 : ℤ) ^ (3 * 3 ^ (k + 1)) = 9 ^ (3 ^ k * 6) * 9 ^ (3 * 3 ^ k) := by
    rw [← pow_add]; congr 1; ring
  rw [← pow_mul, e, pow_succ]
  ring

/-- |D_k|, |u_k| ≤ E_k: the rational forced at level k has height at
    most 9^{(3/2)·3^{k+1}}·3^k·max(|D₀|,|u₀|). -/
theorem lv_bounds (D0 u0 m0 : ℤ) (hm : 0 ≤ m0) (hD : |D0| ≤ m0) (hu : |u0| ≤ m0) :
    ∀ k, |lvD D0 k| ≤ lvE m0 k ∧ |lvU D0 u0 k| ≤ lvE m0 k := by
  intro k
  induction k with
  | zero =>
    simp only [lvD, lvU, lvE, pow_zero, one_mul, mul_one]
    constructor <;> nlinarith
  | succ k ih =>
    obtain ⟨hDk, huk⟩ := ih
    have ha0 := lvA_nonneg k
    have hab := lvA_le_lvB k
    have hb1 : 0 < lvB k := lvB_pos k
    set a := lvA k
    set b := lvB k
    set E := lvE m0 k
    have hE0 : 0 ≤ E := le_trans (abs_nonneg _) hDk
    have h2 : 0 ≤ b ^ 2 - a ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ ha0 hab 2)
    have h3 : 0 ≤ b ^ 3 - a ^ 3 := sub_nonneg.mpr (pow_le_pow_left₀ ha0 hab 3)
    have h2' : b ^ 2 - a ^ 2 ≤ b ^ 2 := by linarith [pow_nonneg ha0 2]
    have h3' : b ^ 3 - a ^ 3 ≤ b ^ 3 := by linarith [pow_nonneg ha0 3]
    have hb2 : 0 ≤ b ^ 2 := by positivity
    have hb3 : 0 ≤ b ^ 3 := by positivity
    have hb5 : 0 ≤ b ^ 5 := by positivity
    have hbb : b ^ 5 ≤ b ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [lvE_succ]
    constructor
    · simp only [lvD]
      rw [abs_mul, abs_mul, abs_of_nonneg h2, abs_of_nonneg h3]
      calc |lvD D0 k| * (b ^ 2 - a ^ 2) * (b ^ 3 - a ^ 3)
          ≤ E * b ^ 2 * b ^ 3 :=
            mul_le_mul (mul_le_mul hDk h2' h2 hE0) h3' h3 (by positivity)
        _ = b ^ 5 * E := by ring
        _ ≤ 3 * b ^ 6 * E := by nlinarith
    · simp only [lvU]
      rw [abs_mul, abs_of_nonneg hb2]
      have hin : |(b ^ 3 - a ^ 3) * lvU D0 u0 k - lvD D0 k * a * (a + b) * b|
          ≤ b ^ 3 * E + E * (2 * b ^ 3) := by
        calc |(b ^ 3 - a ^ 3) * lvU D0 u0 k - lvD D0 k * a * (a + b) * b|
            ≤ |(b ^ 3 - a ^ 3) * lvU D0 u0 k| + |lvD D0 k * a * (a + b) * b| :=
              abs_sub _ _
          _ = (b ^ 3 - a ^ 3) * |lvU D0 u0 k| + |lvD D0 k| * a * (a + b) * b := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h3,
                abs_of_nonneg ha0, abs_of_nonneg (by linarith : 0 ≤ a + b),
                abs_of_nonneg (le_of_lt hb1)]
          _ ≤ b ^ 3 * E + E * (2 * b ^ 3) := by
              apply add_le_add
              · exact mul_le_mul h3' huk (abs_nonneg _) hb3
              · have : |lvD D0 k| * a * (a + b) * b ≤ E * b * (2 * b) * b := by
                  apply mul_le_mul (mul_le_mul (mul_le_mul hDk hab ha0 hE0)
                    (by linarith) (by linarith) (by positivity)) le_rfl
                    (le_of_lt hb1) (by positivity)
                linarith
      calc b ^ 2 * |(b ^ 3 - a ^ 3) * lvU D0 u0 k - lvD D0 k * a * (a + b) * b|
          ≤ b ^ 2 * (b ^ 3 * E + E * (2 * b ^ 3)) :=
            mul_le_mul_of_nonneg_left hin hb2
        _ = 3 * b ^ 5 * E := by ring
        _ ≤ 3 * b ^ 6 * E := by nlinarith

/-- THE NUMERIC INEQUALITY: 2^{27·3^k} beats 7·3^k·9^{7·3^k}·m₀ once k ≥ m₀,
    because 2^27 = 134217728 > 28·9^7 = 133923132. -/
theorem final_ineq (k : ℕ) (m0 : ℤ) (hk : m0 ≤ k) :
    7 * lvB k ^ 4 * lvE m0 k < 2 ^ (9 * 3 ^ (k + 1)) := by
  unfold lvB lvE
  have hk3 : k + 1 ≤ 3 ^ k := Nat.lt_pow_self (by norm_num)
  have hk9 : (k : ℤ) < 9 ^ k := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 9)
  have h3k : (0 : ℤ) < 3 ^ k := by positivity
  have h9 : (0 : ℤ) < 9 ^ (7 * 3 ^ k) := by positivity
  -- 28^(3^k) ≥ 28^(k+1) = 28·28^k ≥ 28·27^k = 28·3^k·9^k > 7·3^k·k ≥ 7·3^k·m0
  have hA : (28 : ℤ) ^ (k + 1) ≤ 28 ^ (3 ^ k) :=
    pow_le_pow_right₀ (by norm_num) hk3
  have hB : (27 : ℤ) ^ k ≤ 28 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hC : (27 : ℤ) ^ k = 3 ^ k * 9 ^ k := by rw [← mul_pow]; norm_num
  have hD : 7 * 3 ^ k * m0 < (28 : ℤ) ^ (3 ^ k) := by
    calc 7 * 3 ^ k * m0 ≤ 7 * 3 ^ k * k := by
          apply mul_le_mul_of_nonneg_left hk (by positivity)
      _ < 28 * (3 ^ k * 9 ^ k) := by nlinarith
      _ = 28 * 27 ^ k := by rw [hC]
      _ ≤ 28 * 28 ^ k := by nlinarith
      _ = 28 ^ (k + 1) := by ring
      _ ≤ 28 ^ (3 ^ k) := hA
  -- 2^(27·3^k) ≥ (28·9^7)^(3^k)
  have hE : (2 : ℤ) ^ (9 * 3 ^ (k + 1)) = (2 ^ 27) ^ (3 ^ k) := by
    rw [← pow_mul, pow_succ]; congr 1; ring
  have hF : ((28 : ℤ) * 9 ^ 7) ^ (3 ^ k) ≤ (2 ^ 27) ^ (3 ^ k) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hG : ((28 : ℤ) * 9 ^ 7) ^ (3 ^ k) = 28 ^ (3 ^ k) * 9 ^ (7 * 3 ^ k) := by
    rw [mul_pow, ← pow_mul]
  have hH : ((9 : ℤ) ^ (3 ^ k)) ^ 4 * 9 ^ (3 * 3 ^ k) = 9 ^ (7 * 3 ^ k) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [hE]
  calc 7 * ((9 : ℤ) ^ (3 ^ k)) ^ 4 * (3 ^ k * 9 ^ (3 * 3 ^ k) * m0)
      = (7 * 3 ^ k * m0) * (((9 : ℤ) ^ (3 ^ k)) ^ 4 * 9 ^ (3 * 3 ^ k)) := by ring
    _ = (7 * 3 ^ k * m0) * 9 ^ (7 * 3 ^ k) := by rw [hH]
    _ < 28 ^ (3 ^ k) * 9 ^ (7 * 3 ^ k) := by
        apply mul_lt_mul_of_pos_right hD h9
    _ = ((28 : ℤ) * 9 ^ 7) ^ (3 ^ k) := hG.symm
    _ ≤ (2 ^ 27) ^ (3 ^ k) := hF

/-! ## The core theorem and its consequences -/

/-- THE CORE: no rational with odd denominator D₀ (numerator encoded in
    u₀) is the 2-adic value x(w). Stated as: the level-0 hypothesis for
    all sufficiently long prefixes is contradictory. -/
theorem core (D0 u0 : ℤ) (hD : Odd D0) (L0 : ℕ) (h0 : Hyp D0 u0 L0 0) : False := by
  set m0 := max |D0| |u0| with hm0
  have hm0n : 0 ≤ m0 := le_trans (abs_nonneg D0) (le_max_left _ _)
  set k := m0.toNat with hk
  have hkm : m0 ≤ (k : ℤ) := by rw [hk]; exact Int.self_le_toNat m0
  have hyp := Hyp_all D0 u0 L0 h0 k
  obtain ⟨M, hM⟩ : ∃ M, max L0 9 = 9 + M := ⟨max L0 9 - 9, by omega⟩
  have hL := hyp (9 + M) (by omega)
  obtain ⟨hdvd, hne⟩ := level_dvd (lvD D0 k) (lvU D0 u0 k) (lvA k) (lvB k)
    (3 ^ (k + 1)) (Nat.one_le_pow _ _ (by norm_num)) (lvA_eq_two_pow k)
    (lvB_odd k) (lvD_odd D0 hD k) M hL
  have hlow : (2 : ℤ) ^ (9 * 3 ^ (k + 1)) ≤ |P0 (lvA k) (lvB k) * lvD D0 k + P1 (lvA k) (lvB k) * lvU D0 u0 k| :=
    Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  obtain ⟨hDb, hub⟩ := lv_bounds D0 u0 m0 hm0n (le_max_left _ _) (le_max_right _ _) k
  have hup := abs_Z_le (lvD D0 k) (lvU D0 u0 k) (lvA k) (lvB k) (lvA_nonneg k)
    (lvA_le_lvB k) (lvE m0 k) hDb hub
  have hnum := final_ineq k m0 hkm
  linarith

/-- RUNG ONE, running example: no natural number has a Terras parity
    itinerary that is a shift of the fixed point of σ : 1 ↦ 110, 0 ↦ 011.
    Equivalently: the 2-adic realization x(w) is not a rational number
    with denominator a power of 3 — in particular not a positive integer,
    and no Collatz orbit ever synchronises with w. -/
theorem no_shifted_sigWord_itinerary (n s : ℕ) :
    ¬ ∀ t, terras_iter t n % 2 = sigWord (s + t) := by
  intro h
  have hlink := link n s h
  apply core (5 * 3 ^ wordJ sigWord s)
    (9 * ((2 ^ s * n - wordD sigWord s) + 10 * 3 ^ wordJ sigWord s)) ?_ s
  · intro L hL
    have this := hlink (L + 1) (by omega)
    simp only [lvA, lvB, lvU, lvD, pow_zero, pow_one, zero_add]
    have e : (9 : ℤ) ^ (L + 1) = 9 * 9 ^ L := by ring
    rw [e] at this
    convert this using 2
    ring
  · exact (Int.odd_iff.mpr (by norm_num)).mul (Odd.pow (Int.odd_iff.mpr (by norm_num)))

/-- The unshifted statement: no natural number has itinerary w itself. -/
theorem no_sigWord_itinerary (n : ℕ) : ¬ ∀ t, terras_iter t n % 2 = sigWord t := by
  have := no_shifted_sigWord_itinerary n 0
  simpa using this

/-!
## What this means

The fixed point w of σ has odd-step density 2/3, above the critical
line log 2/log 3 ≈ 0.631, so nothing in the density corridor forbids a
divergent orbit with itinerary w.  This file shows there is none — and
none with any tail of w either — by the 2-adic Mahler method in
degree one: the Padé certificate (`pade_base`), the functional
equation (`preS_three`), the tower transport (`Hyp_succ`), the exact
2-adic size (`level_dvd`), and the height ledger (`lv_bounds`,
`final_ineq`).  The ledger closes because 2^27 > 28·9^7: per tower
level the 2-adic vanishing order triples, the height only grows like
9^{(13/2)·3^k}, and 27·log 2 > 13·log 9 + log 28.

The argument is generic: it uses only integrality of the coefficients,
constant-length substitution structure with uniform block weight, and
|8/9|₂ < 1.  Every constant-length substitution word in the
supercritical band admits the same certificate shape (a Padé pair found
by linear algebra on its first few letters), and the same proof.

The Collatz conjecture remains OPEN.  This is one rung of the ladder.
-/

end Collatz
