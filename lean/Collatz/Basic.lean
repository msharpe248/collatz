/-
  Collatz Conjecture - Basic Definitions

  This file defines the core Collatz function and related concepts.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Collatz

/-! ## Core Definitions -/

/-- The Collatz function: n ↦ n/2 if even, n ↦ 3n+1 if odd -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Iterate the Collatz function t times -/
def collatz_iter : ℕ → ℕ → ℕ
  | 0, n => n
  | t + 1, n => collatz_iter t (collatz n)

/-- The 2-adic valuation: largest k such that 2^k divides n.
    Returns 0 for n = 0 by convention. -/
def v2 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 1 then 0
  else 1 + v2 (n / 2)
termination_by n
decreasing_by
  apply Nat.div_lt_self <;> omega

/-! ## Basic Properties of Collatz -/

@[simp]
theorem collatz_even (n : ℕ) (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

@[simp]
theorem collatz_odd (n : ℕ) (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp only [collatz]
  split_ifs with h'
  · omega
  · rfl

theorem collatz_iter_zero (n : ℕ) : collatz_iter 0 n = n := rfl

theorem collatz_iter_succ (t n : ℕ) :
  collatz_iter (t + 1) n = collatz_iter t (collatz n) := rfl

/-! ## Properties of v2 -/

@[simp]
theorem v2_zero : v2 0 = 0 := by
  unfold v2
  simp

@[simp]
theorem v2_one : v2 1 = 0 := by
  unfold v2
  simp

theorem v2_odd (n : ℕ) (h : n % 2 = 1) (hn : n ≠ 0) : v2 n = 0 := by
  unfold v2
  simp [h, hn]

theorem v2_even (n : ℕ) (h : n % 2 = 0) (hn : n ≠ 0) : v2 n = 1 + v2 (n / 2) := by
  conv_lhs => unfold v2
  simp only [hn, ↓reduceIte]
  split_ifs with hodd
  · omega
  · rfl

/-- 2^(v2 n) divides n -/
theorem pow_v2_dvd (n : ℕ) (hn : n ≠ 0) : 2^(v2 n) ∣ n := by
  -- Proof by strong induction on n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hodd : n % 2 = 1
    · -- Case 1: n is odd
      -- Then v2 n = 0, so 2^0 = 1 divides n
      rw [v2_odd n hodd hn]
      simp
    · -- Case 2: n is even
      -- Then v2 n = 1 + v2 (n/2)
      have heven : n % 2 = 0 := by omega
      rw [v2_even n heven hn]
      -- Need to show: 2^(1 + v2 (n/2)) ∣ n
      -- Rewrite as 2^1 * 2^(v2 (n/2)) = 2 * 2^(v2 (n/2))
      rw [pow_add, pow_one]
      -- By IH: 2^(v2 (n/2)) ∣ (n/2)
      have hn2_pos : n / 2 ≠ 0 := by
        intro h
        have : n < 2 := by omega
        have hmod : n % 2 = n := Nat.mod_eq_of_lt this
        omega
      have hn2_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
      have ih_n2 : 2^(v2 (n / 2)) ∣ (n / 2) := ih (n / 2) hn2_lt hn2_pos
      -- Therefore 2 * 2^(v2 (n/2)) ∣ 2 * (n/2) = n
      have h1 : 2 * 2^(v2 (n/2)) ∣ 2 * (n/2) := Nat.mul_dvd_mul_left 2 ih_n2
      have h2 : n = 2 * (n/2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)).symm
      have h3 : 2 * (n/2) / 2 = n / 2 := Nat.mul_div_cancel_left (n/2) (by omega)
      rw [h2]
      simp only [h3]
      exact h1

/-- For odd r, 3r+1 is always even -/
theorem three_r_plus_one_even (r : ℕ) (hr : r % 2 = 1) : (3 * r + 1) % 2 = 0 := by
  omega

/-- For odd r, v2(3r+1) ≥ 1 -/
theorem v2_three_r_plus_one_pos (r : ℕ) (hr : r % 2 = 1) :
  v2 (3 * r + 1) ≥ 1 := by
  have heven : (3 * r + 1) % 2 = 0 := three_r_plus_one_even r hr
  have hpos : 3 * r + 1 ≠ 0 := by omega
  rw [v2_even (3 * r + 1) heven hpos]
  omega

/-! ## v2 Matching Lemmas -/

/-- If 2^v | n and n/2^v is odd, then v2(n) = v -/
theorem v2_eq_of_div_odd (n v : ℕ) (hn : n ≠ 0)
    (hdiv : 2^v ∣ n) (hodd : (n / 2^v) % 2 = 1) : v2 n = v := by
  induction v generalizing n with
  | zero =>
    simp at hdiv hodd
    exact v2_odd n hodd hn
  | succ v ih =>
    -- 2^(v+1) | n means n = 2^(v+1) * q
    -- So n is even, and n/2 = 2^v * q
    have h2v1 : 2^(v+1) = 2 * 2^v := by ring
    obtain ⟨q, hq⟩ := hdiv
    -- n = 2^(v+1) * q, so n is even
    have heven : n % 2 = 0 := by
      rw [hq, h2v1]
      simp [Nat.mul_mod]
    rw [v2_even n heven hn]
    -- Need to show: 1 + v2 (n/2) = v + 1, i.e., v2 (n/2) = v
    have h2v_pos : 2^v > 0 := by positivity
    have h2v1_pos : 2^(v+1) > 0 := by positivity
    have hn2 : n / 2 = 2^v * q := by
      rw [hq, h2v1]
      have : 2 * 2^v * q = 2 * (2^v * q) := by ring
      rw [this]
      exact Nat.mul_div_cancel_left (2^v * q) (by norm_num : 2 > 0)
    -- Show v2 (n/2) = v, then goal 1 + v2(n/2) = v+1 follows
    have hgoal : v2 (n / 2) = v := by
      apply ih
      · -- n/2 ≠ 0
        rw [hn2]
        intro h
        have : 2^v * q = 0 := h
        cases Nat.eq_zero_or_pos q with
        | inl hq0 =>
          rw [hq0, Nat.mul_zero] at hq
          exact hn hq
        | inr hqpos =>
          have : 2^v * q > 0 := Nat.mul_pos h2v_pos hqpos
          omega
      · -- 2^v | (n/2)
        rw [hn2]; exact Nat.dvd_mul_right (2^v) q
      · -- (n/2) / 2^v is odd
        rw [hn2, Nat.mul_div_cancel_left q h2v_pos]
        have h3 : n / 2^(v+1) = q := by
          rw [hq]
          exact Nat.mul_div_cancel_left q h2v1_pos
        rw [← h3]; exact hodd
    omega

/-- 2^(v2 n) does NOT divide (n / 2^(v2 n)) when n > 0 -/
theorem two_not_dvd_div_pow_v2 (n : ℕ) (hn : n ≠ 0) : (n / 2^(v2 n)) % 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hodd : n % 2 = 1
    · -- n is odd: v2 n = 0, n / 2^0 = n, n % 2 = 1
      rw [v2_odd n hodd hn]
      simp [hodd]
    · -- n is even
      have heven : n % 2 = 0 := by omega
      rw [v2_even n heven hn]
      -- v2 n = 1 + v2 (n/2)
      -- n / 2^(1 + v2(n/2)) = n / (2 * 2^(v2(n/2))) = (n/2) / 2^(v2(n/2))
      have h1 : 2^(1 + v2 (n/2)) = 2 * 2^(v2 (n/2)) := by ring
      rw [h1]
      have hdiv : n / (2 * 2^(v2 (n/2))) = n / 2 / 2^(v2 (n/2)) := by
        rw [Nat.div_div_eq_div_mul]
      rw [hdiv]
      have hn2_pos : n / 2 ≠ 0 := by
        intro h
        have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
        obtain ⟨k, hk⟩ := hdvd
        rw [hk] at h
        simp at h
        rw [h, Nat.mul_zero] at hk
        exact hn hk
      have hn2_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num)
      exact ih (n / 2) hn2_lt hn2_pos

/-- KEY LEMMA: If a ≡ b (mod 2^k) and v2(b) < k, then v2(a) = v2(b).

    Proof sketch:
    - Let v = v2(b). We have 2^v | b and b/2^v is odd.
    - Since v < k, from a ≡ b (mod 2^k) we get a ≡ b (mod 2^(v+1)).
    - Write b = 2^v * m where m = b/2^v is odd.
    - Then b % 2^(v+1) = 2^v (since m is odd).
    - So a % 2^(v+1) = 2^v as well.
    - This means a = r * 2^(v+1) + 2^v = 2^v * (2r + 1) for some r.
    - Therefore 2^v | a and a/2^v = 2r + 1 is odd.
    - By v2_eq_of_div_odd, v2(a) = v.

    This is a standard result in modular arithmetic. -/
theorem v2_of_mod_eq (a b k : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hmod : a % (2^k) = b % (2^k)) (hv : v2 b < k) : v2 a = v2 b := by
  set v := v2 b with hv_def
  have hv_dvd_b : 2^v ∣ b := pow_v2_dvd b hb
  have hb_div_odd : (b / 2^v) % 2 = 1 := two_not_dvd_div_pow_v2 b hb
  have hv1_le_k : v + 1 ≤ k := hv
  have h2v1_dvd_2k : 2^(v+1) ∣ 2^k := Nat.pow_dvd_pow 2 hv1_le_k
  have hmod_v1 : a % (2^(v+1)) = b % (2^(v+1)) := by
    calc a % (2^(v+1)) = (a % 2^k) % (2^(v+1)) := (Nat.mod_mod_of_dvd a h2v1_dvd_2k).symm
      _ = (b % 2^k) % (2^(v+1)) := by rw [hmod]
      _ = b % (2^(v+1)) := Nat.mod_mod_of_dvd b h2v1_dvd_2k
  -- Step 1: Show b % 2^(v+1) = 2^v
  -- Since 2^v | b and b/2^v is odd, we have b = 2^v * (2q + 1) for some q
  -- So b % 2^(v+1) = 2^v
  have h2v_pos : 2^v > 0 := by positivity
  have h2v1_pos : 2^(v+1) > 0 := by positivity
  have hb_eq : b = 2^v * (b / 2^v) := (Nat.mul_div_cancel' hv_dvd_b).symm
  -- b / 2^v is odd, so b / 2^v = 2 * (b / 2^v / 2) + 1
  set m := b / 2^v with hm_def
  have hm_odd : m % 2 = 1 := hb_div_odd
  -- m = 2 * (m / 2) + (m % 2) = 2 * (m / 2) + 1
  have hm_form : m = 2 * (m / 2) + 1 := by
    have := Nat.div_add_mod m 2
    omega
  -- b = 2^v * m = 2^v * (2 * (m/2) + 1) = 2^(v+1) * (m/2) + 2^v
  -- We use the fact that m = 2*(m/2) + 1 since m is odd
  have hb_form : b = 2^(v+1) * (m / 2) + 2^v := by
    -- b = 2^v * m and m = 2*(m/2) + 1 (since m is odd)
    rw [hb_eq]
    -- 2^v * m = 2^(v+1) * (m / 2) + 2^v
    -- Since m = 2*(m/2) + 1, we have 2^v * m = 2^v * (2*(m/2) + 1)
    --   = 2^v * 2 * (m/2) + 2^v = 2^(v+1) * (m/2) + 2^v
    have hpow : 2^(v+1) = 2 * 2^v := by ring
    -- Set q = m / 2 to avoid rewriting issues
    set q := m / 2 with hq_def
    have hm_eq_2q1 : m = 2 * q + 1 := hm_form
    calc 2^v * m = 2^v * (2 * q + 1) := by rw [hm_eq_2q1]
      _ = 2^v * 2 * q + 2^v := by ring
      _ = 2 * 2^v * q + 2^v := by ring
      _ = 2^(v+1) * q + 2^v := by rw [← hpow]
  -- Since 2^v < 2^(v+1), we have b % 2^(v+1) = 2^v
  have h2v_lt_2v1 : 2^v < 2^(v+1) := by
    have : 2^(v+1) = 2 * 2^v := by ring
    omega
  have hb_mod : b % 2^(v+1) = 2^v := by
    rw [hb_form]
    have h1 : (2^(v+1) * (m / 2) + 2^v) % 2^(v+1) = 2^v % 2^(v+1) := by
      have h2 : 2^(v+1) * (m / 2) % 2^(v+1) = 0 := Nat.mul_mod_right _ _
      simp [Nat.add_mod, h2]
    rw [h1, Nat.mod_eq_of_lt h2v_lt_2v1]
  -- Step 2: a % 2^(v+1) = 2^v
  have ha_mod : a % 2^(v+1) = 2^v := by rw [hmod_v1, hb_mod]
  -- Step 3: From a % 2^(v+1) = 2^v, derive 2^v | a
  -- a = q * 2^(v+1) + 2^v = 2^v * (2q + 1) for some q
  have ha_form : ∃ q, a = 2^(v+1) * q + 2^v := by
    use a / 2^(v+1)
    have := Nat.div_add_mod a (2^(v+1))
    omega
  obtain ⟨q, hq⟩ := ha_form
  -- 2^v | a
  have hv_dvd_a : 2^v ∣ a := by
    rw [hq]
    have : 2^(v+1) * q + 2^v = 2^v * (2 * q + 1) := by ring
    rw [this]
    exact Nat.dvd_mul_right (2^v) (2 * q + 1)
  -- a / 2^v = 2q + 1, which is odd
  have ha_div : a / 2^v = 2 * q + 1 := by
    rw [hq]
    have h1 : 2^(v+1) * q + 2^v = 2^v * (2 * q + 1) := by ring
    rw [h1]
    exact Nat.mul_div_cancel_left (2 * q + 1) h2v_pos
  have ha_div_odd : (a / 2^v) % 2 = 1 := by
    rw [ha_div]
    omega
  -- Step 4: Apply v2_eq_of_div_odd
  exact v2_eq_of_div_odd a v ha hv_dvd_a ha_div_odd

/-- v2 matching: When m ≡ r (mod 2^k) with v2(3r+1) < k, then v2(3m+1) = v2(3r+1) -/
theorem v2_matching' (m k r : ℕ) (hk : k ≥ 1)
    (hm_res : m % (2^k) = r) (hm_odd : m % 2 = 1) (hr_odd : r % 2 = 1)
    (hr_bound : r < 2^k)
    (hv_bound : v2 (3 * r + 1) < k) :
    v2 (3 * m + 1) = v2 (3 * r + 1) := by
  -- 3m + 1 ≡ 3r + 1 (mod 2^k)
  have hmod : (3 * m + 1) % (2^k) = (3 * r + 1) % (2^k) := by
    have h1 : (3 * m) % (2^k) = (3 * r) % (2^k) := by
      have h2 : 3 * m % 2^k = (3 % 2^k) * (m % 2^k) % 2^k := Nat.mul_mod 3 m (2^k)
      have h3 : 3 * r % 2^k = (3 % 2^k) * (r % 2^k) % 2^k := Nat.mul_mod 3 r (2^k)
      rw [h2, h3, hm_res]
      have hr_mod : r % 2^k = r := Nat.mod_eq_of_lt hr_bound
      rw [hr_mod]
    calc (3 * m + 1) % (2^k)
      = ((3 * m) % (2^k) + 1 % (2^k)) % (2^k) := Nat.add_mod (3 * m) 1 (2^k)
      _ = ((3 * r) % (2^k) + 1 % (2^k)) % (2^k) := by rw [h1]
      _ = (3 * r + 1) % (2^k) := (Nat.add_mod (3 * r) 1 (2^k)).symm
  have hm_pos : 3 * m + 1 ≠ 0 := by omega
  have hr_pos : 3 * r + 1 ≠ 0 := by omega
  exact v2_of_mod_eq (3 * m + 1) (3 * r + 1) k hm_pos hr_pos hmod hv_bound

/-! ## The Syracuse Function (compressed Collatz on odd numbers) -/

/-- Syracuse function: for odd n, compute (3n+1)/2^v where v = v2(3n+1) -/
def syracuse (n : ℕ) : ℕ :=
  if n % 2 = 1 ∧ n ≠ 0 then
    (3 * n + 1) / 2^(v2 (3 * n + 1))
  else
    n  -- undefined for even n, return n as placeholder

/-- Syracuse step: matches coef_step behavior on actual values.
    Even: divide by 2
    Odd: apply full Syracuse (3n+1)/2^v -/
def syracuse_step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2
  else if n = 0 then 0
  else (3 * n + 1) / 2^(v2 (3 * n + 1))

/-- Iterate syracuse_step t times -/
def syracuse_iter : ℕ → ℕ → ℕ
  | 0, n => n
  | t + 1, n => syracuse_iter t (syracuse_step n)

@[simp]
theorem syracuse_step_even (n : ℕ) (h : n % 2 = 0) : syracuse_step n = n / 2 := by
  simp [syracuse_step, h]

@[simp]
theorem syracuse_step_odd (n : ℕ) (h : n % 2 = 1) (hn : n ≠ 0) :
    syracuse_step n = (3 * n + 1) / 2^(v2 (3 * n + 1)) := by
  simp only [syracuse_step]
  have hne : ¬(n % 2 = 0) := by omega
  simp [hne, hn]

theorem syracuse_iter_zero (n : ℕ) : syracuse_iter 0 n = n := rfl

theorem syracuse_iter_succ (t n : ℕ) :
    syracuse_iter (t + 1) n = syracuse_iter t (syracuse_step n) := rfl

/-- Syracuse step preserves positivity -/
theorem syracuse_step_pos (n : ℕ) (hn : n > 0) : syracuse_step n > 0 := by
  simp only [syracuse_step]
  split_ifs with heven h0
  · -- Even case: n / 2 > 0 when n > 0 and n is even
    omega
  · -- n = 0 case: contradiction with hn
    omega
  · -- Odd case: (3n+1)/2^v > 0
    have hv_pos : 2^(v2 (3 * n + 1)) > 0 := by positivity
    have h3n1_pos : 3 * n + 1 > 0 := by omega
    have hdvd : 2^(v2 (3 * n + 1)) ∣ (3 * n + 1) := pow_v2_dvd (3 * n + 1) (by omega)
    exact Nat.div_pos (Nat.le_of_dvd h3n1_pos hdvd) hv_pos

/-- Syracuse iteration preserves positivity -/
theorem syracuse_iter_pos (t n : ℕ) (hn : n > 0) : syracuse_iter t n > 0 := by
  induction t generalizing n with
  | zero => simp [syracuse_iter]; exact hn
  | succ t ih =>
    simp only [syracuse_iter]
    apply ih
    exact syracuse_step_pos n hn

/-! ## Syracuse to Collatz Connection -/

/-- Helper: v divisions by 2 on a number divisible by 2^v gives m/2^v -/
theorem collatz_iter_div2_pow (m v : ℕ) (hm : m ≠ 0) (hdvd : 2^v ∣ m) (hodd : (m / 2^v) % 2 = 1) :
    collatz_iter v m = m / 2^v := by
  induction v generalizing m with
  | zero => simp [collatz_iter]
  | succ v ih =>
    -- 2^(v+1) | m, so m is even
    have h2v1 : 2^(v+1) = 2 * 2^v := by ring
    have h2_dvd : 2 ∣ m := by
      have h1 : 2 ∣ 2^(v+1) := by
        have : 2^1 ∣ 2^(v+1) := Nat.pow_dvd_pow 2 (by omega : 1 ≤ v + 1)
        simpa using this
      exact Nat.dvd_trans h1 hdvd
    have hm_even : m % 2 = 0 := Nat.mod_eq_zero_of_dvd h2_dvd
    have hc : collatz m = m / 2 := collatz_even m hm_even
    simp only [collatz_iter_succ, hc]
    -- Show IH applies to m/2
    have h2v_dvd_m2 : 2^v ∣ (m / 2) := by
      rw [h2v1] at hdvd
      obtain ⟨q, hq⟩ := hdvd
      have : m / 2 = 2^v * q := by
        rw [hq]
        have : 2 * 2^v * q / 2 = 2^v * q := by
          have h4 : 2 * 2^v * q = 2 * (2^v * q) := by ring
          rw [h4]
          exact Nat.mul_div_cancel_left (2^v * q) (by norm_num)
        exact this
      rw [this]
      exact Nat.dvd_mul_right (2^v) q
    have hodd_m2 : (m / 2 / 2^v) % 2 = 1 := by
      have h5 : m / 2 / 2^v = m / (2 * 2^v) := Nat.div_div_eq_div_mul m 2 (2^v)
      rw [h5, ← h2v1]
      exact hodd
    have hm2_pos : m / 2 ≠ 0 := by
      intro h
      have : m < 2 := by omega
      have hmod : m % 2 = m := Nat.mod_eq_of_lt this
      omega
    rw [ih (m / 2) hm2_pos h2v_dvd_m2 hodd_m2]
    rw [Nat.div_div_eq_div_mul, h2v1]

/-- One syracuse_step corresponds to one or more collatz steps.
    - Even n: syracuse_step n = collatz n (1 step)
    - Odd n: syracuse_step n = collatz^(v+1) n where v = v2(3n+1) -/
theorem syracuse_step_eq_collatz_iter (n : ℕ) (hn : n > 0) :
    ∃ steps ≥ 1, collatz_iter steps n = syracuse_step n := by
  by_cases heven : n % 2 = 0
  · -- Even case: one step
    use 1
    constructor
    · omega
    · simp [collatz_iter, collatz, heven, syracuse_step]
  · -- Odd case: v+1 steps where v = v2(3n+1)
    have hodd : n % 2 = 1 := by omega
    have hn0 : n ≠ 0 := by omega
    let v := v2 (3 * n + 1)
    use v + 1
    constructor
    · have hv_ge_1 : v ≥ 1 := v2_three_r_plus_one_pos n hodd
      omega
    · -- Need: collatz_iter (v+1) n = (3n+1)/2^v
      have h1 : collatz n = 3 * n + 1 := collatz_odd n hodd
      have hdvd : 2^v ∣ (3 * n + 1) := pow_v2_dvd (3 * n + 1) (by omega)
      have hodd_after : ((3 * n + 1) / 2^v) % 2 = 1 := two_not_dvd_div_pow_v2 (3 * n + 1) (by omega)
      have hgoal : collatz_iter (v + 1) n = (3 * n + 1) / 2^v := by
        simp only [collatz_iter_succ, h1]
        exact collatz_iter_div2_pow (3 * n + 1) v (by omega) hdvd hodd_after
      simp only [syracuse_step]
      have hne : ¬(n % 2 = 0) := by omega
      simp [hne, hn0]
      exact hgoal

/-- Helper: collatz_iter distributes over addition of steps -/
theorem collatz_iter_add' (s t n : ℕ) :
    collatz_iter (s + t) n = collatz_iter t (collatz_iter s n) := by
  induction s generalizing n with
  | zero => simp [collatz_iter]
  | succ s ih =>
    simp only [collatz_iter_succ, Nat.succ_add]
    exact ih (collatz n)

/-- Syracuse iteration corresponds to some number of Collatz iterations -/
theorem syracuse_iter_eq_collatz_iter (t n : ℕ) (hn : n > 0) :
    ∃ T, collatz_iter T n = syracuse_iter t n := by
  induction t generalizing n with
  | zero =>
    use 0
    simp [collatz_iter, syracuse_iter]
  | succ t ih =>
    simp only [syracuse_iter]
    obtain ⟨s, _, hs_eq⟩ := syracuse_step_eq_collatz_iter n hn
    have hstep_pos : syracuse_step n > 0 := syracuse_step_pos n hn
    obtain ⟨T', hT'⟩ := ih (syracuse_step n) hstep_pos
    use s + T'
    rw [collatz_iter_add', hs_eq, hT']

/-! ## The Main Conjecture (to be proven) -/

/-- The Collatz Conjecture: every positive integer eventually reaches 1 -/
def CollatzConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 → ∃ t : ℕ, collatz_iter t n = 1

end Collatz
