/-
  Collatz — Sturmian itineraries: the level theorem

  This file contains NO axioms and NO claim to prove the conjecture.

  A mechanical (Sturmian) word of slope α and intercept ρ is
      w_n = ⌊(n+1)α + ρ⌋ − ⌊nα + ρ⌋ ∈ {0,1},
  with ones-density α. Suppose a natural number N has this word as its
  Terras parity itinerary, with α above the critical line
  (2 ≤ 3^α, i.e. α ≥ log 2/log 3). Fix a rational approximation
  qα = p + δ, 0 < δ < 1, and call n a VISIT if {nα+ρ} ≥ 1 − δ. Then

    * w_{n+q} = w_n unless n or n+1 is a visit            (`mech_shift`);
    * two visits are ≥ Q apart, given that ‖mα‖ ≥ δ for 0 < m < Q
      (Lagrange's best-approximation property when q = q_k, δ = ‖q_kα‖,
      Q = q_{k+1})                                         (`visit_sep`);
    * if some visit occurs in every window of length G (the
      three-distance theorem gives G = q_k + q_{k+1}), the itinerary is
      q-periodic on a run of length Q − 2 starting at s ≤ G, and the
      orbit is not q-periodic there.

  The prefix-power criterion (`prefix_power_bound`) then bounds
  2^(q+Q−2) by the size of the tail T^s(N), which the exact orbit
  identity bounds by 3^{sα}(3N + 3s)/2^s — the correction term d_s is
  at most 3s·3^{sα} because 2 ≤ 3^α. The conclusion is the inequality

      2^(Q − 3 + s) ≤ 3^((q+s)α + 1) · (3N + 3s + 1)      for some s ≤ G,

  which fails for large levels whenever the partial quotient
  Q/q ≈ a_{k+1} exceeds (1+2η)/(1−η), η = α·log₂3 − 1 (see the paper).
  The theorem `sturmian_level` packages this: the two Diophantine
  facts and the negation of the inequality are hypotheses, and the
  conclusion is that no N has the itinerary. The classical facts
  supplying the hypotheses for infinitely many levels are NOT
  formalized here.
-/

import Collatz.Rung1
import Collatz.PrefixPower
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Collatz

open Real Classical

/-! ## Mechanical words -/

/-- The mechanical word of slope `α` and intercept `ρ`. -/
noncomputable def mech (α ρ : ℝ) (n : ℕ) : ℤ :=
  ⌊((n : ℝ) + 1) * α + ρ⌋ - ⌊(n : ℝ) * α + ρ⌋

/-- `n` is a visit (for the approximation `qα = p + δ`) if `{nα+ρ} ≥ 1 − δ`. -/
def visit (α ρ δ : ℝ) (n : ℕ) : Prop := 1 - δ ≤ Int.fract ((n : ℝ) * α + ρ)

theorem mech_nonneg {α ρ : ℝ} (hα : 0 ≤ α) (n : ℕ) : 0 ≤ mech α ρ n := by
  unfold mech
  have : (n : ℝ) * α + ρ ≤ ((n : ℝ) + 1) * α + ρ := by nlinarith
  linarith [Int.floor_mono this]

theorem mech_le_one {α ρ : ℝ} (hα : α ≤ 1) (n : ℕ) : mech α ρ n ≤ 1 := by
  unfold mech
  have : ((n : ℝ) + 1) * α + ρ ≤ ((n : ℝ) * α + ρ) + 1 := by nlinarith
  have h := Int.floor_mono this
  rw [Int.floor_add_one] at h
  omega

/-- Telescoping: the number of ones among the first `s` letters. -/
theorem mech_sum (α ρ : ℝ) (s : ℕ) :
    ∑ t ∈ Finset.range s, mech α ρ t = ⌊(s : ℝ) * α + ρ⌋ - ⌊ρ⌋ := by
  have e : ∀ t : ℕ, mech α ρ t = ⌊((t + 1 : ℕ) : ℝ) * α + ρ⌋ - ⌊(t : ℝ) * α + ρ⌋ := by
    intro t; unfold mech; simp only [Nat.cast_add, Nat.cast_one]
  simp_rw [e]
  rw [Finset.sum_range_sub (fun t : ℕ => ⌊(t : ℝ) * α + ρ⌋)]
  simp

theorem mech_sum_le {α ρ : ℝ} (s : ℕ) :
    ((∑ t ∈ Finset.range s, mech α ρ t : ℤ) : ℝ) ≤ (s : ℝ) * α + 1 := by
  rw [mech_sum]
  push_cast
  have h1 := Int.floor_le ((s : ℝ) * α + ρ)
  have h2 := Int.lt_floor_add_one ρ
  linarith

/-- Ones in a window `[a, a+ℓ)`. -/
theorem mech_window_le {α ρ : ℝ} (a ℓ : ℕ) :
    ((∑ t ∈ Finset.range ℓ, mech α ρ (a + t) : ℤ) : ℝ) ≤ (ℓ : ℝ) * α + 1 := by
  have : ∑ t ∈ Finset.range ℓ, mech α ρ (a + t) =
      ⌊((a + ℓ : ℕ) : ℝ) * α + ρ⌋ - ⌊(a : ℝ) * α + ρ⌋ := by
    have e : ∀ t : ℕ, mech α ρ (a + t) =
        ⌊((a + (t + 1) : ℕ) : ℝ) * α + ρ⌋ - ⌊((a + t : ℕ) : ℝ) * α + ρ⌋ := by
      intro t; unfold mech; congr 2; push_cast; ring
    simp_rw [e]
    rw [Finset.sum_range_sub (fun t : ℕ => ⌊((a + t : ℕ) : ℝ) * α + ρ⌋)]
    simp
  rw [this]
  push_cast
  have h1 := Int.floor_le (((a : ℝ) + ℓ) * α + ρ)
  have h2 := Int.lt_floor_add_one ((a : ℝ) * α + ρ)
  nlinarith

/-! ## The shift by `q` -/

/-- `⌊(n+q)α + ρ⌋ = ⌊nα+ρ⌋ + p + [visit n]` when `qα = p + δ`, `0 ≤ δ < 1`. -/
theorem floor_shift {α ρ δ : ℝ} {q : ℕ} {p : ℤ} (hq : (q : ℝ) * α = p + δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (n : ℕ) :
    ⌊((n + q : ℕ) : ℝ) * α + ρ⌋ =
      ⌊(n : ℝ) * α + ρ⌋ + p + (if visit α ρ δ n then 1 else 0) := by
  set x := (n : ℝ) * α + ρ with hx
  have e : ((n + q : ℕ) : ℝ) * α + ρ = (x + δ) + p := by
    push_cast; rw [hx]; linear_combination hq
  rw [e, Int.floor_add_intCast]
  -- ⌊x + δ⌋ = ⌊x⌋ + [fract x + δ ≥ 1]
  have hx' : x + δ = (Int.fract x + δ) + ((⌊x⌋ : ℤ) : ℝ) := by
    have := Int.floor_add_fract x
    linarith
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have key : ⌊x + δ⌋ = ⌊x⌋ + (if visit α ρ δ n then 1 else 0) := by
    rw [hx', Int.floor_add_intCast]
    by_cases hv : visit α ρ δ n
    · have hv' : 1 - δ ≤ Int.fract x := hv
      rw [if_pos hv]
      have : ⌊Int.fract x + δ⌋ = 1 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      omega
    · have hv' : ¬ (1 - δ ≤ Int.fract x) := hv
      push_neg at hv'
      rw [if_neg hv]
      have : ⌊Int.fract x + δ⌋ = 0 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      omega
  rw [key]; ring

/-- The letter `q` steps later differs only through visits at `n` and `n+1`. -/
theorem mech_shift {α ρ δ : ℝ} {q : ℕ} {p : ℤ} (hq : (q : ℝ) * α = p + δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (n : ℕ)
    (h0 : ¬ visit α ρ δ n) (h1 : ¬ visit α ρ δ (n + 1)) :
    mech α ρ (n + q) = mech α ρ n := by
  unfold mech
  have e1 := floor_shift (ρ := ρ) hq hδ0 hδ1 n
  have e2 := floor_shift (ρ := ρ) hq hδ0 hδ1 (n + 1)
  rw [if_neg h0] at e1
  rw [if_neg h1] at e2
  have c1 : (((n + q : ℕ) : ℝ) + 1) * α + ρ = ((n + 1 + q : ℕ) : ℝ) * α + ρ := by
    push_cast; ring
  have c2 : ((n : ℝ) + 1) * α + ρ = ((n + 1 : ℕ) : ℝ) * α + ρ := by push_cast; ring
  rw [c1, c2, e1, e2]
  ring

/-- Two visits are at least `Q` apart, given `‖mα‖ ≥ δ` for `0 < m < Q`. -/
theorem visit_sep {α ρ δ : ℝ} {Q : ℕ}
    (hL : ∀ m : ℕ, 0 < m → m < Q → ∀ r : ℤ, δ ≤ |(m : ℝ) * α - r|)
    {n n' : ℕ} (hn : visit α ρ δ n) (hn' : visit α ρ δ n') (hlt : n < n') :
    Q ≤ n' - n := by
  by_contra hcon
  push_neg at hcon
  unfold visit at hn hn'
  set x := (n : ℝ) * α + ρ
  set x' := (n' : ℝ) * α + ρ
  have hf0 := Int.fract_lt_one x
  have hf0' := Int.fract_lt_one x'
  -- fract x' − fract x = (n'−n)α − (⌊x'⌋ − ⌊x⌋)
  have key : Int.fract x' - Int.fract x =
      ((n' - n : ℕ) : ℝ) * α - ((⌊x'⌋ - ⌊x⌋ : ℤ) : ℝ) := by
    unfold Int.fract
    push_cast [Nat.cast_sub (le_of_lt hlt)]
    ring
  have hb := hL (n' - n) (by omega) hcon (⌊x'⌋ - ⌊x⌋)
  rw [← key] at hb
  -- both fract's lie in [1−δ, 1): their difference is < δ in absolute value
  have hd : |Int.fract x' - Int.fract x| < δ := by
    rw [abs_lt]; constructor <;> linarith
  linarith

/-! ## The itinerary hypothesis and the orbit -/

/-- `N` has itinerary `mech α ρ`. -/
def HasItin (α ρ : ℝ) (N : ℕ) : Prop :=
  ∀ t, ((terras_iter t N % 2 : ℕ) : ℤ) = mech α ρ t

theorem oddSteps_of_itin {α ρ : ℝ} {N : ℕ} (h : HasItin α ρ N) (s : ℕ) :
    ((oddSteps s N : ℕ) : ℤ) = ∑ t ∈ Finset.range s, mech α ρ t := by
  rw [oddSteps_eq_sum]
  push_cast
  exact Finset.sum_congr rfl (fun t _ => h t)

theorem oddSteps_tail_of_itin {α ρ : ℝ} {N : ℕ} (h : HasItin α ρ N) (s ℓ : ℕ) :
    ((oddSteps ℓ (terras_iter s N) : ℕ) : ℤ) = ∑ t ∈ Finset.range ℓ, mech α ρ (s + t) := by
  rw [oddSteps_eq_sum]
  push_cast
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [terras_iter_add]
  exact h (s + t)

/-- The correction term is at most `3s·3^{sα}` above the critical line. -/
theorem dcoef_le_of_itin {α ρ : ℝ} (hα0 : 0 ≤ α) (hcrit : (2 : ℝ) ≤ (3 : ℝ) ^ α)
    {N : ℕ} (h : HasItin α ρ N) (s : ℕ) :
    ((dcoef s N : ℕ) : ℝ) ≤ 3 * s * (3 : ℝ) ^ ((s : ℝ) * α) := by
  rw [dcoef_closed]
  push_cast
  -- bound each term by 3·3^{sα}
  have hterm : ∀ i ∈ Finset.range s,
      ((terras_iter i N % 2 : ℕ) : ℝ) * (2 : ℝ) ^ i *
        (3 : ℝ) ^ (oddSteps s N - oddSteps (i + 1) N) ≤ 3 * (3 : ℝ) ^ ((s : ℝ) * α) := by
    intro i hi
    have hi' : i + 1 ≤ s := Finset.mem_range.mp hi
    have hpar : ((terras_iter i N % 2 : ℕ) : ℝ) ≤ 1 := by
      have := Nat.mod_lt (terras_iter i N) (show 0 < 2 by norm_num)
      exact_mod_cast Nat.lt_succ_iff.mp this
    -- ones in the window [i+1, s): ≤ (s − i − 1)α + 1
    have hmono : oddSteps (i + 1) N ≤ oddSteps s N := by
      have := oddSteps_add (i + 1) (s - (i + 1)) N
      rw [show i + 1 + (s - (i + 1)) = s by omega] at this
      omega
    have hwin : ((oddSteps s N - oddSteps (i + 1) N : ℕ) : ℝ) ≤ ((s - (i + 1) : ℕ) : ℝ) * α + 1 := by
      have e : oddSteps s N = oddSteps (i + 1) N + oddSteps (s - (i + 1)) (terras_iter (i + 1) N) := by
        have := oddSteps_add (i + 1) (s - (i + 1)) N
        rw [show i + 1 + (s - (i + 1)) = s by omega] at this
        exact this
      have hsub : oddSteps s N - oddSteps (i + 1) N =
          oddSteps (s - (i + 1)) (terras_iter (i + 1) N) := by omega
      rw [hsub]
      have e2 := oddSteps_tail_of_itin h (i + 1) (s - (i + 1))
      have e4 : ((oddSteps (s - (i + 1)) (terras_iter (i + 1) N) : ℕ) : ℝ) =
          ((∑ t ∈ Finset.range (s - (i + 1)), mech α ρ (i + 1 + t) : ℤ) : ℝ) := by
        exact_mod_cast e2
      rw [e4]; exact mech_window_le (i + 1) (s - (i + 1))
    -- 3^(window) ≤ 3^((s−i−1)α + 1)
    have h3 : (3 : ℝ) ^ (oddSteps s N - oddSteps (i + 1) N) ≤
        (3 : ℝ) ^ (((s - (i + 1) : ℕ) : ℝ) * α + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hwin
    -- 2^i ≤ 3^(iα)
    have h2 : (2 : ℝ) ^ i ≤ (3 : ℝ) ^ ((i : ℝ) * α) := by
      rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
      exact pow_le_pow_left₀ (by norm_num) hcrit i
    have hpos1 : (0 : ℝ) ≤ (2 : ℝ) ^ i := by positivity
    have hpos2 : (0 : ℝ) ≤ (3 : ℝ) ^ (oddSteps s N - oddSteps (i + 1) N) := by positivity
    have hpos3 : (0 : ℝ) ≤ (3 : ℝ) ^ ((i : ℝ) * α) := by positivity
    have hpos4 : (0 : ℝ) ≤ (3 : ℝ) ^ (((s - (i + 1) : ℕ) : ℝ) * α + 1) := by positivity
    calc ((terras_iter i N % 2 : ℕ) : ℝ) * (2 : ℝ) ^ i *
          (3 : ℝ) ^ (oddSteps s N - oddSteps (i + 1) N)
        ≤ 1 * (3 : ℝ) ^ ((i : ℝ) * α) * (3 : ℝ) ^ (((s - (i + 1) : ℕ) : ℝ) * α + 1) := by
          apply mul_le_mul (mul_le_mul hpar h2 hpos1 (by norm_num)) h3 hpos2 (by positivity)
      _ = (3 : ℝ) ^ ((i : ℝ) * α + (((s - (i + 1) : ℕ) : ℝ) * α + 1)) := by
          rw [one_mul, ← Real.rpow_add (by norm_num)]
      _ ≤ (3 : ℝ) ^ ((s : ℝ) * α + 1) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : ((s - (i + 1) : ℕ) : ℝ) = (s : ℝ) - ((i : ℝ) + 1) := by
            push_cast [Nat.cast_sub hi']; ring
          rw [this]; nlinarith
      _ = 3 * (3 : ℝ) ^ ((s : ℝ) * α) := by rw [Real.rpow_add_one (by norm_num)]; ring
  calc (∑ i ∈ Finset.range s, ((terras_iter i N % 2 : ℕ) : ℝ) * (2 : ℝ) ^ i *
          (3 : ℝ) ^ (oddSteps s N - oddSteps (i + 1) N))
      ≤ ∑ i ∈ Finset.range s, 3 * (3 : ℝ) ^ ((s : ℝ) * α) := Finset.sum_le_sum hterm
    _ = 3 * s * (3 : ℝ) ^ ((s : ℝ) * α) := by
        rw [Finset.sum_const, Finset.card_range]; simp; ring

/-- The tail `T^s(N)` is at most `3^{sα}·(3N + 3s)/2^s`. -/
theorem tail_le_of_itin {α ρ : ℝ} (hα0 : 0 ≤ α) (hcrit : (2 : ℝ) ≤ (3 : ℝ) ^ α)
    {N : ℕ} (h : HasItin α ρ N) (s : ℕ) :
    (2 : ℝ) ^ s * ((terras_iter s N : ℕ) : ℝ) ≤
      (3 : ℝ) ^ ((s : ℝ) * α) * (3 * N + 3 * s) := by
  have hex := terras_exact_form s N
  have hexR : (2 : ℝ) ^ s * ((terras_iter s N : ℕ) : ℝ) =
      (3 : ℝ) ^ oddSteps s N * N + ((dcoef s N : ℕ) : ℝ) := by exact_mod_cast hex
  rw [hexR]
  have hj : ((oddSteps s N : ℕ) : ℝ) ≤ (s : ℝ) * α + 1 := by
    have := oddSteps_of_itin h s
    have e : ((oddSteps s N : ℕ) : ℝ) = ((∑ t ∈ Finset.range s, mech α ρ t : ℤ) : ℝ) := by
      exact_mod_cast this
    rw [e]; exact mech_sum_le s
  have h3 : (3 : ℝ) ^ oddSteps s N ≤ 3 * (3 : ℝ) ^ ((s : ℝ) * α) := by
    rw [← Real.rpow_natCast]
    calc (3 : ℝ) ^ ((oddSteps s N : ℕ) : ℝ) ≤ (3 : ℝ) ^ ((s : ℝ) * α + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hj
      _ = 3 * (3 : ℝ) ^ ((s : ℝ) * α) := by rw [Real.rpow_add_one (by norm_num)]; ring
  have hd := dcoef_le_of_itin hα0 hcrit h s
  have hN : (0 : ℝ) ≤ N := by positivity
  have hp : (0 : ℝ) ≤ (3 : ℝ) ^ ((s : ℝ) * α) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h3 hN]

/-! ## The level theorem -/

/-- THE LEVEL THEOREM. Let `α` be above the critical line, `qα = p + δ`
    with `0 < δ < 1`, and suppose
      (L) `‖mα‖ ≥ δ` for `0 < m < Q`  (Lagrange, for a convergent),
      (T) every window of length `G` contains a visit  (three-distance),
      (S) for every `s ≤ G`:  `2^(Q−3+s) > 3^((q+s)α+1)·(3N+3s+1)`.
    Then `N` does not have itinerary `mech α ρ`. -/
theorem sturmian_level {α ρ δ : ℝ} {q Q G : ℕ} {p : ℤ}
    (hα0 : 0 ≤ α) (hcrit : (2 : ℝ) ≤ (3 : ℝ) ^ α)
    (hq : (q : ℝ) * α = p + δ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hQ : 3 ≤ Q)
    (hL : ∀ m : ℕ, 0 < m → m < Q → ∀ r : ℤ, δ ≤ |(m : ℝ) * α - r|)
    (hT : ∀ a : ℕ, ∃ n, a ≤ n ∧ n < a + G ∧ visit α ρ δ n)
    (N : ℕ)
    (hS : ∀ s : ℕ, s ≤ G →
      (3 : ℝ) ^ (((q + s : ℕ) : ℝ) * α + 1) * (3 * N + 3 * s + 1) < (2 : ℝ) ^ (Q - 3 + s)) :
    ¬ HasItin α ρ N := by
  intro h
  -- the first visit
  obtain ⟨n₀, -, hn₀G, hv₀⟩ := hT 0
  set s := n₀ + 1 with hs
  set m := terras_iter s N with hm
  have hsG : s ≤ G := by omega
  -- no visits in (n₀, n₀ + Q)
  have hnov : ∀ t, n₀ < t → t < n₀ + Q → ¬ visit α ρ δ t := by
    intro t h1 h2 hv
    have := visit_sep hL hv₀ hv h1
    omega
  -- the tail itinerary is q-periodic on Q − 2 letters
  have hper : ∀ t, t + q < q + Q - 2 →
      terras_iter t m % 2 = terras_iter (t + q) m % 2 := by
    intro t ht
    have e1 : terras_iter t m = terras_iter (s + t) N := by rw [hm, terras_iter_add]
    have e2 : terras_iter (t + q) m = terras_iter (s + t + q) N := by
      rw [hm, terras_iter_add]; congr 1; ring
    have hsh := mech_shift (ρ := ρ) hq (le_of_lt hδ0) hδ1 (s + t)
      (hnov (s + t) (by omega) (by omega)) (hnov (s + t + 1) (by omega) (by omega))
    have h1 := h (s + t)
    have h2 := h (s + t + q)
    rw [e1, e2]
    rw [hsh] at h2
    exact_mod_cast h1.trans h2.symm
  -- the orbit is not q-periodic at the tail
  have hne : terras_iter q m ≠ m := by
    intro hfix
    -- then mech is q-periodic from s on, so visits are constant from s on
    have hall : ∀ t, mech α ρ (s + t + q) = mech α ρ (s + t) := by
      intro t
      have h1 := h (s + t)
      have h2 := h (s + t + q)
      have e : terras_iter (s + t + q) N = terras_iter (s + t) N := by
        rw [show s + t + q = s + (q + t) by ring, ← terras_iter_add, ← hm,
          ← terras_iter_add, hfix, hm, terras_iter_add]
      rw [← h1, ← h2, e]
    -- a visit at some u ≥ s, and then u+1 is also a visit (or u−1 …): derive two
    -- adjacent visits, contradicting separation with Q ≥ 3.
    obtain ⟨u, hus, -, hvu⟩ := hT s
    -- from hall: [visit (n+1)] − [visit n] = 0 for all n ≥ s
    have hstep : ∀ n, s ≤ n → (visit α ρ δ n ↔ visit α ρ δ (n + 1)) := by
      intro n hn
      obtain ⟨t, rfl⟩ : ∃ t, n = s + t := ⟨n - s, by omega⟩
      have := hall t
      unfold mech at this
      have e1 := floor_shift (ρ := ρ) hq (le_of_lt hδ0) hδ1 (s + t)
      have e2 := floor_shift (ρ := ρ) hq (le_of_lt hδ0) hδ1 (s + t + 1)
      have c1 : (((s + t + q : ℕ) : ℝ) + 1) * α + ρ = ((s + t + 1 + q : ℕ) : ℝ) * α + ρ := by
        push_cast; ring
      have c2 : (((s + t : ℕ) : ℝ) + 1) * α + ρ = ((s + t + 1 : ℕ) : ℝ) * α + ρ := by
        push_cast; ring
      rw [c1, c2, e1, e2] at this
      constructor
      · intro hv
        by_contra hv'
        rw [if_pos hv, if_neg hv'] at this; omega
      · intro hv'
        by_contra hv
        rw [if_neg hv, if_pos hv'] at this; omega
    have hv1 : visit α ρ δ (u + 1) := (hstep u hus).mp hvu
    have := visit_sep hL hvu hv1 (by omega)
    omega
  -- apply the prefix-power criterion at the tail
  have hpp := prefix_power_bound m q (q + Q - 2) (by omega) hper hne
  -- cast and combine with the size bounds
  have ho : ((oddSteps q m : ℕ) : ℝ) ≤ (q : ℝ) * α + 1 := by
    have := oddSteps_tail_of_itin h s q
    have e : ((oddSteps q m : ℕ) : ℝ) = ((∑ t ∈ Finset.range q, mech α ρ (s + t) : ℤ) : ℝ) := by
      rw [hm]; exact_mod_cast this
    rw [e]; exact mech_window_le s q
  have h3o : (3 : ℝ) ^ oddSteps q m ≤ (3 : ℝ) ^ ((q : ℝ) * α + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) ho
  have htail := tail_le_of_itin hα0 hcrit h s
  rw [← hm] at htail
  have hppR : (2 : ℝ) ^ (q + Q - 2) ≤ 2 ^ q * (m : ℝ) + 3 ^ oddSteps q m * ((m : ℝ) + 2 ^ q) := by
    exact_mod_cast hpp
  have hS' := hS s hsG
  -- 2^s ≤ 3^(sα)
  have h2s : (2 : ℝ) ^ s ≤ (3 : ℝ) ^ ((s : ℝ) * α) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact pow_le_pow_left₀ (by norm_num) hcrit s
  -- assemble: 2^(q+Q−2) ≤ 2^(q+1)·3^(qα+1)·(m+1) and 2^s (m+1) ≤ 3^(sα)(3N+3s+1)
  have hA : (2 : ℝ) ^ (q + Q - 2) ≤ 2 ^ (q + 1) * (3 : ℝ) ^ ((q : ℝ) * α + 1) * ((m : ℝ) + 1) := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have h2q : (0 : ℝ) ≤ 2 ^ q := by positivity
    have h3q : (1 : ℝ) ≤ (3 : ℝ) ^ ((q : ℝ) * α + 1) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have h3q0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((q : ℝ) * α + 1) := by positivity
    have t1 : 2 ^ q * (m : ℝ) ≤ 2 ^ q * (3 : ℝ) ^ ((q : ℝ) * α + 1) * (m : ℝ) := by
      nlinarith [mul_nonneg (mul_nonneg h2q hm0) (sub_nonneg.mpr h3q)]
    have t2 : (3 : ℝ) ^ oddSteps q m * ((m : ℝ) + 2 ^ q) ≤
        (3 : ℝ) ^ ((q : ℝ) * α + 1) * ((m : ℝ) + 2 ^ q) :=
      mul_le_mul_of_nonneg_right h3o (by positivity)
    have h1q : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
    have t3 : 2 ^ q * (3 : ℝ) ^ ((q : ℝ) * α + 1) * (m : ℝ) +
        (3 : ℝ) ^ ((q : ℝ) * α + 1) * ((m : ℝ) + 2 ^ q) ≤
        2 ^ (q + 1) * (3 : ℝ) ^ ((q : ℝ) * α + 1) * ((m : ℝ) + 1) := by
      rw [pow_succ]
      nlinarith [mul_nonneg (mul_nonneg h3q0 hm0) (sub_nonneg.mpr h1q)]
    linarith
  have hB : (2 : ℝ) ^ s * ((m : ℝ) + 1) ≤ (3 : ℝ) ^ ((s : ℝ) * α) * (3 * N + 3 * s + 1) := by
    nlinarith [htail, h2s]
  -- combine
  have hpos : (0 : ℝ) < 2 ^ (q + 1) * (3 : ℝ) ^ ((q : ℝ) * α + 1) := by positivity
  have hC : (2 : ℝ) ^ (q + Q - 2) * 2 ^ s ≤
      2 ^ (q + 1) * (3 : ℝ) ^ ((q : ℝ) * α + 1) * ((3 : ℝ) ^ ((s : ℝ) * α) * (3 * N + 3 * s + 1)) := by
    calc (2 : ℝ) ^ (q + Q - 2) * 2 ^ s
        ≤ 2 ^ (q + 1) * (3 : ℝ) ^ ((q : ℝ) * α + 1) * ((m : ℝ) + 1) * 2 ^ s := by
          apply mul_le_mul_of_nonneg_right hA (by positivity)
      _ = 2 ^ (q + 1) * (3 : ℝ) ^ ((q : ℝ) * α + 1) * (2 ^ s * ((m : ℝ) + 1)) := by ring
      _ ≤ _ := by apply mul_le_mul_of_nonneg_left hB (le_of_lt hpos)
  -- rewrite powers: 2^(q+Q−2)·2^s = 2^(q+1)·2^(Q−3+s), and 3^(qα+1)·3^(sα) = 3^((q+s)α+1)
  have e2 : (2 : ℝ) ^ (q + Q - 2) * 2 ^ s = 2 ^ (q + 1) * 2 ^ (Q - 3 + s) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have e3 : (3 : ℝ) ^ ((q : ℝ) * α + 1) * (3 : ℝ) ^ ((s : ℝ) * α) =
      (3 : ℝ) ^ (((q + s : ℕ) : ℝ) * α + 1) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
  have hC2 : (2 : ℝ) ^ (q + 1) * 2 ^ (Q - 3 + s) ≤
      2 ^ (q + 1) * ((3 : ℝ) ^ ((q : ℝ) * α + 1) * (3 : ℝ) ^ ((s : ℝ) * α) * (3 * N + 3 * s + 1)) := by
    rw [← e2]; convert hC using 1; ring
  have h2 : (0 : ℝ) < 2 ^ (q + 1) := by positivity
  have hC' := le_of_mul_le_mul_left hC2 h2
  rw [e3] at hC'
  linarith

end Collatz
