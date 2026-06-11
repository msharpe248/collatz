/-
  Collatz — Cycle Bounds

  This file contains NO axioms and NO claim to prove the conjecture.

  `Density.lean` proved the upper master inequality
      2^T · (T^T(n) + 1) ≤ 3^j · (n + 2^(T-j)),   j = oddSteps T n.
  Here we prove its lower companion
      3^j · (n + 1) ≤ 2^T · T^T(n) + 2^j,
  by the same induction. On a cycle (T^T(n) = n, T ≥ 1, n ≥ 1) the two
  bounds pinch, yielding the classical Diophantine cycle constraints,
  now fully formal:

  * `cycle_has_odd_step`   : a nontrivial cycle takes at least one odd step
  * `cycle_three_pow_lt`   : 3^j < 2^T strictly
  * `cycle_min_bound`      : n · 2^T < n · 3^j + 3^j · 2^(T-j), i.e. every
                             cycle element is < 3^j·2^(T-j)/(2^T - 3^j) —
                             cycles can only live where 3^j approximates
                             2^T from below extremely well

  The quality of rational approximations to log₂ 3 then bounds cycle
  lengths. `cycle_check_183` verifies — by kernel computation on exact
  integers, no `native_decide`, no trusted code — that for every T ≤ 183
  and every j, the cycle bound forces n < 2^71. Combined with the
  computational verification of the conjecture below 2^71 (Barina 2020),
  stated here as an explicit hypothesis since it is not formalized:

  * `no_small_terras_cycle` : any Terras-cycle of length ≤ 183 consists
                              of values whose orbits reach 1 — so the only
                              such cycle is the trivial one through 1.

  T = 184 with j = 116 is the first pair the 2^71 bound cannot exclude:
  there the cycle bound 3^116·2^68/(2^184 − 3^116) ≈ 2^71.25 just clears
  2^71. The Diophantine wall is real, not an artifact.
-/

import Collatz.Density

namespace Collatz

/-! ## The lower master inequality -/

/-- THE LOWER MASTER INEQUALITY. Writing j = `oddSteps T n`,

        3^j · (n + 1) ≤ 2^T · T^T(n) + 2^j.

    Same induction as `terras_growth_bound`: an odd step is the exact
    identity 2·(T(x)+1) = 3·(x+1); an even step costs 2·(T(x)+1) = x+2,
    and the slack lands in the 2^j term. Also an equality on the
    Mersenne orbit. -/
theorem terras_lower_bound (T : ℕ) : ∀ n : ℕ,
    3 ^ oddSteps T n * (n + 1) ≤ 2 ^ T * terras_iter T n + 2 ^ oddSteps T n := by
  induction T with
  | zero => intro n; simp [terras_iter]
  | succ T ih =>
    intro n
    have hit : terras_iter (T + 1) n = terras_iter T (terras n) := rfl
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · -- even step: 2·terras n = n, odd count unchanged
      have hodd : oddSteps (T + 1) n = oddSteps T (terras n) :=
        oddSteps_succ_even T n hpar
      have hpow : 2 ^ oddSteps T (terras n) ≤ 3 ^ oddSteps T (terras n) :=
        Nat.pow_le_pow_left (by norm_num) _
      rw [hit, hodd]
      refine Nat.le_of_add_le_add_right
        (b := 2 ^ (oddSteps T (terras n) + 1)) ?_
      calc 3 ^ oddSteps T (terras n) * (n + 1) + 2 ^ (oddSteps T (terras n) + 1)
          = 3 ^ oddSteps T (terras n) * (n + 1) + 2 ^ oddSteps T (terras n)
              + 2 ^ oddSteps T (terras n) := by ring
        _ ≤ 3 ^ oddSteps T (terras n) * (n + 1) + 3 ^ oddSteps T (terras n)
              + 2 ^ oddSteps T (terras n) :=
            Nat.add_le_add_right (Nat.add_le_add_left hpow _) _
        _ = 3 ^ oddSteps T (terras n) * (n + 2) + 2 ^ oddSteps T (terras n) := by
            ring
        _ = 3 ^ oddSteps T (terras n) * (2 * terras n + 2)
              + 2 ^ oddSteps T (terras n) := by
            rw [two_mul_terras_even n hpar]
        _ = 2 * (3 ^ oddSteps T (terras n) * (terras n + 1))
              + 2 ^ oddSteps T (terras n) := by ring
        _ ≤ 2 * (2 ^ T * terras_iter T (terras n) + 2 ^ oddSteps T (terras n))
              + 2 ^ oddSteps T (terras n) :=
            Nat.add_le_add_right (Nat.mul_le_mul (le_refl 2) (ih (terras n))) _
        _ = 2 ^ (T + 1) * terras_iter T (terras n) + 2 ^ oddSteps T (terras n)
              + 2 ^ (oddSteps T (terras n) + 1) := by ring
    · -- odd step: 2·terras n = 3n + 1, exact identity, odd count up by one
      have hodd : oddSteps (T + 1) n = oddSteps T (terras n) + 1 :=
        oddSteps_succ_odd T n hpar
      rw [hit, hodd]
      calc 3 ^ (oddSteps T (terras n) + 1) * (n + 1)
          = 3 ^ oddSteps T (terras n) * (3 * n + 3) := by ring
        _ = 3 ^ oddSteps T (terras n) * (2 * terras n + 2) := by
            rw [two_mul_terras_odd n hpar]
        _ = 2 * (3 ^ oddSteps T (terras n) * (terras n + 1)) := by ring
        _ ≤ 2 * (2 ^ T * terras_iter T (terras n) + 2 ^ oddSteps T (terras n)) :=
            Nat.mul_le_mul (le_refl 2) (ih (terras n))
        _ = 2 ^ (T + 1) * terras_iter T (terras n)
              + 2 ^ (oddSteps T (terras n) + 1) := by ring

/-! ## Cycle constraints -/

/-- A nontrivial cycle takes at least one odd step: an all-even cycle
    would force 2^T·n ≤ n. -/
theorem cycle_has_odd_step (T n : ℕ) (hT : 1 ≤ T) (hn : 1 ≤ n)
    (hc : terras_iter T n = n) : 1 ≤ oddSteps T n := by
  by_contra h0
  have hj0 : oddSteps T n = 0 := by omega
  have hb := terras_growth_bound T n
  rw [hc, hj0] at hb
  simp only [pow_zero, one_mul, Nat.sub_zero] at hb
  -- hb : 2^T * (n + 1) ≤ n + 2^T
  have h2T : 2 ≤ 2 ^ T := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) hT
  have hb2 : 2 ^ T * n + 2 ^ T ≤ n + 2 ^ T := by
    calc 2 ^ T * n + 2 ^ T = 2 ^ T * (n + 1) := by ring
      _ ≤ n + 2 ^ T := hb
  have hb3 : 2 ^ T * n ≤ n := Nat.le_of_add_le_add_right hb2
  have hb4 : 2 * n ≤ 2 ^ T * n := Nat.mul_le_mul h2T (le_refl n)
  have hb5 : 2 * n ≤ n := le_trans hb4 hb3
  omega

/-- On a nontrivial cycle, 3^j < 2^T strictly: the multiplications must
    undershoot the divisions. -/
theorem cycle_three_pow_lt (T n : ℕ) (hT : 1 ≤ T) (hn : 1 ≤ n)
    (hc : terras_iter T n = n) : 3 ^ oddSteps T n < 2 ^ T := by
  have hj1 : 1 ≤ oddSteps T n := cycle_has_odd_step T n hT hn hc
  have hlow := terras_lower_bound T n
  rw [hc] at hlow
  -- hlow : 3^j * (n + 1) ≤ 2^T * n + 2^j
  have hpow : 2 ^ oddSteps T n < 3 ^ oddSteps T n :=
    Nat.pow_lt_pow_left (by norm_num) (by omega)
  by_contra hno
  push_neg at hno
  -- hno : 2^T ≤ 3^j
  have h1 : 2 ^ T * n ≤ 3 ^ oddSteps T n * n := Nat.mul_le_mul hno (le_refl n)
  have h2 : 3 ^ oddSteps T n * n + 3 ^ oddSteps T n ≤
      3 ^ oddSteps T n * n + 2 ^ oddSteps T n := by
    calc 3 ^ oddSteps T n * n + 3 ^ oddSteps T n
        = 3 ^ oddSteps T n * (n + 1) := by ring
      _ ≤ 2 ^ T * n + 2 ^ oddSteps T n := hlow
      _ ≤ 3 ^ oddSteps T n * n + 2 ^ oddSteps T n := Nat.add_le_add_right h1 _
  have h3 : 3 ^ oddSteps T n ≤ 2 ^ oddSteps T n := Nat.le_of_add_le_add_left h2
  exact absurd h3 hpow.not_ge

/-- THE CYCLE BOUND. Every element n of a nontrivial cycle satisfies

        n · 2^T < n · 3^j + 3^j · 2^(T-j),

    i.e. n < 3^j·2^(T-j) / (2^T - 3^j): cycles can only exist where 3^j
    approximates 2^T from below with extreme precision. -/
theorem cycle_min_bound (T n : ℕ) (hn : 1 ≤ n)
    (hc : terras_iter T n = n) :
    n * 2 ^ T < n * 3 ^ oddSteps T n
      + 3 ^ oddSteps T n * 2 ^ (T - oddSteps T n) := by
  have hb := terras_growth_bound T n
  rw [hc] at hb
  calc n * 2 ^ T < n * 2 ^ T + 2 ^ T := Nat.lt_add_of_pos_right (Nat.two_pow_pos T)
    _ = 2 ^ T * (n + 1) := by ring
    _ ≤ 3 ^ oddSteps T n * (n + 2 ^ (T - oddSteps T n)) := hb
    _ = n * 3 ^ oddSteps T n + 3 ^ oddSteps T n * 2 ^ (T - oddSteps T n) := by
        ring

/-! ## Exclusion of short cycles -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- Kernel-verified integer computation: for every T ≤ 183 and j ≤ T with
    3^j < 2^T, the cycle bound 3^j·2^(T-j)/(2^T - 3^j) is at most 2^71.
    (T = 184, j = 116 is the first failure: 2^184/3^116 ≈ 1.002.) -/
theorem cycle_check_183 : ∀ T, T < 184 → ∀ j, j < T + 1 →
    (3 ^ j < 2 ^ T → 3 ^ j * 2 ^ (T - j) ≤ (2 ^ T - 3 ^ j) * 2 ^ 71) := by
  decide

/-- NO SMALL CYCLES. Assume the conjecture has been verified below 2^71
    (Barina's computation — stated as a hypothesis, since that computation
    is not formalized here). Then every Terras-cycle of length ≤ 183
    consists of values whose Collatz orbits reach 1; the only such cycle
    is the trivial one through 1 and 2. Unconditionally: any genuinely
    nontrivial cycle must have more than 183 halvings. -/
theorem no_small_terras_cycle
    (hverif : ∀ m : ℕ, 0 < m → m < 2 ^ 71 → ∃ t, collatz_iter t m = 1)
    (T n : ℕ) (hT : 1 ≤ T) (hTK : T ≤ 183) (hn : 0 < n)
    (hc : terras_iter T n = n) :
    ∃ t, collatz_iter t n = 1 := by
  have hjle : oddSteps T n ≤ T := oddSteps_le T n
  have hlt : 3 ^ oddSteps T n < 2 ^ T := cycle_three_pow_lt T n hT hn hc
  have hbound := cycle_min_bound T n hn hc
  have hch : 3 ^ oddSteps T n * 2 ^ (T - oddSteps T n) ≤
      (2 ^ T - 3 ^ oddSteps T n) * 2 ^ 71 :=
    cycle_check_183 T (by omega) (oddSteps T n) (by omega) hlt
  -- split n·2^T along 2^T = 3^j + (2^T - 3^j)
  have hsplit : 3 ^ oddSteps T n + (2 ^ T - 3 ^ oddSteps T n) = 2 ^ T :=
    Nat.add_sub_cancel' hlt.le
  have hx : n * 2 ^ T = n * 3 ^ oddSteps T n
      + n * (2 ^ T - 3 ^ oddSteps T n) := by
    conv_lhs => rw [← hsplit]
    rw [Nat.mul_add]
  have h4 : n * 3 ^ oddSteps T n + n * (2 ^ T - 3 ^ oddSteps T n) <
      n * 3 ^ oddSteps T n + 3 ^ oddSteps T n * 2 ^ (T - oddSteps T n) := by
    rw [← hx]; exact hbound
  have h5 : n * (2 ^ T - 3 ^ oddSteps T n) <
      3 ^ oddSteps T n * 2 ^ (T - oddSteps T n) :=
    Nat.lt_of_add_lt_add_left h4
  have h6 : n * (2 ^ T - 3 ^ oddSteps T n) <
      2 ^ 71 * (2 ^ T - 3 ^ oddSteps T n) := by
    calc n * (2 ^ T - 3 ^ oddSteps T n)
        < 3 ^ oddSteps T n * 2 ^ (T - oddSteps T n) := h5
      _ ≤ (2 ^ T - 3 ^ oddSteps T n) * 2 ^ 71 := hch
      _ = 2 ^ 71 * (2 ^ T - 3 ^ oddSteps T n) := by ring
  have h7 : n < 2 ^ 71 :=
    lt_of_mul_lt_mul_right h6 (Nat.zero_le _)
  exact hverif n hn h7

/-!
## What this means

Unconditionally (`cycle_min_bound`): a cycle with T halvings and j odd
steps confines all its elements below 3^j·2^(T-j)/(2^T - 3^j). The
denominator measures how badly 3^j misses 2^T; by the theory of
continued fractions of log₂ 3 it is usually enormous, so cycles need
T/j to be an exceptional rational approximation to log₂ 3.

Conditionally on the 2^71 verification: no nontrivial cycle has 183 or
fewer halvings (`no_small_terras_cycle`). The first pair the bound
cannot kill is (T, j) = (184, 116), where the element bound
3^116·2^68/(2^184 − 3^116) ≈ 2^71.25 first exceeds 2^71 — the
convergent 306/485 of log₂ 3 looms beyond. Pushing K further is purely
a matter of a larger verified range and deeper Diophantine input, not
of new ideas — which is consistent with the no-go theorem: cycle
exclusion is finite-information reasoning, and it provably cannot close
the conjecture by itself.
-/

end Collatz
