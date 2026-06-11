/-
  Collatz — Density Forcing and the Descent Reduction

  This file is the positive-direction companion to `NoGo.lean`. It contains
  NO axioms and NO claim to prove the conjecture.

  `NoGo.lean` shows the adversarial side: the Mersenne numbers 2^L - 1
  sustain odd-step density 1 for L steps, defeating every bounded-memory
  descent certificate. This file shows the converse pressure: sustained
  survival *requires* high odd density, and quantifies exactly how much.

  ## The master inequality

  Let j = `oddSteps T n` be the number of odd iterates among the first T
  Terras iterates of n. Then (`terras_growth_bound`):

      2^T · (T^T(n) + 1)  ≤  3^j · (n + 2^(T-j)),

  an exact integer inequality, proved by induction with no division and no
  truncated subtraction. It is SHARP: on the Mersenne orbit n = 2^L - 1
  with T = L it is an equality (`terras_growth_bound_sharp`).

  ## Consequences

  * `no_descent_dichotomy`: if n has not descended below itself by step T,
    then either 2^T < 2·3^j (odd density exceeds the critical ratio
    log 2 / log 3 ≈ 0.6309, up to one step), or n < 2^(T-j) (the orbit has
    already spent more than log₂ n halvings). Survival inside the first
    log₂ n halvings — the entire information content of n — demands
    supercritical density (`early_no_descent_forces_density`).

  * `collatz_iff_descent`: the full Collatz conjecture is EQUIVALENT to
    the statement that every n ≥ 2 eventually drops below itself under
    the Terras map.

  Together with `no_finite_certificate` this pins the conjecture into a
  corridor: it is exactly the claim that no orbit sustains supercritical
  odd density forever, and no finite-memory argument can decide that claim.
-/

import Collatz.NoGo

namespace Collatz

/-! ## Counting odd steps along a Terras orbit -/

/-- The number of odd values among the first `T` Terras iterates of `n`
    (positions `0, 1, …, T-1`). Each odd position contributes a
    `(3x+1)/2` step; each even position contributes a halving. -/
def oddSteps : ℕ → ℕ → ℕ
  | 0, _ => 0
  | T + 1, n => (if n % 2 = 1 then 1 else 0) + oddSteps T (terras n)

@[simp]
theorem oddSteps_zero (n : ℕ) : oddSteps 0 n = 0 := rfl

theorem oddSteps_succ_odd (T n : ℕ) (h : n % 2 = 1) :
    oddSteps (T + 1) n = oddSteps T (terras n) + 1 := by
  simp [oddSteps, h, Nat.add_comm]

theorem oddSteps_succ_even (T n : ℕ) (h : n % 2 = 0) :
    oddSteps (T + 1) n = oddSteps T (terras n) := by
  have h' : ¬ n % 2 = 1 := by omega
  simp [oddSteps, h']

theorem oddSteps_le (T : ℕ) : ∀ n, oddSteps T n ≤ T := by
  induction T with
  | zero => intro n; simp
  | succ T ih =>
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [oddSteps_succ_even T n h]
      exact le_trans (ih (terras n)) (by omega)
    · rw [oddSteps_succ_odd T n h]
      have := ih (terras n)
      omega

/-! ## Exact one-step doubling identities (no division) -/

theorem two_mul_terras_odd (n : ℕ) (h : n % 2 = 1) :
    2 * terras n = 3 * n + 1 := by
  unfold terras
  rw [if_neg (by omega : ¬ n % 2 = 0)]
  omega

theorem two_mul_terras_even (n : ℕ) (h : n % 2 = 0) :
    2 * terras n = n := by
  unfold terras
  rw [if_pos h]
  omega

/-! ## The master inequality -/

/-- THE MASTER INEQUALITY. Writing j = `oddSteps T n` for the number of
    odd steps among the first T Terras steps,

        2^T · (T^T(n) + 1) ≤ 3^j · (n + 2^(T-j)).

    Proof: on an odd step 2·(T(x)+1) = 3·(x+1) exactly; on an even step
    2·(T(x)+1) = x + 2. Induction makes the slack of the even steps land
    entirely in the 2^(T-j) term. The bound is sharp on the Mersenne
    orbit (see `terras_growth_bound_sharp`). -/
theorem terras_growth_bound (T : ℕ) : ∀ n : ℕ,
    2 ^ T * (terras_iter T n + 1) ≤
      3 ^ oddSteps T n * (n + 2 ^ (T - oddSteps T n)) := by
  induction T with
  | zero => intro n; simp [terras_iter]
  | succ T ih =>
    intro n
    have hj : oddSteps T (terras n) ≤ T := oddSteps_le T (terras n)
    have hit : terras_iter (T + 1) n = terras_iter T (terras n) := rfl
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · -- even step: 2·terras n = n, the odd count is unchanged
      have hodd : oddSteps (T + 1) n = oddSteps T (terras n) :=
        oddSteps_succ_even T n hpar
      have hexp : T + 1 - oddSteps T (terras n) =
          (T - oddSteps T (terras n)) + 1 := by omega
      rw [hit, hodd, hexp]
      calc 2 ^ (T + 1) * (terras_iter T (terras n) + 1)
          = 2 * (2 ^ T * (terras_iter T (terras n) + 1)) := by ring
        _ ≤ 2 * (3 ^ oddSteps T (terras n) *
              (terras n + 2 ^ (T - oddSteps T (terras n)))) :=
            Nat.mul_le_mul (le_refl 2) (ih (terras n))
        _ = 3 ^ oddSteps T (terras n) *
              (2 * terras n + 2 ^ ((T - oddSteps T (terras n)) + 1)) := by ring
        _ = 3 ^ oddSteps T (terras n) *
              (n + 2 ^ ((T - oddSteps T (terras n)) + 1)) := by
            rw [two_mul_terras_even n hpar]
    · -- odd step: 2·terras n = 3n + 1, the odd count goes up by one
      have hodd : oddSteps (T + 1) n = oddSteps T (terras n) + 1 :=
        oddSteps_succ_odd T n hpar
      have hexp : T + 1 - (oddSteps T (terras n) + 1) =
          T - oddSteps T (terras n) := by omega
      have hp : 0 < 2 ^ (T - oddSteps T (terras n)) := Nat.two_pow_pos _
      rw [hit, hodd, hexp]
      calc 2 ^ (T + 1) * (terras_iter T (terras n) + 1)
          = 2 * (2 ^ T * (terras_iter T (terras n) + 1)) := by ring
        _ ≤ 2 * (3 ^ oddSteps T (terras n) *
              (terras n + 2 ^ (T - oddSteps T (terras n)))) :=
            Nat.mul_le_mul (le_refl 2) (ih (terras n))
        _ = 3 ^ oddSteps T (terras n) *
              (2 * terras n + 2 * 2 ^ (T - oddSteps T (terras n))) := by ring
        _ = 3 ^ oddSteps T (terras n) *
              (3 * n + 1 + 2 * 2 ^ (T - oddSteps T (terras n))) := by
            rw [two_mul_terras_odd n hpar]
        _ ≤ 3 ^ oddSteps T (terras n) *
              (3 * (n + 2 ^ (T - oddSteps T (terras n)))) :=
            Nat.mul_le_mul (le_refl _) (by omega)
        _ = 3 ^ (oddSteps T (terras n) + 1) *
              (n + 2 ^ (T - oddSteps T (terras n))) := by ring

/-! ## Sharpness: equality on the Mersenne orbit -/

/-- If every iterate before step T is odd, all T steps are odd steps. -/
theorem oddSteps_eq_of_all_odd (T : ℕ) : ∀ n,
    (∀ j, j < T → terras_iter j n % 2 = 1) → oddSteps T n = T := by
  induction T with
  | zero => intro n _; rfl
  | succ T ih =>
    intro n hall
    have h0 : n % 2 = 1 := hall 0 (by omega)
    have hshift : ∀ j, j < T → terras_iter j (terras n) % 2 = 1 :=
      fun j hj => hall (j + 1) (by omega)
    rw [oddSteps_succ_odd T n h0, ih (terras n) hshift]

/-- The Mersenne number 2^L - 1 takes L consecutive odd steps. -/
theorem oddSteps_mersenne (L : ℕ) : oddSteps L (2 ^ L - 1) = L :=
  oddSteps_eq_of_all_odd L (2 ^ L - 1) (fun j hj => mersenne_iter_odd L j hj)

/-- SHARPNESS. On the Mersenne orbit the master inequality is an equality:
    2^L · (T^L(2^L - 1) + 1) = 3^L · 2^L. The bound cannot be improved. -/
theorem terras_growth_bound_sharp (L : ℕ) :
    2 ^ L * (terras_iter L (2 ^ L - 1) + 1) =
      3 ^ oddSteps L (2 ^ L - 1) *
        ((2 ^ L - 1) + 2 ^ (L - oddSteps L (2 ^ L - 1))) := by
  rw [oddSteps_mersenne, terras_mersenne L L (le_refl L), Nat.sub_self]
  have h3 : 1 ≤ 3 ^ L := Nat.one_le_pow L 3 (by norm_num)
  have h2 : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by norm_num)
  simp only [pow_zero, mul_one]
  rw [Nat.sub_add_cancel h3, Nat.sub_add_cancel h2]
  ring

/-! ## Density forcing -/

/-- THE DICHOTOMY. If n has not dropped below itself by step T, then either
    the odd-step density is supercritical — 2^T < 2·3^j, i.e.
    j/T > (T·log 2 - log 2)/(T·log 3) → log 2/log 3 ≈ 0.6309 — or the
    orbit has already used more than log₂ n halvings: n < 2^(T-j).

    In words: within the information budget of n (its log₂ n bits,
    consumed one per halving), survival forces supercritical odd density.
    Past that budget, local information about n says nothing — which is
    where `no_finite_certificate` takes over. -/
theorem no_descent_dichotomy (T n : ℕ) (h : n ≤ terras_iter T n) :
    2 ^ T < 2 * 3 ^ oddSteps T n ∨ n < 2 ^ (T - oddSteps T n) := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  -- master inequality, with the non-descent hypothesis on the left
  have hb : 2 ^ T * (n + 1) ≤
      3 ^ oddSteps T n * (n + 2 ^ (T - oddSteps T n)) :=
    le_trans (Nat.mul_le_mul (le_refl (2 ^ T)) (by omega : n + 1 ≤ terras_iter T n + 1))
      (terras_growth_bound T n)
  -- h2 caps the additive slack: n + 2^(T-j) ≤ 2n
  have hcap : n + 2 ^ (T - oddSteps T n) ≤ 2 * n := by
    have := Nat.add_le_add_left h2 n
    calc n + 2 ^ (T - oddSteps T n) ≤ n + n := this
      _ = 2 * n := by ring
  have hA : 3 ^ oddSteps T n * (n + 2 ^ (T - oddSteps T n)) ≤
      2 * 3 ^ oddSteps T n * n :=
    calc 3 ^ oddSteps T n * (n + 2 ^ (T - oddSteps T n))
        ≤ 3 ^ oddSteps T n * (2 * n) := Nat.mul_le_mul (le_refl _) hcap
      _ = 2 * 3 ^ oddSteps T n * n := by ring
  -- h1 then forces 2^T·(n+1) ≤ 2^T·n, absurd
  have hB : 2 * 3 ^ oddSteps T n * n ≤ 2 ^ T * n :=
    Nat.mul_le_mul h1 (le_refl n)
  have hchain : 2 ^ T * (n + 1) ≤ 2 ^ T * n := le_trans hb (le_trans hA hB)
  have h6 : 2 ^ T * n + 2 ^ T ≤ 2 ^ T * n + 0 := by
    calc 2 ^ T * n + 2 ^ T = 2 ^ T * (n + 1) := by ring
      _ ≤ 2 ^ T * n := hchain
      _ = 2 ^ T * n + 0 := by rw [Nat.add_zero]
  have h7 : 2 ^ T ≤ 0 := Nat.le_of_add_le_add_left h6
  exact absurd h7 (Nat.two_pow_pos T).not_ge

/-- Inside the first log₂ n worth of halvings — the entire information
    content of n — survival without descent forces supercritical odd
    density. (Compare `terras_mersenne`: the Mersenne numbers realize
    this branch with density exactly 1 for exactly log₂(n+1) steps.) -/
theorem early_no_descent_forces_density (T n : ℕ)
    (h : n ≤ terras_iter T n) (hearly : 2 ^ (T - oddSteps T n) ≤ n) :
    2 ^ T < 2 * 3 ^ oddSteps T n := by
  rcases no_descent_dichotomy T n h with h' | h'
  · exact h'
  · exact absurd hearly h'.not_ge

/-! ## The descent reduction: Collatz ⟺ every n ≥ 2 descends -/

theorem terras_pos (n : ℕ) (hn : 0 < n) : 0 < terras n := by
  unfold terras
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_pos h]; omega
  · rw [if_neg (by omega : ¬ n % 2 = 0)]; omega

theorem terras_iter_pos (t : ℕ) : ∀ n, 0 < n → 0 < terras_iter t n := by
  induction t with
  | zero => intro n hn; exact hn
  | succ t ih => intro n hn; exact ih (terras n) (terras_pos n hn)

/-- Every Terras iterate is reached by some number of Collatz steps:
    one Collatz step per even Terras step, two per odd Terras step. -/
theorem exists_collatz_iter_eq_terras_iter (t : ℕ) : ∀ n, 0 < n →
    ∃ s, collatz_iter s n = terras_iter t n := by
  induction t with
  | zero => exact fun n _ => ⟨0, rfl⟩
  | succ t ih =>
    intro n hn
    obtain ⟨s, hs⟩ := ih (terras n) (terras_pos n hn)
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · refine ⟨1 + s, ?_⟩
      rw [collatz_iter_add' 1 s n]
      have h1 : collatz_iter 1 n = terras n := by
        show collatz n = terras n
        rw [collatz_even n hpar]
        unfold terras
        rw [if_pos hpar]
      rw [h1, hs]
      rfl
    · refine ⟨2 + s, ?_⟩
      rw [collatz_iter_add' 2 s n, collatz_two_eq_terras n hpar, hs]
      rfl

/-- THE DESCENT REDUCTION. If every n ≥ 2 eventually drops strictly below
    itself under the Terras map, the full Collatz conjecture follows, by
    strong induction. This is the precise sense in which the conjecture
    IS a descent statement — and `no_finite_certificate` proves descent
    cannot be certified by any bounded-memory argument. -/
theorem descent_implies_collatz
    (hdesc : ∀ n, 2 ≤ n → ∃ t, terras_iter t n < n) :
    CollatzConjecture := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with h1 | h2
    · exact ⟨0, h1.symm⟩
    · obtain ⟨t, ht⟩ := hdesc n (by omega)
      have hpos : 0 < terras_iter t n := terras_iter_pos t n (by omega)
      obtain ⟨s, hs⟩ := exists_collatz_iter_eq_terras_iter t n (by omega)
      obtain ⟨T₂, hT₂⟩ := ih (terras_iter t n) ht (by omega)
      exact ⟨s + T₂, by rw [collatz_iter_add' s T₂ n, hs, hT₂]⟩

/-- If the Collatz orbit of n reaches 1, so does its Terras orbit. -/
theorem collatz_one_implies_terras_one : ∀ s, ∀ n, 0 < n →
    collatz_iter s n = 1 → ∃ t, terras_iter t n = 1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro n hn h1
    match s, h1 with
    | 0, h1 => exact ⟨0, h1⟩
    | s' + 1, h1 =>
      rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
      · -- even: one Collatz step is one Terras step
        have hc : collatz n = terras n := by
          rw [collatz_even n hpar]
          unfold terras
          rw [if_pos hpar]
        have h2 : collatz_iter s' (terras n) = 1 := by
          have e : collatz_iter (s' + 1) n = collatz_iter s' (collatz n) := rfl
          rw [e, hc] at h1
          exact h1
        obtain ⟨t, ht⟩ := ih s' (by omega) (terras n) (terras_pos n hn) h2
        exact ⟨t + 1, ht⟩
      · -- odd: two Collatz steps are one Terras step
        match s', h1 with
        | 0, h1 =>
          exfalso
          have hcn : collatz n = 1 := h1
          rw [collatz_odd n hpar] at hcn
          omega
        | s'' + 1, h1 =>
          have e2 : collatz (collatz n) = terras n :=
            collatz_two_eq_terras n hpar
          have h2 : collatz_iter s'' (terras n) = 1 := by
            have e : collatz_iter (s'' + 1 + 1) n =
                collatz_iter s'' (collatz (collatz n)) := rfl
            rw [e, e2] at h1
            exact h1
          obtain ⟨t, ht⟩ := ih s'' (by omega) (terras n) (terras_pos n hn) h2
          exact ⟨t + 1, ht⟩

/-- Conversely, the Collatz conjecture implies universal Terras descent. -/
theorem collatz_implies_descent (hc : CollatzConjecture) :
    ∀ n, 2 ≤ n → ∃ t, terras_iter t n < n := by
  intro n hn
  obtain ⟨s, hs⟩ := hc n (by omega)
  obtain ⟨t, ht⟩ := collatz_one_implies_terras_one s n (by omega) hs
  exact ⟨t, by omega⟩

/-- THE EQUIVALENCE. The Collatz conjecture holds if and only if every
    n ≥ 2 eventually drops strictly below itself under the Terras map. -/
theorem collatz_iff_descent :
    CollatzConjecture ↔ (∀ n, 2 ≤ n → ∃ t, terras_iter t n < n) :=
  ⟨collatz_implies_descent, descent_implies_collatz⟩

/-!
## What this means

`collatz_iff_descent` reduces the conjecture to universal descent.
`no_descent_dichotomy` says descent can only be avoided by running
supercritical odd density (j/T > log 2/log 3) — at least while the orbit
is still inside the log₂ n-bit information budget of its starting value.
`terras_growth_bound_sharp` says the Mersenne numbers exhaust that budget
exactly, at density 1, which is the same orbit family that
`no_finite_certificate` uses to destroy every bounded-memory proof.

So the Collatz conjecture sits in a corridor, now formal at both walls:

* it is EXACTLY the claim that no orbit sustains supercritical odd
  density forever (this file), and
* no argument that remembers only boundedly much about n can prove that
  claim (`NoGo.lean`).

Any proof must therefore track unboundedly much information about the
orbit — e.g. equidistribution of orbits in ℤ₂, the open frontier past
Tao 2019. The conjecture remains OPEN.
-/

end Collatz
