/-
  Collatz Conjecture — The No-Go Theorem

  This file contains NO axioms and NO claim to prove the conjecture.
  It proves that an entire family of proof strategies — "finite-memory
  descent certificates" — cannot possibly work.

  ## The certificate family

  A descent certificate is a potential V(n) = n · W(n) where W is bounded
  above and below (away from 0), together with a window B and a
  contraction factor ρ < 1, such that every sufficiently large n has some
  step count t ≤ B with V(T^t n) ≤ V(n) · ρ. Here T is the Terras map
  (n/2 for even n, (3n+1)/2 for odd n). If such a certificate existed,
  iterating it would force every large n to descend, and the Collatz
  conjecture would follow from the verified base case.

  This family includes every "verify descent for all residue classes
  mod m" argument (W = function of n mod m), every finite-automaton
  potential, and every unweighted uniform-descent claim (W = 1).

  ## The obstruction

  -1 is a fixed point of the odd branch of T on the 2-adic integers:
  T(-1) = (3·(-1)+1)/2 = -1, with drift log(3/2) > 0. The integers
  n = 2^L - 1 shadow this phantom fixed point for L steps:

      T^j(2^L - 1) = 3^j · 2^(L-j) - 1   for all j ≤ L,

  rising monotonically. Since L is unbounded, any bounded potential is
  eventually exhausted: chaining ⌊L/B⌋ certificate windows inside the
  rising stretch forces W down by the factor ρ^⌊L/B⌋ → 0, contradicting
  the lower bound on W.

  ## Contents

  * `terras_mersenne`            : the shadowing orbit formula
  * `no_uniform_descent_bound`   : no uniform descent window exists
  * `uniform_descent_53_false`   : a concrete uniform-descent claim, refuted
  * `no_finite_certificate`      : the no-go theorem (bounded potentials)
  * `no_finite_state_certificate`: corollary for finite-state observers
-/

import Collatz.Basic
import Mathlib

namespace Collatz

/-! ## The Terras map -/

/-- The Terras map: one halving per step, so size bookkeeping is uniform. -/
def terras (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Iterate the Terras map t times. -/
def terras_iter : ℕ → ℕ → ℕ
  | 0, n => n
  | t + 1, n => terras_iter t (terras n)

theorem terras_iter_add (s t n : ℕ) :
    terras_iter t (terras_iter s n) = terras_iter (s + t) n := by
  induction s generalizing n with
  | zero => simp [terras_iter]
  | succ s ih =>
    have h : s + 1 + t = (s + t) + 1 := by omega
    rw [h]
    simp only [terras_iter]
    exact ih (terras n)

theorem terras_iter_succ' (t n : ℕ) :
    terras_iter (t + 1) n = terras (terras_iter t n) := by
  rw [← terras_iter_add t 1 n]
  rfl

/-! ## The shadowing orbit: 2^L - 1 rises for L steps -/

/-- Local, version-stable form of `n < 2^n`. -/
theorem lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : 0 < 2 ^ n := by positivity
    rw [pow_succ]
    omega

/-- The orbit of 2^L - 1 under the Terras map: it shadows the 2-adic
    fixed point -1 for L steps, following T^j(2^L-1) = 3^j·2^(L-j) - 1. -/
theorem terras_mersenne (L : ℕ) : ∀ j, j ≤ L →
    terras_iter j (2 ^ L - 1) = 3 ^ j * 2 ^ (L - j) - 1 := by
  intro j
  induction j with
  | zero => intro _; simp [terras_iter]
  | succ j ih =>
    intro hj
    have hjL : j < L := by omega
    have hprev := ih (by omega)
    rw [terras_iter_succ', hprev]
    have hsplit : L - j = (L - (j + 1)) + 1 := by omega
    have hA : 0 < 3 ^ j * 2 ^ (L - (j + 1)) := by positivity
    have h2 : 3 ^ j * 2 ^ (L - j) = 2 * (3 ^ j * 2 ^ (L - (j + 1))) := by
      rw [hsplit, pow_succ]; ring
    have h3 : 3 ^ (j + 1) * 2 ^ (L - (j + 1)) = 3 * (3 ^ j * 2 ^ (L - (j + 1))) := by
      rw [pow_succ]; ring
    rw [h2, h3]
    unfold terras
    rw [if_neg (by omega : ¬(2 * (3 ^ j * 2 ^ (L - (j + 1))) - 1) % 2 = 0)]
    omega

/-- Along the shadowing orbit, every iterate up to step L is ≥ the start. -/
theorem terras_mersenne_ge (L j : ℕ) (h : j ≤ L) :
    2 ^ L - 1 ≤ terras_iter j (2 ^ L - 1) := by
  rw [terras_mersenne L j h]
  have h1 : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by norm_num) j
  have h2 : 2 ^ j * 2 ^ (L - j) = 2 ^ L := by
    rw [← pow_add]
    congr 1
    omega
  have h3 : 2 ^ L ≤ 3 ^ j * 2 ^ (L - j) := by
    calc 2 ^ L = 2 ^ j * 2 ^ (L - j) := h2.symm
      _ ≤ 3 ^ j * 2 ^ (L - j) := Nat.mul_le_mul h1 (le_refl _)
  omega

/-- The iterates of the shadowing orbit are odd before step L. -/
theorem mersenne_iter_odd (L j : ℕ) (h : j < L) :
    (terras_iter j (2 ^ L - 1)) % 2 = 1 := by
  rw [terras_mersenne L j (le_of_lt h)]
  have hsplit : L - j = (L - (j + 1)) + 1 := by omega
  have hA : 0 < 3 ^ j * 2 ^ (L - (j + 1)) := by positivity
  have h2 : 3 ^ j * 2 ^ (L - j) = 2 * (3 ^ j * 2 ^ (L - (j + 1))) := by
    rw [hsplit, pow_succ]; ring
  omega

/-- NO UNIFORM DESCENT BOUND: for every window B and cutoff N₀ there is an
    n ≥ N₀ none of whose first B Terras iterates drops below n. -/
theorem no_uniform_descent_bound (B N₀ : ℕ) :
    ∃ n, N₀ ≤ n ∧ ∀ t ≤ B, n ≤ terras_iter t n := by
  refine ⟨2 ^ (B + N₀ + 1) - 1, ?_, fun t ht => terras_mersenne_ge _ t (by omega)⟩
  have := lt_two_pow' (B + N₀ + 1)
  omega

/-! ## Refutation of a concrete uniform-descent claim -/

theorem collatz_iter_two (m : ℕ) : collatz_iter 2 m = collatz (collatz m) := rfl

/-- Two Collatz steps on an odd number equal one Terras step. -/
theorem collatz_two_eq_terras (m : ℕ) (hm : m % 2 = 1) :
    collatz_iter 2 m = terras m := by
  rw [collatz_iter_two, collatz_odd m hm, collatz_even (3 * m + 1) (by omega)]
  unfold terras
  rw [if_neg (by omega : ¬m % 2 = 0)]

theorem collatz_mersenne_even_steps (L : ℕ) : ∀ j, j ≤ L →
    collatz_iter (2 * j) (2 ^ L - 1) = terras_iter j (2 ^ L - 1) := by
  intro j
  induction j with
  | zero => intro _; simp [collatz_iter, terras_iter]
  | succ j ih =>
    intro hj
    have hjL : j < L := by omega
    have h2j : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [h2j, collatz_iter_add' (2 * j) 2, ih (by omega), terras_iter_succ']
    exact collatz_two_eq_terras _ (mersenne_iter_odd L j hjL)

/-- A concrete representative of the uniform-descent genre —
    `∀ n > 300, ∃ t ≤ 53, collatz_iter t n < n` — is FALSE.
    Witness: n = 2^28 - 1 rises for 56 Collatz steps.
    (Smallest violator: n = 447.) -/
theorem uniform_descent_53_false :
    ¬(∀ n : ℕ, n > 300 → ∃ t : ℕ, t ≤ 53 ∧ collatz_iter t n < n) := by
  intro h
  obtain ⟨t, ht53, hlt⟩ := h (2 ^ 28 - 1) (by norm_num)
  have key : 2 ^ 28 - 1 ≤ collatz_iter t (2 ^ 28 - 1) := by
    have hj : t / 2 < 28 := by omega
    rcases Nat.mod_two_eq_zero_or_one t with hpar | hpar
    · have ht' : t = 2 * (t / 2) := by omega
      rw [ht', collatz_mersenne_even_steps 28 (t / 2) (by omega)]
      exact terras_mersenne_ge 28 (t / 2) (by omega)
    · have ht' : t = 2 * (t / 2) + 1 := by omega
      rw [ht', collatz_iter_add' (2 * (t / 2)) 1]
      have h1 : collatz_iter 1 (collatz_iter (2 * (t / 2)) (2 ^ 28 - 1)) =
          collatz (collatz_iter (2 * (t / 2)) (2 ^ 28 - 1)) := rfl
      rw [h1, collatz_mersenne_even_steps 28 (t / 2) (by omega),
        collatz_odd _ (mersenne_iter_odd 28 (t / 2) hj)]
      have := terras_mersenne_ge 28 (t / 2) (by omega)
      omega
  omega

/-! ## The No-Go Theorem -/

/-- THE NO-GO THEOREM. There is no descent certificate built from a
    bounded multiplicative potential: no W : ℕ → ℚ with
    0 < lo ≤ W(n) ≤ hi, window B, and contraction factor ρ < 1 such that
    every n ≥ N₀ has some t ≤ B with

        T^t(n) · W(T^t(n)) ≤ n · W(n) · ρ.

    Taking W = exp(Φ ∘ S) for any finite-state observer S and any
    Φ : Q → ℝ, this rules out every finite-memory Lyapunov argument:
    residue-class verification at any modulus, finite-automaton
    potentials, and unweighted uniform-descent claims (W = 1) alike.

    Proof: chain certificate windows along the orbit of n₀ = 2^L - 1,
    which rises for L steps. The potential must shrink geometrically
    while the orbit only grows, exhausting the bounds on W. -/
theorem no_finite_certificate
    (W : ℕ → ℚ) (lo hi : ℚ) (hlo : 0 < lo)
    (hW : ∀ n, lo ≤ W n ∧ W n ≤ hi)
    (B N₀ : ℕ) (ρ : ℚ) (hρ₀ : 0 ≤ ρ) (hρ : ρ < 1)
    (hcert : ∀ n, N₀ ≤ n → ∃ t, 1 ≤ t ∧ t ≤ B ∧
      (terras_iter t n : ℚ) * W (terras_iter t n) ≤ (n : ℚ) * W n * ρ) :
    False := by
  -- hi is positive, so ρ^k eventually beats lo/hi
  have hhi_pos : 0 < hi := lt_of_lt_of_le hlo (le_trans (hW 0).1 (hW 0).2)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hlo hhi_pos) hρ
  have hk_bound : hi * ρ ^ k < lo := by
    have h1 : hi * ρ ^ k < hi * (lo / hi) := mul_lt_mul_of_pos_left hk hhi_pos
    have h2 : hi * (lo / hi) = lo := by field_simp
    linarith
  -- the shadowing orbit, long enough to chain k windows
  have hL : ∀ τ ≤ k * B, τ ≤ k * B + N₀ + 1 := by omega
  have hN₀ : N₀ ≤ 2 ^ (k * B + N₀ + 1) - 1 := by
    have := lt_two_pow' (k * B + N₀ + 1)
    omega
  have hn₀_pos : 0 < 2 ^ (k * B + N₀ + 1) - 1 := by
    have := lt_two_pow' (k * B + N₀ + 1)
    omega
  -- chain i certificate windows: potential shrinks by ρ^i, time stays ≤ i·B
  have chain : ∀ i, i ≤ k → ∃ τ, τ ≤ i * B ∧
      (terras_iter τ (2 ^ (k * B + N₀ + 1) - 1) : ℚ) *
        W (terras_iter τ (2 ^ (k * B + N₀ + 1) - 1)) ≤
      ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * W (2 ^ (k * B + N₀ + 1) - 1) * ρ ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨0, by omega, by simp [terras_iter]⟩
    | succ i ih =>
      intro hik
      obtain ⟨τ, hτB, hval⟩ := ih (by omega)
      have hiB : i * B ≤ k * B := Nat.mul_le_mul (by omega) (le_refl B)
      have hτL : τ ≤ k * B + N₀ + 1 := by omega
      have hge : 2 ^ (k * B + N₀ + 1) - 1 ≤
          terras_iter τ (2 ^ (k * B + N₀ + 1) - 1) :=
        terras_mersenne_ge _ τ hτL
      obtain ⟨t, ht1, htB, hstep⟩ :=
        hcert (terras_iter τ (2 ^ (k * B + N₀ + 1) - 1)) (by omega)
      rw [terras_iter_add τ t] at hstep
      refine ⟨τ + t, ?_, ?_⟩
      · have : (i + 1) * B = i * B + B := by ring
        omega
      · calc (terras_iter (τ + t) (2 ^ (k * B + N₀ + 1) - 1) : ℚ) *
              W (terras_iter (τ + t) (2 ^ (k * B + N₀ + 1) - 1))
            ≤ (terras_iter τ (2 ^ (k * B + N₀ + 1) - 1) : ℚ) *
              W (terras_iter τ (2 ^ (k * B + N₀ + 1) - 1)) * ρ := hstep
          _ ≤ ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) *
              W (2 ^ (k * B + N₀ + 1) - 1) * ρ ^ i * ρ :=
              mul_le_mul_of_nonneg_right hval hρ₀
          _ = ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) *
              W (2 ^ (k * B + N₀ + 1) - 1) * ρ ^ (i + 1) := by ring
  -- after k windows the potential is below its own floor
  obtain ⟨τ, hτkB, hfinal⟩ := chain k le_rfl
  have hτL : τ ≤ k * B + N₀ + 1 := by omega
  have hge : 2 ^ (k * B + N₀ + 1) - 1 ≤
      terras_iter τ (2 ^ (k * B + N₀ + 1) - 1) :=
    terras_mersenne_ge _ τ hτL
  have hn₀_posQ : (0 : ℚ) < ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast hn₀_pos
  have hlow : ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * lo ≤
      (terras_iter τ (2 ^ (k * B + N₀ + 1) - 1) : ℚ) *
        W (terras_iter τ (2 ^ (k * B + N₀ + 1) - 1)) :=
    mul_le_mul (by exact_mod_cast hge) (hW _).1 (le_of_lt hlo) (by positivity)
  have hup : ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) *
      W (2 ^ (k * B + N₀ + 1) - 1) * ρ ^ k ≤
      ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * (hi * ρ ^ k) := by
    have h1 : ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * W (2 ^ (k * B + N₀ + 1) - 1) ≤
        ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * hi :=
      mul_le_mul_of_nonneg_left (hW _).2 (le_of_lt hn₀_posQ)
    calc ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) *
          W (2 ^ (k * B + N₀ + 1) - 1) * ρ ^ k
        ≤ ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * hi * ρ ^ k :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ₀ k)
      _ = ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * (hi * ρ ^ k) := by ring
  have hstrict : ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * (hi * ρ ^ k) <
      ((2 ^ (k * B + N₀ + 1) - 1 : ℕ) : ℚ) * lo :=
    mul_lt_mul_of_pos_left hk_bound hn₀_posQ
  linarith

/-- Corollary: no finite-state observer S : ℕ → Q with positive weights
    w : Q → ℚ yields a descent certificate. This is the form that directly
    kills residue-class arguments: take Q = ZMod m and S = (· mod m). -/
theorem no_finite_state_certificate
    (Q : Type) [Fintype Q] (S : ℕ → Q) (w : Q → ℚ) (hw : ∀ q, 0 < w q)
    (B N₀ : ℕ) (ρ : ℚ) (hρ₀ : 0 ≤ ρ) (hρ : ρ < 1)
    (hcert : ∀ n, N₀ ≤ n → ∃ t, 1 ≤ t ∧ t ≤ B ∧
      (terras_iter t n : ℚ) * w (S (terras_iter t n)) ≤
        (n : ℚ) * w (S n) * ρ) :
    False := by
  have hne : Nonempty Q := ⟨S 0⟩
  obtain ⟨qmin, hqmin⟩ := Finite.exists_min w
  obtain ⟨qmax, hqmax⟩ := Finite.exists_max w
  exact no_finite_certificate (fun n => w (S n)) (w qmin) (w qmax) (hw qmin)
    (fun n => ⟨hqmin (S n), hqmax (S n)⟩) B N₀ ρ hρ₀ hρ hcert

/-!
## What this means

The Collatz conjecture remains OPEN. These theorems delimit where a proof
cannot come from: any argument whose only memory of n is a bounded amount
of information (a residue class, an automaton state, a bounded potential)
is defeated by the integers 2^L - 1, which shadow the 2-adic fixed point
-1 for arbitrarily long stretches.

Equivalently: worst-case reasoning over finitely many bits of n must
treat the bits revealed by successive halvings as adversarial, and the
adversarial answer — all ones — has positive drift log(3/2) forever.
A proof must therefore establish that no actual orbit sustains odd-step
density ≥ log 2 / log 3 ≈ 0.6309 indefinitely. That is an equidistribution
statement about individual orbits in ℤ₂, the precise point where the best
known result (Tao 2019: almost all orbits attain almost bounded values)
stops short of the full conjecture.
-/

end Collatz
