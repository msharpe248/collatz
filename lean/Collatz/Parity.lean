/-
  Collatz — Terras' Parity-Vector Theorem

  This file contains NO axioms and NO claim to prove the conjecture.

  THE THEOREM (Terras 1976). The first k parities of a Terras orbit
  depend only on n mod 2^k, and conversely determine n mod 2^k: the map

      residues mod 2^k  →  parity vectors of length k

  is a bijection. Consequences proved here:

  * `parity_of_modEq` / `modEq_of_parity` : the bijection, both directions
  * `oddSteps_modEq`        : oddSteps k is a function of n mod 2^k
  * `parity_pattern_realized`: EVERY parity pattern occurs below 2^k —
        the all-ones pattern of `terras_mersenne` is just one point of a
        complete combinatorial spectrum of adversaries
  * `card_oddSteps`         : THE BINOMIAL LAW — exactly choose(k, j)
        residues mod 2^k take j odd steps in their first k Terras steps

  Why this matters. `Density.lean` shows survival without descent
  requires supercritical odd density (j ≳ 0.6309·k). The binomial law
  says the number of residue classes that can even *exhibit* such a
  prefix is the binomial tail ∑_{j ≥ 0.631k} C(k,j) ≈ 2^{0.95k} — an
  exponentially vanishing 2^{-0.05k} fraction. That is the engine of
  Terras' theorem ("almost all n have finite stopping time"), whose full
  formalization is the natural next step on top of this file.

  The proofs ride entirely on the exact doubling identities
  2·T(n) = n (even) and 2·T(n) = 3n+1 (odd) pushed through Nat.ModEq:
  doubling maps congruence mod 2^k to congruence mod 2^(k+1) and back,
  and 3 is invertible mod every power of 2.
-/

import Collatz.Density

namespace Collatz

/-! ## Doubling and congruences -/

/-- Halve a congruence: 2a ≡ 2b (mod 2m) gives a ≡ b (mod m). -/
theorem modEq_of_two_mul {a b m : ℕ} (h : 2 * a ≡ 2 * b [MOD 2 * m]) :
    a ≡ b [MOD m] := by
  have h1 : 2 * a % (2 * m) = 2 * b % (2 * m) := h
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h1
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1

/-- FORWARD DIRECTION: congruence mod 2^k determines the first k parities. -/
theorem parity_of_modEq (k : ℕ) : ∀ n m, n ≡ m [MOD 2 ^ k] → ∀ t, t < k →
    terras_iter t n % 2 = terras_iter t m % 2 := by
  induction k with
  | zero => intro n m _ t ht; omega
  | succ k ih =>
    intro n m h t ht
    have hpar : n % 2 = m % 2 := by
      have hdvd : (2 : ℕ) ∣ 2 ^ (k + 1) := ⟨2 ^ k, by ring⟩
      exact Nat.ModEq.of_dvd hdvd h
    rcases t with _ | t'
    · exact hpar
    · have hstep : terras n ≡ terras m [MOD 2 ^ k] := by
        have hsplit : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rcases Nat.mod_two_eq_zero_or_one n with hp | hp
        · have hmp : m % 2 = 0 := by omega
          apply modEq_of_two_mul
          rw [two_mul_terras_even n hp, two_mul_terras_even m hmp, ← hsplit]
          exact h
        · have hmp : m % 2 = 1 := by omega
          apply modEq_of_two_mul
          rw [two_mul_terras_odd n hp, two_mul_terras_odd m hmp, ← hsplit]
          exact (h.mul_left 3).add_right 1
      exact ih (terras n) (terras m) hstep t' (by omega)

/-- BACKWARD DIRECTION: the first k parities determine n mod 2^k. -/
theorem modEq_of_parity (k : ℕ) : ∀ n m,
    (∀ t, t < k → terras_iter t n % 2 = terras_iter t m % 2) →
    n ≡ m [MOD 2 ^ k] := by
  induction k with
  | zero =>
    intro n m _
    have h1 : (2 : ℕ) ^ 0 = 1 := pow_zero 2
    rw [h1]
    exact Nat.modEq_one
  | succ k ih =>
    intro n m hv
    have hpar : n % 2 = m % 2 := hv 0 (by omega)
    have hrec : terras n ≡ terras m [MOD 2 ^ k] :=
      ih (terras n) (terras m) (fun t ht => hv (t + 1) (by omega))
    have hdouble : 2 * terras n ≡ 2 * terras m [MOD 2 ^ (k + 1)] := by
      have h2 := Nat.ModEq.mul_left' (c := 2) hrec
      have hsplit : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      rwa [hsplit] at h2
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · have hmp : m % 2 = 0 := by omega
      rwa [two_mul_terras_even n hp, two_mul_terras_even m hmp] at hdouble
    · have hmp : m % 2 = 1 := by omega
      rw [two_mul_terras_odd n hp, two_mul_terras_odd m hmp] at hdouble
      have h3 : 3 * n ≡ 3 * m [MOD 2 ^ (k + 1)] :=
        Nat.ModEq.add_right_cancel' 1 hdouble
      have hco : Nat.Coprime (2 ^ (k + 1)) 3 :=
        Nat.Coprime.pow_left (k + 1) (by norm_num)
      exact Nat.ModEq.cancel_left_of_coprime hco h3

/-! ## oddSteps as a sum of parities -/

theorem oddSteps_eq_sum (T : ℕ) : ∀ n,
    oddSteps T n = ∑ t ∈ Finset.range T, terras_iter t n % 2 := by
  induction T with
  | zero => intro n; simp
  | succ T ih =>
    intro n
    rw [Finset.sum_range_succ']
    have hshift : (∑ t ∈ Finset.range T, terras_iter (t + 1) n % 2)
        = ∑ t ∈ Finset.range T, terras_iter t (terras n) % 2 :=
      Finset.sum_congr rfl (fun t _ => rfl)
    rw [hshift, ← ih (terras n)]
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · rw [oddSteps_succ_even T n hp]
      have h0 : terras_iter 0 n % 2 = 0 := hp
      rw [h0]
      exact (Nat.add_zero _).symm
    · rw [oddSteps_succ_odd T n hp]
      have h0 : terras_iter 0 n % 2 = 1 := hp
      rw [h0]

/-- The odd-step count over a window of length k is a function of
    n mod 2^k: finite information at every scale, exactly matching the
    information budget of `no_descent_dichotomy`. -/
theorem oddSteps_modEq (k : ℕ) {n m : ℕ} (h : n ≡ m [MOD 2 ^ k]) :
    oddSteps k n = oddSteps k m := by
  rw [oddSteps_eq_sum, oddSteps_eq_sum]
  exact Finset.sum_congr rfl
    (fun t ht => parity_of_modEq k n m h t (Finset.mem_range.mp ht))

/-! ## The bijection with parity patterns -/

/-- The set of odd positions in the first k Terras steps of n. -/
def parities (k n : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun t => terras_iter t n % 2 = 1

theorem oddSteps_eq_card (k n : ℕ) : oddSteps k n = (parities k n).card := by
  unfold parities
  rw [oddSteps_eq_sum, Finset.card_filter]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one (terras_iter t n) with h | h <;> simp [h]

/-- Distinct residues below 2^k have distinct parity patterns. -/
theorem parities_inj (k : ℕ) {r s : ℕ} (hr : r < 2 ^ k) (hs : s < 2 ^ k)
    (h : parities k r = parities k s) : r = s := by
  have hpv : ∀ t, t < k → terras_iter t r % 2 = terras_iter t s % 2 := by
    intro t ht
    have hmem : (t ∈ parities k r) ↔ (t ∈ parities k s) := by rw [h]
    simp only [parities, Finset.mem_filter, Finset.mem_range] at hmem
    rcases Nat.mod_two_eq_zero_or_one (terras_iter t r) with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (terras_iter t s) with h2 | h2 <;>
      omega
  have hmod : r % 2 ^ k = s % 2 ^ k := modEq_of_parity k r s hpv
  rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at hmod

/-- EVERY PATTERN OCCURS: for any prescribed set S of odd positions
    within the first k steps, some r < 2^k realizes exactly that pattern.
    By injectivity and counting: 2^k residues, 2^k patterns. The Mersenne
    adversary of `NoGo.lean` (S = everything) is one point of this
    spectrum. -/
theorem parity_pattern_realized (k : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range k) :
    ∃ r < 2 ^ k, parities k r = S := by
  have hsurj := Finset.surj_on_of_inj_on_of_card_le
    (s := Finset.range (2 ^ k)) (t := (Finset.range k).powerset)
    (f := fun r _ => parities k r)
    (hf := fun r _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _))
    (hinj := fun r s hr hs h =>
      parities_inj k (Finset.mem_range.mp hr) (Finset.mem_range.mp hs) h)
    (hst := by rw [Finset.card_powerset, Finset.card_range, Finset.card_range])
  obtain ⟨r, hr, hpr⟩ := hsurj S (Finset.mem_powerset.mpr hS)
  exact ⟨r, Finset.mem_range.mp hr, hpr.symm⟩

/-! ## The binomial law -/

/-- THE BINOMIAL LAW (Terras 1976). Exactly choose(k, j) residues mod 2^k
    take j odd steps among their first k Terras steps. Combined with
    `no_descent_dichotomy` (survival needs j ≳ 0.6309·k), the residue
    classes that can survive k steps without descending number at most
    the binomial tail ∑_{j > 0.63k} C(k,j) — an exponentially vanishing
    fraction of all classes. -/
theorem card_oddSteps (k j : ℕ) :
    ((Finset.range (2 ^ k)).filter (fun r => oddSteps k r = j)).card
      = Nat.choose k j := by
  have hcard : ((Finset.range k).powersetCard j).card = Nat.choose k j := by
    rw [Finset.card_powersetCard, Finset.card_range]
  rw [← hcard]
  apply Finset.card_bij (fun r _ => parities k r)
  · -- well-defined into powersetCard j
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    rw [← oddSteps_eq_card]
    exact hr.2
  · -- injective
    intro r hr s hs h
    simp only [Finset.mem_filter, Finset.mem_range] at hr hs
    exact parities_inj k hr.1 hs.1 h
  · -- surjective
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨r, hr, hpr⟩ := parity_pattern_realized k S hS.1
    refine ⟨r, ?_, hpr⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hr, ?_⟩
    rw [oddSteps_eq_card, hpr]
    exact hS.2

/-!
## What this means

The parity-vector bijection is the exact statement that the Terras
dynamics, restricted to its first k steps, is a COMPLETE shuffle of the
residues mod 2^k: every finite behavior occurs exactly once. Three
formal walls now stand together:

* every k-step behavior occurs (`parity_pattern_realized`) — so
  worst-case finite reasoning is hopeless (`no_finite_certificate`);
* but behaviors are binomially distributed (`card_oddSteps`), and
  survival demands the exponentially rare supercritical tail
  (`no_descent_dichotomy`);
* so the conjecture — equivalent to universal descent
  (`collatz_iff_descent`) — is the claim that no single integer rides
  the vanishing tail at every scale k simultaneously.

Next step on this road: the binomial tail bound, giving Terras' theorem
that the density of n with stopping time > k vanishes as k → ∞ — the
first density-1 result, within reach of this machinery.
-/

end Collatz
