/-
  Collatz — The Word-Complexity Ladder, Rung Zero

  This file contains NO axioms and NO claim to prove the conjecture.

  THE LADDER. Order potential divergent orbits by the complexity of
  their parity itineraries: eventually periodic words, automatic words,
  morphic/Sturmian words, and beyond. Excluding each class is a theorem
  target; this file formalizes the floor:

    RUNG ZERO (`divergent_itinerary_aperiodic`): an orbit with
    unbounded values has a parity itinerary that is NOT eventually
    periodic.

  The mechanism is the infinite-precision form of the parity bijection
  (Parity.lean): two integers whose itineraries agree at every step are
  EQUAL (`eq_of_itinerary_eq`). An eventually periodic itinerary
  therefore forces the orbit itself to be eventually periodic
  (`orbit_eq_of_periodic_itinerary`), hence bounded
  (`bounded_of_orbit_periodic`) — and divergence is contradicted.

  Also here, for the next rungs: the CLOSED FORM of the correction term
  (`dcoef_closed`),

      d(w) = Σ_{i < T, w_i = 1} 2^i · 3^(#ones of w after position i),

  the binary-ternary mixed sum behind the 2-adic realization series
  x = −Σ_{w_i = 1} 2^i 3^(−(1 + #ones before i)) of an itinerary, and
  the engine of the Mahler-method attack on the automatic rung (see
  analysis/NOVEL_APPROACHES.md).
-/

import Collatz.Shadow

namespace Collatz

/-! ## Itineraries determine integers exactly -/

/-- Two naturals whose parity itineraries agree at every time are equal:
    the infinite-precision parity bijection. -/
theorem eq_of_itinerary_eq {n m : ℕ}
    (h : ∀ t, terras_iter t n % 2 = terras_iter t m % 2) : n = m := by
  set k := n + m + 1 with hk
  have hmod : n ≡ m [MOD 2 ^ k] :=
    modEq_of_parity k n m (fun t _ => h t)
  have hn : n < 2 ^ k := by
    calc n < 2 ^ n := lt_two_pow' n
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : m < 2 ^ k := by
    calc m < 2 ^ m := lt_two_pow' m
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := hmod
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this

/-- An eventually periodic itinerary forces an eventually periodic
    orbit: the tail points s and s+P have identical itineraries, hence
    are equal integers. -/
theorem orbit_eq_of_periodic_itinerary {n s P : ℕ}
    (h : ∀ t, terras_iter (s + t) n % 2 = terras_iter (s + P + t) n % 2) :
    terras_iter s n = terras_iter (s + P) n := by
  apply eq_of_itinerary_eq
  intro t
  rw [terras_iter_add, terras_iter_add]
  exact h t

/-! ## Periodic orbits are bounded -/

/-- Pumping: if u returns to itself after P steps, its orbit repeats. -/
theorem orbit_pump {u P : ℕ} (hu : terras_iter P u = u) :
    ∀ q r, terras_iter (q * P + r) u = terras_iter r u := by
  intro q
  induction q with
  | zero => intro r; rw [Nat.zero_mul, Nat.zero_add]
  | succ q ih =>
    intro r
    have e : (q + 1) * P + r = P + (q * P + r) := by ring
    rw [e, ← terras_iter_add, hu, ih r]

/-- A periodic tail bounds the whole orbit by its first s + P values. -/
theorem bounded_of_orbit_periodic {n s P : ℕ} (hP : 1 ≤ P)
    (hper : terras_iter s n = terras_iter (s + P) n) :
    ∀ t, terras_iter t n ≤
      ((Finset.range (s + P + 1)).image (fun i => terras_iter i n)).max'
        ⟨terras_iter 0 n, Finset.mem_image.mpr
          ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩ := by
  intro t
  set S := (Finset.range (s + P + 1)).image (fun i => terras_iter i n)
    with hS
  have hmem : ∀ i, i ≤ s + P → terras_iter i n ∈ S := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  rcases le_or_lt t (s + P) with ht | ht
  · exact Finset.le_max' S _ (hmem t ht)
  · -- t > s + P: fold back using periodicity of u := T^s(n)
    have hu : terras_iter P (terras_iter s n) = terras_iter s n := by
      rw [terras_iter_add]
      exact hper.symm
    have hdm : (t - s) / P * P + (t - s) % P = t - s := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod (t - s) P
    have e1 : terras_iter t n =
        terras_iter ((t - s) / P * P + (t - s) % P) (terras_iter s n) := by
      rw [terras_iter_add]
      congr 1
      rw [hdm]
      omega
    rw [e1, orbit_pump hu, terras_iter_add]
    apply Finset.le_max' S
    apply hmem
    have : (t - s) % P < P := Nat.mod_lt _ (by omega)
    omega

/-! ## Rung zero -/

/-- RUNG ZERO of the word-complexity ladder: a divergent orbit
    (unbounded values) has an itinerary that is not eventually
    periodic. Eventually periodic itineraries belong exclusively to
    eventually periodic — hence bounded — orbits. -/
theorem divergent_itinerary_aperiodic {n : ℕ}
    (hdiv : ∀ B, ∃ t, B < terras_iter t n) :
    ¬ ∃ s P, 1 ≤ P ∧
      ∀ t, terras_iter (s + t) n % 2 = terras_iter (s + P + t) n % 2 := by
  rintro ⟨s, P, hP, hper⟩
  have heq := orbit_eq_of_periodic_itinerary hper
  have hbd := bounded_of_orbit_periodic hP heq
  obtain ⟨t, ht⟩ := hdiv
    (((Finset.range (s + P + 1)).image (fun i => terras_iter i n)).max'
      ⟨terras_iter 0 n, Finset.mem_image.mpr
        ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩)
  exact absurd (hbd t) (by omega)

/-! ## The closed form of the correction term -/

/-- THE CLOSED FORM: d(w) = Σ_{i<T, w_i=1} 2^i · 3^(#ones after i).
    Written with the parity as a 0/1 multiplier. This is the finite
    truncation of the 2-adic realization series of an itinerary, and
    the object of the exponential-sum and Mahler-method programs. -/
theorem dcoef_closed (T : ℕ) : ∀ n,
    dcoef T n = ∑ i ∈ Finset.range T,
      (terras_iter i n % 2) * 2 ^ i *
        3 ^ (oddSteps T n - oddSteps (i + 1) n) := by
  induction T with
  | zero => intro n; simp
  | succ T ih =>
    intro n
    rw [Finset.sum_range_succ']
    have hshift : ∀ i, terras_iter (i + 1) n % 2 =
        terras_iter i (terras n) % 2 := fun i => rfl
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · -- even head: the i = 0 term vanishes, the rest is 2 · d(tail)
      rw [dcoef_succ_even hp]
      have h0 : (terras_iter 0 n % 2) * 2 ^ 0 *
          3 ^ (oddSteps (T + 1) n - oddSteps (0 + 1) n) = 0 := by
        have : terras_iter 0 n % 2 = 0 := hp
        rw [this]
        ring
      rw [h0, Nat.add_zero, ih (terras n), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have he1 : oddSteps (T + 1) n = oddSteps T (terras n) :=
        oddSteps_succ_even T n hp
      have he2 : oddSteps (i + 1 + 1) n = oddSteps (i + 1) (terras n) :=
        oddSteps_succ_even (i + 1) n hp
      rw [hshift i, he1, he2]
      ring
    · -- odd head: the i = 0 term is 3^(j of the tail)
      rw [dcoef_succ_odd hp]
      have he1 : oddSteps (T + 1) n = oddSteps T (terras n) + 1 :=
        oddSteps_succ_odd T n hp
      have h0 : (terras_iter 0 n % 2) * 2 ^ 0 *
          3 ^ (oddSteps (T + 1) n - oddSteps (0 + 1) n) =
          3 ^ oddSteps T (terras n) := by
        have hpar : terras_iter 0 n % 2 = 1 := hp
        have he0 : oddSteps (0 + 1) n = oddSteps 0 (terras n) + 1 :=
          oddSteps_succ_odd 0 n hp
        rw [hpar, he1, he0]
        have h00 : oddSteps 0 (terras n) = 0 := rfl
        rw [h00]
        have hexp : oddSteps T (terras n) + 1 - (0 + 1) =
            oddSteps T (terras n) := by omega
        rw [hexp]
        ring
      rw [h0, ih (terras n), Finset.mul_sum]
      have hsum : ∀ i ∈ Finset.range T,
          (terras_iter (i + 1) n % 2) * 2 ^ (i + 1) *
            3 ^ (oddSteps (T + 1) n - oddSteps (i + 1 + 1) n) =
          2 * ((terras_iter i (terras n) % 2) * 2 ^ i *
            3 ^ (oddSteps T (terras n) - oddSteps (i + 1) (terras n))) := by
        intro i hi
        have he2 : oddSteps (i + 1 + 1) n =
            oddSteps (i + 1) (terras n) + 1 :=
          oddSteps_succ_odd (i + 1) n hp
        rw [hshift i, he1, he2]
        have he3 : oddSteps T (terras n) + 1 -
            (oddSteps (i + 1) (terras n) + 1) =
            oddSteps T (terras n) - oddSteps (i + 1) (terras n) := by
          omega
        rw [he3]
        ring
      rw [Finset.sum_congr rfl hsum]
      omega

/-!
## What this means

Rung zero closes the simplest escape route by complexity: an itinerary
that ever settles into a repeating pattern belongs to a bounded orbit
(in fact to one of the rational-cycle realizations classified by the
shadow machinery — for positive integers, by `no_small_terras_cycle`
territory). A divergent orbit must therefore improvise forever: its
parity word is aperiodic, and by the density floor it improvises
inside the narrow supercritical band.

The next rungs, in order of attack (see NOVEL_APPROACHES.md): words
generated by finite automata (via the closed form above, the 2-adic
realization of an automatic word satisfies a Mahler-type functional
equation along substitution towers — the classical method for proving
such values are not integers), then morphic and Sturmian words, where
the shadow-clustering experiments already show the 3-adic footprint of
structure. Each rung excluded is a theorem; the conjecture is the top
of the ladder. It remains open.
-/

end Collatz
