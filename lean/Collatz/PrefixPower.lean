/-
  Collatz — The Prefix-Power Criterion

  This file contains NO axioms and NO claim to prove the conjecture.

  THE CRITERION (`prefix_power`). If the parity itinerary of n is
  ℓ-periodic for its first M letters (M ≥ ℓ) — i.e. begins with a
  (possibly fractional) power u^{M/ℓ} of a word u of length ℓ — then
  either the orbit itself is ℓ-periodic (T^ℓ(n) = n), or

      2^(M − ℓ) ≤ max(n, T^ℓ(n)),

  and hence (`prefix_power_bound`, using the master inequality)

      2^M ≤ 2^ℓ·n + 3^o·(n + 2^ℓ),   o = number of odd steps in u.

  In logarithmic form, with e = M/ℓ the exponent of the initial power
  and δ = o/ℓ the density of ones in u:

      (e − 1)·ℓ  ≤  δ·ℓ·log₂ 3 + log₂(n+1) + O(1).

  MEANING. A Collatz orbit cannot begin with a long high power of a
  short word unless the start is enormous. The threshold exponent
  e = 1 + δ·log₂3 equals 2 exactly at the critical density
  δ = log 2/log 3: below the critical line squares are already
  impossible for large ℓ, above it one needs e > 2. This is the
  elementary Diophantine content of the parity bijection: the 2-adic
  realizations of periodic words u^∞ are rationals d(u)/(2^ℓ − 3^o),
  and an integer cannot sit 2-adically within 2^{−M} of one of them
  unless it is as large as the approximation is good. Characteristic
  Sturmian words have initial critical exponent ≥ 2 + 1/φ ≈ 2.618
  (Berthé–Holton–Zamboni), so this criterion bites on Sturmian
  itineraries of every slope in a neighbourhood above the critical
  line; the combinatorial side is not formalized here.

  The proof is three lines: n and T^ℓ(n) share their first M − ℓ
  parities, so n ≡ T^ℓ(n) (mod 2^(M−ℓ)) by the parity bijection.
-/

import Collatz.Shadow

namespace Collatz

/-- THE PREFIX-POWER CRITERION. If the itinerary of `n` is `ℓ`-periodic
    on its first `M` letters, then the orbit is `ℓ`-periodic, or
    `2^(M−ℓ) ≤ max n (T^ℓ n)`. -/
theorem prefix_power (n ℓ M : ℕ) (hM : ℓ ≤ M)
    (h : ∀ t, t + ℓ < M → terras_iter t n % 2 = terras_iter (t + ℓ) n % 2) :
    terras_iter ℓ n = n ∨ 2 ^ (M - ℓ) ≤ max n (terras_iter ℓ n) := by
  -- n and T^ℓ(n) share their first M − ℓ parities
  have hpar : ∀ t, t < M - ℓ →
      terras_iter t n % 2 = terras_iter t (terras_iter ℓ n) % 2 := by
    intro t ht
    rw [terras_iter_add ℓ t n, Nat.add_comm]
    exact h t (by omega)
  have hmod : n ≡ terras_iter ℓ n [MOD 2 ^ (M - ℓ)] :=
    modEq_of_parity (M - ℓ) n (terras_iter ℓ n) hpar
  by_cases heq : terras_iter ℓ n = n
  · exact Or.inl heq
  · right
    -- two distinct naturals congruent mod 2^k differ by at least 2^k
    set m := terras_iter ℓ n with hm
    have hne : n ≠ m := fun e => heq e.symm
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hdvd : 2 ^ (M - ℓ) ∣ m - n :=
        (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hmod
      have := Nat.le_of_dvd (by omega) hdvd
      exact le_trans (by omega) (le_max_right n m)
    · have hdvd : 2 ^ (M - ℓ) ∣ n - m :=
        (Nat.modEq_iff_dvd' (le_of_lt hgt)).mp hmod.symm
      have := Nat.le_of_dvd (by omega) hdvd
      exact le_trans (by omega) (le_max_left n m)

/-- The criterion in size form: `2^M ≤ 2^ℓ·n + 3^o·(n + 2^ℓ)` where
    `o` is the number of odd steps among the first `ℓ`. -/
theorem prefix_power_bound (n ℓ M : ℕ) (hM : ℓ ≤ M)
    (h : ∀ t, t + ℓ < M → terras_iter t n % 2 = terras_iter (t + ℓ) n % 2)
    (hne : terras_iter ℓ n ≠ n) :
    2 ^ M ≤ 2 ^ ℓ * n + 3 ^ oddSteps ℓ n * (n + 2 ^ ℓ) := by
  rcases prefix_power n ℓ M hM h with heq | hle
  · exact absurd heq hne
  · have hgrow := terras_growth_bound ℓ n
    -- 2^ℓ · T^ℓ(n) ≤ 3^o (n + 2^(ℓ−o)) ≤ 3^o (n + 2^ℓ)
    have h1 : 2 ^ ℓ * terras_iter ℓ n ≤ 3 ^ oddSteps ℓ n * (n + 2 ^ ℓ) := by
      have h2 : 2 ^ (ℓ - oddSteps ℓ n) ≤ 2 ^ ℓ :=
        Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
      calc 2 ^ ℓ * terras_iter ℓ n ≤ 2 ^ ℓ * (terras_iter ℓ n + 1) := by
            apply Nat.mul_le_mul_left; omega
        _ ≤ 3 ^ oddSteps ℓ n * (n + 2 ^ (ℓ - oddSteps ℓ n)) := hgrow
        _ ≤ 3 ^ oddSteps ℓ n * (n + 2 ^ ℓ) := by
            apply Nat.mul_le_mul_left; omega
    have hsplit : 2 ^ M = 2 ^ ℓ * 2 ^ (M - ℓ) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    calc 2 ^ ℓ * 2 ^ (M - ℓ) ≤ 2 ^ ℓ * max n (terras_iter ℓ n) :=
          Nat.mul_le_mul_left _ hle
      _ ≤ 2 ^ ℓ * (n + terras_iter ℓ n) := by
          apply Nat.mul_le_mul_left
          exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
      _ = 2 ^ ℓ * n + 2 ^ ℓ * terras_iter ℓ n := by ring
      _ ≤ 2 ^ ℓ * n + 3 ^ oddSteps ℓ n * (n + 2 ^ ℓ) := by
          exact Nat.add_le_add_left h1 _

/-- A divergent orbit is never periodic, so on a divergent orbit the
    size bound holds at every tail: whenever the itinerary from time
    `s` on is `ℓ`-periodic for `M` letters,
    `2^M ≤ 2^ℓ·n_s + 3^o·(n_s + 2^ℓ)` with `n_s = T^s(n)`. -/
theorem prefix_power_divergent (n : ℕ) (hdiv : ∀ B, ∃ t, B < terras_iter t n)
    (s ℓ M : ℕ) (hℓ : 1 ≤ ℓ) (hM : ℓ ≤ M)
    (h : ∀ t, t + ℓ < M →
      terras_iter (s + t) n % 2 = terras_iter (s + (t + ℓ)) n % 2) :
    2 ^ M ≤ 2 ^ ℓ * terras_iter s n +
      3 ^ oddSteps ℓ (terras_iter s n) * (terras_iter s n + 2 ^ ℓ) := by
  set m := terras_iter s n with hm
  have h' : ∀ t, t + ℓ < M → terras_iter t m % 2 = terras_iter (t + ℓ) m % 2 := by
    intro t ht
    rw [hm, terras_iter_add s t n, terras_iter_add s (t + ℓ) n]
    exact h t ht
  apply prefix_power_bound m ℓ M hM h'
  -- a periodic tail would bound the orbit
  intro hper
  -- the orbit of m is periodic with period ℓ, hence bounded by the max over one period
  have hbdd : ∀ t, terras_iter t m ≤
      ((Finset.range ℓ).image (fun i => terras_iter i m)).max'
        ⟨terras_iter 0 m, Finset.mem_image.mpr
          ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩ := by
    intro t
    have hcyc : ∀ k, terras_iter (k * ℓ) m = m := by
      intro k
      induction k with
      | zero => simp [terras_iter]
      | succ k ih =>
        rw [Nat.succ_mul, ← terras_iter_add, ih, hper]
    have : terras_iter t m = terras_iter (t % ℓ) m := by
      conv_lhs => rw [← Nat.mod_add_div t ℓ, Nat.add_comm, ← terras_iter_add,
        Nat.mul_comm, hcyc]
    rw [this]
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨t % ℓ, Finset.mem_range.mpr (Nat.mod_lt _ hℓ), rfl⟩
  obtain ⟨t, ht⟩ := hdiv (((Finset.range ℓ).image (fun i => terras_iter i m)).max'
    ⟨terras_iter 0 m, Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩ + 0)
  -- translate to the orbit of m: terras_iter (s + t') n = terras_iter t' m
  rcases Nat.lt_or_ge t s with hts | hts
  · -- t < s: bound by the max over the first s + ℓ iterates instead — handle via
    -- monotone trick: shift to time s + t which is also ≥ the bound? Not directly;
    -- use divergence again at a larger bound.
    obtain ⟨t2, ht2⟩ := hdiv (((Finset.range ℓ).image (fun i => terras_iter i m)).max'
      ⟨terras_iter 0 m, Finset.mem_image.mpr
        ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩ +
      ((Finset.range s).image (fun i => terras_iter i n)).sup id)
    rcases Nat.lt_or_ge t2 s with h2 | h2
    · have : terras_iter t2 n ≤ ((Finset.range s).image (fun i => terras_iter i n)).sup id :=
        Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨t2, Finset.mem_range.mpr h2, rfl⟩)
      omega
    · have e : terras_iter t2 n = terras_iter (t2 - s) m := by
        rw [hm, terras_iter_add]; congr 1; omega
      have := hbdd (t2 - s)
      omega
  · have e : terras_iter t n = terras_iter (t - s) m := by
      rw [hm, terras_iter_add]; congr 1; omega
    have := hbdd (t - s)
    omega

end Collatz
