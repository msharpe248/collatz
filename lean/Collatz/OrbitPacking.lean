import Collatz.Terras
import Collatz.CorrectionGrowth

/-! Finite power-saving counts for sets on which equal-time iteration is
injective. In particular this applies to every unbounded natural orbit.
The argument uses the main project's binomial tail and growth bounds. -/
namespace Collatz

private theorem card_odd_tail (k m : ℕ) :
    ((Finset.range (2^k)).filter (fun n => m ≤ oddSteps k n)).card =
      ∑ j ∈ (Finset.range (k+1)).filter (fun j => m ≤ j), k.choose j := by
  have hm : Set.MapsTo (oddSteps k)
      ((Finset.range (2^k)).filter (fun n => m ≤ oddSteps k n))
      ((Finset.range (k+1)).filter (fun j => m ≤ j)) := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨by have := oddSteps_le k n; omega, hn.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm := (Finset.mem_filter.mp hj).2
  rw [Finset.filter_filter]
  have he : (Finset.range (2^k)).filter (fun n => m ≤ oddSteps k n ∧ oddSteps k n = j) =
      (Finset.range (2^k)).filter (fun n => oddSteps k n = j) := by
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by omega, h⟩
  rw [he, card_oddSteps]

private theorem small_start_endpoint {k n : ℕ} (hn : n < 2^k) :
    terras_iter k n < 2*3^oddSteps k n := by
  have hg := terras_growth_bound k n
  have hp : 2^(k-oddSteps k n) ≤ 2^k := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have h2 : 0 < 2^k := by positivity
  have h3 : 0 < 3^oddSteps k n := by positivity
  nlinarith only [hg, hp, hn, h2, h3]

/-- A finite subset of [0,32^m) on which T^(5m) is injective has an
explicit power-saving cardinal bound. No dynamical coverage assumed. -/
theorem packing_bound {m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range (32^m))
    (hi : Set.InjOn (terras_iter (5*m)) S) :
    8^m*S.card ≤ 2*216^m+243^m := by
  classical
  let lo := S.filter (fun n => oddSteps (5*m) n < 3*m)
  let high := S.filter (fun n => 3*m ≤ oddSteps (5*m) n)
  have hpow2 : 2^(5*m) = 32^m := by rw [pow_mul]; norm_num
  have hlo : lo.card ≤ 2*27^m := by
    have hmap : Set.MapsTo (terras_iter (5*m)) lo (Finset.range (2*27^m)) := by
      intro n hn
      have hh := Finset.mem_filter.mp hn
      have hnlt : n < 2^(5*m) := by rw [hpow2]; exact Finset.mem_range.mp (hS hh.1)
      have he := small_start_endpoint hnlt
      have ho : 3^oddSteps (5*m) n ≤ 27^m := by
        calc 3^oddSteps (5*m) n ≤ 3^(3*m) := Nat.pow_le_pow_right (by decide) (by omega)
             _ = 27^m := by rw [pow_mul]; norm_num
      exact Finset.mem_range.mpr (by omega)
    simpa using Finset.card_le_card_of_injOn (terras_iter (5*m)) hmap
      (hi.mono (Finset.filter_subset _ _))
  have hhigh : 8^m*high.card ≤ 243^m := by
    have hsub : high ⊆ (Finset.range (2^(5*m))).filter (fun n => 3*m ≤ oddSteps (5*m) n) := by
      intro n hn
      have hh := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨by rw [hpow2]; exact hS hh.1, hh.2⟩
    have hb := Nat.mul_le_mul_left (2^(3*m)) (Finset.card_le_card hsub)
    rw [card_odd_tail] at hb
    have ht := choose_tail_bound (5*m) (3*m)
    have he := hb.trans ht
    simpa [pow_mul] using he
  have hc : lo.card+high.card = S.card := by
    have he := Finset.card_filter_add_card_filter_not (s := S) (p := fun n => oddSteps (5*m) n < 3*m)
    simpa [lo, high, Nat.not_lt] using he
  have h8 : 8^m*(2*27^m) = 2*216^m := by
    rw [show 216 = 8*27 by decide, mul_pow]
    ring
  calc
    8^m*S.card = 8^m*lo.card+8^m*high.card := by rw [← hc]; ring
    _ ≤ 8^m*(2*27^m)+243^m := Nat.add_le_add (Nat.mul_le_mul_left _ hlo) hhigh
    _ = 2*216^m+243^m := by rw [h8]

/-- Values on an unbounded orbit cannot coalesce under equal-time iteration. -/
theorem unbounded_orbit_coalescence_free {N : ℕ}
    (h : ∀ B, ∃ t, B < terras_iter t N) (k : ℕ) :
    Set.InjOn (terras_iter k) (Set.range (fun t => terras_iter t N)) := by
  intro a ha b hb he
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rw [terras_iter_add, terras_iter_add] at he
  have hh := unbounded_orbit_injective h he
  have hs : s = t := by omega
  rw [hs]

/-- Uniform packing bound for every finite collection of values from an
unbounded orbit, including arbitrarily late values. -/
theorem unbounded_orbit_packing {N m : ℕ} (h : ∀ B, ∃ t, B < terras_iter t N)
    {S : Finset ℕ} (hS : S ⊆ Finset.range (32^m))
    (horb : ∀ n ∈ S, ∃ t, terras_iter t N = n) :
    8^m*S.card ≤ 2*216^m+243^m :=
  packing_bound hS ((unbounded_orbit_coalescence_free h (5*m)).mono horb)

end Collatz
