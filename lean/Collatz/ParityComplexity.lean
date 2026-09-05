import Collatz.CorrectionGrowth
import Collatz.DefectHeight

/-! Factor complexity of actual parity itineraries. Equal long factors force
state congruence; the universal height bound makes early factors distinct
on an unbounded orbit. No universal complexity upper bound is assumed. -/
namespace Collatz.ParityComplexity

/-- A length-L parity factor starting at time t. -/
def block (N L t : ℕ) : Fin L → Fin 2 := fun i =>
  ⟨terras_iter (t+i) N % 2, Nat.mod_lt _ (by decide)⟩

noncomputable def factors (N L : ℕ) : Finset (Fin L → Fin 2) := by
  classical
  exact Finset.univ.filter (fun w => ∃ t, block N L t = w)

noncomputable def complexity (N L : ℕ) : ℕ := (factors N L).card

theorem block_mem (N L t : ℕ) : block N L t ∈ factors N L := by
  classical
  simp only [factors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨t, rfl⟩

theorem block_shift (N L t : ℕ) : block N L t = block (terras_iter t N) L 0 := by
  funext i
  apply Fin.ext
  simp [block, terras_iter_add]

/-- Bounded state values give a uniform bound on factor complexity. -/
theorem complexity_le_of_bounded {N B : ℕ} (hB : ∀ t, terras_iter t N ≤ B) (L : ℕ) :
    complexity N L ≤ B+1 := by
  classical
  have hs : factors N L ⊆ (Finset.range (B+1)).image (fun n => block n L 0) := by
    intro w hw
    obtain ⟨t, rfl⟩ := (Finset.mem_filter.mp hw).2
    exact Finset.mem_image.mpr ⟨terras_iter t N, Finset.mem_range.mpr (by have := hB t; omega),
      (block_shift N L t).symm⟩
  exact (Finset.card_le_card hs).trans (by simpa using (Finset.card_image_le (s := Finset.range (B+1)) (f := fun n => block n L 0)))

/-- Early factors cannot repeat on an unbounded orbit when their states
are below the parity modulus. -/
theorem factor_floor_of_injective_prefix {N K q : ℕ} (hN : N+1 ≤ 2^K)
    (hstate : Set.InjOn (fun t => terras_iter t N) (Finset.range (5*q+1))) :
    5*q+1 ≤ complexity N (3*q+K) := by
  classical
  let L := 3*q+K
  have height (t : ℕ) (ht : t < 5*q+1) : terras_iter t N < 2^L := by
    have hh := ParityDefects.height_from_growthBits N K hN t
    have hg := ParityDefects.growthBits_mono (show t ≤ 5*q by omega)
    have he : ParityDefects.growthBits (5*q) = 3*q := by
      unfold ParityDefects.growthBits
      omega
    rw [he] at hg
    exact hh.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by dsimp [L]; omega))
  have hi : Set.InjOn (block N L) (Finset.range (5*q+1)) := by
    intro a ha b hb hab
    have hmod : terras_iter a N ≡ terras_iter b N [MOD 2^L] := by
      apply modEq_of_parity
      intro i hi
      have hh := congrArg Fin.val (congrFun hab ⟨i, hi⟩)
      simpa only [block, terras_iter_add] using hh
    have he : terras_iter a N = terras_iter b N := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (height a (Finset.mem_range.mp ha)),
        Nat.mod_eq_of_lt (height b (Finset.mem_range.mp hb))] using hmod
    exact hstate ha hb he
  have hs : (Finset.range (5*q+1)).image (block N L) ⊆ factors N L := by
    intro w hw
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
    exact block_mem N L t
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn hi, Finset.card_range] at hc
  exact hc

/-- Uniform finite-scale complexity floor on every unbounded orbit. -/
theorem unbounded_factor_floor {N K : ℕ} (hN : N+1 ≤ 2^K)
    (h : ∀ B, ∃ t, B < terras_iter t N) (q : ℕ) :
    5*q+1 ≤ complexity N (3*q+K) :=
  factor_floor_of_injective_prefix hN (unbounded_orbit_injective h).injOn

/-- A uniform linear complexity envelope of slope below 5/3 forces
boundedness. No such envelope is asserted for all parity itineraries. -/
theorem bounded_of_linear_complexity {N A B C : ℕ} (hab : 3*B < 5*A)
    (hc : ∀ L, A*complexity N L ≤ B*L+C) :
    ∃ H, ∀ t, terras_iter t N ≤ H := by
  by_contra hh
  push_neg at hh
  let K := N+1
  let q := B*K+C+1
  have hN : N+1 ≤ 2^K := (Nat.lt_two_pow_self : N+1 < 2^(N+1)).le
  have hf := Nat.mul_le_mul_left A (unbounded_factor_floor hN hh q)
  have hu := hc (3*q+K)
  have hg : 3*B+1 ≤ 5*A := by omega
  have hm := Nat.mul_le_mul_right q hg
  have hq : B*K+C < q := by dsimp [q]; omega
  nlinarith

/-- An additive-linear factor bound forces boundedness, without a density
or summability assumption. It does not identify the eventual cycle. -/
theorem bounded_of_additive_linear_complexity {N C : ℕ}
    (hc : ∀ L, complexity N L ≤ L+C) : ∃ B, ∀ t, terras_iter t N ≤ B := by
  by_contra hh
  push_neg at hh
  have hN : N+1 ≤ 2^(N+1) := (Nat.lt_two_pow_self : N+1 < 2^(N+1)).le
  have hf := unbounded_factor_floor hN hh (N+C+2)
  have hu := hc (3*(N+C+2)+(N+1))
  omega

/-- No natural seed has a Sturmian parity itinerary in the standard
factor-complexity definition. Applying this to a shifted seed also excludes
eventually Sturmian tails. No mechanical-word equivalence is imported. -/
theorem no_sturmian_complexity (N : ℕ) :
    ¬ (∀ L, complexity N L = L+1) := by
  intro hc
  obtain ⟨B, hB⟩ := bounded_of_additive_linear_complexity (C := 1)
    (fun L => (hc L).le)
  have hb := complexity_le_of_bounded hB (B+1)
  rw [hc] at hb
  omega

end Collatz.ParityComplexity
