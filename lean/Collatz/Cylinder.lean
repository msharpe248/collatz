import Collatz.Shadow

/-!
# Height-limited survivor cylinders

All prefix endpoints are affine functions of the same quotient. The finite
set of quotients satisfying a height bound and prefix non-descent is order
convex. No theorem here asserts eventual exhaustion for every height.
-/

namespace Collatz.Cylinder

theorem transport (k r q : ℕ) :
    terras_iter k (r + 2 ^ k * q) = terras_iter k r + 3 ^ oddSteps k r * q := by
  have hm : r + 2 ^ k * q ≡ r [MOD 2 ^ k] := by simp [Nat.ModEq]
  have ho := oddSteps_modEq k hm
  have hd := dcoef_modEq k _ _ hm
  have hA := terras_exact_form k (r + 2 ^ k * q)
  have hB := terras_exact_form k r
  rw [ho, hd] at hA
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ k)
  nlinarith

theorem prefix_transport (k r q i : ℕ) (hi : i ≤ k) :
    terras_iter i (r + 2 ^ k * q) =
      terras_iter i r + (3 ^ oddSteps i r * 2 ^ (k - i)) * q := by
  have he : r + 2 ^ k * q = r + 2 ^ i * (2 ^ (k - i) * q) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
  rw [he, transport]
  ring

def Survives (k n : ℕ) : Prop := ∀ i, i ≤ k → n ≤ terras_iter i n

instance (k n : ℕ) : Decidable (Survives k n) :=
  inferInstanceAs (Decidable (∀ i ≤ k, n ≤ terras_iter i n))

theorem survives_iff (k r q : ℕ) :
    Survives k (r + 2 ^ k * q) ↔
      ∀ i, i ≤ k → r + 2 ^ k * q ≤
        terras_iter i r + (3 ^ oddSteps i r * 2 ^ (k - i)) * q := by
  unfold Survives
  constructor <;> intro h i hi
  · simpa only [prefix_transport k r q i hi] using h i hi
  · simpa only [prefix_transport k r q i hi] using h i hi

/-- The explicit finite parameter set uses affine inequalities rather than
    reevaluating an orbit at each represented seed. -/
def parameters (k r H : ℕ) : Finset ℕ :=
  (Finset.range (H / 2 ^ k + 1)).filter fun q =>
    1 ≤ r + 2 ^ k * q ∧ r + 2 ^ k * q ≤ H ∧
      ∀ i ≤ k, r + 2 ^ k * q ≤
        terras_iter i r + (3 ^ oddSteps i r * 2 ^ (k - i)) * q

theorem mem_parameters (k r H q : ℕ) :
    q ∈ parameters k r H ↔
      1 ≤ r + 2 ^ k * q ∧ r + 2 ^ k * q ≤ H ∧ Survives k (r + 2 ^ k * q) := by
  simp only [parameters, Finset.mem_filter, Finset.mem_range, survives_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hmul : q * 2 ^ k ≤ H := by nlinarith [h.2.1]
    have := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).mpr hmul
    omega

/-- Every quotient between two survivors in the same cylinder survives.
    Together with `mem_parameters`, this is an exact interval characterization. -/
theorem parameters_convex {k r H a b q : ℕ}
    (ha : a ∈ parameters k r H) (hb : b ∈ parameters k r H)
    (haq : a ≤ q) (hqb : q ≤ b) : q ∈ parameters k r H := by
  rw [mem_parameters] at ha hb ⊢
  refine ⟨?_, ?_, ?_⟩
  · exact ha.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ haq) r)
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ hqb) r).trans hb.2.1
  · rw [survives_iff] at ha hb ⊢
    intro i hi
    have hia := ha.2.2 i hi
    have hib := hb.2.2 i hi
    rcases le_total (2 ^ k) (3 ^ oddSteps i r * 2 ^ (k - i)) with hc | hc
    · nlinarith
    · nlinarith

/-- Once the cylinder modulus exceeds the height, its only possible quotient
    is zero. This makes the ordinary-integer boundary explicit. -/
theorem quotient_zero_of_height {k r H q : ℕ}
    (hH : H < 2 ^ k) (hq : q ∈ parameters k r H) : q = 0 := by
  have h := (mem_parameters k r H q).mp hq
  by_contra hn
  have : 1 ≤ q := by omega
  nlinarith [h.2.1]

end Collatz.Cylinder
