import Collatz.Sturmian

/-! An endpoint reduction for the quantitative hypothesis of `sturmian_level`.
The rotation separation and coverage hypotheses remain explicit. -/

namespace Collatz

private theorem geometric_endpoint {a C : ℝ} {f : ℕ → ℝ} {K G : ℕ}
    (ha : 2 ≤ a) (hC : 0 ≤ C) (hf : ∀ s, 0 ≤ f s) (hmono : Monotone f)
    (hG : C * a ^ G * f G < (2 : ℝ) ^ (K + G))
    {s : ℕ} (hs : s ≤ G) : C * a ^ s * f s < (2 : ℝ) ^ (K + s) := by
  have ha0 : 0 ≤ a := by linarith
  have hpow : (2 : ℝ) ^ (G - s) ≤ a ^ (G - s) :=
    pow_le_pow_left₀ (by norm_num) ha _
  have hfs : f s ≤ f G := hmono hs
  have hfs0 := hf s
  have hprod : C * a ^ s * f s * (2 : ℝ) ^ (G - s) ≤ C * a ^ G * f G := by
    calc C * a ^ s * f s * (2 : ℝ) ^ (G - s)
        ≤ C * a ^ s * f s * a ^ (G - s) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = C * (a ^ s * a ^ (G - s)) * f s := by ring
      _ = C * a ^ G * f s := by rw [← pow_add, Nat.add_sub_of_le hs]
      _ ≤ C * a ^ G * f G := mul_le_mul_of_nonneg_left hfs (by positivity)
  have hlt := lt_of_le_of_lt hprod hG
  have he : (2 : ℝ) ^ (K + G) = 2 ^ (K + s) * 2 ^ (G - s) := by
    rw [← pow_add]
    congr 1
    omega
  rw [he] at hlt
  exact lt_of_mul_lt_mul_right hlt (by positivity)

/-- Above the critical line, checking the size inequality at `s = G`
    suffices for every earlier `s`. No continued-fraction facts are assumed. -/
theorem sturmian_size_at_endpoint {α : ℝ} {q Q G N : ℕ}
    (hcrit : (2 : ℝ) ≤ (3 : ℝ) ^ α)
    (hG : (3 : ℝ) ^ (((q + G : ℕ) : ℝ) * α + 1) * (3 * N + 3 * G + 1) <
      (2 : ℝ) ^ (Q - 3 + G)) :
    ∀ s : ℕ, s ≤ G →
      (3 : ℝ) ^ (((q + s : ℕ) : ℝ) * α + 1) * (3 * N + 3 * s + 1) <
        (2 : ℝ) ^ (Q - 3 + s) := by
  have expand (s : ℕ) : (3 : ℝ) ^ (((q + s : ℕ) : ℝ) * α + 1) =
      (3 : ℝ) ^ ((q : ℝ) * α + 1) * ((3 : ℝ) ^ α) ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  rw [expand G] at hG
  intro s hs
  rw [expand s]
  apply geometric_endpoint (f := fun t : ℕ => 3 * (N : ℝ) + 3 * (t : ℝ) + 1) hcrit
      (by positivity) (by intro t; positivity) _ hG hs
  intro i j hij
  dsimp
  exact_mod_cast (show 3 * N + 3 * i + 1 ≤ 3 * N + 3 * j + 1 by omega)

theorem sturmian_level_endpoint {α ρ δ : ℝ} {q Q G : ℕ} {p : ℤ}
    (hα0 : 0 ≤ α) (hcrit : (2 : ℝ) ≤ (3 : ℝ) ^ α)
    (hq : (q : ℝ) * α = p + δ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hQ : 3 ≤ Q)
    (hL : ∀ m : ℕ, 0 < m → m < Q → ∀ r : ℤ, δ ≤ |(m : ℝ) * α - r|)
    (hT : ∀ a : ℕ, ∃ n, a ≤ n ∧ n < a + G ∧ visit α ρ δ n)
    (N : ℕ)
    (hG : (3 : ℝ) ^ (((q + G : ℕ) : ℝ) * α + 1) * (3 * N + 3 * G + 1) <
      (2 : ℝ) ^ (Q - 3 + G)) : ¬ HasItin α ρ N :=
  sturmian_level hα0 hcrit hq hδ0 hδ1 hQ hL hT N
    (sturmian_size_at_endpoint hcrit hG)

end Collatz
