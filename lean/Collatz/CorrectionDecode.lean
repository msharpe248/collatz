import Collatz.WordCongruence

/-! Exact correction attainability by deterministic reconstruction.
The final equality checks are essential: subtraction in the decoder is truncated.
No uniform bound on accepted lengths is asserted. -/
namespace Collatz.WordAffine

/-- The correction's low bit determines the first parity. Invalid inputs still
produce a word; `CorrectionAttainable` checks its exact reconstructed data. -/
def decodeCorrection : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | h+1, k, D =>
    if D % 2 = 0 then false :: decodeCorrection h k (D/2)
    else true :: decodeCorrection h (k-1) ((D-3^(k-1))/2)

@[simp] theorem decodeCorrection_length (h k D : ℕ) :
    (decodeCorrection h k D).length = h := by
  induction h generalizing k D with
  | zero => rfl
  | succ h ih => simp [decodeCorrection]; split <;> simp [ih]

/-- Reconstruction recovers every actual word exactly. -/
theorem decodeCorrection_correct (w : List Bool) :
    decodeCorrection w.length (ones w) (correction w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have h3 : 3^ones w % 2 = 1 := by simp [Nat.pow_mod]
    cases b <;> simp [ones, correction, decodeCorrection, Nat.add_mod,
      h3, ih]

/-- Acceptance means the reconstructed word has exactly the requested odd
count and correction, not merely the same residue or a bounded correction. -/
def CorrectionAttainable (h k D : ℕ) : Prop :=
    ones (decodeCorrection h k D) = k ∧ correction (decodeCorrection h k D) = D

instance (h k D : ℕ) : Decidable (CorrectionAttainable h k D) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem correctionAttainable_iff (h k D : ℕ) :
    CorrectionAttainable h k D ↔
      ∃ w : List Bool, w.length = h ∧ ones w = k ∧ correction w = D := by
  constructor
  · intro ha
    exact ⟨decodeCorrection h k D, decodeCorrection_length h k D, ha⟩
  · rintro ⟨w, rfl, rfl, rfl⟩
    simp [CorrectionAttainable, decodeCorrection_correct]

/-- At fixed length and odd count, the correction identifies at most one word. -/
theorem correction_injective {u v : List Bool} (hl : u.length = v.length)
    (hk : ones u = ones v) (hd : correction u = correction v) : u = v := by
  rw [← decodeCorrection_correct u, hl, hk, hd, decodeCorrection_correct]

/-- Adding exact attainability turns the numerical test into an actual
paradoxical word. This is an equivalence, not an all-length exclusion. -/
theorem attainable_paradoxical_iff (h k D n : ℕ) :
    (CorrectionAttainable h k D ∧ 0 < n ∧ 3^k < 2^h ∧
      2^h ∣ 3^k*n+D ∧ (2^h-3^k)*n ≤ D) ↔
    ∃ w : List Bool, w.length = h ∧ ones w = k ∧ correction w = D ∧
      Realizes n w ∧ IsParadoxical h n := by
  constructor
  · rintro ⟨ha, hp, hc, hd, hb⟩
    obtain ⟨w, rfl, rfl, rfl⟩ := (correctionAttainable_iff h k D).mp ha
    exact ⟨w, rfl, rfl, rfl, (realizes_paradoxical_iff n w).mpr ⟨hp, hc, hd, hb⟩⟩
  · rintro ⟨w, rfl, rfl, rfl, hr, hp⟩
    exact ⟨(correctionAttainable_iff _ _ _).mpr ⟨w, rfl, rfl, rfl⟩,
      (realizes_paradoxical_iff n w).mp ⟨hr, hp⟩⟩

-- Kernel-checked controls: a genuine length-eight correction and the
-- artificial closing correction from the preceding limitation theorem.
example : CorrectionAttainable 8 5 347 := by decide
example : ¬ CorrectionAttainable 16 6 194421 := by decide

end Collatz.WordAffine
