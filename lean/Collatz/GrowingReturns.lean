import Collatz.ResidueCoverage
import Collatz.Cylinder

/-! Arbitrarily long finite strings of growing residue-nine returns.
The seed depends on the requested length; no infinite escaping seed is
constructed. -/
namespace Collatz

private theorem block {n : ℕ} (hn : n % 16 = 11) :
    16 * terras_iter 4 n = 27*n+23 ∧ oddSteps 4 n = 3 := by
  have he : n = 11 + 16*(n/16) := by have := Nat.mod_add_div n 16; omega
  have hm : n ≡ 11 [MOD 2^4] := by simpa [Nat.ModEq] using hn
  have ho := oddSteps_modEq 4 hm
  have ht := Cylinder.transport 4 11 (n/16)
  norm_num only [show terras_iter 4 11 = 20 from rfl,
    show oddSteps 4 11 = 3 from rfl, Nat.reducePow] at ho ht
  constructor
  · rw [← he] at ht
    omega
  · exact ho

private theorem block_mod_nine {n : ℕ} (hn : n % 16 = 11) (hr : n % 9 = 2) :
    terras_iter 1 n % 9 = 8 ∧ terras_iter 2 n % 9 = 8 ∧
    terras_iter 3 n % 9 = 4 ∧ terras_iter 4 n % 9 = 2 := by
  have he : n = 11 + 16*(n/16) := by have := Nat.mod_add_div n 16; omega
  have hq : n/16 % 9 = 0 := by omega
  have h1 := Cylinder.prefix_transport 4 11 (n/16) 1 (by omega)
  have h2 := Cylinder.prefix_transport 4 11 (n/16) 2 (by omega)
  have h3 := Cylinder.prefix_transport 4 11 (n/16) 3 (by omega)
  have h4 := Cylinder.transport 4 11 (n/16)
  norm_num only [show terras_iter 1 11 = 17 from rfl,
    show terras_iter 2 11 = 26 from rfl, show terras_iter 3 11 = 13 from rfl,
    show terras_iter 4 11 = 20 from rfl, show oddSteps 1 11 = 1 from rfl,
    show oddSteps 2 11 = 2 from rfl, show oddSteps 3 11 = 2 from rfl,
    show oddSteps 4 11 = 3 from rfl, Nat.reducePow, Nat.reduceMul,
    Nat.reduceSub] at h1 h2 h3 h4
  rw [← he] at h1 h2 h3 h4
  omega

private theorem block_division {R n : ℕ} (hd : 16^(R+1) ∣ 11*n+23) :
    n % 16 = 11 ∧ 16^R ∣ 11*terras_iter 4 n+23 := by
  obtain ⟨c, hc⟩ := hd
  rw [pow_succ] at hc
  have he : 11*n+23 = 16*(16^R*c) := by nlinarith only [hc]
  have hn : n % 16 = 11 := by omega
  have hb := (block hn).1
  refine ⟨hn, ⟨27*c, ?_⟩⟩
  nlinarith only [he, hb]

/-- An explicit positive seed for each prescribed number of growing returns. -/
def growingReturnSeed : ℕ → ℕ
  | 0 => 2
  | R+1 => 144*growingReturnSeed R+299

private theorem seed_identity (R : ℕ) :
    11*growingReturnSeed R+23 = 45*144^R := by
  induction R with
  | zero => norm_num [growingReturnSeed]
  | succ R ih => simp only [growingReturnSeed, pow_succ]; nlinarith only [ih]

private theorem seed_residue (R : ℕ) : growingReturnSeed R % 9 = 2 := by
  induction R with
  | zero => norm_num [growingReturnSeed]
  | succ R ih => simp only [growingReturnSeed]; omega

private theorem seed_divisibility (R : ℕ) : 16^R ∣ 11*growingReturnSeed R+23 := by
  rw [seed_identity]
  refine ⟨45*9^R, ?_⟩
  rw [show (144:ℕ) = 16*9 by decide, mul_pow]
  ring

private theorem repeated_blocks (R : ℕ) : ∀ n, 16^R ∣ 11*n+23 → n % 9 = 2 →
    oddSteps (4*R) n = 3*R ∧
    ∀ i < R, terras_iter (4*i) n < terras_iter (4*(i+1)) n ∧
      terras_iter (4*i) n % 9 = 2 ∧
      terras_iter (4*i+1) n % 9 = 8 ∧
      terras_iter (4*i+2) n % 9 = 8 ∧
      terras_iter (4*i+3) n % 9 = 4 := by
  induction R with
  | zero => intro n hd hr; simp
  | succ R ih =>
    intro n hd hr
    obtain ⟨hn, hdnext⟩ := block_division hd
    have hb := block hn
    have hm := block_mod_nine hn hr
    obtain ⟨hc, hs⟩ := ih (terras_iter 4 n) hdnext hm.2.2.2
    constructor
    · rw [show 4*(R+1) = 4+4*R by omega, oddSteps_add, hb.2, hc]
      omega
    · intro i hi
      cases i with
      | zero =>
        change n < terras_iter 4 n ∧ n % 9 = 2 ∧
          terras_iter 1 n % 9 = 8 ∧ terras_iter 2 n % 9 = 8 ∧ terras_iter 3 n % 9 = 4
        exact ⟨by omega, hr, hm.1, hm.2.1, hm.2.2.1⟩
      | succ i =>
        have hh := hs i (by omega)
        simpa only [terras_iter_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hh

private theorem repeated_endpoint (R : ℕ) : ∀ n, 16^R ∣ 11*n+23 → n % 9 = 2 →
    terras_iter (4*R) n % 9 = 2 := by
  induction R with
  | zero => intro n hd hr; exact hr
  | succ R ih =>
    intro n hd hr
    obtain ⟨hn, hnext⟩ := block_division hd
    have hh := ih (terras_iter 4 n) hnext (block_mod_nine hn hr).2.2.2
    simpa only [terras_iter_add, Nat.mul_add, Nat.mul_one,
      Nat.add_comm] using hh

/-- Every prescribed finite number of first returns can all grow.
Intermediate residues show these are consecutive visits, not selected ones. -/
theorem arbitrarily_many_growing_returns (R : ℕ) :
    ∃ n, 0 < n ∧ n % 9 = 2 ∧ terras_iter (4*R) n % 9 = 2 ∧
      oddSteps (4*R) n = 3*R ∧
      ∀ i < R, terras_iter (4*i) n < terras_iter (4*(i+1)) n ∧
        terras_iter (4*i) n % 9 = 2 ∧
        terras_iter (4*i+1) n % 9 = 8 ∧
        terras_iter (4*i+2) n % 9 = 8 ∧
        terras_iter (4*i+3) n % 9 = 4 := by
  have hr := seed_residue R
  have hp : 0 < growingReturnSeed R := by omega
  obtain ⟨hc, hs⟩ := repeated_blocks R (growingReturnSeed R) (seed_divisibility R) hr
  exact ⟨growingReturnSeed R, hp, hr,
    repeated_endpoint R _ (seed_divisibility R) hr, hc, hs⟩

/-- Switching the fixed growing branches 1101 then 101 can recharge an
arbitrarily large power of two despite a fixed incoming valuation five.
The congruences specify the actual branch domains. -/
theorem unbounded_reserve_reset (r : ℕ) (hr : 1 ≤ r) :
    ∃ n, n % 144 = 11 ∧ terras_iter 4 n % 72 = 65 ∧
      (11*n+23) % 64 = 32 ∧ terras_iter 4 n+7 = 27*64^r := by
  have ha : 64^r % 72 = 64 := by
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ r hr ih => simp [pow_succ, Nat.mul_mod, ih]
  let n := 16*64^r-5
  have hn : n % 144 = 11 := by dsimp [n]; omega
  have hn16 : n % 16 = 11 := by omega
  have hb := (block hn16).1
  have heN : n+5 = 16*64^r := by dsimp [n]; omega
  have he : terras_iter 4 n+7 = 27*64^r := by omega
  refine ⟨n, hn, ?_, ?_, he⟩
  · omega
  · dsimp [n]; omega

end Collatz
