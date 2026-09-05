import Collatz.PruningLimit
import Collatz.WordCongruence

/-! A correction interval plus endpoint integrality still forgets which
corrections are attained by parity words. This theorem constructs artificial
corrections, never actual return trajectories. -/
namespace Collatz.WordAffine

/-- Every fixed realized prefix admits a fictitious closing correction in the
suffix envelope at every sufficiently large target length. -/
theorem relaxed_closing_correction (s a D n v L : ℕ)
    (hn : 0 < n) (hp : 2^s*v = 3^a*n+D)
    (hL : s+2*(a+2*n)+v+1 ≤ L) :
    ∃ k d, k ≤ L-s ∧ 3^(a+k) < 2^L ∧
      d ≤ 2^(L-s-k)*(3^k-2^k) ∧
      3^(a+k)*n + (3^k*D+2^s*d) = 2^L*n := by
  let k := 2*n
  have hk : k ≤ L-s := by dsimp [k]; omega
  have hpow : 3^(a+k) < 2^L := by
    have hb : 3^(a+k) ≤ (2^2)^(a+k) := Nat.pow_le_pow_left (by norm_num) _
    rw [← pow_mul] at hb
    exact hb.trans_lt (Nat.pow_lt_pow_right (by omega : 1 < 2) (by dsimp [k]; omega))
  have hv : v ≤ 2^v := (Nat.lt_two_pow_self).le
  have hsmall : 3^k*v ≤ 2^(L-s)*n := by
    have h3 : 3^k ≤ (2^2)^k := Nat.pow_le_pow_left (by norm_num) _
    have hb := Nat.mul_le_mul h3 hv
    rw [← pow_mul, ← pow_add] at hb
    have he : 2^(2*k+v) ≤ 2^(L-s) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) (by dsimp [k]; omega)
    exact hb.trans (he.trans (Nat.le_mul_of_pos_right _ hn))
  have hbudget := enough_odd_budget n
  have hmass : n*2^k ≤ 3^k-2^k := by
    have hh : 2^k ≤ 3^k := Nat.pow_le_pow_left (by omega) _
    have hs := Nat.sub_add_cancel hh
    dsimp [k] at *
    nlinarith
  have hupper : 2^(L-s)*n ≤ 2^(L-s-k)*(3^k-2^k) := by
    have hm := Nat.mul_le_mul_left (2^(L-s-k)) hmass
    have he : 2^(L-s-k)*2^k = 2^(L-s) := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    calc 2^(L-s)*n = 2^(L-s-k)*(n*2^k) := by rw [← he]; ring
         _ ≤ _ := hm
  refine ⟨k, 2^(L-s)*n-3^k*v, hk, hpow,
    (Nat.sub_le _ _).trans hupper, ?_⟩
  have hd := Nat.sub_add_cancel hsmall
  have he : 2^s*2^(L-s) = 2^L := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : s ≤ L)]
  have hmul := congrArg (fun x => 3^k*x) hp
  have hd' := congrArg (fun x => 2^s*x) hd
  rw [pow_add]
  nlinarith

end Collatz.WordAffine
