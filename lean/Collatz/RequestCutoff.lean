import Collatz.BoundedTransfer

namespace Collatz.RequestCutoff

/-- Largest natural at most B in residue r modulo four, or zero if none exists. -/
def top (B r : ℕ) : ℕ := if r ≤ B then r+4*((B-r)/4) else 0

private theorem le_top {m B r : ℕ} (hm : m ≤ B) (hr : m%4 = r) :
    m ≤ top B r := by
  have hd := Nat.mod_add_div m 4
  have hb := Nat.mod_add_div (B-r) 4
  unfold top
  split_ifs <;> omega

/-- Only two residue maxima per possible odd-run length need checking. -/
def Check (U N L : ℕ) : Prop :=
  ∀ a : Fin L, ∀ r : Fin 4, 2 ≤ a.val → (r.val = 1 ∨ r.val = 3) →
    (3^a.val*r.val)%4 = 3 → 3^a.val * top (N/2^a.val) r.val < 36*U+27

instance (U N L : ℕ) : Decidable (Check U N L) := by
  unfold Check
  infer_instance

/-- Soundness of the finite cutoff certificate for every odd-run request. -/
theorem sound {U N L : ℕ} (hN : N < 2^L) (hc : Check U N L)
    {a m v : ℕ} (ha : 2 ≤ a) (hm : 0 < m) (hodd : m%2 = 1)
    (hsize : 2^a*m ≤ N) (hv : 36*v+27 = 3^a*m) : v < U := by
  have haL : a < L := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show L ≤ a by omega)
    have hp' : 2^a ≤ N := by nlinarith [Nat.one_le_pow a 2 (by decide)]
    omega
  have hmB : m ≤ N/2^a :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 2^a)).mpr (by simpa [Nat.mul_comm] using hsize)
  have hr : m%4 = 1 ∨ m%4 = 3 := by omega
  have hrprod : (3^a*(m%4))%4 = 3 := by
    have hp : (3^a*m)%4 = 3 := by omega
    simpa only [Nat.mul_mod, Nat.mod_mod] using hp
  have hmax := hc ⟨a, haL⟩ ⟨m%4, Nat.mod_lt _ (by omega)⟩ ha hr hrprod
  change 3^a * top (N/2^a) (m%4) < 36*U+27 at hmax
  have hle := Nat.mul_le_mul_left (3^a) (le_top hmB rfl)
  omega

/-- Certified cutoffs supply convergence from smaller transfer premises. -/
theorem reachesOne {U N L n : ℕ} (hN : N < 2^L) (hc : Check U N L)
    (hrec : ∀ v : ℕ, v < U → AffineTransfer v)
    (hn : 0 < n) (hbound : n < N) : ReachesOne n := by
  apply reachesOne_below_of_odd_run_requests N _ n hn hbound
  intro a m v ha hm hodd hsize hv
  exact hrec v (sound hN hc ha hm hodd hsize hv)

/-- A concrete optimized cutoff, checked without enumerating all seed values. -/
theorem check_61 : Check 61 415 9 := by decide

/-- A large-parameter cutoff certificate uses only 45 possible run lengths. -/
theorem check_mersenne64 : Check 18446744073709551615 30786325577727 45 := by decide

/-- Seed 415 requests parameter 87, preventing any larger cutoff in this schema. -/
theorem maximal_61 {N L : ℕ} (hN : 416 ≤ N) (hL : N < 2^L) :
    ¬ Check 61 N L := by
  intro hc
  have hv := sound hL hc (a := 5) (m := 13) (v := 87)
    (by decide) (by decide) (by decide) (by norm_num; omega) (by decide)
  omega

/-- The large certificate is also maximal for the odd-run request schema. -/
theorem maximal_mersenne64 {N L : ℕ} (hN : 30786325577728 ≤ N)
    (hL : N < 2^L) : ¬ Check 18446744073709551615 N L := by
  intro hc
  have hv := sound hL hc (a := 42) (m := 7) (v := 21275914553349625401)
    (by decide) (by decide) (by decide) (by norm_num; omega) (by norm_num)
  omega

end Collatz.RequestCutoff

namespace Collatz

/-- Any sound request-cutoff certificate can replace the dyadic descent threshold. -/
theorem AffineTransfer.of_request_cutoff_descent {u N L t : ℕ}
    (hN : N < 2^L) (hc : RequestCutoff.Check u N L)
    (hrec : ∀ v : ℕ, v < u → AffineTransfer v)
    (hdescent : terras_iter t (27*u+20) < N) : AffineTransfer u := by
  intro _
  apply (ReachesOne.shift_iff (27*u+20) t).mp
  exact RequestCutoff.reachesOne hN hc hrec
    (terras_iter_pos t (27*u+20) (by omega)) hdescent

end Collatz
