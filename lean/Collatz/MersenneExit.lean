import Collatz.EarlyInverseBridge

set_option exponentiation.threshold 2048

namespace Collatz

/-- A uniform merge for the power parameter at the end of a Mersenne prefix. -/
theorem mersenne_exit_merge (Q : ℕ) :
    terras_iter 12 (2988 + 4096*Q) =
      terras_iter 12 (8975 + 12288*Q) := by
  have hx := Cylinder.transport 12 2988 Q
  have hy := Cylinder.transport 12 8975 (3*Q)
  simp only [show terras_iter 12 2988 = 533 from rfl,
    show oddSteps 12 2988 = 6 from rfl] at hx
  simp only [show terras_iter 12 8975 = 533 from rfl,
    show oddSteps 12 8975 = 5 from rfl] at hy
  have ex : 2988 + 4096*Q = 2988 + 2^12*Q := by ring
  have ey : 8975 + 12288*Q = 8975 + 2^12*(3*Q) := by ring
  rw [ex, ey, hx, hy]
  ring

private theorem shadow_seven (q : ℕ) (hq : 1 ≤ q) :
    terras_iter 3 (8*q-7) = 9*q-7 := by
  have h1 := two_mul_terras_odd (8*q-7) (by omega)
  have h2 := two_mul_terras_even (terras (8*q-7)) (by omega)
  have h3 := two_mul_terras_odd (terras (terras (8*q-7))) (by omega)
  change terras (terras (terras (8*q-7))) = 9*q-7
  omega

private theorem shadow_ten (q : ℕ) (hq : 2 ≤ q) :
    terras_iter 3 (8*q-10) = 9*q-10 := by
  have h1 := two_mul_terras_even (8*q-10) (by omega)
  have h2 := two_mul_terras_odd (terras (8*q-10)) (by omega)
  have h3 := two_mul_terras_odd (terras (terras (8*q-10))) (by omega)
  change terras (terras (terras (8*q-10))) = 9*q-10
  omega

private theorem shadow_iter (h a : ℕ) (ha : 2 ≤ a) :
    terras_iter (3*h) (8^h*a-7) = 9^h*a-7 ∧
    terras_iter (3*h) (8^h*a-10) = 9^h*a-10 := by
  induction h generalizing a with
  | zero => simp [terras_iter]
  | succ h ih =>
    have hpow : 1 ≤ 8^h := Nat.one_le_pow _ _ (by decide)
    have hq : 2 ≤ 8^h*a := by nlinarith
    have hi := ih (9*a) (by omega)
    have he : 8^(h+1)*a = 8*(8^h*a) := by ring
    have ht : 3*(h+1) = 3+3*h := by omega
    rw [ht, ← terras_iter_add, ← terras_iter_add, he,
      shadow_seven _ (by omega), shadow_ten _ hq]
    have hn : 9*(8^h*a) = 8^h*(9*a) := by ring
    rw [hn, hi.1, hi.2]
    constructor <;> congr 1 <;> ring

/-- Exact endpoints after the growing Mersenne prefix; no convergence premise. -/
theorem mersenne_inverse_exit (h : ℕ) :
    terras_iter (6*h+4) (27*2^(6*h+4)-14) = 3^(4*h+5)-7 ∧
    terras_iter (6*h+4) (27*2^(6*h+4)-7) = 3^(4*h+6)-10 := by
  let N := 8^(2*h)
  have hN : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
  have hp : 2^(6*h+4) = 16*N := by
    dsimp [N]
    calc
      2^(6*h+4) = 2^4 * (2^3)^(2*h) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ = 16 * 8^(2*h) := by norm_num
  have hx := Cylinder.transport 4 418 (27*(N-1))
  have hy := Cylinder.transport 4 425 (27*(N-1))
  simp only [show terras_iter 4 418 = 236 from rfl,
    show oddSteps 4 418 = 2 from rfl] at hx
  simp only [show terras_iter 4 425 = 719 from rfl,
    show oddSteps 4 425 = 3 from rfl] at hy
  have ex : 27*2^(6*h+4)-14 = 418+2^4*(27*(N-1)) := by rw [hp]; omega
  have ey : 27*2^(6*h+4)-7 = 425+2^4*(27*(N-1)) := by rw [hp]; omega
  have sx : terras_iter 4 (27*2^(6*h+4)-14) = N*243-7 := by rw [ex, hx]; omega
  have sy : terras_iter 4 (27*2^(6*h+4)-7) = N*729-10 := by rw [ey, hy]; omega
  have ha := (shadow_iter (2*h) 243 (by norm_num)).1
  have hb := (shadow_iter (2*h) 729 (by norm_num)).2
  have ht : 6*h+4 = 4+3*(2*h) := by omega
  have pa : 9^(2*h)*243 = 3^(4*h+5) := by
    calc
      9^(2*h)*243 = (3^2)^(2*h)*3^5 := by norm_num
      _ = 3^(4*h+5) := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have pb : 9^(2*h)*729 = 3^(4*h+6) := by
    calc
      9^(2*h)*729 = (3^2)^(2*h)*3^6 := by norm_num
      _ = 3^(4*h+6) := by rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [ht] at sx sy
  rw [ht, ← terras_iter_add, ← terras_iter_add, sx, sy]
  exact ⟨ha.trans (congrArg (fun n => n-7) pa), hb.trans (congrArg (fun n => n-10) pb)⟩

/-- Infinitely many Mersenne exponents admit a merge after their growing prefix. -/
theorem mersenne_inverse_exit_progression (z : ℕ) :
    terras_iter (1480+1536*z) (27*2^(1468+1536*z)-14) =
    terras_iter (1480+1536*z) (27*2^(1468+1536*z)-7) := by
  have hs : (3:ℕ)^981 ≡ 2995 [MOD 4096] := by norm_num [Nat.ModEq]
  have hp : (3:ℕ)^1024 ≡ 1 [MOD 4096] := by norm_num [Nat.ModEq]
  have hm := hs.mul (hp.pow z)
  have he : 3^981 * (3^1024)^z = (3:ℕ)^(981+1024*z) := by rw [pow_add, pow_mul]
  rw [he, one_pow, mul_one] at hm
  have hmod : (3:ℕ)^(981+1024*z) % 4096 = 2995 := hm
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, (3:ℕ)^(981+1024*z) = 2995+4096*Q := by
    refine ⟨(3:ℕ)^(981+1024*z) / 4096, ?_⟩
    have hd := Nat.mod_add_div ((3:ℕ)^(981+1024*z)) 4096
    rw [hmod] at hd
    exact hd.symm
  clear hs hp hm hmod he
  obtain ⟨hx, hy⟩ := mersenne_inverse_exit (244+256*z)
  have hk : 6*(244+256*z)+4 = 1468+1536*z := by ring
  have ha : 4*(244+256*z)+5 = 981+1024*z := by ring
  have hb : 4*(244+256*z)+6 = (981+1024*z)+1 := by ring
  simp only [hk, ha, hQ] at hx
  have hnext : (3:ℕ)^(4*(244+256*z)+6) = (2995+4096*Q)*3 := by
    calc
      _ = (3:ℕ)^((981+1024*z)+1) := congrArg (fun e => (3:ℕ)^e) hb
      _ = (3:ℕ)^(981+1024*z)*3 := pow_succ _ _
      _ = (2995+4096*Q)*3 := congrArg (fun n => n*3) hQ
  have hy := hy.trans (congrArg (fun n => n-10) hnext)
  simp only [hk] at hy
  have ex : 2995+4096*Q-7 = 2988+4096*Q := by omega
  have ey : (2995+4096*Q)*3-10 = 8975+12288*Q := by omega
  simp only [ex] at hx
  simp only [ey] at hy
  have ht : 1480+1536*z = (1468+1536*z)+12 := by omega
  have hm := (congrArg (terras_iter 12) hx).trans
    ((mersenne_exit_merge Q).trans (congrArg (terras_iter 12) hy).symm)
  simpa only [terras_iter_add, ← ht] using hm

/-- The recursive parameter in the progression rule is strictly smaller. -/
theorem mersenne_exit_smaller (z : ℕ) :
    8*(2^(1468+1536*z)/9)+5 < 2^(1468+1536*z)-1 := by
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 6 ≤ 1468+1536*z by omega)
  have hP : 64 ≤ 2^(1468+1536*z) := hpow
  have hdiv : 7 ≤ 2^(1468+1536*z)/9 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 9)).mpr (by omega)
  have hmul := Nat.mod_add_div (2^(1468+1536*z)) 9
  omega

/-- A smaller transfer premise suffices on an infinite Mersenne exponent progression. -/
theorem AffineTransfer.mersenne_exit (z : ℕ)
    (hrec : AffineTransfer (8*(2^(1468+1536*z)/9)+5)) :
    AffineTransfer (2^(1468+1536*z)-1) := by
  let P := 2^(1468+1536*z)
  let w := P/9
  have hs : (2:ℕ)^4 ≡ 7 [MOD 9] := by norm_num [Nat.ModEq]
  have hp : (2:ℕ)^6 ≡ 1 [MOD 9] := by norm_num [Nat.ModEq]
  have hh := hs.mul (hp.pow (244+256*z))
  have he : (2:ℕ)^4*((2:ℕ)^6)^(244+256*z) = P := by
    change (2:ℕ)^4*((2:ℕ)^6)^(244+256*z) = 2^(1468+1536*z)
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [he, one_pow, mul_one] at hh
  have hmod : P%9 = 7 := hh
  have hP : P = 9*w+7 := by
    have hd := Nat.mod_add_div P 9
    rw [hmod] at hd
    dsimp [w]
    omega
  have hx := Cylinder.transport 3 17 (3*w)
  have hy := Cylinder.transport 3 155 (27*w)
  simp only [show terras_iter 3 17 = 20 from rfl,
    show oddSteps 3 17 = 2 from rfl] at hx
  simp only [show terras_iter 3 155 = 175 from rfl,
    show oddSteps 3 155 = 2 from rfl] at hy
  have ex : 3*(8*w+5)+2 = 17+2^3*(3*w) := by ring
  have ey : 27*(8*w+5)+20 = 155+2^3*(27*w) := by ring
  have sx : terras_iter 3 (3*(8*w+5)+2) = 3*(P-1)+2 := by rw [ex, hx, hP]; omega
  have sy : terras_iter 3 (27*(8*w+5)+20) = 27*P-14 := by rw [ey, hy, hP]; omega
  have ht : 27*(P-1)+20 = 27*P-7 := by rw [hP]; omega
  intro hu
  change ReachesOne (3*(P-1)+2) at hu
  rw [← sx] at hu
  have hv := (ReachesOne.shift_iff (3*(8*w+5)+2) 3).mp hu
  have hv' := hrec hv
  have hw := (ReachesOne.shift_iff (27*(8*w+5)+20) 3).mpr hv'
  rw [sy] at hw
  have hz := (ReachesOne.shift_iff (27*P-14) (1480+1536*z)).mpr hw
  rw [mersenne_inverse_exit_progression z] at hz
  have hy' := (ReachesOne.shift_iff (27*P-7) (1480+1536*z)).mp hz
  change ReachesOne (27*(P-1)+20)
  rw [ht]
  exact hy'

end Collatz
