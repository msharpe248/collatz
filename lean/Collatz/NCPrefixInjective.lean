import Collatz.DominatingMerge
import Collatz.Cycles

/-! Equal-time/equal-count injectivity of noncontracting prefixes through
31 steps. The arithmetic envelope is kernel checked; no all-time claim. -/
namespace Collatz.NCPrefixInjective

private def table : Array (Array ℕ) := #[
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 5, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 23, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 85, 211, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 85, 287, 665, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 319, 925, 2059, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 1085, 2903, 6305, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 1085, 3511, 8965, 19171, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 3767, 11045, 27407, 58025, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 3767, 12325, 34159, 83245, 175099, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 13349, 39023, 104525, 251783, 527345, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 44143, 121165, 317671, 759445, 1586131, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 44143, 140621, 371687, 961205, 2286527, 4766585, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 148813, 438247, 1131445, 2899999, 6875965, 14316139, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 479207, 1347509, 3427103, 8732765, 20660663, 42981185, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 479207, 1503157, 4108063, 10346845, 26263831, 62047525, 129009091, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1568693, 4640543, 12455261, 31171607, 78922565, 186273647, 387158345, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1568693, 4968223, 14183773, 37627927, 93776965, 237029839, 559083085, 1161737179, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5230367, 15428957, 43075607, 113408069, 281855183, 711613805, 1677773543, 3485735825, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16739677, 47335447, 130275397, 341272783, 846614125, 2135889991, 5034369205, 10458256051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16739677, 52316183, 144103493, 392923343, 1025915501, 2541939527, 6409767125, 15105204767, 31376865305, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54413335, 161142853, 436504783, 1182964333, 3081940807, 7630012885, 19233495679, 45319808605, 94134790219, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 171628613, 491817167, 1317902957, 3557281607, 9254211029, 22898427263, 57708875645, 135967814423, 282412759265, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 171628613, 531663055, 1492228717, 3970486087, 10688622037, 27779410303, 68712059005, 173143404151, 407920220485, 847255055011, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 548440271, 1628543597, 4510240583, 11945012693, 32099420543, 83371785341, 206169731447, 519463766885, 1223794215887, 2541798719465, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1712429677, 4952739655, 13597830613, 35902146943, 96365370493, 250182464887, 618576303205, 1558458409519, 3671449756525, 7625463267259, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1712429677, 5271506759, 14992436693, 40927709567, 107840658557, 289230329207, 750681612389, 1855863127343, 4675509446285, 11014483487303, 22876524019505, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5405724487, 16082955733, 45245745535, 123051564157, 323790411127, 867959423077, 2252313272623, 5567857817485, 14026796774311, 33043718897365, 68629840493971, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5405724487, 16754044373, 48785738111, 136274107517, 369691563383, 971908104293, 2604415140143, 6757476688781, 16704110323367, 42080927193845, 99131693563007, 205890058352825, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17290915285, 51335874943, 147430956157, 409896064375, 1110148431973, 2916798054703, 7814319162253, 20273503808167, 50113404711925, 126243855323359, 297396154430845, 617671248800299]]

private def bound (t j : ℕ) : ℕ := (table.getD t #[]).getD j 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_checked : bound 0 0 = 0 ∧
    (∀ t : Fin 31, ∀ j : Fin 32, j.val ≤ t.val →
      (2^(t.val+1) ≤ 3^j.val → bound t.val j.val ≤ bound (t.val+1) j.val) ∧
      (2^(t.val+1) ≤ 3^(j.val+1) →
        3*bound t.val j.val+2^t.val ≤ bound (t.val+1) (j.val+1))) ∧
    (∀ t j : Fin 32, j.val ≤ t.val → 2^t.val ≤ 3^j.val →
      bound t.val j.val + 2^j.val < 5*3^j.val) := by decide

private theorem correction_le_bound (t n : ℕ) (ht : t ≤ 31)
    (hp : ∀ s ≤ t, 2^s ≤ 3^oddSteps s n) : dcoef t n ≤ bound t (oddSteps t n) := by
  induction t with
  | zero => simp [dcoef, oddSteps, table_checked.1]
  | succ t ih =>
    have hi := ih (by omega) (fun s hs => hp s (by omega))
    have hstep := table_checked.2.1 ⟨t, by omega⟩ ⟨oddSteps t n, by have := oddSteps_le t n; omega⟩
      (oddSteps_le t n)
    have hd := dcoef_add t 1 n
    have ho := oddSteps_add t 1 n
    have hcur := hp (t+1) (le_refl _)
    rcases Nat.mod_two_eq_zero_or_one (terras_iter t n) with hb | hb
    · have hnot : ¬ terras_iter t n % 2 = 1 := by omega
      have hd1 : dcoef 1 (terras_iter t n) = 0 := by simp [dcoef, hnot]
      have ho1 : oddSteps 1 (terras_iter t n) = 0 := by simp [oddSteps, hnot]
      rw [hd1, ho1] at hd
      rw [ho1] at ho
      simp only [pow_zero, one_mul, mul_zero, add_zero] at hd ho
      rw [ho] at hcur ⊢
      rw [hd]
      exact hi.trans (hstep.1 hcur)
    · have hd1 : dcoef 1 (terras_iter t n) = 1 := by simp [dcoef, hb]
      have ho1 : oddSteps 1 (terras_iter t n) = 1 := by simp [oddSteps, hb]
      rw [hd1, ho1] at hd
      rw [ho1] at ho
      simp only [pow_one, mul_one] at hd
      rw [ho] at hcur ⊢
      rw [hd]
      have hh := hstep.2 hcur
      exact (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hi) (2^t)).trans hh

/-- A uniform correction interval, with no seed cutoff, through 31 steps. -/
theorem correction_interval_31 (t n : ℕ) (ht : t ≤ 31)
    (hp : ∀ s ≤ t, 2^s ≤ 3^oddSteps s n) :
    3^oddSteps t n ≤ dcoef t n+2^oddSteps t n ∧
      dcoef t n+2^oddSteps t n < 5*3^oddSteps t n := by
  have hlo := terras_lower_bound t n
  have he := terras_exact_form t n
  have hb := correction_le_bound t n ht hp
  have htop := table_checked.2.2 ⟨t, by omega⟩
    ⟨oddSteps t n, by have := oddSteps_le t n; omega⟩ (oddSteps_le t n) (hp t (le_refl _))
  constructor
  · nlinarith only [hlo, he]
  · exact lt_of_le_of_lt (Nat.add_le_add_right hb _) htop

private theorem first_odd (n : ℕ) (h : 2^1 ≤ 3^oddSteps 1 n) : n%2=1 := by
  rcases Nat.mod_two_eq_zero_or_one n with hz | ho
  · simp [oddSteps, hz] at h
  · exact ho

private theorem first_two_residue (n : ℕ)
    (h1 : 2^1 ≤ 3^oddSteps 1 n) (h2 : 2^2 ≤ 3^oddSteps 2 n) : n%4=3 := by
  have ho := first_odd n h1
  have hn : terras n%2=1 := by
    rcases Nat.mod_two_eq_zero_or_one (terras n) with hz | hh
    · simp [oddSteps, ho, hz] at h2
    · exact hh
  have he := two_mul_terras_odd n ho
  omega

/-- Through time 31, two noncontracting prefixes with the same odd count
and endpoint must have the same initial seed. This does not assert injectivity
when odd counts differ, or at arbitrary times. -/
theorem equal_count_injective_31 {t n m : ℕ} (ht : t ≤ 31)
    (hn : ∀ s ≤ t, 2^s ≤ 3^oddSteps s n)
    (hm : ∀ s ≤ t, 2^s ≤ 3^oddSteps s m)
    (hj : oddSteps t n = oddSteps t m)
    (he : terras_iter t n = terras_iter t m) : n=m := by
  by_cases htwo : 2 ≤ t
  · have rn := first_two_residue n (hn 1 (by omega)) (hn 2 htwo)
    have rm := first_two_residue m (hm 1 (by omega)) (hm 2 htwo)
    obtain ⟨hln, hun⟩ := correction_interval_31 t n ht hn
    obtain ⟨hlm, hum⟩ := correction_interval_31 t m ht hm
    have en := terras_exact_form t n
    have em := terras_exact_form t m
    rw [← hj, ← he] at em
    rw [← hj] at hlm hum
    have hnm : n < m+4 := by
      by_contra hh
      have hmul := Nat.mul_le_mul_left (3^oddSteps t n) (show m+4 ≤ n by omega)
      nlinarith only [en, em, hln, hum, hmul]
    have hmn : m < n+4 := by
      by_contra hh
      have hmul := Nat.mul_le_mul_left (3^oddSteps t n) (show n+4 ≤ m by omega)
      nlinarith only [en, em, hlm, hun, hmul]
    omega
  · have ht01 : t=0 ∨ t=1 := by omega
    rcases ht01 with rfl | rfl
    · exact he
    · have hno := first_odd n (hn 1 (le_refl _))
      have hmo := first_odd m (hm 1 (le_refl _))
      have en := two_mul_terras_odd n hno
      have em := two_mul_terras_odd m hmo
      change terras n = terras m at he
      omega

set_option maxRecDepth 100000 in
/-- Removing the equal-count hypothesis is false even at seven steps. -/
theorem different_counts_collision :
    terras_iter 7 31 = 182 ∧ terras_iter 7 95 = 182 ∧
    oddSteps 7 31 = 6 ∧ oddSteps 7 95 = 5 ∧
    (∀ i : Fin 8, 2^i.val ≤ 3^oddSteps i.val 31) ∧
    (∀ i : Fin 8, 2^i.val ≤ 3^oddSteps i.val 95) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The same strict correction interval already fails at time 32.
This is not a counterexample to equal-count injectivity at that time. -/
theorem correction_interval_fails_at_32 :
    oddSteps 32 3384695803 = 21 ∧ dcoef 32 3384695803 = 54020229503 ∧
    (∀ i : Fin 33, 2^i.val ≤ 3^oddSteps i.val 3384695803) ∧
    5*3^oddSteps 32 3384695803 ≤ dcoef 32 3384695803+2^oddSteps 32 3384695803 := by decide

end Collatz.NCPrefixInjective
