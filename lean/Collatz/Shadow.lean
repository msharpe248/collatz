/-
  Collatz — The 3-adic Shadow

  This file contains NO axioms and NO claim to prove the conjecture.

  THE PHENOMENON. The exact orbit identity (terras_exact_form)

      2^T · T^T(n) = 3^j · n + d,    j = oddSteps T n,

  has correction term d = `dcoef T n` depending ONLY on the parity word
  of n (dcoef_modEq) — and reducing mod 3^j kills the n-term entirely:

      T^T(n) ≡ 2^(-T) · d(word)  (mod 3^j)   (shadow_modEq).

  The 3-adic residue of an orbit is a function of its parity word alone.
  Counting (shadow_compression): a window of T steps with no descent
  forces a supercritical word (Density.lean), there are at most
  ~2^(0.95 T) such words, but the residues live among 3^j > 2^(T-1)
  classes — survivors are confined to an exponentially thin, explicit
  subset of the 3-adic world, with the SAME constants 17/27 and 3^T
  that govern the 2-adic Terras theorem (Terras.lean). Even steps
  consume 2-adic digits; odd steps produce 3-adic digits; this file
  proves the production runs at an entropy deficit on any surviving
  orbit.

  Also here:
  * `dcoef_add` — the cocycle law d(w₁w₂) = 3^(j₂) d(w₁) + 2^(|w₁|) d(w₂),
    the integer form of the ℤ₂×ℤ₃ skew product;
  * `density_floor` — orbits whose values stay ≥ N can survive only at
    odd density ≥ log 2 / log((3N+1)/N) → log 2/log 3: the finite form
    of "divergent orbits have liminf parity density ≥ critical", which
    is NOT a consequence of the master inequalities and closes that gap.

  Together with NoGo/Density/Critical, this is the formal core of the
  reduction: Collatz divergence ⟺ an integer orbit sustaining a ~5%
  compression of its own 3-adic digit stream forever (the entropy gap
  1 − H(0.6309), with δ·log₂3 = 1 exactly at the critical density).
-/

import Collatz.Terras

namespace Collatz

/-! ## The exact orbit identity -/

/-- The correction term: a function of the parity word alone. -/
def dcoef : ℕ → ℕ → ℕ
  | 0, _ => 0
  | T + 1, n =>
      (if n % 2 = 1 then 3 ^ oddSteps T (terras n) else 0) +
        2 * dcoef T (terras n)

@[simp] theorem dcoef_zero (n : ℕ) : dcoef 0 n = 0 := rfl

theorem dcoef_succ_even {T n : ℕ} (h : n % 2 = 0) :
    dcoef (T + 1) n = 2 * dcoef T (terras n) := by
  have h' : ¬ n % 2 = 1 := by omega
  simp [dcoef, h']

theorem dcoef_succ_odd {T n : ℕ} (h : n % 2 = 1) :
    dcoef (T + 1) n = 3 ^ oddSteps T (terras n) + 2 * dcoef T (terras n) := by
  simp [dcoef, h]

/-- THE EXACT FORM: 2^T·T^T(n) = 3^j·n + d. The master inequalities of
    Density.lean and Cycles.lean are the two-sided bounds on d; this is
    the identity they bound. -/
theorem terras_exact_form (T : ℕ) : ∀ n : ℕ,
    2 ^ T * terras_iter T n = 3 ^ oddSteps T n * n + dcoef T n := by
  induction T with
  | zero => intro n; simp [terras_iter]
  | succ T ih =>
    intro n
    have hit : terras_iter (T + 1) n = terras_iter T (terras n) := rfl
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · rw [hit, oddSteps_succ_even T n hp, dcoef_succ_even hp]
      have h2 : 2 * terras n = n := two_mul_terras_even n hp
      calc 2 ^ (T + 1) * terras_iter T (terras n)
          = 2 * (2 ^ T * terras_iter T (terras n)) := by ring
        _ = 2 * (3 ^ oddSteps T (terras n) * terras n +
              dcoef T (terras n)) := by rw [ih]
        _ = 3 ^ oddSteps T (terras n) * (2 * terras n) +
              2 * dcoef T (terras n) := by ring
        _ = 3 ^ oddSteps T (terras n) * n + 2 * dcoef T (terras n) := by
            rw [h2]
    · rw [hit, oddSteps_succ_odd T n hp, dcoef_succ_odd hp]
      have h2 : 2 * terras n = 3 * n + 1 := two_mul_terras_odd n hp
      calc 2 ^ (T + 1) * terras_iter T (terras n)
          = 2 * (2 ^ T * terras_iter T (terras n)) := by ring
        _ = 2 * (3 ^ oddSteps T (terras n) * terras n +
              dcoef T (terras n)) := by rw [ih]
        _ = 3 ^ oddSteps T (terras n) * (2 * terras n) +
              2 * dcoef T (terras n) := by ring
        _ = 3 ^ oddSteps T (terras n) * (3 * n + 1) +
              2 * dcoef T (terras n) := by rw [h2]
        _ = 3 ^ (oddSteps T (terras n) + 1) * n +
              (3 ^ oddSteps T (terras n) + 2 * dcoef T (terras n)) := by
            ring

/-! ## The correction is a function of the parity word -/

/-- One Terras step preserves congruence, one level down (re-proved
    here from the doubling identities; cf. Parity.lean). -/
theorem terras_modEq_step {k n m : ℕ} (h : n ≡ m [MOD 2 ^ (k + 1)]) :
    terras n ≡ terras m [MOD 2 ^ k] := by
  have hpar : n % 2 = m % 2 := by
    have hdvd : (2 : ℕ) ∣ 2 ^ (k + 1) := ⟨2 ^ k, by ring⟩
    exact Nat.ModEq.of_dvd hdvd h
  have hsplit : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  rcases Nat.mod_two_eq_zero_or_one n with hp | hp
  · have hmp : m % 2 = 0 := by omega
    apply modEq_of_two_mul
    rw [two_mul_terras_even n hp, two_mul_terras_even m hmp, ← hsplit]
    exact h
  · have hmp : m % 2 = 1 := by omega
    apply modEq_of_two_mul
    rw [two_mul_terras_odd n hp, two_mul_terras_odd m hmp, ← hsplit]
    exact (h.mul_left 3).add_right 1

/-- d depends only on n mod 2^T: the correction is word-determined. -/
theorem dcoef_modEq (T : ℕ) : ∀ n m, n ≡ m [MOD 2 ^ T] →
    dcoef T n = dcoef T m := by
  induction T with
  | zero => intro n m _; rfl
  | succ T ih =>
    intro n m h
    have hpar : n % 2 = m % 2 := by
      have hdvd : (2 : ℕ) ∣ 2 ^ (T + 1) := ⟨2 ^ T, by ring⟩
      exact Nat.ModEq.of_dvd hdvd h
    have hstep : terras n ≡ terras m [MOD 2 ^ T] := terras_modEq_step h
    have hodd : oddSteps T (terras n) = oddSteps T (terras m) :=
      oddSteps_modEq T hstep
    have hrec : dcoef T (terras n) = dcoef T (terras m) := ih _ _ hstep
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · have hmp : m % 2 = 0 := by omega
      rw [dcoef_succ_even hp, dcoef_succ_even hmp, hrec]
    · have hmp : m % 2 = 1 := by omega
      rw [dcoef_succ_odd hp, dcoef_succ_odd hmp, hodd, hrec]

/-! ## The 3-adic shadow -/

/-- THE SHADOW CONGRUENCE: congruent starts mod 2^T have congruent
    endpoints mod 3^j. The orbit's 3-adic residue is a function of its
    parity word alone — the n-dependence cancels exactly. -/
theorem shadow_modEq {T n m : ℕ} (h : n ≡ m [MOD 2 ^ T]) :
    terras_iter T n ≡ terras_iter T m [MOD 3 ^ oddSteps T n] := by
  have hodd : oddSteps T n = oddSteps T m := oddSteps_modEq T h
  have hd : dcoef T n = dcoef T m := dcoef_modEq T n m h
  have hA := terras_exact_form T n
  have hB := terras_exact_form T m
  rw [hodd, hd] at hA
  -- cross identity: 2^T·n_T + 3^j·m = 2^T·m_T + 3^j·n
  set j := oddSteps T m with hj
  have hcross : 2 ^ T * terras_iter T n + 3 ^ j * m =
      2 ^ T * terras_iter T m + 3 ^ j * n := by omega
  have hmod : (2 ^ T * terras_iter T n) % 3 ^ j =
      (2 ^ T * terras_iter T m) % 3 ^ j := by
    calc (2 ^ T * terras_iter T n) % 3 ^ j
        = (2 ^ T * terras_iter T n + 3 ^ j * m) % 3 ^ j := by
          rw [Nat.add_mul_mod_self_left]
      _ = (2 ^ T * terras_iter T m + 3 ^ j * n) % 3 ^ j := by rw [hcross]
      _ = (2 ^ T * terras_iter T m) % 3 ^ j := by
          rw [Nat.add_mul_mod_self_left]
  have hco : Nat.Coprime (3 ^ j) (2 ^ T) :=
    Nat.Coprime.pow _ _ (by norm_num)
  rw [hodd]
  exact Nat.ModEq.cancel_left_of_coprime hco hmod

/-! ## The cocycle law: the skew product in integer form -/

theorem oddSteps_add (S T : ℕ) : ∀ n,
    oddSteps (S + T) n = oddSteps S n + oddSteps T (terras_iter S n) := by
  induction S with
  | zero =>
    intro n
    rw [Nat.zero_add]
    show oddSteps T n = 0 + oddSteps T n
    omega
  | succ S ih =>
    intro n
    have e : S + 1 + T = (S + T) + 1 := by omega
    rw [e]
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · rw [oddSteps_succ_even _ n hp, oddSteps_succ_even S n hp, ih (terras n)]
      rfl
    · rw [oddSteps_succ_odd _ n hp, oddSteps_succ_odd S n hp, ih (terras n)]
      have : terras_iter (S + 1) n = terras_iter S (terras n) := rfl
      rw [this]
      ring

/-- THE COCYCLE LAW: d(w₁w₂) = 3^(j₂)·d(w₁) + 2^(|w₁|)·d(w₂). The
    correction term composes like the ℤ₂×ℤ₃ skew product: the 3-adic
    weight of the second window scales the first correction, the 2-adic
    length of the first window scales the second. -/
theorem dcoef_add (S T n : ℕ) :
    dcoef (S + T) n = 3 ^ oddSteps T (terras_iter S n) * dcoef S n +
      2 ^ S * dcoef T (terras_iter S n) := by
  have hiter : terras_iter (S + T) n = terras_iter T (terras_iter S n) :=
    (terras_iter_add S T n).symm
  -- expand 2^(S+T)·n_{S+T} two ways
  have hA := terras_exact_form (S + T) n
  have hB := terras_exact_form T (terras_iter S n)
  have hC := terras_exact_form S n
  have key : 2 ^ (S + T) * terras_iter (S + T) n =
      3 ^ (oddSteps S n + oddSteps T (terras_iter S n)) * n +
        (3 ^ oddSteps T (terras_iter S n) * dcoef S n +
          2 ^ S * dcoef T (terras_iter S n)) := by
    calc 2 ^ (S + T) * terras_iter (S + T) n
        = 2 ^ S * (2 ^ T * terras_iter T (terras_iter S n)) := by
          rw [hiter]; ring
      _ = 2 ^ S * (3 ^ oddSteps T (terras_iter S n) * terras_iter S n +
            dcoef T (terras_iter S n)) := by rw [hB]
      _ = 3 ^ oddSteps T (terras_iter S n) * (2 ^ S * terras_iter S n) +
            2 ^ S * dcoef T (terras_iter S n) := by ring
      _ = 3 ^ oddSteps T (terras_iter S n) *
            (3 ^ oddSteps S n * n + dcoef S n) +
            2 ^ S * dcoef T (terras_iter S n) := by rw [hC]
      _ = 3 ^ (oddSteps S n + oddSteps T (terras_iter S n)) * n +
            (3 ^ oddSteps T (terras_iter S n) * dcoef S n +
              2 ^ S * dcoef T (terras_iter S n)) := by
          rw [pow_add]; ring
  rw [oddSteps_add S T n] at hA
  omega

/-! ## The density floor for large-valued orbits -/

/-- Refined per-step accounting: while all orbit values are ≥ N, the
    odd-step multiplier is at most (3N+1)/(2N) instead of worst-case.
    In integer form: T^T(n)·2^T·N^j ≤ n·(3N+1)^j. -/
theorem orbit_upper_refined (T : ℕ) : ∀ n N : ℕ,
    (∀ t, t < T → N ≤ terras_iter t n) →
    terras_iter T n * 2 ^ T * N ^ oddSteps T n ≤
      n * (3 * N + 1) ^ oddSteps T n := by
  induction T with
  | zero => intro n N _; simp [terras_iter]
  | succ T ih =>
    intro n N hbig
    have hn : N ≤ n := hbig 0 (by omega)
    have hshift : ∀ t, t < T → N ≤ terras_iter t (terras n) :=
      fun t ht => hbig (t + 1) (by omega)
    have IH := ih (terras n) N hshift
    have hit : terras_iter (T + 1) n = terras_iter T (terras n) := rfl
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · rw [hit, oddSteps_succ_even T n hp]
      have h2 : 2 * terras n = n := two_mul_terras_even n hp
      calc terras_iter T (terras n) * 2 ^ (T + 1) *
            N ^ oddSteps T (terras n)
          = 2 * (terras_iter T (terras n) * 2 ^ T *
              N ^ oddSteps T (terras n)) := by ring
        _ ≤ 2 * (terras n * (3 * N + 1) ^ oddSteps T (terras n)) :=
            Nat.mul_le_mul_left 2 IH
        _ = (2 * terras n) * (3 * N + 1) ^ oddSteps T (terras n) := by ring
        _ = n * (3 * N + 1) ^ oddSteps T (terras n) := by rw [h2]
    · rw [hit, oddSteps_succ_odd T n hp]
      have h2 : 2 * terras n = 3 * n + 1 := two_mul_terras_odd n hp
      have hkey : N * (3 * n + 1) ≤ n * (3 * N + 1) := by nlinarith
      calc terras_iter T (terras n) * 2 ^ (T + 1) *
            N ^ (oddSteps T (terras n) + 1)
          = (2 * N) * (terras_iter T (terras n) * 2 ^ T *
              N ^ oddSteps T (terras n)) := by ring
        _ ≤ (2 * N) * (terras n * (3 * N + 1) ^ oddSteps T (terras n)) :=
            Nat.mul_le_mul_left _ IH
        _ = (N * (2 * terras n)) * (3 * N + 1) ^ oddSteps T (terras n) := by
            ring
        _ = (N * (3 * n + 1)) * (3 * N + 1) ^ oddSteps T (terras n) := by
            rw [h2]
        _ ≤ (n * (3 * N + 1)) * (3 * N + 1) ^ oddSteps T (terras n) :=
            Nat.mul_le_mul_right _ hkey
        _ = n * (3 * N + 1) ^ (oddSteps T (terras n) + 1) := by ring

/-- THE DENSITY FLOOR. An orbit whose values all stay ≥ N and which has
    not descended below its start satisfies 2^T·N^j ≤ (3N+1)^j: its odd
    density is at least log 2 / log((3N+1)/N), which tends to the
    critical log 2/log 3 as N → ∞. This is the finite form of
    "divergent orbits have liminf parity density ≥ critical" — the
    statement the master inequalities deliberately do not give. -/
theorem density_floor {T n N : ℕ} (hN : 1 ≤ N)
    (hbig : ∀ t, t < T → N ≤ terras_iter t n)
    (hsurv : n ≤ terras_iter T n) :
    2 ^ T * N ^ oddSteps T n ≤ (3 * N + 1) ^ oddSteps T n := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hn : 1 ≤ n := le_trans hN (hbig 0 hT)
  have h := orbit_upper_refined T n N hbig
  have h2 : n * (2 ^ T * N ^ oddSteps T n) ≤
      n * (3 * N + 1) ^ oddSteps T n := by
    calc n * (2 ^ T * N ^ oddSteps T n)
        ≤ terras_iter T n * (2 ^ T * N ^ oddSteps T n) :=
          Nat.mul_le_mul_right _ hsurv
      _ = terras_iter T n * 2 ^ T * N ^ oddSteps T n := by ring
      _ ≤ n * (3 * N + 1) ^ oddSteps T n := h
  exact Nat.le_of_mul_le_mul_left h2 (by omega)

/-! ## The confinement count: the 3-adic mirror of Terras' theorem -/

/-- The shadow data of a window: the odd count and the 3-adic residue. -/
noncomputable def shadowPair (T n : ℕ) : ℕ × ℕ :=
  (oddSteps T n, terras_iter T n % 3 ^ oddSteps T n)

/-- The shadow is determined by the residue class mod 2^T. -/
theorem shadowPair_mod (T n : ℕ) :
    shadowPair T n = shadowPair T (n % 2 ^ T) := by
  have h : n % 2 ^ T ≡ n [MOD 2 ^ T] := Nat.mod_modEq n (2 ^ T)
  have hodd : oddSteps T (n % 2 ^ T) = oddSteps T n :=
    oddSteps_modEq T h
  have hsh : terras_iter T (n % 2 ^ T) % 3 ^ oddSteps T (n % 2 ^ T) =
      terras_iter T n % 3 ^ oddSteps T (n % 2 ^ T) := shadow_modEq h
  unfold shadowPair
  rw [hodd] at hsh ⊢
  rw [Prod.mk.injEq]
  exact ⟨rfl, hsh.symm⟩

/-- The shadows of all supercritical windows form an explicitly small
    set: at most the binomial tail, weighed against 3^j > 2^(T-1)
    ambient classes per fiber. -/
noncomputable def shadowSet (T : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (2 ^ T)).filter
    (fun r => 2 ^ T < 2 * 3 ^ oddSteps T r)).image (shadowPair T)

/-- THE COMPRESSION BOUND, with the same constants as the 2-adic Terras
    theorem: 2^(17(T-1)/27) · #(shadowSet) ≤ 3^T. Since each member has
    3^j > 2^(T-1) ambient residues available, the shadows occupy an
    exponentially vanishing ≈ 2^(-0.045T) fraction: the 3-adic digits of
    surviving orbits are compressible, forever, by the entropy gap. -/
theorem shadow_compression (T : ℕ) :
    2 ^ (17 * (T - 1) / 27) * (shadowSet T).card ≤ 3 ^ T := by
  have h1 : (shadowSet T).card ≤
      ((Finset.range (2 ^ T)).filter
        (fun r => 2 ^ T < 2 * 3 ^ oddSteps T r)).card :=
    Finset.card_image_le
  have h2 := card_supercritical_residues T
  have h3 : (∑ j ∈ (Finset.range (T + 1)).filter
      (fun j => 2 ^ T < 2 * 3 ^ j), T.choose j) ≤
      ∑ j ∈ (Finset.range (T + 1)).filter
        (fun j => 17 * (T - 1) / 27 ≤ j), T.choose j := by
    refine Finset.sum_le_sum_of_subset ?_
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨hj.1, tail_exponent T j hj.2⟩
  calc 2 ^ (17 * (T - 1) / 27) * (shadowSet T).card
      ≤ 2 ^ (17 * (T - 1) / 27) *
        (∑ j ∈ (Finset.range (T + 1)).filter
          (fun j => 2 ^ T < 2 * 3 ^ j), T.choose j) := by
        apply Nat.mul_le_mul_left
        rw [← h2]
        exact h1
    _ ≤ 2 ^ (17 * (T - 1) / 27) *
        (∑ j ∈ (Finset.range (T + 1)).filter
          (fun j => 17 * (T - 1) / 27 ≤ j), T.choose j) :=
        Nat.mul_le_mul_left _ h3
    _ ≤ 3 ^ T := choose_tail_bound T (17 * (T - 1) / 27)

/-- MEMBERSHIP: every integer in the dyadic window that survives T steps
    has its shadow in the small set — and its fiber is large
    (2·3^j > 2^T). Confinement is unconditional for survivors. -/
theorem surviving_shadow_mem {T n : ℕ} (hlo : 2 ^ T ≤ n)
    (hsurv : ∀ t, t ≤ T → n ≤ terras_iter t n) :
    shadowPair T n ∈ shadowSet T ∧ 2 ^ T < 2 * 3 ^ oddSteps T n := by
  have hsc : 2 ^ T < 2 * 3 ^ oddSteps T n := by
    apply early_no_descent_forces_density T n (hsurv T le_rfl)
    have hp : 2 ^ (T - oddSteps T n) ≤ 2 ^ T :=
      Nat.pow_le_pow_right (by norm_num) (Nat.sub_le T _)
    omega
  constructor
  · unfold shadowSet
    rw [Finset.mem_image]
    refine ⟨n % 2 ^ T, ?_, (shadowPair_mod T n).symm⟩
    rw [Finset.mem_filter, Finset.mem_range]
    have hr : n % 2 ^ T ≡ n [MOD 2 ^ T] := Nat.mod_modEq n (2 ^ T)
    constructor
    · exact Nat.mod_lt _ (Nat.two_pow_pos T)
    · rw [oddSteps_modEq T hr]
      exact hsc
  · exact hsc

/-!
## What this means

Pair the two halves. `surviving_shadow_mem` says every survivor's 3-adic
residue lies in `shadowSet T`, inside a fiber of more than 2^(T-1)
classes; `shadow_compression` says the whole set has at most
3^T / 2^(17(T-1)/27) ≈ 2^(0.955 T) members. A surviving orbit's 3-adic
digits are produced at ≥ 1 bit per step but carry ≤ 0.955 bits per step
of information — a sustained compression by the entropy gap
1 − H(log 2/log 3) ≈ 4.5%. The cocycle law `dcoef_add` shows the
compression composes across scales exactly like the ℤ₂×ℤ₃ skew product,
and `density_floor` pins divergent orbits to the critical density where
the production rate δ·log₂3 equals exactly 1.

The reduction this makes formal: the Collatz conjecture's divergence
half is precisely the statement that no integer orbit can sustain this
3-adic compression forever. By `parity_pattern_realized` the compressed
shadows are inhabited at every finite scale, and by
`no_finite_certificate` no bounded-memory argument decides who inhabits
them — the remaining question is genuinely about the joint base-2/base-3
structure of integers. The conjecture remains OPEN.
-/

end Collatz
