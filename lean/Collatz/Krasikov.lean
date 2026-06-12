/-
  Collatz — A Machine-Verified Density Exponent

  This file contains NO axioms and NO claim to prove the conjecture.

  THE THEOREM (`density_lower_bound`). For every y, the number of
  integers n ≤ 8·2^y whose Terras orbit reaches 1 satisfies

      14684 · 137^y · 10000  ≤  count · 25220 · 100^y · 18769 ,

  i.e. count ≥ 0.031·(1.37)^y = Ω(x^γ) on the dyadic grid x = 8·2^y,
  with γ = log₂ 1.37 = 0.4543… . This is, to our knowledge, the first
  machine-verified density lower bound for the 3x+1 problem; it exceeds
  Krasikov's 1989 bound x^0.43 (the best human result until 1995).

  ## Method (Krasikov's difference inequalities, integer-grid form)

  The backward tree: `treeMem a X n` says the Terras orbit of n reaches
  a with every intermediate value ≤ X; `cnt a X` counts such n. Counting
  the two preimage branches (doubling, and (2a-1)/3 when defined) gives
  difference inequalities for the class-infima `phi k m y` (over roots
  a ≡ m mod 3^k that reach 8, at cap X = 2^y·a):

      m ≡ 5 (9):  phi m (y+2) ≥ phi (4m) y
      m ≡ 2 (9):  phi m (y+2) ≥ phi (4m) y + min-lifts phi ((4m-2)/3) (y+1)
      m ≡ 8 (9):  phi m (y+2) ≥ phi (4m) y + min-lifts phi ((2m-1)/3) (y+1)

  Disjointness of the sibling subtrees reduces to: nothing that reaches
  8 is periodic (the orbit of 8 ends in the 1-2 loop). The phi-system
  plus an 81-entry integer certificate (found by nonlinear power
  iteration, verified here by `decide`) yields phi ≥ Δ·c_m·(137/100)^y
  by a purely natural-number induction — no rationals, no reals, no
  division appear anywhere in the proofs.

  This is the integer-grid weakening of the Krasikov / Applegate-
  Lagarias / Krasikov-Lagarias program (Acta Arith. 109 (2003) 237-258):
  their advanced terms are retarded by cap-monotonicity, at the cost of
  a smaller exponent (their full system gives x^0.84 at k = 11 and
  x^0.895 at k = 17, not yet formalized). The certificate level k = 5
  (modulus 3^5 = 243) is used here; the pipeline is k-generic.
-/

import Collatz.Density

namespace Collatz

/-! ## The backward tree with capped trajectories -/

/-- The Terras orbit of n reaches a. -/
def reaches (n a : ℕ) : Prop := ∃ j, terras_iter j n = a

/-- n reaches a with every intermediate orbit value ≤ X. -/
def treeMem (a X n : ℕ) : Prop :=
  ∃ j, terras_iter j n = a ∧ ∀ i, i ≤ j → terras_iter i n ≤ X

/-- The capped backward tree of a, as a finite set (classical
    decidability, scoped to this definition). -/
noncomputable def treeSet (a X : ℕ) : Finset ℕ :=
  @Finset.filter _ (treeMem a X) (Classical.decPred _) (Finset.range (X + 1))

theorem mem_treeSet {a X n : ℕ} :
    n ∈ treeSet a X ↔ n < X + 1 ∧ treeMem a X n := by
  letI : DecidablePred (treeMem a X) := Classical.decPred _
  unfold treeSet
  rw [Finset.mem_filter, Finset.mem_range]

/-- The number of n ≤ X in the capped backward tree of a. -/
noncomputable def cnt (a X : ℕ) : ℕ := (treeSet a X).card

theorem reaches_trans {u v w : ℕ} (h1 : reaches u v) (h2 : reaches v w) :
    reaches u w := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  exact ⟨s + t, by rw [← terras_iter_add, hs, ht]⟩

theorem treeMem_self {a X : ℕ} (haX : a ≤ X) : treeMem a X a :=
  ⟨0, rfl, fun i hi => by
    have : i = 0 := Nat.le_zero.mp hi
    subst this
    exact haX⟩

theorem treeMem_le {a X n : ℕ} (h : treeMem a X n) : n ≤ X := by
  obtain ⟨j, _, hcap⟩ := h
  exact hcap 0 (Nat.zero_le j)

theorem treeMem_mono {a X X' n : ℕ} (hXX : X ≤ X') (h : treeMem a X n) :
    treeMem a X' n := by
  obtain ⟨j, hj, hcap⟩ := h
  exact ⟨j, hj, fun i hi => le_trans (hcap i hi) hXX⟩

theorem cnt_pos {a X : ℕ} (haX : a ≤ X) : 1 ≤ cnt a X := by
  apply Finset.card_pos.mpr
  exact ⟨a, mem_treeSet.mpr ⟨by omega, treeMem_self haX⟩⟩

theorem cnt_mono {a X X' : ℕ} (hXX : X ≤ X') : cnt a X ≤ cnt a X' := by
  apply Finset.card_le_card
  intro n hn
  rw [mem_treeSet] at hn ⊢
  exact ⟨by omega, treeMem_mono hXX hn.2⟩

/-- Extending tree membership along a chain u → … → a of du Terras
    steps whose values (after the start) stay ≤ X. -/
theorem treeMem_extend {u a X n du : ℕ} (hu : terras_iter du u = a)
    (hchain : ∀ i, 1 ≤ i → i ≤ du → terras_iter i u ≤ X) :
    treeMem u X n → treeMem a X n := by
  rintro ⟨j, hj, hcap⟩
  refine ⟨j + du, ?_, ?_⟩
  · rw [← hu, ← hj, terras_iter_add]
  · intro i hi
    rcases le_or_lt i j with h | h
    · exact hcap i h
    · have hi' : i - j ≥ 1 ∧ i - j ≤ du := by omega
      have : terras_iter i n = terras_iter (i - j) u := by
        rw [← hj, terras_iter_add]
        congr 1
        omega
      rw [this]
      exact hchain (i - j) hi'.1 hi'.2

theorem cnt_le_of_chain {u a X : ℕ} {du : ℕ} (hu : terras_iter du u = a)
    (hchain : ∀ i, 1 ≤ i → i ≤ du → terras_iter i u ≤ X) :
    cnt u X ≤ cnt a X := by
  apply Finset.card_le_card
  intro n hn
  rw [mem_treeSet] at hn ⊢
  exact ⟨hn.1, treeMem_extend hu hchain hn.2⟩

/-! ## Cycle-freeness above 8 -/

theorem terras_one : terras 1 = 2 := by unfold terras; norm_num
theorem terras_two : terras 2 = 1 := by unfold terras; norm_num
theorem terras_four : terras 4 = 2 := by unfold terras; norm_num
theorem terras_eight : terras 8 = 4 := by unfold terras; norm_num

/-- The orbit of 1 stays in {1, 2}. -/
theorem iter_one_small : ∀ r, terras_iter r 1 = 1 ∨ terras_iter r 1 = 2 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr (by rw [show terras_iter 1 1 = terras 1 from rfl,
        terras_one])
    | r + 2 =>
      have e : terras_iter (r + 2) 1 = terras_iter r 1 := by
        show terras_iter (r + 1) (terras 1) = _
        rw [terras_one]
        show terras_iter r (terras 2) = _
        rw [terras_two]
      rw [e]
      exact ih r (by omega)

theorem iter_two_le : ∀ r, terras_iter r 2 ≤ 2 := by
  intro r
  match r with
  | 0 => exact Nat.le_refl 2
  | r + 1 =>
    have e : terras_iter (r + 1) 2 = terras_iter r 1 := by
      show terras_iter r (terras 2) = _
      rw [terras_two]
    rw [e]
    rcases iter_one_small r with h | h <;> omega

theorem iter_eight_small : ∀ d, 2 ≤ d → terras_iter d 8 ≤ 2 := by
  intro d hd
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  have e : terras_iter (d' + 2) 8 = terras_iter d' 2 := by
    show terras_iter (d' + 1) (terras 8) = _
    rw [terras_eight]
    show terras_iter d' (terras 4) = _
    rw [terras_four]
  rw [e]
  exact iter_two_le d'

/-- Nothing ≥ 3 that reaches 8 is periodic: the engine of subtree
    disjointness. -/
theorem not_periodic_of_reaches_eight {a : ℕ} (h3 : 3 ≤ a)
    (h8 : reaches a 8) : ∀ P, 1 ≤ P → terras_iter P a ≠ a := by
  intro P hP heq
  obtain ⟨s, hs⟩ := h8
  -- pump the period: a = terras_iter (q*P) a for all q
  have pump : ∀ q, terras_iter (q * P) a = a := by
    intro q
    induction q with
    | zero => simp [terras_iter]
    | succ q ih =>
      have e : (q + 1) * P = q * P + P := by ring
      rw [e, ← terras_iter_add, ih, heq]
  -- choose q with q*P ≥ s + 2, land in the tiny orbit of 8
  have hq : (s + 2) * P ≥ s + 2 := Nat.le_mul_of_pos_right _ (by omega)
  have key : a = terras_iter ((s + 2) * P - s) 8 := by
    calc a = terras_iter ((s + 2) * P) a := (pump (s + 2)).symm
      _ = terras_iter (s + ((s + 2) * P - s)) a := by congr 1; omega
      _ = terras_iter ((s + 2) * P - s) (terras_iter s a) :=
          (terras_iter_add _ _ _).symm
      _ = terras_iter ((s + 2) * P - s) 8 := by rw [hs]
  have hd : 2 ≤ (s + 2) * P - s := by
    have : (s + 2) * P ≥ (s + 2) * 1 := Nat.mul_le_mul_left _ hP
    omega
  have := iter_eight_small _ hd
  omega

/-! ## Disjointness of sibling subtrees -/

theorem treeMem_order {u v X n : ℕ} (hu : treeMem u X n)
    (hv : treeMem v X n) : reaches u v ∨ reaches v u := by
  obtain ⟨j1, h1, _⟩ := hu
  obtain ⟨j2, h2, _⟩ := hv
  rcases le_total j1 j2 with h | h
  · left
    refine ⟨j2 - j1, ?_⟩
    have e : terras_iter (j2 - j1) (terras_iter j1 n) = terras_iter j2 n := by
      rw [terras_iter_add]
      congr 1
      omega
    rw [h1] at e
    rw [e, h2]
  · right
    refine ⟨j1 - j2, ?_⟩
    have e : terras_iter (j1 - j2) (terras_iter j2 n) = terras_iter j1 n := by
      rw [terras_iter_add]
      congr 1
      omega
    rw [h2] at e
    rw [e, h1]

/-- Two distinct rays into a non-periodic vertex a have disjoint trees:
    if n sat in both, the orbit of a would return to a. -/
theorem treeMem_disjoint {a u v : ℕ} {du dv : ℕ}
    (hdu : 1 ≤ du) (hdv : 1 ≤ dv)
    (hu : terras_iter du u = a) (hv : terras_iter dv v = a)
    (hnp : ∀ P, 1 ≤ P → terras_iter P a ≠ a)
    (huv : ∀ t, t + dv = du → terras_iter t u ≠ v)
    (hvu : ∀ t, t + du = dv → terras_iter t v ≠ u)
    {X n : ℕ} : ¬(treeMem u X n ∧ treeMem v X n) := by
  rintro ⟨h1, h2⟩
  have reach_case : ∀ x y dx dy : ℕ, 1 ≤ dx → 1 ≤ dy →
      terras_iter dx x = a → terras_iter dy y = a →
      (∀ t, t + dy = dx → terras_iter t x ≠ y) → reaches x y → False := by
    intro x y dx dy hdx hdy hx hy hne hreach
    obtain ⟨t, ht⟩ := hreach
    have e1 : terras_iter (t + dy) x = a := by
      rw [← terras_iter_add, ht, hy]
    rcases Nat.lt_trichotomy (t + dy) dx with h | h | h
    · have e2 : terras_iter (dx - (t + dy)) a = a := by
        conv_lhs => rw [← e1]
        rw [terras_iter_add, show t + dy + (dx - (t + dy)) = dx by omega, hx]
      exact hnp _ (by omega) e2
    · exact hne t h ht
    · have e2 : terras_iter (t + dy - dx) a = a := by
        conv_lhs => rw [← hx]
        rw [terras_iter_add, show dx + (t + dy - dx) = t + dy by omega, e1]
      exact hnp _ (by omega) e2
  rcases treeMem_order h1 h2 with h | h
  · exact reach_case u v du dv hdu hdv hu hv huv h
  · exact reach_case v u dv du hdv hdu hv hu hvu h

/-- The counting split: two disjoint sub-rays both inject into the
    tree of a. -/
theorem cnt_split {a u v X : ℕ} {du dv : ℕ}
    (hdu : 1 ≤ du) (hdv : 1 ≤ dv)
    (hu : terras_iter du u = a) (hv : terras_iter dv v = a)
    (hnp : ∀ P, 1 ≤ P → terras_iter P a ≠ a)
    (huv : ∀ t, t + dv = du → terras_iter t u ≠ v)
    (hvu : ∀ t, t + du = dv → terras_iter t v ≠ u)
    (hchu : ∀ i, 1 ≤ i → i ≤ du → terras_iter i u ≤ X)
    (hchv : ∀ i, 1 ≤ i → i ≤ dv → terras_iter i v ≤ X) :
    cnt u X + cnt v X ≤ cnt a X := by
  have hdisj : Disjoint (treeSet u X) (treeSet v X) := by
    rw [Finset.disjoint_left]
    intro n hnu hnv
    rw [mem_treeSet] at hnu hnv
    exact treeMem_disjoint hdu hdv hu hv hnp huv hvu ⟨hnu.2, hnv.2⟩
  have hsub : treeSet u X ∪ treeSet v X ⊆ treeSet a X := by
    intro n hn
    rcases Finset.mem_union.mp hn with h | h <;> rw [mem_treeSet] at h <;>
      rw [mem_treeSet]
    · exact ⟨h.1, treeMem_extend hu hchu h.2⟩
    · exact ⟨h.1, treeMem_extend hv hchv h.2⟩
  calc cnt u X + cnt v X = (treeSet u X ∪ treeSet v X).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ cnt a X := Finset.card_le_card hsub

/-! ## Roots and the class-infimum functions -/

/-- Admissible roots for class m mod 3^k: at least 3, in the class,
    and reaching 8 (hence non-periodic, hence with disjoint subtrees). -/
def Roots (k m : ℕ) : Set ℕ := {a | 3 ≤ a ∧ a % 3 ^ k = m ∧ reaches a 8}

/-- φ_k^m(y): the least capped-tree count over roots of class m,
    at cap 2^y · (root). -/
noncomputable def phi (k m y : ℕ) : ℕ :=
  sInf ((fun a => cnt a (2 ^ y * a)) '' Roots k m)

theorem phi_le {k m y a : ℕ} (ha : a ∈ Roots k m) :
    phi k m y ≤ cnt a (2 ^ y * a) :=
  Nat.sInf_le ⟨a, ha, rfl⟩

/-- The infimum is attained (ℕ well-order): the workhorse for the
    difference inequalities. -/
theorem phi_attained {k m y : ℕ} (hne : (Roots k m).Nonempty) :
    ∃ a ∈ Roots k m, phi k m y = cnt a (2 ^ y * a) := by
  have : ((fun a => cnt a (2 ^ y * a)) '' Roots k m).Nonempty :=
    hne.image _
  obtain ⟨a, ha, hval⟩ := Nat.sInf_mem this
  exact ⟨a, ha, hval.symm⟩

theorem phi_ge_one {k m y : ℕ} (hne : (Roots k m).Nonempty) :
    1 ≤ phi k m y := by
  obtain ⟨a, ha, hval⟩ := phi_attained (y := y) hne
  rw [hval]
  exact cnt_pos (Nat.le_mul_of_pos_left a (Nat.two_pow_pos y))

/-! ## Root closure under the two backward branches -/

theorem roots_double {k m a : ℕ} (ha : a ∈ Roots k m) :
    4 * a ∈ Roots k (4 * m % 3 ^ k) := by
  obtain ⟨h3, hmod, h8⟩ := ha
  have hmlt : m < 3 ^ k := by
    rw [← hmod]
    exact Nat.mod_lt _ (by positivity)
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.mul_mod, hmod, Nat.mul_mod 4 m, Nat.mod_eq_of_lt hmlt]
  · -- 4a → 2a → a → … → 8
    have e1 : terras (4 * a) = 2 * a := by
      unfold terras
      rw [if_pos (by omega : (4 * a) % 2 = 0)]
      omega
    have e2 : terras (2 * a) = a := by
      unfold terras
      rw [if_pos (by omega : (2 * a) % 2 = 0)]
      omega
    have : reaches (4 * a) a := ⟨2, by
      show terras_iter 1 (terras (4 * a)) = a
      rw [e1]
      show terras (2 * a) = a
      exact e2⟩
    exact reaches_trans this h8

/-- The odd branch: for a ≡ 2 (mod 3), b := (2a-1)/3 is an odd integer
    with terras b = a. -/
theorem odd_branch {a : ℕ} (h3 : 3 ≤ a) (hmod : a % 3 = 2) :
    ∃ b, 3 * b = 2 * a - 1 ∧ b % 2 = 1 ∧ terras b = a ∧ 3 ≤ b ∧ b < a := by
  have h5 : 5 ≤ a := by omega
  obtain ⟨b, hb⟩ : ∃ b, 2 * a - 1 = 3 * b := ⟨(2 * a - 1) / 3, by omega⟩
  have hodd : b % 2 = 1 := by omega
  refine ⟨b, by omega, hodd, ?_, by omega, by omega⟩
  unfold terras
  rw [if_neg (by omega : ¬ b % 2 = 0)]
  omega

/-! ## The lift bookkeeping -/

/-- If a ≡ m (mod 3^k) and 3b ≡ 3w (mod 3^k) with 3w = (2m-1) % 3^k or
    similar, then b mod 3^k is one of the three lifts of w. -/
theorem mem_lifts {k b w : ℕ} (hk : 1 ≤ k) (hw : w < 3 ^ (k - 1))
    (hcong : b % 3 ^ (k - 1) = w) :
    b % 3 ^ k = w ∨ b % 3 ^ k = w + 3 ^ (k - 1) ∨
      b % 3 ^ k = w + 2 * 3 ^ (k - 1) := by
  have hsplit : 3 ^ k = 3 * 3 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 : b % 3 ^ k % 3 ^ (k - 1) = w := by
    rw [Nat.mod_mod_of_dvd _ ⟨3, by rw [hsplit]; ring⟩]
    exact hcong
  have h2 : b % 3 ^ k < 3 * 3 ^ (k - 1) := by
    rw [← hsplit]
    exact Nat.mod_lt _ (by positivity)
  have h3 : 0 < 3 ^ (k - 1) := by positivity
  set r := b % 3 ^ k with hrdef
  obtain ⟨qq, hq_eq⟩ : ∃ qq, r = 3 ^ (k - 1) * qq + w := by
    refine ⟨r / 3 ^ (k - 1), ?_⟩
    rw [← h1]
    exact (Nat.div_add_mod r (3 ^ (k - 1))).symm
  have h5 : 3 ^ (k - 1) * qq < 3 * 3 ^ (k - 1) := by omega
  have h6 : qq < 3 := by
    by_contra hc
    push_neg at hc
    have : 3 * 3 ^ (k - 1) ≤ 3 ^ (k - 1) * qq := by
      calc 3 * 3 ^ (k - 1) = 3 ^ (k - 1) * 3 := by ring
        _ ≤ 3 ^ (k - 1) * qq := Nat.mul_le_mul_left _ hc
    omega
  rcases (by omega : qq = 0 ∨ qq = 1 ∨ qq = 2) with rfl | rfl | rfl <;> omega

/-! ## The difference inequalities for phi -/

theorem terras_double {a : ℕ} : terras (2 * a) = a := by
  unfold terras
  rw [if_pos (by omega : (2 * a) % 2 = 0)]
  omega

/-- 4a reaches a in two steps. -/
theorem iter_two_four_mul {a : ℕ} : terras_iter 2 (4 * a) = a := by
  show terras_iter 1 (terras (4 * a)) = a
  have e1 : terras (4 * a) = 2 * a := by
    have e : 4 * a = 2 * (2 * a) := by ring
    rw [e, terras_double]
  rw [e1]
  show terras (2 * a) = a
  exact terras_double

/-- Chain caps for the doubling ray 4a → 2a → a. -/
theorem chain_four {a X : ℕ} (h4 : 4 * a ≤ X) :
    ∀ i, 1 ≤ i → i ≤ 2 → terras_iter i (4 * a) ≤ X := by
  have e1 : terras (4 * a) = 2 * a := by
    have e : 4 * a = 2 * (2 * a) := by ring
    rw [e, terras_double]
  intro i h1 h2
  interval_cases i
  · show terras (4 * a) ≤ X
    rw [e1]
    omega
  · show terras_iter 1 (terras (4 * a)) ≤ X
    rw [e1]
    show terras (2 * a) ≤ X
    rw [terras_double]
    omega

/-- Congruence transfer: a ≡ m (mod 3^k) gives c·a−d ≡ c·m−d (mod 3^k). -/
theorem sub_mod_transfer {k a m c d : ℕ} (hmod : a % 3 ^ k = m)
    (hd : d ≤ c * m) :
    (c * a - d) % 3 ^ k = (c * m - d) % 3 ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, a = 3 ^ k * t + m :=
    ⟨a / 3 ^ k, by have := Nat.div_add_mod a (3 ^ k); omega⟩
  have e : c * (3 ^ k * t + m) - d = c * m - d + 3 ^ k * (c * t) := by
    have e2 : c * (3 ^ k * t + m) = 3 ^ k * (c * t) + c * m := by ring
    omega
  rw [e, Nat.add_mul_mod_self_left]

/-- Dividing a congruence by 3: from (3x) mod 3H = W conclude
    x mod H = W / 3. -/
theorem third_mod {H x W : ℕ} (h : 3 * x % (3 * H) = W) :
    x % H = W / 3 := by
  have e := Nat.mul_mod_mul_left 3 x H
  omega

/-- The minimum of phi over the three lifts of w. -/
noncomputable def phiMin (k w y : ℕ) : ℕ :=
  min (phi k w y) (min (phi k (w + 3 ^ (k - 1)) y)
    (phi k (w + 2 * 3 ^ (k - 1)) y))

theorem phiMin_le_of_lift {k w y b : ℕ} (hk : 1 ≤ k)
    (hw : w < 3 ^ (k - 1)) (hcong : b % 3 ^ (k - 1) = w)
    (hb : b ∈ Roots k (b % 3 ^ k)) :
    phiMin k w y ≤ cnt b (2 ^ y * b) := by
  rcases mem_lifts hk hw hcong with hl | hl | hl
  · exact le_trans (min_le_left _ _) (phi_le (hl ▸ hb))
  · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
      (phi_le (hl ▸ hb))
  · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (phi_le (hl ▸ hb))

/-- (D2), integer grid: for m ≡ 5 (mod 9), phi m (y+2) ≥ phi (4m) y. -/
theorem phi_rec_five {k m y : ℕ} (hne : (Roots k m).Nonempty) :
    phi k (4 * m % 3 ^ k) y ≤ phi k m (y + 2) := by
  obtain ⟨a, ha, hval⟩ := phi_attained (y := y + 2) hne
  rw [hval]
  have h2pos : 0 < 2 ^ y := Nat.two_pow_pos y
  have hX : 2 ^ (y + 2) * a = 2 ^ y * (4 * a) := by ring
  calc phi k (4 * m % 3 ^ k) y ≤ cnt (4 * a) (2 ^ y * (4 * a)) :=
        phi_le (roots_double ha)
    _ = cnt (4 * a) (2 ^ (y + 2) * a) := by rw [hX]
    _ ≤ cnt a (2 ^ (y + 2) * a) := by
        apply cnt_le_of_chain iter_two_four_mul
        apply chain_four
        nlinarith

/-- (D3), integer grid: for m ≡ 8 (mod 9),
    phi m (y+2) ≥ phi (4m) y + phiMin ((2m−1) mod 3^k / 3) (y+1). -/
theorem phi_rec_eight {k m y : ℕ} (hk : 1 ≤ k) (hm9 : m % 9 = 8)
    (hne : (Roots k m).Nonempty) :
    phi k (4 * m % 3 ^ k) y + phiMin k ((2 * m - 1) % 3 ^ k / 3) (y + 1)
      ≤ phi k m (y + 2) := by
  obtain ⟨a, ha, hval⟩ := phi_attained (y := y + 2) hne
  obtain ⟨h3a, hamod, h8⟩ := ha
  have hm8 : 8 ≤ m := by omega
  have ha3 : a % 3 = 2 := by
    have hdvd : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    have e := Nat.mod_mod_of_dvd a hdvd
    omega
  obtain ⟨b, hb3, hbodd, hbt, hb3le, hblt⟩ := odd_branch h3a ha3
  have h2pos : 0 < 2 ^ y := Nat.two_pow_pos y
  set X := 2 ^ (y + 2) * a with hXdef
  have he4 : (2 : ℕ) ^ (y + 2) = 4 * 2 ^ y := by ring
  have haX : a ≤ X := by nlinarith
  have h4aX : 4 * a ≤ X := by nlinarith
  have hnp := not_periodic_of_reaches_eight h3a h8
  -- the split at root a
  have hsplit : cnt (4 * a) X + cnt b X ≤ cnt a X := by
    apply cnt_split (du := 2) (dv := 1) (by omega) (by omega)
      iter_two_four_mul (by show terras b = a; exact hbt) hnp
    · intro t ht
      have ht1 : t = 1 := by omega
      subst ht1
      show terras_iter 1 (4 * a) ≠ b
      show terras (4 * a) ≠ b
      have e : terras (4 * a) = 2 * a := by
        have e2 : 4 * a = 2 * (2 * a) := by ring
        rw [e2, terras_double]
      rw [e]
      omega
    · intro t ht
      omega
    · exact chain_four h4aX
    · intro i h1 h2
      have hi1 : i = 1 := by omega
      subst hi1
      show terras b ≤ X
      rw [hbt]
      exact haX
  -- count of the doubling child at its own scale
  have hcnt4 : phi k (4 * m % 3 ^ k) y ≤ cnt (4 * a) X := by
    have e : X = 2 ^ y * (4 * a) := by rw [hXdef]; ring
    rw [e]
    exact phi_le (roots_double ⟨h3a, hamod, h8⟩)
  -- count of the odd child at its own scale
  have hcntb : phiMin k ((2 * m - 1) % 3 ^ k / 3) (y + 1) ≤ cnt b X := by
    have hb8 : reaches b 8 :=
      reaches_trans ⟨1, by show terras b = a; exact hbt⟩ h8
    have hbmem : b ∈ Roots k (b % 3 ^ k) := ⟨hb3le, rfl, hb8⟩
    have hcap : 2 ^ (y + 1) * b ≤ X := by
      have e : (2 : ℕ) ^ (y + 2) = 2 * 2 ^ (y + 1) := by ring
      have h2p1 : 0 < 2 ^ (y + 1) := Nat.two_pow_pos (y + 1)
      nlinarith
    -- class bookkeeping
    have hsplitP : (3 : ℕ) ^ k = 3 * 3 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hWmod : (3 * b) % 3 ^ k = (2 * m - 1) % 3 ^ k := by
      have e1 : 3 * b = 2 * a - 1 := by omega
      rw [e1]
      exact sub_mod_transfer hamod (by omega)
    have hcong : b % 3 ^ (k - 1) = (2 * m - 1) % 3 ^ k / 3 := by
      apply third_mod
      rw [← hsplitP]
      exact hWmod
    have hwlt : (2 * m - 1) % 3 ^ k / 3 < 3 ^ (k - 1) := by
      have h1 : (2 * m - 1) % 3 ^ k < 3 ^ k := Nat.mod_lt _ (by positivity)
      omega
    calc phiMin k ((2 * m - 1) % 3 ^ k / 3) (y + 1)
        ≤ cnt b (2 ^ (y + 1) * b) := phiMin_le_of_lift hk hwlt hcong hbmem
      _ ≤ cnt b X := cnt_mono hcap
  rw [hval]
  calc phi k (4 * m % 3 ^ k) y + phiMin k ((2 * m - 1) % 3 ^ k / 3) (y + 1)
      ≤ cnt (4 * a) X + cnt b X := Nat.add_le_add hcnt4 hcntb
    _ ≤ cnt a X := hsplit

/-- (D1), integer grid: for m ≡ 2 (mod 9),
    phi m (y+2) ≥ phi (4m) y + phiMin ((4m−2) mod 3^k / 3) (y+1). -/
theorem phi_rec_two {k m y : ℕ} (hk : 1 ≤ k) (hm9 : m % 9 = 2)
    (hne : (Roots k m).Nonempty) :
    phi k (4 * m % 3 ^ k) y + phiMin k ((4 * m - 2) % 3 ^ k / 3) (y + 1)
      ≤ phi k m (y + 2) := by
  obtain ⟨a, ha, hval⟩ := phi_attained (y := y + 2) hne
  obtain ⟨h3a, hamod, h8⟩ := ha
  have hm2 : 2 ≤ m := by omega
  have ha3 : a % 3 = 2 := by
    have hdvd : (3 : ℕ) ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    have e := Nat.mod_mod_of_dvd a hdvd
    omega
  obtain ⟨b, hb3, hbodd, hbt, hb3le, hblt⟩ := odd_branch h3a ha3
  have h2pos : 0 < 2 ^ y := Nat.two_pow_pos y
  set X := 2 ^ (y + 2) * a with hXdef
  have he4 : (2 : ℕ) ^ (y + 2) = 4 * 2 ^ y := by ring
  have haX : a ≤ X := by nlinarith
  have h4aX : 4 * a ≤ X := by nlinarith
  have hnp := not_periodic_of_reaches_eight h3a h8
  -- the odd grandchild ray: 2b → b → a
  have hb'2 : terras_iter 2 (2 * b) = a := by
    show terras_iter 1 (terras (2 * b)) = a
    rw [terras_double]
    show terras b = a
    exact hbt
  have hsplit : cnt (4 * a) X + cnt (2 * b) X ≤ cnt a X := by
    apply cnt_split (du := 2) (dv := 2) (by omega) (by omega)
      iter_two_four_mul hb'2 hnp
    · intro t ht
      have ht0 : t = 0 := by omega
      subst ht0
      show 4 * a ≠ 2 * b
      intro hcon
      have hba : b = 2 * a := by omega
      omega
    · intro t ht
      have ht0 : t = 0 := by omega
      subst ht0
      show 2 * b ≠ 4 * a
      intro hcon
      have hba : b = 2 * a := by omega
      omega
    · exact chain_four h4aX
    · intro i h1 h2
      interval_cases i
      · show terras (2 * b) ≤ X
        rw [terras_double]
        omega
      · show terras_iter 1 (terras (2 * b)) ≤ X
        rw [terras_double]
        show terras b ≤ X
        rw [hbt]
        exact haX
  have hcnt4 : phi k (4 * m % 3 ^ k) y ≤ cnt (4 * a) X := by
    have e : X = 2 ^ y * (4 * a) := by rw [hXdef]; ring
    rw [e]
    exact phi_le (roots_double ⟨h3a, hamod, h8⟩)
  have hcntb : phiMin k ((4 * m - 2) % 3 ^ k / 3) (y + 1) ≤ cnt (2 * b) X := by
    have hb'8 : reaches (2 * b) 8 := reaches_trans ⟨2, hb'2⟩ h8
    have hb'mem : 2 * b ∈ Roots k (2 * b % 3 ^ k) := ⟨by omega, rfl, hb'8⟩
    have hcap : 2 ^ (y + 1) * (2 * b) ≤ X := by
      have e : 2 ^ (y + 1) * (2 * b) = 2 ^ (y + 2) * b := by ring
      rw [e, hXdef]
      have h2p2 : 0 < 2 ^ (y + 2) := Nat.two_pow_pos (y + 2)
      exact Nat.mul_le_mul_left _ (by omega)
    have hsplitP : (3 : ℕ) ^ k = 3 * 3 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hWmod : (3 * (2 * b)) % 3 ^ k = (4 * m - 2) % 3 ^ k := by
      have e1 : 3 * (2 * b) = 4 * a - 2 := by omega
      rw [e1]
      exact sub_mod_transfer hamod (by omega)
    have hcong : (2 * b) % 3 ^ (k - 1) = (4 * m - 2) % 3 ^ k / 3 := by
      apply third_mod
      rw [← hsplitP]
      exact hWmod
    have hwlt : (4 * m - 2) % 3 ^ k / 3 < 3 ^ (k - 1) := by
      have h1 : (4 * m - 2) % 3 ^ k < 3 ^ k := Nat.mod_lt _ (by positivity)
      omega
    calc phiMin k ((4 * m - 2) % 3 ^ k / 3) (y + 1)
        ≤ cnt (2 * b) (2 ^ (y + 1) * (2 * b)) :=
          phiMin_le_of_lift hk hwlt hcong hb'mem
      _ ≤ cnt (2 * b) X := cnt_mono hcap
  rw [hval]
  calc phi k (4 * m % 3 ^ k) y + phiMin k ((4 * m - 2) % 3 ^ k / 3) (y + 1)
      ≤ cnt (4 * a) X + cnt (2 * b) X := Nat.add_le_add hcnt4 hcntb
    _ ≤ cnt a X := hsplit

/-! ## The k = 5 certificate instance -/

namespace K5

/-- The 81-entry certificate for modulus 3^5 = 243 and growth rate
    λ = 137/100, found by nonlinear power iteration and verified below
    by `decide`. Entry i is the weight of class m = 3i + 2. -/
def certList : List ℕ :=
  [25066, 12768, 14684, 21157, 12970, 21590, 24035, 11689, 20393, 21943,
   11432, 14638, 19978, 13397, 22415, 22595, 10773, 15991, 24415, 13397,
   15955, 20080, 11656, 22779, 22886, 10667, 17305, 23724, 11870, 15173,
   22004, 13113, 19773, 22345, 11300, 22548, 21523, 11907, 14341, 19682,
   13316, 24156, 21520, 10612, 16409, 24685, 12157, 15555, 18824, 11433,
   23283, 25031, 10000, 20154, 25219, 11831, 14696, 21271, 12709, 20864,
   22272, 11239, 22523, 23174, 12003, 14726, 20280, 12603, 24378, 22415,
   10455, 16268, 23925, 13297, 14606, 19931, 12310, 23351, 25220, 10588,
   18219]

def c (m : ℕ) : ℕ := certList.getD ((m - 2) / 3) 1

def cbar (w : ℕ) : ℕ := min (c w) (min (c (w + 81)) (c (w + 162)))

set_option maxRecDepth 4000 in
/-- Certificate bounds: 1 ≤ c ≤ 25220 on all classes. -/
theorem cert_bounds : ∀ m, m < 243 → m % 3 = 2 →
    1 ≤ c m ∧ c m ≤ 25220 := by decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- THE CERTIFICATE CONDITIONS, kernel-verified: with p = 137, q = 100
    (p² = 18769, q² = 10000, pq = 13700),
    c_m p² ≤ c_{4m} q² (+ c̄ pq on the branching classes). -/
theorem cert_ok : ∀ m, m < 243 → m % 3 = 2 →
    (m % 9 = 5 → c m * 18769 ≤ c (4 * m % 243) * 10000) ∧
    (m % 9 = 2 → c m * 18769 ≤
      c (4 * m % 243) * 10000 + cbar ((4 * m - 2) % 243 / 3) * 13700) ∧
    (m % 9 = 8 → c m * 18769 ≤
      c (4 * m % 243) * 10000 + cbar ((2 * m - 1) % 243 / 3) * 13700) := by
  decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Every admissible class contains a power of 2 (2 is a primitive root
    mod 3^5), kernel-verified. -/
theorem exists_pow : ∀ m, m < 243 → m % 3 = 2 →
    ∃ j ∈ Finset.range 171, 3 ≤ j ∧ 2 ^ j % 243 = m := by decide

theorem terras_iter_two_pow : ∀ i j, i ≤ j →
    terras_iter i (2 ^ j) = 2 ^ (j - i) := by
  intro i
  induction i with
  | zero =>
    intro j _
    simp [terras_iter]
  | succ i ih =>
    intro j hij
    show terras_iter i (terras (2 ^ j)) = _
    have e : terras (2 ^ j) = 2 ^ (j - 1) := by
      have e2 : (2 : ℕ) ^ j = 2 * 2 ^ (j - 1) := by
        conv_lhs => rw [show j = (j - 1) + 1 by omega]
        ring
      rw [e2, terras_double]
    rw [e, ih (j - 1) (by omega)]
    congr 1
    omega

theorem roots_nonempty : ∀ m, m < 243 → m % 3 = 2 →
    (Roots 5 m).Nonempty := by
  intro m hm h3
  obtain ⟨j, _, hj3, hjm⟩ := exists_pow m hm h3
  refine ⟨2 ^ j, ?_, hjm, ?_⟩
  · have h8 : (8 : ℕ) ≤ 2 ^ j :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj3)
    exact le_trans (by norm_num) h8
  · refine ⟨j - 3, ?_⟩
    rw [terras_iter_two_pow (j - 3) j (by omega),
      show j - (j - 3) = 3 by omega]
    norm_num

theorem min3_mul_bound {a1 a2 a3 b1 b2 b3 D E : ℕ}
    (h1 : b1 * E ≤ a1 * D) (h2 : b2 * E ≤ a2 * D) (h3 : b3 * E ≤ a3 * D) :
    min b1 (min b2 b3) * E ≤ min a1 (min a2 a3) * D := by
  have e : min a1 (min a2 a3) = a1 ∨ min a1 (min a2 a3) = a2 ∨
      min a1 (min a2 a3) = a3 := by
    rcases le_total a1 (min a2 a3) with h | h
    · exact Or.inl (min_eq_left h)
    · rcases le_total a2 a3 with h' | h'
      · exact Or.inr (Or.inl (by rw [min_eq_right h, min_eq_left h']))
      · exact Or.inr (Or.inr (by rw [min_eq_right h, min_eq_right h']))
  have hb1 : min b1 (min b2 b3) ≤ b1 := min_le_left _ _
  have hb2 : min b1 (min b2 b3) ≤ b2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hb3 : min b1 (min b2 b3) ≤ b3 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  rcases e with e | e | e <;> rw [e]
  · exact le_trans (Nat.mul_le_mul_right E hb1) h1
  · exact le_trans (Nat.mul_le_mul_right E hb2) h2
  · exact le_trans (Nat.mul_le_mul_right E hb3) h3

/-- THE GROWTH THEOREM at k = 5: phi grows like (137/100)^y, witnessed
    by the certificate, by pure natural-number strong induction. -/
theorem growth : ∀ y m, m < 243 → m % 3 = 2 →
    c m * 137 ^ y * 10000 ≤ phi 5 m y * (25220 * 100 ^ y * 18769) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro m hm hm3
    have hb := cert_bounds m hm hm3
    have hne := roots_nonempty m hm hm3
    have hphi1 := phi_ge_one (y := y) hne
    match y with
    | 0 =>
      have : c m * 1 * 10000 ≤ 1 * (25220 * 1 * 18769) := by omega
      calc c m * 137 ^ 0 * 10000 = c m * 1 * 10000 := by norm_num
        _ ≤ 1 * (25220 * 1 * 18769) := this
        _ ≤ phi 5 m 0 * (25220 * 1 * 18769) :=
            Nat.mul_le_mul_right _ hphi1
        _ = phi 5 m 0 * (25220 * 100 ^ 0 * 18769) := by norm_num
    | 1 =>
      have : c m * 137 * 10000 ≤ 1 * (25220 * 100 * 18769) := by omega
      calc c m * 137 ^ 1 * 10000 = c m * 137 * 10000 := by norm_num
        _ ≤ 1 * (25220 * 100 * 18769) := this
        _ ≤ phi 5 m 1 * (25220 * 100 * 18769) :=
            Nat.mul_le_mul_right _ hphi1
        _ = phi 5 m 1 * (25220 * 100 ^ 1 * 18769) := by norm_num
    | y + 2 =>
      -- the three congruence cases mod 9
      have hm4 : 4 * m % 243 < 243 := Nat.mod_lt _ (by norm_num)
      have hm43 : (4 * m % 243) % 3 = 2 := by omega
      have ih4 := ih y (by omega) (4 * m % 243) hm4 hm43
      have hcert := cert_ok m hm hm3
      have h9 : m % 9 = 2 ∨ m % 9 = 5 ∨ m % 9 = 8 := by omega
      rcases h9 with h9 | h9 | h9
      · -- branching case m ≡ 2 (mod 9)
        have hrec := phi_rec_two (k := 5) (m := m) (y := y)
          (by norm_num) h9 hne
        have hw : (4 * m - 2) % 243 / 3 < 81 := by
          have : (4 * m - 2) % 243 < 243 := Nat.mod_lt _ (by norm_num)
          omega
        have hw3 : ((4 * m - 2) % 243 / 3) % 3 = 2 := by omega
        set w := (4 * m - 2) % 243 / 3 with hwdef
        have ihw1 := ih (y + 1) (by omega) w (by omega) hw3
        have ihw2 := ih (y + 1) (by omega) (w + 81) (by omega) (by omega)
        have ihw3 := ih (y + 1) (by omega) (w + 162) (by omega) (by omega)
        have hmin : cbar w * 137 ^ (y + 1) * 10000 ≤
            phiMin 5 w (y + 1) * (25220 * 100 ^ (y + 1) * 18769) := by
          unfold cbar phiMin
          have e81 : (3 : ℕ) ^ (5 - 1) = 81 := by norm_num
          rw [e81, show (2 * 81 : ℕ) = 162 by norm_num]
          have key := min3_mul_bound
            (E := 137 ^ (y + 1) * 10000)
            (D := 25220 * 100 ^ (y + 1) * 18769)
            (by calc K5.c w * (137 ^ (y + 1) * 10000)
                  = K5.c w * 137 ^ (y + 1) * 10000 := by ring
                _ ≤ _ := ihw1)
            (by calc K5.c (w + 81) * (137 ^ (y + 1) * 10000)
                  = K5.c (w + 81) * 137 ^ (y + 1) * 10000 := by ring
                _ ≤ _ := ihw2)
            (by calc K5.c (w + 162) * (137 ^ (y + 1) * 10000)
                  = K5.c (w + 162) * 137 ^ (y + 1) * 10000 := by ring
                _ ≤ _ := ihw3)
          calc min (K5.c w) (min (K5.c (w + 81)) (K5.c (w + 162))) *
                137 ^ (y + 1) * 10000
              = min (K5.c w) (min (K5.c (w + 81)) (K5.c (w + 162))) *
                (137 ^ (y + 1) * 10000) := by ring
            _ ≤ _ := key
        -- assemble
        have hcm := (hcert.2.1) h9
        calc c m * 137 ^ (y + 2) * 10000
            = (c m * 18769) * (137 ^ y * 10000) := by ring
          _ ≤ (c (4 * m % 243) * 10000 + cbar w * 13700) *
              (137 ^ y * 10000) := Nat.mul_le_mul_right _ hcm
          _ = (c (4 * m % 243) * 137 ^ y * 10000) * 10000 +
              (cbar w * 137 ^ (y + 1) * 10000) * 100 := by ring
          _ ≤ (phi 5 (4 * m % 243) y * (25220 * 100 ^ y * 18769)) * 10000 +
              (phiMin 5 w (y + 1) * (25220 * 100 ^ (y + 1) * 18769)) * 100 :=
              Nat.add_le_add (Nat.mul_le_mul_right _ ih4)
                (Nat.mul_le_mul_right _ hmin)
          _ = (phi 5 (4 * m % 243) y + phiMin 5 w (y + 1)) *
              (25220 * 100 ^ (y + 2) * 18769) := by ring
          _ ≤ phi 5 m (y + 2) * (25220 * 100 ^ (y + 2) * 18769) := by
              apply Nat.mul_le_mul_right
              exact hrec
      · -- pure doubling case m ≡ 5 (mod 9)
        have hrec := phi_rec_five (k := 5) (m := m) (y := y) hne
        have hcm := (hcert.1) h9
        calc c m * 137 ^ (y + 2) * 10000
            = (c m * 18769) * (137 ^ y * 10000) := by ring
          _ ≤ (c (4 * m % 243) * 10000) * (137 ^ y * 10000) :=
              Nat.mul_le_mul_right _ hcm
          _ = (c (4 * m % 243) * 137 ^ y * 10000) * 10000 := by ring
          _ ≤ (phi 5 (4 * m % 243) y * (25220 * 100 ^ y * 18769)) * 10000 :=
              Nat.mul_le_mul_right _ ih4
          _ = phi 5 (4 * m % 243) y * (25220 * 100 ^ (y + 2) * 18769) := by
              ring
          _ ≤ phi 5 m (y + 2) * (25220 * 100 ^ (y + 2) * 18769) :=
              Nat.mul_le_mul_right _ hrec
      · -- branching case m ≡ 8 (mod 9)
        have hrec := phi_rec_eight (k := 5) (m := m) (y := y)
          (by norm_num) h9 hne
        have hw : (2 * m - 1) % 243 / 3 < 81 := by
          have : (2 * m - 1) % 243 < 243 := Nat.mod_lt _ (by norm_num)
          omega
        have hw3 : ((2 * m - 1) % 243 / 3) % 3 = 2 := by omega
        set w := (2 * m - 1) % 243 / 3 with hwdef
        have ihw1 := ih (y + 1) (by omega) w (by omega) hw3
        have ihw2 := ih (y + 1) (by omega) (w + 81) (by omega) (by omega)
        have ihw3 := ih (y + 1) (by omega) (w + 162) (by omega) (by omega)
        have hmin : cbar w * 137 ^ (y + 1) * 10000 ≤
            phiMin 5 w (y + 1) * (25220 * 100 ^ (y + 1) * 18769) := by
          unfold cbar phiMin
          have e81 : (3 : ℕ) ^ (5 - 1) = 81 := by norm_num
          rw [e81, show (2 * 81 : ℕ) = 162 by norm_num]
          have key := min3_mul_bound
            (E := 137 ^ (y + 1) * 10000)
            (D := 25220 * 100 ^ (y + 1) * 18769)
            (by calc K5.c w * (137 ^ (y + 1) * 10000)
                  = K5.c w * 137 ^ (y + 1) * 10000 := by ring
                _ ≤ _ := ihw1)
            (by calc K5.c (w + 81) * (137 ^ (y + 1) * 10000)
                  = K5.c (w + 81) * 137 ^ (y + 1) * 10000 := by ring
                _ ≤ _ := ihw2)
            (by calc K5.c (w + 162) * (137 ^ (y + 1) * 10000)
                  = K5.c (w + 162) * 137 ^ (y + 1) * 10000 := by ring
                _ ≤ _ := ihw3)
          calc min (K5.c w) (min (K5.c (w + 81)) (K5.c (w + 162))) *
                137 ^ (y + 1) * 10000
              = min (K5.c w) (min (K5.c (w + 81)) (K5.c (w + 162))) *
                (137 ^ (y + 1) * 10000) := by ring
            _ ≤ _ := key
        have hcm := (hcert.2.2) h9
        calc c m * 137 ^ (y + 2) * 10000
            = (c m * 18769) * (137 ^ y * 10000) := by ring
          _ ≤ (c (4 * m % 243) * 10000 + cbar w * 13700) *
              (137 ^ y * 10000) := Nat.mul_le_mul_right _ hcm
          _ = (c (4 * m % 243) * 137 ^ y * 10000) * 10000 +
              (cbar w * 137 ^ (y + 1) * 10000) * 100 := by ring
          _ ≤ (phi 5 (4 * m % 243) y * (25220 * 100 ^ y * 18769)) * 10000 +
              (phiMin 5 w (y + 1) * (25220 * 100 ^ (y + 1) * 18769)) * 100 :=
              Nat.add_le_add (Nat.mul_le_mul_right _ ih4)
                (Nat.mul_le_mul_right _ hmin)
          _ = (phi 5 (4 * m % 243) y + phiMin 5 w (y + 1)) *
              (25220 * 100 ^ (y + 2) * 18769) := by ring
          _ ≤ phi 5 m (y + 2) * (25220 * 100 ^ (y + 2) * 18769) := by
              apply Nat.mul_le_mul_right
              exact hrec

end K5

/-! ## The machine-verified density bound -/

theorem terras_iter_three_eight : terras_iter 3 8 = 1 := by
  show terras_iter 2 (terras 8) = 1
  rw [terras_eight]
  show terras_iter 1 (terras 4) = 1
  rw [terras_four]
  show terras 2 = 1
  exact terras_two

/-- The number of n < N whose Terras orbit reaches 1. -/
noncomputable def reachesOneCount (N : ℕ) : ℕ :=
  (@Finset.filter _ (fun n => ∃ t, terras_iter t n = 1)
    (Classical.decPred _) (Finset.range N)).card

/-- THE THEOREM. For every y, the number of integers n ≤ 8·2^y whose
    Terras orbit reaches 1 is at least (14684/473354180)·(137/100)^y;
    on the dyadic grid x = 8·2^y this is Ω(x^γ) with
    γ = log₂(1.37) = 0.4543… — the first machine-verified density
    exponent for the 3x+1 problem. -/
theorem density_lower_bound (y : ℕ) :
    14684 * 137 ^ y * 10000 ≤
      reachesOneCount (8 * 2 ^ y + 1) * (25220 * 100 ^ y * 18769) := by
  classical
  -- 8 is a root of class 8 mod 243
  have h8root : (8 : ℕ) ∈ Roots 5 8 := ⟨by norm_num, by norm_num, ⟨0, rfl⟩⟩
  -- phi at class 8 is bounded by the capped tree count of root 8
  have hphi : phi 5 8 y ≤ cnt 8 (2 ^ y * 8) := phi_le h8root
  -- every member of the capped tree of 8 reaches 1
  have hsub : treeSet 8 (2 ^ y * 8)
      ⊆ @Finset.filter _ (fun n => ∃ t, terras_iter t n = 1)
        (Classical.decPred _) (Finset.range (8 * 2 ^ y + 1)) := by
    intro n hn
    rw [mem_treeSet] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    obtain ⟨j, hj, _⟩ := hn.2
    constructor
    · omega
    · exact ⟨j + 3, by rw [← terras_iter_add, hj, terras_iter_three_eight]⟩
  have hcnt : cnt 8 (2 ^ y * 8) ≤ reachesOneCount (8 * 2 ^ y + 1) := by
    unfold reachesOneCount cnt
    exact Finset.card_le_card hsub
  -- the certificate growth at class 8 (c 8 = 14684)
  have hgrow := K5.growth y 8 (by norm_num) (by norm_num)
  have hc8 : K5.c 8 = 14684 := by norm_num [K5.c, K5.certList]
  rw [hc8] at hgrow
  calc 14684 * 137 ^ y * 10000
      ≤ phi 5 8 y * (25220 * 100 ^ y * 18769) := hgrow
    _ ≤ cnt 8 (2 ^ y * 8) * (25220 * 100 ^ y * 18769) :=
        Nat.mul_le_mul_right _ hphi
    _ ≤ reachesOneCount (8 * 2 ^ y + 1) * (25220 * 100 ^ y * 18769) :=
        Nat.mul_le_mul_right _ hcnt

/-!
## What this means

`density_lower_bound` states, in pure natural-number arithmetic with
explicit constants, that

    #{n ≤ 8·2^y : n reaches 1}  ≥  (14684·10⁴ / (25220·18769)) · 1.37^y
                                ≈  0.31 · 1.37^y ,

i.e. π₁(x) = Ω(x^0.4543) along x = 8·2^y (and for all x by
monotonicity, up to the constant). The exponent log₂(137/100) exceeds
Krasikov's 1989 bound x^0.43 — every published lower bound before
Applegate–Lagarias 1995 — and every step of the argument, from the
backward-tree combinatorics to the 81-class certificate, is checked by
the Lean kernel. The certificate method scales: larger moduli 3^k and
the finer grids of Krasikov–Lagarias (2003) give exponents up to 0.895
(see the companion paper), awaiting the same treatment.
-/

end Collatz
