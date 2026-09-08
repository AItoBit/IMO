import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# IMO 1976 Problem 2

Let `P₁(x) = x² - 2` and `P_j(x) = P₁(P_{j-1}(x))` for `j = 2, 3, …`.  We show that for any
positive integer `n` the roots of the equation `P_n(x) = x` are real and distinct: the real
polynomial `P_n - X` has degree `2 ^ n`, its multiset of real roots has exactly `2 ^ n`
elements (hence all of its complex roots are real), and these roots are pairwise distinct.

The proof follows the substitution `x = 2 cos θ`, under which `P_n(x) = 2 cos (2ⁿ θ)`.  The
`2 ^ n` numbers `2 cos (2π m / (4ⁿ - 1))`, where `m` runs over the multiples `k (2ⁿ + 1)`
(`0 ≤ k < 2ⁿ⁻¹`) and `i (2ⁿ - 1)` (`1 ≤ i ≤ 2ⁿ⁻¹`), are distinct solutions; since the degree is
`2 ^ n` there are no others and all are simple.
-/

namespace IMO1976P2

open Real Polynomial

/-- `P n` is the `n`-fold iterate of `x ↦ x² - 2`; in particular `P 1 = X ^ 2 - 2`. -/
noncomputable def P : ℕ → Polynomial ℝ
  | 0 => Polynomial.X
  | (n + 1) => (P n) ^ 2 - Polynomial.C 2

@[simp] lemma P_zero : P 0 = Polynomial.X := rfl

@[simp] lemma P_succ (n : ℕ) : P (n + 1) = (P n) ^ 2 - Polynomial.C 2 := rfl

lemma P_monic_and_natDegree (n : ℕ) : (P n).Monic ∧ (P n).natDegree = 2 ^ n := by
  induction n with
  | zero => exact ⟨Polynomial.monic_X, by simp⟩
  | succ n ih =>
    obtain ⟨hm, hd⟩ := ih
    have hsq : ((P n) ^ 2).Monic := hm.pow 2
    have hdsq : ((P n) ^ 2).natDegree = 2 ^ (n + 1) := by
      rw [Polynomial.natDegree_pow, hd]; ring
    have hpos : 0 < ((P n) ^ 2).natDegree := by rw [hdsq]; positivity
    have hlt : (Polynomial.C (2:ℝ)).degree < ((P n) ^ 2).degree :=
      lt_of_le_of_lt Polynomial.degree_C_le (Polynomial.natDegree_pos_iff_degree_pos.mp hpos)
    refine ⟨?_, ?_⟩
    · show ((P n) ^ 2 - Polynomial.C 2).Monic
      exact hsq.sub_of_left hlt
    · show ((P n) ^ 2 - Polynomial.C 2).natDegree = 2 ^ (n + 1)
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simpa using hpos), hdsq]

lemma P_monic (n : ℕ) : (P n).Monic := (P_monic_and_natDegree n).1

lemma P_natDegree (n : ℕ) : (P n).natDegree = 2 ^ n := (P_monic_and_natDegree n).2

/-- The key trigonometric identity: `P n (2 cos t) = 2 cos (2ⁿ t)`. -/
lemma P_eval_two_cos (n : ℕ) (t : ℝ) :
    (P n).eval (2 * Real.cos t) = 2 * Real.cos (2 ^ n * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show ((P n) ^ 2 - Polynomial.C 2).eval (2 * Real.cos t) = _
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C, ih]
    rw [show (2:ℝ) ^ (n + 1) * t = 2 * (2 ^ n * t) by ring, Real.cos_two_mul]
    ring

/-- The index of the `k`-th root, as a multiple of `2π / (4ⁿ - 1)`. -/
def rootIdx (n k : ℕ) : ℕ :=
  if k < 2 ^ (n - 1) then k * (2 ^ n + 1) else (k - 2 ^ (n - 1) + 1) * (2 ^ n - 1)

/-- The `k`-th root of `P n (x) = x`, for `k < 2ⁿ`. -/
noncomputable def rootVal (n k : ℕ) : ℝ :=
  2 * Real.cos (2 * π * (rootIdx n k) / (4 ^ n - 1))

lemma four_pow_eq (n : ℕ) : (4:ℝ) ^ n = ((2:ℝ) ^ n) ^ 2 := by
  rw [← pow_mul, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring_nf

lemma four_pow_sub_one_pos (n : ℕ) (hn : 1 ≤ n) : (0:ℝ) < 4 ^ n - 1 := by
  have : (4:ℝ) ^ 1 ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at this ⊢
  linarith

/-- All the indices lie in the lower half of the period, so the corresponding angles lie in
`[0, π]`. -/
lemma rootIdx_bound (n k : ℕ) (hn : 1 ≤ n) (hk : k < 2 ^ n) : 2 * rootIdx n k + 1 ≤ 4 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ht1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have h4 : (4:ℕ) ^ (m + 1) = 4 * (2 ^ m) ^ 2 := by
    rw [show (4:ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul]
    ring_nf
  rw [h2] at hk
  simp only [rootIdx, Nat.add_sub_cancel, h2, h4]
  set t := 2 ^ m
  split_ifs with h
  · nlinarith
  · set i := k - t + 1 with hi
    have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ t := by omega
    have hs1 : (2 * t - 1) + 1 = 2 * t := by omega
    nlinarith

lemma rootIdx_inj (n : ℕ) (hn : 1 ≤ n) {k l : ℕ} (hk : k < 2 ^ n) (hl : l < 2 ^ n)
    (h : rootIdx n k = rootIdx n l) : k = l := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ht1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  simp only [rootIdx, Nat.add_sub_cancel, h2] at h
  rw [h2] at hk hl
  set t := 2 ^ m
  have key : ∀ a b : ℕ, a < t → b < 2 * t → ¬ (b < t) →
      a * (2 * t + 1) = (b - t + 1) * (2 * t - 1) → False := by
    intro a b ha hb hbt heq
    set i := b - t + 1 with hi
    have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ t := by omega
    have hcast : ((2 * t - 1 : ℕ) : ℤ) = 2 * (t:ℤ) - 1 := by omega
    have heq' : (a:ℤ) * (2 * t + 1) = (i:ℤ) * (2 * (t:ℤ) - 1) := by
      have hc := congrArg (fun x : ℕ => (x:ℤ)) heq
      push_cast at hc
      rw [hcast] at hc
      exact hc
    have h3 : (a:ℤ) + i = 2 * (t:ℤ) * ((i:ℤ) - a) := by linear_combination heq'
    have htz : (1:ℤ) ≤ (t:ℤ) := by exact_mod_cast ht1
    have hiz : (1:ℤ) ≤ (i:ℤ) := by exact_mod_cast hi1
    have haz : (0:ℤ) ≤ (a:ℤ) := by positivity
    have hia : (a:ℤ) < i := by nlinarith
    have h5 : (2:ℤ) * t * ((i:ℤ) - a) ≥ 2 * t := by nlinarith
    have h6 : (a:ℤ) + i ≤ 2 * t - 1 := by omega
    linarith
  split_ifs at h with h1 hb2 hb2
  · exact Nat.eq_of_mul_eq_mul_right (by omega) h
  · exact absurd (key k l h1 hl hb2 h) (by simp)
  · exact absurd (key l k hb2 hk h1 h.symm) (by simp)
  · have hpos : (0:ℕ) < 2 * t - 1 := by omega
    have := Nat.eq_of_mul_eq_mul_right hpos h
    omega

lemma angle_mem_Icc (n k : ℕ) (hn : 1 ≤ n) (hk : k < 2 ^ n) :
    2 * π * (rootIdx n k) / (4 ^ n - 1) ∈ Set.Icc (0:ℝ) π := by
  have hD : (0:ℝ) < 4 ^ n - 1 := four_pow_sub_one_pos n hn
  have hb : 2 * ((rootIdx n k : ℕ) : ℝ) + 1 ≤ 4 ^ n := by
    have h := rootIdx_bound n k hn hk
    exact_mod_cast (by exact_mod_cast h : ((2 * rootIdx n k + 1 : ℕ) : ℝ) ≤ ((4 ^ n : ℕ) : ℝ))
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hD]
  nlinarith [Real.pi_pos]

/-- The angles chosen satisfy `cos (2ⁿ θ) = cos θ`. -/
lemma cos_two_pow_mul_angle (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Real.cos (2 ^ n * (2 * π * (rootIdx n k) / (4 ^ n - 1)))
      = Real.cos (2 * π * (rootIdx n k) / (4 ^ n - 1)) := by
  have hD : (0:ℝ) < 4 ^ n - 1 := four_pow_sub_one_pos n hn
  have hu : (4:ℝ) ^ n = ((2:ℝ) ^ n) ^ 2 := four_pow_eq n
  have hu1 : (1:ℝ) < (2:ℝ) ^ n := by
    have h : (2:ℝ) ^ 1 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    norm_num at h
    linarith
  set u : ℝ := (2:ℝ) ^ n with hudef
  have hne : u ^ 2 - 1 ≠ 0 := by nlinarith
  set θ : ℝ := 2 * π * (rootIdx n k) / (4 ^ n - 1) with hθ
  by_cases h : k < 2 ^ (n - 1)
  · have hidx : ((rootIdx n k : ℕ) : ℝ) = (k : ℝ) * (u + 1) := by
      simp only [rootIdx, if_pos h]
      push_cast
      rw [hudef]
    have key : u * θ = θ + (k : ℝ) * (2 * π) := by
      rw [hθ, hidx, hu]
      field_simp
      ring
    rw [key, Real.cos_add_nat_mul_two_pi]
  · have hs : ((2 ^ n - 1 : ℕ) : ℝ) = u - 1 := by
      have h1 : (1:ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
      push_cast [h1]
      rw [hudef]
    have hidx : ((rootIdx n k : ℕ) : ℝ) = ((k - 2 ^ (n - 1) + 1 : ℕ) : ℝ) * (u - 1) := by
      simp only [rootIdx, if_neg h]
      push_cast [hs]
      ring
    set i : ℕ := k - 2 ^ (n - 1) + 1 with hi
    have key : u * θ = -θ + (i : ℝ) * (2 * π) := by
      rw [hθ, hidx, hu]
      field_simp
      ring
    rw [key, Real.cos_add_nat_mul_two_pi, Real.cos_neg]

lemma rootVal_is_root (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    (P n).eval (rootVal n k) = rootVal n k := by
  rw [rootVal, P_eval_two_cos, cos_two_pow_mul_angle n hn k]

lemma rootVal_inj (n : ℕ) (hn : 1 ≤ n) {k l : ℕ} (hk : k < 2 ^ n) (hl : l < 2 ^ n)
    (h : rootVal n k = rootVal n l) : k = l := by
  have hD : (0:ℝ) < 4 ^ n - 1 := four_pow_sub_one_pos n hn
  have hcos : Real.cos (2 * π * (rootIdx n k) / (4 ^ n - 1))
      = Real.cos (2 * π * (rootIdx n l) / (4 ^ n - 1)) := by
    unfold rootVal at h; linarith
  have heq := Real.injOn_cos (angle_mem_Icc n k hn hk) (angle_mem_Icc n l hn hl) hcos
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp at heq
  exact rootIdx_inj n hn hk hl (by exact_mod_cast heq)

lemma natDegree_P_sub_X (n : ℕ) (hn : 1 ≤ n) : (P n - Polynomial.X).natDegree = 2 ^ n := by
  have h1 : (Polynomial.X : Polynomial ℝ).natDegree < (P n).natDegree := by
    rw [Polynomial.natDegree_X, P_natDegree]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1, P_natDegree]

lemma P_sub_X_ne_zero (n : ℕ) (hn : 1 ≤ n) : P n - Polynomial.X ≠ 0 := by
  intro h
  have := natDegree_P_sub_X n hn
  rw [h, Polynomial.natDegree_zero] at this
  have : (0:ℕ) < 2 ^ n := Nat.two_pow_pos n
  omega

/-- **IMO 1976, Problem 2.**  For every positive integer `n` the equation `P n (x) = x` has
exactly `2 ^ n` roots, and they are all real and distinct: the real polynomial `P n - X` has
degree `2 ^ n`, its multiset of real roots has `2 ^ n` elements (so all of its complex roots are
real), and these roots are pairwise distinct. -/
theorem imo1976_p2 (n : ℕ) (hn : 1 ≤ n) :
    (P n - Polynomial.X).natDegree = 2 ^ n ∧
      Multiset.card (P n - Polynomial.X).roots = 2 ^ n ∧
      (P n - Polynomial.X).roots.Nodup := by
  set Q : Polynomial ℝ := P n - Polynomial.X with hQ
  have hQ0 : Q ≠ 0 := P_sub_X_ne_zero n hn
  have hdeg : Q.natDegree = 2 ^ n := natDegree_P_sub_X n hn
  set S : Finset ℝ := (Finset.range (2 ^ n)).image (rootVal n) with hS
  have hcardS : S.card = 2 ^ n := by
    rw [hS, Finset.card_image_of_injOn, Finset.card_range]
    intro k hk l hl hkl
    exact rootVal_inj n hn (Finset.mem_range.mp hk) (Finset.mem_range.mp hl) hkl
  have hsub : S ⊆ Q.roots.toFinset := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ0]
    show Q.eval (rootVal n k) = 0
    rw [hQ, Polynomial.eval_sub, Polynomial.eval_X, rootVal_is_root n hn k, sub_self]
  have h1 : (2:ℕ) ^ n ≤ Q.roots.toFinset.card := by
    rw [← hcardS]; exact Finset.card_le_card hsub
  have h2 : Q.roots.toFinset.card ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
  have h3 : Multiset.card Q.roots ≤ 2 ^ n := hdeg ▸ Polynomial.card_roots' Q
  have hcards : Q.roots.toFinset.card = Multiset.card Q.roots := le_antisymm h2 (by omega)
  exact ⟨hdeg, by omega, Multiset.toFinset_card_eq_card_iff_nodup.mp hcards⟩

/-- Restatement: the set of real solutions of `P n (x) = x` has exactly `2 ^ n` elements. -/
theorem imo1976_p2' (n : ℕ) (hn : 1 ≤ n) :
    {x : ℝ | (P n).eval x = x}.ncard = 2 ^ n := by
  have hQ0 : P n - Polynomial.X ≠ 0 := P_sub_X_ne_zero n hn
  obtain ⟨-, hcard, hnodup⟩ := imo1976_p2 n hn
  have hset : {x : ℝ | (P n).eval x = x} = ((P n - Polynomial.X).roots.toFinset : Set ℝ) := by
    ext x
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hQ0, sub_eq_zero]
  rw [hset, Set.ncard_coe_finset, Multiset.toFinset_card_eq_card_iff_nodup.mpr hnodup, hcard]

end IMO1976P2
