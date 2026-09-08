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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Imo1974P6

open Polynomial

/-- If `P(a) = 1` and `P(b) = -1`, then `a` and `b` differ by at most `2`:
indeed `a - b` divides `P(a) - P(b) = 2`. -/
theorem abs_sub_le_two_of_eval_eq_one_of_eval_eq_neg_one
    (P : Polynomial ℤ) {a b : ℤ} (ha : P.eval a = 1) (hb : P.eval b = -1) :
    |a - b| ≤ 2 := by
  have h : (a - b) ∣ (2 : ℤ) := by
    have := Polynomial.sub_dvd_eval_sub a b P
    rw [ha, hb] at this
    simpa using this
  exact Int.le_of_dvd (by norm_num) ((abs_dvd _ _).mpr h)

/-- The set of integers `k` with `P(k)^2 = 1`, as a `Finset` (for `P` non-constant). -/
noncomputable def solSet (P : Polynomial ℤ) : Finset ℤ :=
  (P - 1).roots.toFinset ∪ (P + 1).roots.toFinset

theorem sub_one_ne_zero {P : Polynomial ℤ} (hP : 0 < P.natDegree) : P - 1 ≠ 0 := by
  intro h
  have : P = 1 := by linear_combination (norm := ring_nf) h
  rw [this] at hP
  simp at hP

theorem add_one_ne_zero {P : Polynomial ℤ} (hP : 0 < P.natDegree) : P + 1 ≠ 0 := by
  intro h
  have : P = -1 := by linear_combination (norm := ring_nf) h
  rw [this] at hP
  simp at hP

theorem mem_solSet_iff {P : Polynomial ℤ} (hP : 0 < P.natDegree) (k : ℤ) :
    k ∈ solSet P ↔ (P.eval k) ^ 2 = 1 := by
  simp only [solSet, Finset.mem_union, Multiset.mem_toFinset,
    Polynomial.mem_roots (sub_one_ne_zero hP), Polynomial.mem_roots (add_one_ne_zero hP),
    Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_one,
    sq_eq_one_iff]
  constructor
  · rintro (h | h) <;> omega
  · rintro (h | h) <;> omega

theorem coe_solSet {P : Polynomial ℤ} (hP : 0 < P.natDegree) :
    ↑(solSet P) = {k : ℤ | (P.eval k) ^ 2 = 1} := by
  ext k; simpa using mem_solSet_iff hP k

theorem eval_eq_one_or_neg_one_of_mem {P : Polynomial ℤ} (hP : 0 < P.natDegree) {k : ℤ}
    (hk : k ∈ solSet P) : P.eval k = 1 ∨ P.eval k = -1 :=
  sq_eq_one_iff.mp ((mem_solSet_iff hP k).mp hk)

theorem card_roots_toFinset_le (Q : Polynomial ℤ) : Q.roots.toFinset.card ≤ Q.natDegree :=
  le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' Q)

theorem natDegree_sub_one (P : Polynomial ℤ) : (P - 1).natDegree = P.natDegree := by
  simpa using Polynomial.natDegree_sub_C (p := P) (a := (1 : ℤ))

theorem natDegree_add_one (P : Polynomial ℤ) : (P + 1).natDegree = P.natDegree := by
  simpa using Polynomial.natDegree_add_C (p := P) (a := (1 : ℤ))

/-- Crude bound: `|S| ≤ 2 * deg P`. -/
theorem card_solSet_le_two_mul (P : Polynomial ℤ) :
    (solSet P).card ≤ 2 * P.natDegree := by
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := card_roots_toFinset_le (P - 1)
  have h2 := card_roots_toFinset_le (P + 1)
  rw [natDegree_sub_one] at h1
  rw [natDegree_add_one] at h2
  omega

/-- If `P` never takes the value `-1` on the integers, then `|S| ≤ deg P`. -/
theorem card_solSet_le_of_no_neg_one {P : Polynomial ℤ} (hP : 0 < P.natDegree)
    (h : ∀ k : ℤ, P.eval k ≠ -1) : (solSet P).card ≤ P.natDegree := by
  have hsub : solSet P ⊆ (P - 1).roots.toFinset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx' | hx'
    · exact hx'
    · exfalso
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (add_one_ne_zero hP)] at hx'
      have := hx'
      simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_one] at this
      exact h x (by omega)
  refine le_trans (Finset.card_le_card hsub) ?_
  simpa [natDegree_sub_one] using card_roots_toFinset_le (P - 1)

/-- If `P` never takes the value `1` on the integers, then `|S| ≤ deg P`. -/
theorem card_solSet_le_of_no_one {P : Polynomial ℤ} (hP : 0 < P.natDegree)
    (h : ∀ k : ℤ, P.eval k ≠ 1) : (solSet P).card ≤ P.natDegree := by
  have hsub : solSet P ⊆ (P + 1).roots.toFinset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx' | hx'
    · exfalso
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (sub_one_ne_zero hP)] at hx'
      have := hx'
      simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_one] at this
      exact h x (by omega)
    · exact hx'
  refine le_trans (Finset.card_le_card hsub) ?_
  simpa [natDegree_add_one] using card_roots_toFinset_le (P + 1)

/-- If `P` takes both the values `1` and `-1` on the integers, then `|S| ≤ 5`:
the smallest and the largest solution would otherwise be more than `4` apart,
which is impossible since both are within distance `2` of a point where `P` takes
the opposite value. -/
theorem card_solSet_le_five {P : Polynomial ℤ} (hP : 0 < P.natDegree)
    {a b : ℤ} (ha : P.eval a = 1) (hb : P.eval b = -1) :
    (solSet P).card ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  have hne : (solSet P).Nonempty := Finset.card_pos.mp (by omega)
  set m := (solSet P).min' hne with hm
  set M := (solSet P).max' hne with hM
  have hmmem : m ∈ solSet P := Finset.min'_mem _ _
  have hMmem : M ∈ solSet P := Finset.max'_mem _ _
  have hsub : solSet P ⊆ Finset.Icc m M := fun x hx =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hgap : 5 ≤ M - m := by omega
  have key : ∀ x y : ℤ, P.eval x = 1 → P.eval y = -1 → -2 ≤ x - y ∧ x - y ≤ 2 := by
    intro x y hx hy
    exact abs_le.mp (abs_sub_le_two_of_eval_eq_one_of_eval_eq_neg_one P hx hy)
  rcases eval_eq_one_or_neg_one_of_mem hP hmmem with h1 | h1 <;>
    rcases eval_eq_one_or_neg_one_of_mem hP hMmem with h2 | h2
  · have k1 := key m b h1 hb
    have k2 := key M b h2 hb
    omega
  · have k := key m M h1 h2
    omega
  · have k := key M m h2 h1
    omega
  · have k1 := key a m ha h1
    have k2 := key a M ha h2
    omega

/-- **IMO 1974, Problem 6.**  Let `P` be a non-constant polynomial with integer
coefficients and let `n(P)` be the number of distinct integers `k` with `P(k)^2 = 1`.
Then `n(P) ≤ deg(P) + 2`. -/
theorem imo1974_p6 (P : Polynomial ℤ) (hP : 0 < P.natDegree) :
    {k : ℤ | (P.eval k) ^ 2 = 1}.ncard ≤ P.natDegree + 2 := by
  rw [← coe_solSet hP, Set.ncard_coe_finset]
  by_cases h1 : ∃ a : ℤ, P.eval a = 1
  · by_cases h2 : ∃ b : ℤ, P.eval b = -1
    · obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      rcases Nat.lt_or_ge P.natDegree 3 with hd | hd
      · exact le_trans (card_solSet_le_two_mul P) (by omega)
      · exact le_trans (card_solSet_le_five hP ha hb) (by omega)
    · push_neg at h2
      exact le_trans (card_solSet_le_of_no_neg_one hP h2) (by omega)
  · push_neg at h1
    exact le_trans (card_solSet_le_of_no_one hP h1) (by omega)

end Imo1974P6
