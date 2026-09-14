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
# IMO 1999 Problem 2

Let `n ≥ 2` be a fixed integer.

* (a) Find the least constant `C` such that for all nonnegative reals `x 1, …, x n`,
  `∑_{i < j} x i * x j * (x i ^ 2 + x j ^ 2) ≤ C * (∑ i, x i) ^ 4`.
* (b) Determine when equality occurs for this value of `C`.

The answer to (a) is `C = 1 / 8`, and equality in (b) holds exactly when two of the `x i`
are equal to each other and all the other `x i` are zero.
-/

namespace Imo1999P2

open Finset

variable {n : ℕ}

/-- The sum of the squares of the coordinates. -/
noncomputable def sumSq (x : Fin n → ℝ) : ℝ := ∑ k, x k ^ 2

/-- The sum of the pairwise products `x i * x j` over `i < j`. -/
noncomputable def pairSum (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j

/-- The left-hand side of the problem: `∑_{i < j} x i * x j * (x i ^ 2 + x j ^ 2)`. -/
noncomputable def lhsSum (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * (x i ^ 2 + x j ^ 2)

/-- A symmetric double sum splits into its diagonal plus twice its strict upper triangle. -/
theorem sum_sum_symm (g : Fin n → Fin n → ℝ) (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j, g i j = ∑ i, g i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
  have hsplit : ∀ i : Fin n, ∑ j, g i j
      = ∑ j ∈ Finset.Iio i, g i j + (∑ j ∈ Finset.Ioi i, g i j + g i i) := by
    intro i
    rw [Finset.sum_Ioi_add_eq_sum_Ici,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j < i)]
    congr 1
    · congr 1; ext j; simp
    · congr 1; ext j; simp [not_lt]
  have hswap : ∑ i, ∑ j ∈ Finset.Iio i, g i j = ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.Ioi j)
      (by intro x y; simp [Finset.mem_Iio, Finset.mem_Ioi])]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hg j i
  simp_rw [hsplit, Finset.sum_add_distrib, hswap]
  ring

/-- The square of the sum equals the sum of squares plus twice the sum of the pairwise
products. -/
theorem sq_sum_eq (x : Fin n → ℝ) :
    (∑ i, x i) ^ 2 = sumSq x + 2 * pairSum x := by
  have h := sum_sum_symm (fun i j => x i * x j) (fun i j => mul_comm _ _)
  have h2 : (∑ i, x i) ^ 2 = ∑ i : Fin n, ∑ j : Fin n, x i * x j := by
    rw [sq, Finset.sum_mul_sum]
  rw [h2, h, sumSq, pairSum]
  simp [sq]

/-- Two distinct coordinates contribute at most the whole sum of squares. -/
theorem two_sq_le_sumSq (x : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    x i ^ 2 + x j ^ 2 ≤ sumSq x := by
  calc x i ^ 2 + x j ^ 2 = ∑ k ∈ ({i, j} : Finset (Fin n)), x k ^ 2 :=
        (Finset.sum_pair (f := fun k => x k ^ 2) hij).symm
    _ ≤ sumSq x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ => sq_nonneg (x k))

/-- Rewriting of `sumSq x * pairSum x` as a double sum. -/
theorem sumSq_mul_pairSum (x : Fin n → ℝ) :
    sumSq x * pairSum x = ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * sumSq x := by
  rw [pairSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The main termwise estimate: `lhsSum x ≤ sumSq x * pairSum x`. -/
theorem lhsSum_le_mul (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    lhsSum x ≤ sumSq x * pairSum x := by
  rw [sumSq_mul_pairSum, lhsSum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  exact mul_le_mul_of_nonneg_left (two_sq_le_sumSq x hij) (mul_nonneg (hx i) (hx j))

/-- The inequality of part (a). -/
theorem lhsSum_le (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    lhsSum x ≤ (1 / 8) * (∑ i, x i) ^ 4 := by
  have hsq : (∑ i, x i) ^ 2 = sumSq x + 2 * pairSum x := sq_sum_eq x
  have h4 : (∑ i, x i) ^ 4 = (sumSq x + 2 * pairSum x) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  have hT := lhsSum_le_mul x hx
  rw [h4]
  nlinarith [sq_nonneg (sumSq x - 2 * pairSum x)]

/-- When equality holds in `lhsSum_le_mul`, each of the nonnegative defect terms vanishes. -/
theorem defect_zero (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (heq : lhsSum x = sumSq x * pairSum x) {i j : Fin n} (hij : i < j) :
    x i * x j * (sumSq x - x i ^ 2 - x j ^ 2) = 0 := by
  have hterm : ∀ i : Fin n, ∀ j ∈ Finset.Ioi i,
      0 ≤ x i * x j * sumSq x - x i * x j * (x i ^ 2 + x j ^ 2) := by
    intro i j hj
    have hij' : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    have hnn : 0 ≤ x i * x j := mul_nonneg (hx i) (hx j)
    have := mul_le_mul_of_nonneg_left (two_sq_le_sumSq x hij') hnn
    linarith
  have hzero : ∑ i, ∑ j ∈ Finset.Ioi i,
      (x i * x j * sumSq x - x i * x j * (x i ^ 2 + x j ^ 2)) = 0 := by
    have hrw : ∑ i, ∑ j ∈ Finset.Ioi i,
        (x i * x j * sumSq x - x i * x j * (x i ^ 2 + x j ^ 2))
        = sumSq x * pairSum x - lhsSum x := by
      rw [sumSq_mul_pairSum, lhsSum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_sub_distrib _ _
    rw [hrw, heq, sub_self]
  have hrow : ∑ j ∈ Finset.Ioi i,
      (x i * x j * sumSq x - x i * x j * (x i ^ 2 + x j ^ 2)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (hterm i))).mp hzero i (Finset.mem_univ i)
  have hij' := (Finset.sum_eq_zero_iff_of_nonneg (hterm i)).mp hrow j (Finset.mem_Ioi.mpr hij)
  linarith

/-- If equality holds in `lhsSum_le_mul`, then at most two of the `x i` are nonzero. -/
theorem support_small (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (heq : lhsSum x = sumSq x * pairSum x)
    {i j : Fin n} (hij : i < j) (hi : x i ≠ 0) (hj : x j ≠ 0) {k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) : x k = 0 := by
  have h := defect_zero x hx heq hij
  have hzero : sumSq x - x i ^ 2 - x j ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (mul_ne_zero hi hj)
    · exact h1
  have hne : i ≠ j := ne_of_lt hij
  have hcard : ∑ l ∈ ({i, j, k} : Finset (Fin n)), x l ^ 2 = x i ^ 2 + x j ^ 2 + x k ^ 2 := by
    rw [Finset.sum_insert (by simp [hne, Ne.symm hki]), Finset.sum_pair (Ne.symm hkj)]
    ring
  have hle : x i ^ 2 + x j ^ 2 + x k ^ 2 ≤ sumSq x := by
    rw [← hcard]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun l _ _ => sq_nonneg (x l))
  have hk2 : x k ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hk2

/-- Two distinct indices always exist when `2 ≤ n`. -/
theorem exists_ne_index (hn : 2 ≤ n) : ∃ a b : Fin n, a ≠ b := by
  have hcard : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  obtain ⟨a⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hcard a
  exact ⟨a, b, (Ne.symm hb)⟩

/-- If equality holds in `lhsSum_le_mul`, there are two distinct indices outside which
`x` vanishes. -/
theorem exists_pair_support (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (heq : lhsSum x = sumSq x * pairSum x) :
    ∃ a b : Fin n, a ≠ b ∧ ∀ k, k ≠ a → k ≠ b → x k = 0 := by
  have hcard : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  by_cases hex : ∃ i j : Fin n, i < j ∧ x i ≠ 0 ∧ x j ≠ 0
  · obtain ⟨i, j, hij, hi, hj⟩ := hex
    exact ⟨i, j, ne_of_lt hij, fun k hki hkj => support_small x hx heq hij hi hj hki hkj⟩
  · push Not at hex
    by_cases hc : ∃ c : Fin n, x c ≠ 0
    · obtain ⟨c, hcne⟩ := hc
      obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hcard c
      refine ⟨c, b, (Ne.symm hb), fun k hkc _ => ?_⟩
      by_contra hk
      rcases lt_trichotomy k c with h | h | h
      · exact hcne (hex k c h hk)
      · exact hkc h
      · exact hk (hex c k h hcne)
    · push Not at hc
      obtain ⟨a, b, hab⟩ := exists_ne_index hn
      exact ⟨a, b, hab, fun k _ _ => hc k⟩

/-- If `x` vanishes outside `{a, b}`, the sum of squares is `x a ^ 2 + x b ^ 2`. -/
theorem sumSq_of_support (x : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b)
    (hsupp : ∀ k, k ≠ a → k ≠ b → x k = 0) : sumSq x = x a ^ 2 + x b ^ 2 := by
  rw [sumSq, ← Finset.sum_pair (f := fun k => x k ^ 2) hab]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro k _ hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rw [hsupp k hk.1 hk.2]
  ring

/-- If `x` vanishes outside `{a, b}`, the sum is `x a + x b`. -/
theorem sum_of_support (x : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b)
    (hsupp : ∀ k, k ≠ a → k ≠ b → x k = 0) : ∑ k, x k = x a + x b := by
  rw [← Finset.sum_pair (f := fun k => x k) hab]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro k _ hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact hsupp k hk.1 hk.2

/-- If `x` vanishes outside `{a, b}` and `x a = x b`, then equality holds in
`lhsSum_le_mul`. -/
theorem lhsSum_eq_mul_of_support (x : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b)
    (hxab : x a = x b) (hsupp : ∀ k, k ≠ a → k ≠ b → x k = 0) :
    lhsSum x = sumSq x * pairSum x := by
  have hp : sumSq x = x a ^ 2 + x b ^ 2 := sumSq_of_support x hab hsupp
  rw [lhsSum, sumSq_mul_pairSum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  rcases eq_or_ne (x i * x j) 0 with h0 | h0
  · rw [h0]; ring
  · have hi : x i ≠ 0 := fun h => h0 (by rw [h]; ring)
    have hj' : x j ≠ 0 := fun h => h0 (by rw [h]; ring)
    have hia : i = a ∨ i = b := by
      by_contra hcon
      push Not at hcon
      exact hi (hsupp i hcon.1 hcon.2)
    have hja : j = a ∨ j = b := by
      by_contra hcon
      push Not at hcon
      exact hj' (hsupp j hcon.1 hcon.2)
    have hxi : x i ^ 2 + x j ^ 2 = sumSq x := by
      rw [hp]
      rcases hia with h1 | h1 <;> rcases hja with h2 | h2 <;> subst h1 <;> subst h2 <;>
        rw [hxab]
    rw [hxi]

/-- Part (a): `1 / 8` is the least constant for which the inequality always holds. -/
theorem imo1999_q2 (hn : 2 ≤ n) :
    IsLeast {C : ℝ | ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
      ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) ≤ C * (∑ i, x i) ^ 4}
      (1 / 8) := by
  constructor
  · intro x hx
    exact lhsSum_le x hx
  · intro C hC
    obtain ⟨a, b, hab⟩ := exists_ne_index hn
    set x : Fin n → ℝ := fun k => if k = a ∨ k = b then 1 else 0 with hxdef
    have hxnn : ∀ i, 0 ≤ x i := by
      intro i; simp only [hxdef]; split <;> norm_num
    have hsupp : ∀ k, k ≠ a → k ≠ b → x k = 0 := by
      intro k h1 h2; simp [hxdef, h1, h2]
    have hxa : x a = 1 := by simp [hxdef]
    have hxb : x b = 1 := by simp [hxdef]
    have hsum : ∑ k, x k = 2 := by
      rw [sum_of_support x hab hsupp, hxa, hxb]; norm_num
    have hsq : sumSq x = 2 := by
      rw [sumSq_of_support x hab hsupp, hxa, hxb]; norm_num
    have hpair : pairSum x = 1 := by
      have h := sq_sum_eq x
      rw [hsum, hsq] at h
      linarith
    have hT : lhsSum x = 2 := by
      rw [lhsSum_eq_mul_of_support x hab (by rw [hxa, hxb]) hsupp, hsq, hpair]
      norm_num
    have hCx := hC x hxnn
    rw [show ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) = lhsSum x from rfl,
      hT, hsum] at hCx
    nlinarith [hCx]

/-- Part (b): for `C = 1 / 8`, equality holds exactly when two of the `x i` are equal to
each other and all the others are zero. -/
theorem imo1999_q2_equality (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) = (1 / 8) * (∑ i, x i) ^ 4
      ↔ ∃ a b : Fin n, a ≠ b ∧ x a = x b ∧ ∀ k, k ≠ a → k ≠ b → x k = 0 := by
  rw [show ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) = lhsSum x from rfl]
  have hsq : (∑ i, x i) ^ 2 = sumSq x + 2 * pairSum x := sq_sum_eq x
  have h4 : (∑ i, x i) ^ 4 = (sumSq x + 2 * pairSum x) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  have hTle : lhsSum x ≤ sumSq x * pairSum x := lhsSum_le_mul x hx
  constructor
  · intro heq
    rw [h4] at heq
    have hTPQ : lhsSum x = sumSq x * pairSum x := by
      nlinarith [sq_nonneg (sumSq x - 2 * pairSum x)]
    have hP2Q : sumSq x = 2 * pairSum x := by
      nlinarith [sq_nonneg (sumSq x - 2 * pairSum x)]
    obtain ⟨a, b, hab, hsupp⟩ := exists_pair_support hn x hx hTPQ
    refine ⟨a, b, hab, ?_, hsupp⟩
    have hs : ∑ k, x k = x a + x b := sum_of_support x hab hsupp
    have hp : sumSq x = x a ^ 2 + x b ^ 2 := sumSq_of_support x hab hsupp
    have h2P : 2 * sumSq x = (∑ i, x i) ^ 2 := by rw [hsq, hP2Q]; ring
    rw [hs, hp] at h2P
    nlinarith [sq_nonneg (x a - x b)]
  · rintro ⟨a, b, hab, hxab, hsupp⟩
    have hs : ∑ k, x k = x a + x b := sum_of_support x hab hsupp
    have hp : sumSq x = x a ^ 2 + x b ^ 2 := sumSq_of_support x hab hsupp
    have hP2Q : sumSq x = 2 * pairSum x := by
      have h := hsq
      rw [hs, hp] at h
      rw [hp]
      nlinarith [h, hxab]
    have hTPQ : lhsSum x = sumSq x * pairSum x :=
      lhsSum_eq_mul_of_support x hab hxab hsupp
    rw [h4, hTPQ, hP2Q]
    ring

end Imo1999P2
