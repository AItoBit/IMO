import Mathlib

/-!
# IMO 1959 Q2

For what real values of $x$ is

$\sqrt{x+\sqrt{2x-1}} + \sqrt{x-\sqrt{2x-1}} = A,$

given (a) $A=\sqrt{2}$, (b) $A=1$, (c) $A=2$,
where only non-negative real numbers are admitted for square roots?

We encode the equation as a predicate saying both that the equation holds
and that all arguments of square roots are nonnegative.

The key step is to rewrite the equation as
$\sqrt{2x-1}+1+|\sqrt{2x-1}-1| = A\sqrt{2}$,
and then to consider the cases $\sqrt{2x-1}\le 1$ and $1 < \sqrt{2x-1}$ separately.

The answers are: (a) $x \in [1/2, 1]$, (b) no solutions, (c) $x = 3/2$.
-/

open Set Real

namespace Imo1959Q2

/-- The equation of the problem, together with the requirement that only non-negative reals
appear under the square roots. -/
def IsGood (x A : ℝ) : Prop :=
  √(x + √(2 * x - 1)) + √(x - √(2 * x - 1)) = A ∧ 0 ≤ 2 * x - 1 ∧
    0 ≤ x + √(2 * x - 1) ∧ 0 ≤ x - √(2 * x - 1)

variable {x A : ℝ}

theorem isGood_iff : IsGood x A ↔
    √(2 * x - 1) + 1 + |√(2 * x - 1) - 1| = A * √2 ∧ 1 / 2 ≤ x := by
  cases le_or_gt (1 / 2) x with
  | inl hx =>
    have hx' : 0 ≤ 2 * x - 1 := by linarith
    have h₁ : x + √(2 * x - 1) = (√(2 * x - 1) + 1) ^ 2 / 2 := by
      rw [add_sq, sq_sqrt hx']; ring
    have h₂ : x - √(2 * x - 1) = (√(2 * x - 1) - 1) ^ 2 / 2 := by
      rw [sub_sq, sq_sqrt hx']; ring
    simp only [IsGood, *, div_nonneg (sq_nonneg _) (zero_le_two (α := ℝ)), sqrt_div (sq_nonneg _),
      and_true]
    rw [sqrt_sq, sqrt_sq_eq_abs] <;> [skip; positivity]
    field_simp
  | inr hx =>
    have : 2 * x - 1 < 0 := by linarith
    simp only [IsGood, this.not_ge, hx.not_ge]; simp

theorem IsGood.one_half_le (h : IsGood x A) : 1 / 2 ≤ x := (isGood_iff.1 h).2

theorem sqrt_two_mul_sub_one_le_one : √(2 * x - 1) ≤ 1 ↔ x ≤ 1 := by
  simp [sqrt_le_iff, ← two_mul]

theorem isGood_iff_eq_sqrt_two (hx : x ∈ Icc (1 / 2) 1) : IsGood x A ↔ A = √2 := by
  have : √(2 * x - 1) ≤ 1 := sqrt_two_mul_sub_one_le_one.2 hx.2
  simp only [isGood_iff, hx.1, abs_sub_comm _ (1 : ℝ), abs_of_nonneg (sub_nonneg.2 this), and_true]
  suffices 2 = A * √2 ↔ A = √2 by convert this; ring
  rw [← div_eq_iff, div_sqrt, eq_comm]
  positivity

theorem isGood_iff_eq_sqrt (hx : 1 < x) : IsGood x A ↔ A = √(4 * x - 2) := by
  have h₁ : 1 < √(2 * x - 1) := by simpa only [← not_le, sqrt_two_mul_sub_one_le_one] using hx
  have h₂ : 1 / 2 ≤ x := by linarith
  simp only [isGood_iff, h₂, abs_of_pos (sub_pos.2 h₁), add_add_sub_cancel, and_true]
  rw [← mul_two, ← div_eq_iff (by positivity), mul_div_assoc, div_sqrt, ← sqrt_mul' _ zero_le_two,
    eq_comm]
  ring_nf

theorem IsGood.sqrt_two_lt_of_one_lt (h : IsGood x A) (hx : 1 < x) : √2 < A := by
  rw [(isGood_iff_eq_sqrt hx).1 h]
  refine sqrt_lt_sqrt zero_le_two ?_
  linarith

theorem IsGood.eq_sqrt_two_iff_le_one (h : IsGood x A) : A = √2 ↔ x ≤ 1 :=
  ⟨fun hA ↦ not_lt.1 fun hx ↦ (h.sqrt_two_lt_of_one_lt hx).ne' hA, fun hx ↦
    (isGood_iff_eq_sqrt_two ⟨h.one_half_le, hx⟩).1 h⟩

theorem IsGood.sqrt_two_lt_iff_one_lt (h : IsGood x A) : √2 < A ↔ 1 < x :=
  ⟨fun hA ↦ not_le.1 fun hx ↦ hA.ne' <| h.eq_sqrt_two_iff_le_one.2 hx, h.sqrt_two_lt_of_one_lt⟩

theorem IsGood.sqrt_two_le (h : IsGood x A) : √2 ≤ A :=
  (le_or_gt x 1).elim (fun hx ↦ (h.eq_sqrt_two_iff_le_one.2 hx).ge) fun hx ↦
    (h.sqrt_two_lt_of_one_lt hx).le

theorem isGood_iff_of_sqrt_two_lt (hA : √2 < A) : IsGood x A ↔ x = (A / 2) ^ 2 + 1 / 2 := by
  have : 0 < A := lt_trans (by simp) hA
  constructor
  · intro h
    have hx : 1 < x := by rwa [h.sqrt_two_lt_iff_one_lt] at hA
    rw [isGood_iff_eq_sqrt hx, eq_comm, sqrt_eq_iff_eq_sq] at h <;> linarith
  · rintro rfl
    rw [isGood_iff_eq_sqrt]
    · conv_lhs => rw [← sqrt_sq this.le]
      ring_nf
    · rw [sqrt_lt' this] at hA
      linarith

theorem isGood_sqrt2_iff : IsGood x (√2) ↔ x ∈ Icc (1 / 2) 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (isGood_iff_eq_sqrt_two h).2 rfl⟩
  exact ⟨h.one_half_le, not_lt.1 fun h₁ ↦ (h.sqrt_two_lt_of_one_lt h₁).false⟩

theorem not_isGood_one : ¬IsGood x 1 := fun h ↦
  h.sqrt_two_le.not_gt <| (lt_sqrt zero_le_one).2 (by simp)

theorem isGood_two_iff : IsGood x 2 ↔ x = 3 / 2 :=
  (isGood_iff_of_sqrt_two_lt <| (sqrt_lt' two_pos).2 (by norm_num)).trans <| by norm_num

/-- The membership condition used in the statement of the problem is exactly `IsGood`. -/
theorem mem_setOf_iff_isGood :
    (0 ≤ 2 * x - 1 ∧ 0 ≤ x + √(2 * x - 1) ∧ 0 ≤ x - √(2 * x - 1) ∧
      √(x + √(2 * x - 1)) + √(x - √(2 * x - 1)) = A) ↔ IsGood x A := by
  unfold IsGood; tauto

end Imo1959Q2

open Imo1959Q2

/-- For what real values of $x$ is $\sqrt{x+\sqrt{2x-1}}+\sqrt{x-\sqrt{2x-1}}=A$
given (a) $A=\sqrt{2}$; (b) $A=1$; (c) $A=2$, where only non-negative real numbers are
admitted for square roots?

Answer: (a) $1/2 \le x \le 1$; (b) no solutions; (c) $x = 3/2$. -/
theorem imo_1959_p2.parts.a :
    {x : ℝ | 0 ≤ 2 * x - 1 ∧ 0 ≤ x + √(2 * x - 1) ∧
      0 ≤ x - √(2 * x - 1) ∧ √(x + √(2 * x - 1)) +
      √(x - √(2 * x - 1)) = √2} =
    Set.Icc (1 / 2) 1 := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_setOf_iff_isGood]
  exact isGood_sqrt2_iff

/-- Part (b): with $A = 1$ there are no solutions. -/
theorem imo_1959_p2.parts.b :
    {x : ℝ | 0 ≤ 2 * x - 1 ∧ 0 ≤ x + √(2 * x - 1) ∧
      0 ≤ x - √(2 * x - 1) ∧ √(x + √(2 * x - 1)) +
      √(x - √(2 * x - 1)) = 1} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_setOf_iff_isGood, Set.mem_empty_iff_false, iff_false]
  exact not_isGood_one

/-- Part (c): with $A = 2$ the unique solution is $x = 3/2$. -/
theorem imo_1959_p2.parts.c :
    {x : ℝ | 0 ≤ 2 * x - 1 ∧ 0 ≤ x + √(2 * x - 1) ∧
      0 ≤ x - √(2 * x - 1) ∧ √(x + √(2 * x - 1)) +
      √(x - √(2 * x - 1)) = 2} = {3 / 2} := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_setOf_iff_isGood, Set.mem_singleton_iff]
  exact isGood_two_iff

/-- The three parts combined. -/
theorem imo_1959_p2 (A : ℝ) (S)
    (hS : S = {x : ℝ | 0 ≤ 2 * x - 1 ∧ 0 ≤ x + √(2 * x - 1) ∧
      0 ≤ x - √(2 * x - 1) ∧ √(x + √(2 * x - 1)) +
      √(x - √(2 * x - 1)) = A}) :
    (A = √2 → S = Set.Icc (1 / 2) 1) ∧ (A = 1 → S = ∅) ∧ (A = 2 → S = {3 / 2}) := by
  subst hS
  refine ⟨fun hA ↦ ?_, fun hA ↦ ?_, fun hA ↦ ?_⟩ <;> subst hA
  · exact imo_1959_p2.parts.a
  · exact imo_1959_p2.parts.b
  · exact imo_1959_p2.parts.c
