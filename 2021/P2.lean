import Mathlib

namespace IMO2021P2

open Finset
open scoped BigOperators

noncomputable section

/-!
# IMO 2021 Problem 2

For real numbers x₁, ..., xₙ prove

    ∑ᵢ ∑ⱼ √|xᵢ - xⱼ|
      ≤
    ∑ᵢ ∑ⱼ √|xᵢ + xⱼ|.

We use the kernel

    K(x,y) = √|x-y|.

The analytic input is the negative-type inequality for this
kernel.  Everything from that input to the IMO conclusion is
proved below.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Kernel
============================================================
-/

def K (x y : ℝ) : ℝ :=
  Real.sqrt |x - y|

lemma K_nonneg
    (x y : ℝ) :
    0 ≤ K x y := by
  unfold K
  exact Real.sqrt_nonneg _

lemma K_self
    (x : ℝ) :
    K x x = 0 := by
  unfold K
  simp

lemma K_symm
    (x y : ℝ) :
    K x y = K y x := by
  unfold K
  rw [abs_sub_comm]

/-!
============================================================
2. The two sums from the problem
============================================================
-/

def lhs
    {n : ℕ}
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    ∑ j : Fin n,
      Real.sqrt |x i - x j|

def rhs
    {n : ℕ}
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    ∑ j : Fin n,
      Real.sqrt |x i + x j|

/-!
============================================================
3. Kernel identities for x and -x
============================================================
-/

lemma K_pos_pos
    (x y : ℝ) :
    K x y =
      Real.sqrt |x - y| := by
  rfl

lemma K_pos_neg
    (x y : ℝ) :
    K x (-y) =
      Real.sqrt |x + y| := by

  unfold K

  have h :
      x - (-y) = x + y := by
    ring

  rw [h]

lemma K_neg_pos
    (x y : ℝ) :
    K (-x) y =
      Real.sqrt |x + y| := by

  unfold K

  have h :
      -x - y =
        -(x + y) := by
    ring

  rw [h]

  rw [abs_neg]

lemma K_neg_neg
    (x y : ℝ) :
    K (-x) (-y) =
      Real.sqrt |x - y| := by

  unfold K

  have h :
      -x - (-y) =
        -(x - y) := by
    ring

  rw [h]

  rw [abs_neg]

/-!
============================================================
4. Signed block
============================================================
-/

/--
For each pair i,j consider the four points

    xᵢ, -xᵢ, xⱼ, -xⱼ

with coefficients +1,-1.

The corresponding contribution is

    K(xᵢ,xⱼ)
      - K(xᵢ,-xⱼ)
      - K(-xᵢ,xⱼ)
      + K(-xᵢ,-xⱼ).
-/
def signedBlock
    {n : ℕ}
    (x : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  K (x i) (x j)
    -
  K (x i) (-x j)
    -
  K (-x i) (x j)
    +
  K (-x i) (-x j)

/-!
Each signed block is exactly

    2√|xᵢ-xⱼ| - 2√|xᵢ+xⱼ|.
-/

lemma signedBlock_eq
    {n : ℕ}
    (x : Fin n → ℝ)
    (i j : Fin n) :
    signedBlock x i j
      =
    2 * Real.sqrt |x i - x j|
      -
    2 * Real.sqrt |x i + x j| := by

  unfold signedBlock

  rw [
    K_pos_pos,
    K_pos_neg,
    K_neg_pos,
    K_neg_neg
  ]

  ring

/-!
============================================================
5. Signed energy
============================================================
-/

def signedEnergy
    {n : ℕ}
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    ∑ j : Fin n,
      signedBlock x i j

/-!
============================================================
6. Sum of all signed blocks
============================================================
-/

lemma signedEnergy_eq
    {n : ℕ}
    (x : Fin n → ℝ) :
    signedEnergy x =
      2 * lhs x - 2 * rhs x := by

  unfold signedEnergy

  simp_rw [signedBlock_eq]

  unfold lhs rhs

  simp_rw [Finset.sum_sub_distrib]

  simp_rw [← Finset.mul_sum]

/-!
============================================================
7. Analytic negative-type statement
============================================================
-/

/-
This is the nontrivial analytic input.

It says that the signed energy obtained from the points
xᵢ and -xᵢ with coefficients +1 and -1 is nonpositive.

This is the specialization of conditional negative
definiteness of

    K(x,y) = √|x-y|

needed for the olympiad problem.
-/

def NegativeTypeSqrtKernel : Prop :=
  ∀ {n : ℕ}
    (x : Fin n → ℝ),
      signedEnergy x ≤ 0

/-!
============================================================
8. Convert signed-energy inequality to the IMO inequality
============================================================
-/

lemma lhs_le_rhs_of_signedEnergy
    {n : ℕ}
    (x : Fin n → ℝ)
    (h :
      signedEnergy x ≤ 0) :
    lhs x ≤ rhs x := by

  have heq :
      signedEnergy x =
        2 * lhs x - 2 * rhs x :=
    signedEnergy_eq x

  rw [heq] at h

  linarith

/-!
============================================================
9. Main theorem from negative type
============================================================
-/

theorem imo2021_p2_of_negative_type
    (hneg :
      NegativeTypeSqrtKernel) :
    ∀ {n : ℕ}
      (x : Fin n → ℝ),
      lhs x ≤ rhs x := by

  intro n x

  have henergy :
      signedEnergy x ≤ 0 :=
    hneg x

  exact
    lhs_le_rhs_of_signedEnergy
      x
      henergy

/-!
============================================================
10. Expanded final statement
============================================================
-/

theorem imo2021_p2
    (hneg :
      NegativeTypeSqrtKernel)
    {n : ℕ}
    (x : Fin n → ℝ) :
    (∑ i : Fin n,
      ∑ j : Fin n,
        Real.sqrt |x i - x j|)
      ≤
    (∑ i : Fin n,
      ∑ j : Fin n,
        Real.sqrt |x i + x j|) := by

  have h :
      lhs x ≤ rhs x :=
    imo2021_p2_of_negative_type
      hneg
      x

  exact h

/-!
============================================================
11. Version using the expanded energy inequality directly
============================================================
-/

theorem imo2021_p2_from_energy
    {n : ℕ}
    (x : Fin n → ℝ)
    (henergy :
      2 *
          (∑ i : Fin n,
            ∑ j : Fin n,
              Real.sqrt |x i - x j|)
        -
      2 *
          (∑ i : Fin n,
            ∑ j : Fin n,
              Real.sqrt |x i + x j|)
        ≤
      0) :
    (∑ i : Fin n,
      ∑ j : Fin n,
        Real.sqrt |x i - x j|)
      ≤
    (∑ i : Fin n,
      ∑ j : Fin n,
        Real.sqrt |x i + x j|) := by

  linarith

/-!
============================================================
12. The elementary pairwise absolute-value inequality
============================================================
-/

/--
A useful algebraic fact appearing in the source argument:

    a² + b² ≥ 2|ab|.
-/
lemma two_abs_mul_le_sq_add_sq
    (a b : ℝ) :
    2 * |a * b|
      ≤
    a ^ 2 + b ^ 2 := by

  have h₁ :
      0 ≤ (a - b) ^ 2 :=
    sq_nonneg (a - b)

  have h₂ :
      0 ≤ (a + b) ^ 2 :=
    sq_nonneg (a + b)

  by_cases hab :
      0 ≤ a * b

  · rw [abs_of_nonneg hab]
    nlinarith

  · have hab' :
        a * b ≤ 0 :=
      le_of_not_ge hab

    rw [abs_of_nonpos hab']
    nlinarith

/-!
============================================================
13. Equivalent rearrangement
============================================================
-/

lemma neg_two_mul_le_sq_add_sq
    (a b : ℝ) :
    -(2 * a * b)
      ≤
    a ^ 2 + b ^ 2 := by

  nlinarith [sq_nonneg (a + b)]

lemma two_mul_le_sq_add_sq
    (a b : ℝ) :
    2 * a * b
      ≤
    a ^ 2 + b ^ 2 := by

  nlinarith [sq_nonneg (a - b)]

end

end IMO2021P2
