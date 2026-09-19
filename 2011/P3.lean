import Mathlib

/-!
# IMO 2011 Problem 3

Let `f : ℝ → ℝ` satisfy

    f (x + y) ≤ y * f x + f (f x)

for every real `x,y`.

Prove that

    f x = 0

for every `x ≤ 0`.

The proof follows the source solution.

First compare

    P(x, f(y) - x)
    P(y, f(x) - y)

to derive

    x * f x + y * f y ≤ 2 * f x * f y.

Setting

    y = 2 * f x

then gives

    x * f x ≤ 0.

Next we prove that every value of `f` is nonpositive.
If `f(k) > 0`, choose a sufficiently negative `y`.  The original
functional inequality then makes `f(k+y) < 0`, while

    (k+y) * f(k+y) ≤ 0

and `k+y < 0` force `f(k+y) ≥ 0`, a contradiction.

For `x < 0`, therefore,

    x * f x ≤ 0  =>  f x ≥ 0

and global nonpositivity gives `f x ≤ 0`, hence `f x = 0`.

Finally we prove `f 0 = 0`.
-/

namespace IMO2011P3

/-- The functional inequality from IMO 2011 Problem 3. -/
def Good (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    f (x + y) ≤ y * f x + f (f x)

/--
**IMO 2011 Problem 3.**

If

    f(x+y) ≤ y f(x) + f(f(x))

for all real `x,y`, then

    f(x) = 0

for every `x ≤ 0`.
-/
theorem imo2011_p3
    (f : ℝ → ℝ)
    (hf : Good f) :
    ∀ x : ℝ,
      x ≤ 0 →
      f x = 0 := by

  /-
  Compare

      P(x, f(y)-x)
      P(y, f(x)-y).

  We obtain

      x*f(x) + y*f(y) ≤ 2*f(x)*f(y).
  -/
  have hmaster :
      ∀ x y : ℝ,
        x * f x + y * f y
          ≤
        2 * f x * f y := by

    intro x y

    have h₁ :=
      hf x (f y - x)

    have h₂ :=
      hf y (f x - y)

    have harg₁ :
        x + (f y - x) = f y := by
      ring

    have harg₂ :
        y + (f x - y) = f x := by
      ring

    have h₁' :
        f (f y)
          ≤
        (f y - x) * f x +
          f (f x) := by

      rw [harg₁] at h₁

      exact h₁

    have h₂' :
        f (f x)
          ≤
        (f x - y) * f y +
          f (f y) := by

      rw [harg₂] at h₂

      exact h₂

    nlinarith

  /-
  Substitute

      y = 2*f(x)

  into the previous inequality.

  The terms containing `f (2*f x)` cancel, giving

      x*f(x) ≤ 0.
  -/
  have hxf :
      ∀ x : ℝ,
        x * f x ≤ 0 := by

    intro x

    have h :=
      hmaster x (2 * f x)

    nlinarith

  /-
  Prove that every value of f is nonpositive.
  -/
  have hnonpos :
      ∀ k : ℝ,
        f k ≤ 0 := by

    intro k

    by_contra hk

    have hp :
        0 < f k := by
      exact lt_of_not_ge hk

    /-
    Abbreviate

        p = f(k) > 0
        C = f(f(k)).
    -/
    let p : ℝ :=
      f k

    let C : ℝ :=
      f (f k)

    have hp' :
        0 < p := by
      simpa [p] using hp

    have hp_ne :
        p ≠ 0 :=
      ne_of_gt hp'

    /-
    Choose y very negative.

    This choice guarantees simultaneously

        k+y < 0

    and

        y*p + C < 0.
    -/
    let y : ℝ :=
      -k -
        (|C| + 1) / p -
        |k| -
        1

    have hquot_pos :
        0 < (|C| + 1) / p := by

      apply div_pos

      · have hCnonneg :
            0 ≤ |C| :=
          abs_nonneg C

        linarith

      · exact hp'

    have htneg :
        k + y < 0 := by

      dsimp [y]

      have hkabs :
          0 ≤ |k| :=
        abs_nonneg k

      linarith

    /-
    Algebraically rewrite the right-hand side.
    -/
    have hyform :
        y * p + C
          =
        (-k - |k| - 1) * p
          - (|C| + 1)
          + C := by

      dsimp [y]

      field_simp [hp_ne]

      ring

    have hkcoeff :
        -k - |k| - 1 < 0 := by

      have hkabs :
          -k ≤ |k| :=
        neg_le_abs k

      linarith

    have hfirstneg :
        (-k - |k| - 1) * p < 0 := by

      exact
        mul_neg_of_neg_of_pos
          hkcoeff
          hp'

    have hCneg :
        -( |C| + 1) + C < 0 := by

      have hCabs :
          C ≤ |C| :=
        le_abs_self C

      linarith

    have hyrhs :
        y * p + C < 0 := by

      rw [hyform]

      linarith

    /-
    Apply the original functional inequality at `(k,y)`.
    -/
    have hbound :=
      hf k y

    have hbound' :
        f (k + y)
          ≤
        y * p + C := by

      simpa [p, C] using hbound

    have hfneg :
        f (k + y) < 0 := by

      exact
        lt_of_le_of_lt
          hbound'
          hyrhs

    /-
    But since `k+y < 0` and

        (k+y) * f(k+y) ≤ 0,

    we must have

        f(k+y) ≥ 0.
    -/
    have hprod :
        (k + y) * f (k + y) ≤ 0 :=
      hxf (k + y)

    have hfnonneg :
        0 ≤ f (k + y) := by

      nlinarith

    linarith

  /-
  Every strictly negative input has value zero.

  If x < 0, then

      x*f(x) ≤ 0

  implies f(x) ≥ 0.

  Together with f(x) ≤ 0, this gives equality.
  -/
  have hnegative :
      ∀ x : ℝ,
        x < 0 →
        f x = 0 := by

    intro x hx

    have hprod :
        x * f x ≤ 0 :=
      hxf x

    have hupper :
        f x ≤ 0 :=
      hnonpos x

    nlinarith

  /-
  In particular,

      f(-1) = 0.
  -/
  have hmone :
      f (-1) = 0 := by

    apply hnegative

    norm_num

  /-
  Use P(-1, z+1):

      f z ≤ (z+1) f(-1) + f(f(-1))
          = f 0.

  Thus every f(z) ≤ f(0).
  -/
  have hglobal_le_zero_value :
      ∀ z : ℝ,
        f z ≤ f 0 := by

    intro z

    have h :=
      hf (-1) (z + 1)

    have harg :
        (-1 : ℝ) + (z + 1) = z := by
      ring

    rw [harg] at h

    rw [hmone] at h

    norm_num at h

    exact h

  /-
  Taking z = -1 gives

      0 = f(-1) ≤ f(0).
  -/
  have hf0_nonneg :
      0 ≤ f 0 := by

    have h :=
      hglobal_le_zero_value (-1)

    rw [hmone] at h

    exact h

  /-
  Global nonpositivity gives the reverse inequality.
  -/
  have hf0_nonpos :
      f 0 ≤ 0 :=
    hnonpos 0

  have hf0 :
      f 0 = 0 := by

    exact
      le_antisymm
        hf0_nonpos
        hf0_nonneg

  /-
  Finish for every x ≤ 0.
  -/
  intro x hx

  by_cases hx0 :
      x = 0

  · subst x

    exact hf0

  · have hxneg :
        x < 0 := by
      exact
        lt_of_le_of_ne
          hx
          hx0

    exact
      hnegative x hxneg

end IMO2011P3
