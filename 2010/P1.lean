import Mathlib

/-!
# IMO 2010 Problem 1

Find all functions `f : ℝ → ℝ` such that

    f (⌊x⌋ * y) = f x * ⌊f y⌋

for all real `x,y`.

The solutions are exactly

* `f ≡ 0`;
* `f ≡ c`, where `1 ≤ c < 2`.

Integer floors are explicitly cast back to `ℝ`.
-/

namespace IMO2010P1

/-- The functional equation. -/
def Good (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    f (((⌊x⌋ : ℤ) : ℝ) * y) =
      f x * (((⌊f y⌋ : ℤ) : ℝ))

/--
**IMO 2010 Problem 1.**

The solutions are precisely the zero function and the constant
functions whose value lies in `[1,2)`.
-/
theorem imo2010_p1
    (f : ℝ → ℝ) :
    Good f ↔
      (∀ x : ℝ, f x = 0) ∨
      ∃ c : ℝ,
        1 ≤ c ∧
        c < 2 ∧
        ∀ x : ℝ, f x = c := by

  constructor

  /- ================================================================
     Forward implication
     ================================================================ -/
  · intro hf

    /-
    Set x = 1:

        f y = f 1 * floor(f y).
    -/
    have hone :
        ∀ y : ℝ,
          f y =
            f 1 * (((⌊f y⌋ : ℤ) : ℝ)) := by

      intro y

      have h := hf 1 y

      simpa using h

    /-
    The functional equation becomes symmetric in x and y.

    We deliberately use `congrArg` instead of `rw [hone x]`,
    because rewriting directly can also rewrite the occurrence of
    `f x` inside `⌊f x⌋`.
    -/
    have hsymm :
        ∀ x y : ℝ,
          f (((⌊x⌋ : ℤ) : ℝ) * y) =
            f (((⌊y⌋ : ℤ) : ℝ) * x) := by

      intro x y

      have hx :
          f x =
            f 1 * (((⌊f x⌋ : ℤ) : ℝ)) :=
        hone x

      have hy :
          f y =
            f 1 * (((⌊f y⌋ : ℤ) : ℝ)) :=
        hone y

      calc
        f (((⌊x⌋ : ℤ) : ℝ) * y)
            =
          f x * (((⌊f y⌋ : ℤ) : ℝ)) :=
            hf x y

        _ =
          (f 1 * (((⌊f x⌋ : ℤ) : ℝ))) *
            (((⌊f y⌋ : ℤ) : ℝ)) := by

              exact
                congrArg
                  (fun z : ℝ =>
                    z * (((⌊f y⌋ : ℤ) : ℝ)))
                  hx

        _ =
          (f 1 * (((⌊f y⌋ : ℤ) : ℝ))) *
            (((⌊f x⌋ : ℤ) : ℝ)) := by
              ring

        _ =
          f y * (((⌊f x⌋ : ℤ) : ℝ)) := by

              exact
                congrArg
                  (fun z : ℝ =>
                    z * (((⌊f x⌋ : ℤ) : ℝ)))
                  hy.symm

        _ =
          f (((⌊y⌋ : ℤ) : ℝ) * x) :=
            (hf y x).symm

    /-
    Elementary floor values.
    -/
    have hfloorHalf :
        ⌊(1 / 2 : ℝ)⌋ = (0 : ℤ) := by
      rw [Int.floor_eq_iff]
      norm_num

    have hfloorTwo :
        ⌊(2 : ℝ)⌋ = (2 : ℤ) := by
      rw [Int.floor_eq_iff]
      norm_num

    /-
    Put x = 1/2 and y = 2:

        f 0 = f 1.
    -/
    have hf0eqf1 :
        f 0 = f 1 := by

      have h :=
        hsymm (1 / 2 : ℝ) 2

      rw [hfloorHalf, hfloorTwo] at h

      norm_num at h

      exact h

    /-
    Split according to whether f(0) = 0.
    -/
    by_cases hf0 : f 0 = 0

    /- ---------------------------------------------------------------
       Case 1: f(0) = 0.
       --------------------------------------------------------------- -/
    · left

      have hf1 :
          f 1 = 0 := by
        calc
          f 1 = f 0 := hf0eqf1.symm
          _ = 0 := hf0

      intro x

      have hx := hone x

      rw [hf1] at hx

      simpa using hx

    /- ---------------------------------------------------------------
       Case 2: f(0) ≠ 0.
       --------------------------------------------------------------- -/
    · right

      /-
      Put x = y = 0:

          f 0 = f 0 * floor(f 0).
      -/
      have h00 :
          f 0 =
            f 0 * (((⌊f 0⌋ : ℤ) : ℝ)) := by

        have h := hf 0 0

        simpa using h

      /-
      Since f(0) ≠ 0,

          floor(f 0) = 1.
      -/
      have hfloor0Cast :
          (((⌊f 0⌋ : ℤ) : ℝ)) = 1 := by

        have hfactor :
            f 0 *
                (1 - (((⌊f 0⌋ : ℤ) : ℝ)))
              =
            0 := by
          nlinarith [h00]

        rcases mul_eq_zero.mp hfactor with hzero | hrest

        · exact False.elim (hf0 hzero)

        · linarith

      have hfloor0 :
          ⌊f 0⌋ = (1 : ℤ) := by
        exact_mod_cast hfloor0Cast

      /-
      floor(f 0) = 1 iff

          1 ≤ f 0 < 2.
      -/
      have hinterval :
          (1 : ℝ) ≤ f 0 ∧
          f 0 < 2 := by

        have h :=
          (Int.floor_eq_iff).1 hfloor0

        norm_num at h

        exact h

      /-
      Put y = 0:

          f 0 = f x * floor(f 0)
              = f x.

      Hence f is constant.
      -/
      have hconst :
          ∀ x : ℝ,
            f x = f 0 := by

        intro x

        have hx := hf x 0

        rw [hfloor0] at hx
        norm_num at hx

        exact hx.symm

      exact
        ⟨f 0,
         hinterval.1,
         hinterval.2,
         hconst⟩

  /- ================================================================
     Reverse implication
     ================================================================ -/
  · intro hsol

    rcases hsol with hzero | hconst

    /- ---------------------------------------------------------------
       Zero solution.
       --------------------------------------------------------------- -/
    · intro x y

      rw [
        hzero (((⌊x⌋ : ℤ) : ℝ) * y),
        hzero x,
        hzero y
      ]

      norm_num

    /- ---------------------------------------------------------------
       Constant solution with 1 ≤ c < 2.
       --------------------------------------------------------------- -/
    · rcases hconst with
        ⟨c, hc1, hc2, hc⟩

      /-
      From 1 ≤ c < 2,

          floor c = 1.
      -/
      have hfloorc :
          ⌊c⌋ = (1 : ℤ) := by

        apply (Int.floor_eq_iff).2

        constructor

        · norm_num
          exact hc1

        · norm_num
          exact hc2

      intro x y

      have hleft :
          f (((⌊x⌋ : ℤ) : ℝ) * y) = c :=
        hc _

      have hx :
          f x = c :=
        hc x

      have hy :
          f y = c :=
        hc y

      calc
        f (((⌊x⌋ : ℤ) : ℝ) * y)
            = c := hleft

        _ =
          c * (1 : ℝ) := by
            ring

        _ =
          f x * (((⌊f y⌋ : ℤ) : ℝ)) := by

            rw [hx, hy, hfloorc]

            norm_num

end IMO2010P1
