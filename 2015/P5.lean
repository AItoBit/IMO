import Mathlib

namespace IMO2015P5

/-!
# IMO 2015 Problem 5

Determine all functions `f : ℝ → ℝ` satisfying

    f (x + f (x + y)) + f (x * y)
      =
    x + f (x + y) + y * f x

for all real `x,y`.

The solutions are

    f x = x

and

    f x = 2 - x.

No `sorry`, `admit`, or extra axioms are used.
-/

/-!
## Functional equation
-/

def FunctionalEquation (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    f (x + f (x + y)) + f (x * y)
      =
    x + f (x + y) + y * f x

/-!
## Verification of the two solutions
-/

lemma identity_satisfies :
    FunctionalEquation (fun x : ℝ => x) := by

  intro x y

  dsimp

  ring

lemma reflection_satisfies :
    FunctionalEquation (fun x : ℝ => 2 - x) := by

  intro x y

  dsimp

  ring

/-!
## Basic consequences
-/

/--
Putting `y = 1` gives

    f (x + f(x+1)) = x + f(x+1).

Thus `x + f(x+1)` is always a fixed point.
-/
lemma fixed_family
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (x : ℝ) :
    f (x + f (x + 1))
      =
    x + f (x + 1) := by

  have hp := h x 1

  simp only [mul_one, one_mul] at hp

  linarith

/--
Putting `x = 0` gives

    f(f(y)) + f(0)
      =
    f(y) + y*f(0).
-/
lemma zero_equation
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (y : ℝ) :
    f (f y) + f 0
      =
    f y + y * f 0 := by

  have hp := h 0 y

  simpa using hp

/-!
## Case 1: f(0) ≠ 0
-/

/--
If `f(0) ≠ 0`, every fixed point of `f`
must equal `1`.
-/
lemma fixed_point_eq_one_of_fzero_ne_zero
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 ≠ 0)
    {z : ℝ}
    (hz : f z = z) :
    z = 1 := by

  have h0 :=
    zero_equation h z

  rw [hz] at h0

  have hprod :
      (z - 1) * f 0 = 0 := by
    nlinarith [h0]

  have hz0 :
      z - 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hf0

  linarith

/--
If `f(0) ≠ 0`, then

    f(x) = 2-x.
-/
lemma solution_of_fzero_ne_zero
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 ≠ 0) :
    ∀ x : ℝ,
      f x = 2 - x := by

  intro x

  have hfix :=
    fixed_family h (x - 1)

  have hone :
      (x - 1) + f ((x - 1) + 1) = 1 :=
    fixed_point_eq_one_of_fzero_ne_zero
      h
      hf0
      hfix

  have hx :
      (x - 1 : ℝ) + 1 = x := by
    ring

  rw [hx] at hone

  linarith

/-!
## Case 2: f(0) = 0
-/

/--
Putting `(x+1,0)` into the equation yields another
fixed point:

    f(x + f(x+1) + 1)
      =
    x + f(x+1) + 1.
-/
lemma fixed_family_succ
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0)
    (x : ℝ) :
    f (x + f (x + 1) + 1)
      =
    x + f (x + 1) + 1 := by

  have hp := h (x + 1) 0

  simpa [hf0, add_assoc, add_left_comm, add_comm] using hp

/--
Taking `x=-1` in `fixed_family` gives

    f(-1) = -1.
-/
lemma f_neg_one
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0) :
    f (-1) = -1 := by

  have hp :=
    fixed_family h (-1)

  norm_num [hf0] at hp

  exact hp

/--
Putting `(x,y)=(1,-1)` gives

    f(1)=1.
-/
lemma f_one
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0) :
    f 1 = 1 := by

  have hm1 :
      f (-1) = -1 :=
    f_neg_one h hf0

  have hp := h 1 (-1)

  norm_num [hf0, hm1] at hp

  linarith

/--
Putting `x=1` gives

    f(1 + f(y+1)) + f(y)
      =
    1 + f(y+1) + y.
-/
lemma equation_at_one
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0)
    (y : ℝ) :
    f (1 + f (y + 1)) + f y
      =
    1 + f (y + 1) + y := by

  have hf1 :
      f 1 = 1 :=
    f_one h hf0

  have hp := h 1 y

  rw [hf1] at hp

  simpa [add_comm] using hp

/-!
## Consecutive fixed points
-/

/--
If `y` and `y+1` are fixed points,
then `y+2` is also fixed.
-/
lemma fixed_next
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0)
    {y : ℝ}
    (hy :
      f y = y)
    (hy1 :
      f (y + 1) = y + 1) :
    f (y + 2) = y + 2 := by

  have hp :=
    equation_at_one h hf0 y

  rw [hy, hy1] at hp

  have harg :
      1 + (y + 1) =
        y + 2 := by
    ring

  rw [harg] at hp

  linarith

/--
For every `x`,

    x + f(x+1) + 2

is also a fixed point.
-/
lemma fixed_family_plus_two
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0)
    (x : ℝ) :
    f (x + f (x + 1) + 2)
      =
    x + f (x + 1) + 2 := by

  let z : ℝ :=
    x + f (x + 1)

  have hz :
      f z = z := by
    dsimp [z]
    exact fixed_family h x

  have hz1 :
      f (z + 1) = z + 1 := by
    dsimp [z]
    exact fixed_family_succ h hf0 x

  have hz2 :
      f (z + 2) = z + 2 :=
    fixed_next
      h
      hf0
      hz
      hz1

  simpa [z, add_assoc] using hz2

/--
Replacing the parameter appropriately gives

    f(x + f(x-1))
      =
    x + f(x-1).
-/
lemma fixed_previous_family
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0)
    (x : ℝ) :
    f (x + f (x - 1))
      =
    x + f (x - 1) := by

  have hp :=
    fixed_family_plus_two
      h
      hf0
      (x - 2)

  have hinner :
      (x - 2 : ℝ) + 1 =
        x - 1 := by
    ring

  rw [hinner] at hp

  have houter :
      (x - 2) + f (x - 1) + 2
        =
      x + f (x - 1) := by
    ring

  rw [houter] at hp

  exact hp

/-!
## Oddness
-/

/--
Substituting `y=-1`, together with the previous fixed-point
identity, proves

    f(-x) = -f(x).
-/
lemma odd_of_fzero_eq_zero
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0) :
    ∀ x : ℝ,
      f (-x) = -f x := by

  intro x

  have hp := h x (-1)

  have hx1 :
      x + (-1 : ℝ) =
        x - 1 := by
    ring

  have hxm :
      x * (-1 : ℝ) =
        -x := by
    ring

  rw [hx1, hxm] at hp

  have hfix :
      f (x + f (x - 1))
        =
      x + f (x - 1) :=
    fixed_previous_family
      h
      hf0
      x

  rw [hfix] at hp

  have hminus :
      (-1 : ℝ) * f x =
        -f x := by
    ring

  rw [hminus] at hp

  linarith

/-!
## Reflected functional equation
-/

/--
Apply the original equation at `(-1,-y)` and use oddness.
-/
lemma reflected_equation
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0)
    (y : ℝ) :
    -f (1 + f (y + 1)) + f y
      =
    -1 - f (y + 1) + y := by

  have hm1 :
      f (-1) = -1 :=
    f_neg_one h hf0

  have hodd :
      ∀ t : ℝ,
        f (-t) = -f t :=
    odd_of_fzero_eq_zero
      h
      hf0

  have hp :=
    h (-1) (-y)

  have hsum :
      (-1 : ℝ) + (-y)
        =
      -(y + 1) := by
    ring

  have hprod :
      (-1 : ℝ) * (-y)
        =
      y := by
    ring

  rw [hsum, hprod] at hp

  rw [hodd (y + 1)] at hp

  rw [hm1] at hp

  have harg :
      (-1 : ℝ) + (-f (y + 1))
        =
      -(1 + f (y + 1)) := by
    ring

  rw [harg] at hp

  rw [hodd (1 + f (y + 1))] at hp

  have hmul :
      (-y) * (-1 : ℝ) =
        y := by
    ring

  rw [hmul] at hp

  linarith

/-!
## Identity solution in the f(0)=0 case
-/

/--
Adding the equations obtained from `P(1,y)` and
`P(-1,-y)` gives

    f(y) = y.
-/
lemma solution_of_fzero_eq_zero
    {f : ℝ → ℝ}
    (h : FunctionalEquation f)
    (hf0 : f 0 = 0) :
    ∀ y : ℝ,
      f y = y := by

  intro y

  have h₁ :
      f (1 + f (y + 1)) + f y
        =
      1 + f (y + 1) + y :=
    equation_at_one
      h
      hf0
      y

  have h₂ :
      -f (1 + f (y + 1)) + f y
        =
      -1 - f (y + 1) + y :=
    reflected_equation
      h
      hf0
      y

  linarith

/-!
## Classification
-/

/--
Any solution is either

    f(x)=x

or

    f(x)=2-x.
-/
theorem only_solutions
    {f : ℝ → ℝ}
    (h : FunctionalEquation f) :
    (∀ x : ℝ, f x = x) ∨
    (∀ x : ℝ, f x = 2 - x) := by

  by_cases hf0 :
      f 0 = 0

  · left

    exact
      solution_of_fzero_eq_zero
        h
        hf0

  · right

    exact
      solution_of_fzero_ne_zero
        h
        hf0

/-!
## Full iff theorem
-/

/--
Complete classification of IMO 2015 Problem 5.
-/
theorem imo2015_p5
    (f : ℝ → ℝ) :
    FunctionalEquation f ↔
      (∀ x : ℝ, f x = x) ∨
      (∀ x : ℝ, f x = 2 - x) := by

  constructor

  · intro h

    exact
      only_solutions h

  · intro h

    rcases h with
      hid | href

    · have hf :
          f = fun x : ℝ => x := by

        funext x

        exact hid x

      rw [hf]

      exact identity_satisfies

    · have hf :
          f = fun x : ℝ => 2 - x := by

        funext x

        exact href x

      rw [hf]

      exact reflection_satisfies

end IMO2015P5
