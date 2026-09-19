import Mathlib

/-!
# IMO 2012 Problem 4 — algebraic core

Let `f : ℤ → ℤ` satisfy, whenever `a+b+c=0`,

    f(a)^2 + f(b)^2 + f(c)^2
      =
    2*f(a)*f(b) + 2*f(b)*f(c) + 2*f(c)*f(a).

We prove:

* `f 0 = 0`;
* `f x = f (-x)`;
* `(f (a+b) - f a - f b)^2 = 4*f a*f b`;
* if `f b = 0`, then `f (a+b) = f a`;
* `f 2 = 0 ∨ f 2 = 4*f 1`;
* if `f 2 = 4*f 1`, then
      `f 3 = f 1 ∨ f 3 = 9*f 1`;
* in the low branch `f 3 = f 1`, one gets `f 4 = 0`;
* every quadratic map `f x = C*x^2` is a solution.

No `sorry`, `admit`, or extra axioms are used.
-/

namespace IMO2012P4

/-- The original functional equation. -/
def Good (f : ℤ → ℤ) : Prop :=
  ∀ a b c : ℤ,
    a + b + c = 0 →
    f a ^ 2 + f b ^ 2 + f c ^ 2
      =
    2 * f a * f b +
    2 * f b * f c +
    2 * f c * f a

/-!
## f(0)=0
-/

lemma f_zero
    {f : ℤ → ℤ}
    (hf : Good f) :
    f 0 = 0 := by

  have h :=
    hf 0 0 0 (by ring)

  have hsquare :
      f 0 ^ 2 = 0 := by
    nlinarith

  nlinarith

/-!
## Evenness
-/

/--
The functional equation implies

    f(x)=f(-x).
-/
lemma f_neg
    {f : ℤ → ℤ}
    (hf : Good f)
    (x : ℤ) :
    f (-x) = f x := by

  have h0 :
      f 0 = 0 :=
    f_zero hf

  have h :=
    hf x (-x) 0 (by ring)

  rw [h0] at h

  have hsquare :
      (f x - f (-x)) ^ 2 = 0 := by
    nlinarith

  nlinarith

lemma f_neg'
    {f : ℤ → ℤ}
    (hf : Good f)
    (x : ℤ) :
    f x = f (-x) := by

  symm

  exact
    f_neg
      hf
      x

/-!
## Fundamental two-variable identity
-/

/--
Taking `c = -(a+b)` gives

    (f(a+b) - f(a) - f(b))² = 4 f(a) f(b).
-/
lemma fundamental_identity
    {f : ℤ → ℤ}
    (hf : Good f)
    (a b : ℤ) :
    (f (a + b) - f a - f b) ^ 2
      =
    4 * f a * f b := by

  have h :=
    hf a b (-(a + b)) (by ring)

  have hneg :
      f (-(a + b)) =
        f (a + b) :=
    f_neg hf (a + b)

  rw [hneg] at h

  nlinarith

/-!
## Zero values give periods
-/

/--
If `f b = 0`, then

    f(a+b)=f(a).
-/
lemma add_eq_of_value_zero
    {f : ℤ → ℤ}
    (hf : Good f)
    {a b : ℤ}
    (hb : f b = 0) :
    f (a + b) = f a := by

  have h :=
    fundamental_identity
      hf
      a
      b

  rw [hb] at h

  have hsquare :
      (f (a + b) - f a) ^ 2 = 0 := by
    simpa using h

  nlinarith

/--
If `f d = 0`, then `d` is a period of `f`.
-/
lemma periodic_of_value_zero
    {f : ℤ → ℤ}
    (hf : Good f)
    {d : ℤ}
    (hd : f d = 0) :
    ∀ x : ℤ,
      f (x + d) = f x := by

  intro x

  exact
    add_eq_of_value_zero
      hf
      hd

/-!
## First case split: f(2)
-/

/--
From the identity with `a=b=1`,

    f(2)=0  or  f(2)=4f(1).
-/
lemma f_two_cases
    {f : ℤ → ℤ}
    (hf : Good f) :
    f 2 = 0 ∨
    f 2 = 4 * f 1 := by

  have h :=
    fundamental_identity
      hf
      1
      1

  norm_num at h

  have hfactor :
      f 2 * (f 2 - 4 * f 1) = 0 := by
    nlinarith

  rcases mul_eq_zero.mp hfactor with h0 | h4

  · exact Or.inl h0

  · right
    nlinarith

/-!
## Period 1 branch
-/

/--
If `f(1)=0`, then `1` is a period.
-/
lemma period_one_of_f_one_zero
    {f : ℤ → ℤ}
    (hf : Good f)
    (h1 : f 1 = 0) :
    ∀ x : ℤ,
      f (x + 1) = f x := by

  exact
    periodic_of_value_zero
      hf
      h1

/-!
## Period 2 branch
-/

lemma period_two_of_f_two_zero
    {f : ℤ → ℤ}
    (hf : Good f)
    (h2 : f 2 = 0) :
    ∀ x : ℤ,
      f (x + 2) = f x := by

  exact
    periodic_of_value_zero
      hf
      h2

/-!
## Second case split: f(3)
-/

/--
If

    f(2)=4f(1),

then

    f(3)=f(1)  or  f(3)=9f(1).
-/
lemma f_three_cases
    {f : ℤ → ℤ}
    (hf : Good f)
    (h2 :
      f 2 = 4 * f 1) :
    f 3 = f 1 ∨
    f 3 = 9 * f 1 := by

  have h :=
    fundamental_identity
      hf
      2
      1

  rw [h2] at h

  norm_num at h

  have hfactor :
      (f 3 - f 1) *
        (f 3 - 9 * f 1) = 0 := by
    nlinarith

  rcases mul_eq_zero.mp hfactor with hlow | hhigh

  · left
    nlinarith

  · right
    nlinarith

/-!
## Low branch gives f(4)=0
-/

/--
In the branch

    f(2)=4f(1)
    f(3)=f(1)
    f(1)≠0,

one obtains `f(4)=0`.
-/
lemma f_four_zero_of_low_branch
    {f : ℤ → ℤ}
    (hf : Good f)
    (h1 : f 1 ≠ 0)
    (h2 :
      f 2 = 4 * f 1)
    (h3 :
      f 3 = f 1) :
    f 4 = 0 := by

  /-
  From 1+3:
      f4 = 0 or f4 = 4 f1.
  -/
  have h13 :=
    fundamental_identity
      hf
      1
      3

  rw [h3] at h13

  norm_num at h13

  have hA :
      f 4 = 0 ∨
      f 4 = 4 * f 1 := by

    have hfactor :
        f 4 * (f 4 - 4 * f 1) = 0 := by
      nlinarith

    rcases mul_eq_zero.mp hfactor with h0 | h4

    · exact Or.inl h0

    · right
      nlinarith

  /-
  From 2+2:
      f4 = 0 or f4 = 16 f1.
  -/
  have h22 :=
    fundamental_identity
      hf
      2
      2

  rw [h2] at h22

  norm_num at h22

  have hB :
      f 4 = 0 ∨
      f 4 = 16 * f 1 := by

    have hfactor :
        f 4 * (f 4 - 16 * f 1) = 0 := by
      nlinarith

    rcases mul_eq_zero.mp hfactor with h0 | h16

    · exact Or.inl h0

    · right
      nlinarith

  rcases hA with h0 | h4

  · exact h0

  · rcases hB with h0 | h16

    · exact h0

    · exfalso

      apply h1

      nlinarith

/--
Therefore `4` is a period in the low branch.
-/
lemma period_four_of_low_branch
    {f : ℤ → ℤ}
    (hf : Good f)
    (h1 : f 1 ≠ 0)
    (h2 :
      f 2 = 4 * f 1)
    (h3 :
      f 3 = f 1) :
    ∀ x : ℤ,
      f (x + 4) = f x := by

  have h4 :
      f 4 = 0 :=
    f_four_zero_of_low_branch
      hf
      h1
      h2
      h3

  exact
    periodic_of_value_zero
      hf
      h4

/-!
## Quadratic family
-/

/--
Every quadratic map

    f(x)=C*x²

satisfies the original equation.
-/
lemma quadratic_solution
    (C : ℤ) :
    Good (fun x : ℤ => C * x ^ 2) := by

  intro a b c habc

  have hc :
      c = -(a + b) := by
    linarith

  subst c

  ring

/-!
## Zero solution
-/

/--
The zero function satisfies the original equation.
-/
lemma zero_solution :
    Good (fun _ : ℤ => 0) := by

  simpa using
    (quadratic_solution 0)

/-!
## Initial classification tree
-/

/--
Every solution enters the same initial case tree as in the source:

* `f 1 = 0`, or
* `f 1 ≠ 0` and `f 2 = 0`, or
* `f 1 ≠ 0`, `f 2 = 4 f 1`, and
  `f 3 = f 1` or `f 3 = 9 f 1`.
-/
theorem initial_classification
    {f : ℤ → ℤ}
    (hf : Good f) :
    f 1 = 0 ∨
    (f 1 ≠ 0 ∧ f 2 = 0) ∨
    (f 1 ≠ 0 ∧
      f 2 = 4 * f 1 ∧
      (f 3 = f 1 ∨
       f 3 = 9 * f 1)) := by

  by_cases h1 :
      f 1 = 0

  · exact Or.inl h1

  · right

    rcases f_two_cases hf with h2zero | h2four

    · exact
        Or.inl
          ⟨h1, h2zero⟩

    · exact
        Or.inr
          ⟨h1,
           h2four,
           f_three_cases hf h2four⟩

end IMO2012P4
