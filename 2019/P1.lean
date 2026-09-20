import Mathlib

namespace IMO2019P1

/-!
# IMO 2019 Problem 1

Determine all functions `f : ℤ → ℤ` satisfying

    f (2 * a) + 2 * f b = f (f (a + b))

for all integers `a, b`.

The solutions are exactly

    f x = 0

and

    f x = 2 * x + c

for arbitrary `c : ℤ`.

No `sorry`, `admit`, or additional axioms.
-/

/-!
============================================================
1. Functional equation
============================================================
-/

def FunctionalEquation
    (f : ℤ → ℤ) : Prop :=
  ∀ a b : ℤ,
    f (2 * a) + 2 * f b =
      f (f (a + b))

/-!
============================================================
2. Doubling identity
============================================================
-/

/--
Comparing `P(a,0)` and `P(0,a)` gives

    f(2a) = 2f(a) - f(0).
-/
lemma double_identity
    {f : ℤ → ℤ}
    (h : FunctionalEquation f)
    (a : ℤ) :
    f (2 * a) =
      2 * f a - f 0 := by

  have h₁ :=
    h a 0

  have h₂ :=
    h 0 a

  simp only [
    add_zero,
    zero_add,
    mul_zero
  ] at h₁ h₂

  omega

/-!
============================================================
3. Shifted additivity
============================================================
-/

/--
The key identity:

    f(a+b) = f(a) + f(b) - f(0).
-/
lemma shifted_additive
    {f : ℤ → ℤ}
    (h : FunctionalEquation f)
    (a b : ℤ) :
    f (a + b) =
      f a + f b - f 0 := by

  have hab :=
    h a b

  have hzero :=
    h 0 (a + b)

  have hdouble :=
    double_identity
      h
      a

  simp only [
    mul_zero,
    zero_add
  ] at hzero

  rw [hdouble] at hab

  /-
  At this point:

    hab :
      2 * f a - f 0 + 2 * f b
        = f (f (a+b))

    hzero :
      f 0 + 2 * f (a+b)
        = f (f (a+b))

  This is Presburger arithmetic over ℤ.
  -/

  omega

/-!
============================================================
4. Subtracting f(0) gives an additive function
============================================================
-/

lemma shifted_is_additive
    {f : ℤ → ℤ}
    (h : FunctionalEquation f) :
    ∀ a b : ℤ,
      f (a + b) - f 0 =
        (f a - f 0) +
          (f b - f 0) := by

  intro a b

  have hab :=
    shifted_additive
      h
      a
      b

  omega

/-!
============================================================
5. Additive maps ℤ → ℤ are linear
============================================================
-/

/--
Every additive function on `ℤ` is multiplication by its
value at `1`.
-/
lemma additive_int_linear
    (g : ℤ → ℤ)
    (hadd :
      ∀ a b : ℤ,
        g (a + b) =
          g a + g b) :
    ∀ x : ℤ,
      g x =
        x * g 1 := by

  have hzero :
      g 0 = 0 := by

    have h :=
      hadd 0 0

    simp only [zero_add] at h

    omega

  let G : ℤ →+ ℤ :=
    {
      toFun := g
      map_zero' := hzero
      map_add' := by
        intro a b
        exact hadd a b
    }

  intro x

  have hx :=
    G.toIntLinearMap.map_smul
      x
      (1 : ℤ)

  simpa [G, zsmul_eq_mul] using hx

/-!
============================================================
6. Every solution is affine
============================================================
-/

/--
Every solution has the form

    f(x) = x*d + f(0).
-/
lemma affine_form
    {f : ℤ → ℤ}
    (h : FunctionalEquation f) :
    ∃ d : ℤ,
      ∀ x : ℤ,
        f x =
          x * d + f 0 := by

  let g : ℤ → ℤ :=
    fun x =>
      f x - f 0

  have gadd :
      ∀ a b : ℤ,
        g (a + b) =
          g a + g b := by

    intro a b

    dsimp [g]

    exact
      shifted_is_additive
        h
        a
        b

  have glinear :
      ∀ x : ℤ,
        g x =
          x * g 1 :=
    additive_int_linear
      g
      gadd

  refine
    ⟨g 1, ?_⟩

  intro x

  have hx :=
    glinear x

  dsimp [g] at hx ⊢

  omega

/-!
============================================================
7. Substitute the affine form
============================================================
-/

lemma affine_polynomial_identity
    {f : ℤ → ℤ}
    (h : FunctionalEquation f)
    (d : ℤ)
    (hform :
      ∀ x : ℤ,
        f x =
          x * d + f 0)
    (a b : ℤ) :
    2 * d * (a + b) +
        3 * f 0
      =
    d * d * (a + b) +
        d * f 0 +
        f 0 := by

  have hab :=
    h a b

  rw [
    hform (2 * a),
    hform b,
    hform (f (a + b)),
    hform (a + b)
  ] at hab

  ring_nf at hab ⊢

  exact hab

/-!
============================================================
8. The slope is 0 or 2
============================================================
-/

/--
Substitution forces

    d(d-2)=0.
-/
lemma slope_zero_or_two
    {f : ℤ → ℤ}
    (h : FunctionalEquation f)
    (d : ℤ)
    (hform :
      ∀ x : ℤ,
        f x =
          x * d + f 0) :
    d = 0 ∨ d = 2 := by

  have h00 :=
    affine_polynomial_identity
      h
      d
      hform
      0
      0

  have h10 :=
    affine_polynomial_identity
      h
      d
      hform
      1
      0

  have hfactor :
      d * (d - 2) = 0 := by
    nlinarith

  rcases mul_eq_zero.mp hfactor with
    hd | hd

  · exact
      Or.inl hd

  · right
    omega

/-!
============================================================
9. Slope zero forces the zero function
============================================================
-/

lemma zero_slope_gives_zero
    {f : ℤ → ℤ}
    (h : FunctionalEquation f)
    (hform :
      ∀ x : ℤ,
        f x = f 0) :
    ∀ x : ℤ,
      f x = 0 := by

  have h00 :=
    h 0 0

  norm_num at h00

  /-
  Now

      h00 : f 0 + 2 * f 0 = f (f 0).

  Since the function is constant,
      f (f 0) = f 0.
  -/

  rw [hform (f 0)] at h00

  have hc :
      f 0 = 0 := by
    omega

  intro x

  calc
    f x =
        f 0 :=
      hform x

    _ = 0 :=
      hc

/-!
============================================================
10. Necessity
============================================================
-/

theorem classify
    {f : ℤ → ℤ}
    (h : FunctionalEquation f) :
    (∀ x : ℤ,
      f x = 0)
    ∨
    (∃ c : ℤ,
      ∀ x : ℤ,
        f x =
          2 * x + c) := by

  obtain ⟨d, hform⟩ :=
    affine_form h

  have hd :
      d = 0 ∨ d = 2 :=
    slope_zero_or_two
      h
      d
      hform

  rcases hd with hd0 | hd2

  · left

    have hconstant :
        ∀ x : ℤ,
          f x = f 0 := by

      intro x

      have hx :=
        hform x

      rw [hd0] at hx

      simpa using hx

    exact
      zero_slope_gives_zero
        h
        hconstant

  · right

    refine
      ⟨f 0, ?_⟩

    intro x

    have hx :=
      hform x

    rw [hd2] at hx

    calc
      f x =
          x * 2 + f 0 :=
        hx

      _ =
          2 * x + f 0 := by
        ring

/-!
============================================================
11. The zero solution works
============================================================
-/

lemma zero_solution :
    FunctionalEquation
      (fun _ : ℤ => 0) := by

  intro a b

  norm_num

/-!
============================================================
12. Every f(x)=2x+c works
============================================================
-/

lemma affine_two_solution
    (c : ℤ) :
    FunctionalEquation
      (fun x : ℤ =>
        2 * x + c) := by

  intro a b

  ring

/-!
============================================================
13. Converse
============================================================
-/

lemma functionalEquation_of_classified
    {f : ℤ → ℤ}
    (hsol :
      (∀ x : ℤ,
        f x = 0)
      ∨
      (∃ c : ℤ,
        ∀ x : ℤ,
          f x =
            2 * x + c)) :
    FunctionalEquation f := by

  rcases hsol with hzero | haffine

  · intro a b

    /-
    Rewrite the OUTER nested call first.

      f (f (a+b)) = 0

    directly, since `hzero` holds for every integer argument.
    -/

    rw [
      hzero (2 * a),
      hzero b,
      hzero (f (a + b))
    ]

    norm_num

  · obtain ⟨c, hc⟩ :=
      haffine

    intro a b

    /-
    Again rewrite the outer nested call before its argument.
    -/

    rw [
      hc (2 * a),
      hc b,
      hc (f (a + b)),
      hc (a + b)
    ]

    ring

/-!
============================================================
14. Complete classification
============================================================
-/

/--
IMO 2019 Problem 1.

    FunctionalEquation f

holds if and only if either

    f(x)=0

for every integer `x`, or there is `c : ℤ` such that

    f(x)=2x+c

for every integer `x`.
-/
theorem imo2019_p1
    (f : ℤ → ℤ) :
    FunctionalEquation f
      ↔
    ((∀ x : ℤ,
        f x = 0)
      ∨
      (∃ c : ℤ,
        ∀ x : ℤ,
          f x =
            2 * x + c)) := by

  constructor

  · intro h

    exact classify h

  · intro h

    exact
      functionalEquation_of_classified
        h

end IMO2019P1
