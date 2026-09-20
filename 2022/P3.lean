import Mathlib

namespace IMO2022P2

/-!
# IMO 2022 Problem 2

Let f : ℝ₊ → ℝ₊ satisfy:

for every positive x there is exactly one positive y such that

    x * f y + y * f x ≤ 2.

Then

    f x = 1 / x

for every positive x.

We work with ordinary real numbers and carry positivity
explicitly in the hypotheses.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. The relation from the problem
============================================================
-/

def Good
    (f : ℝ → ℝ)
    (x y : ℝ) : Prop :=
  0 < y ∧
  x * f y + y * f x ≤ 2

/-!
The relation is symmetric on positive x,y.
-/

lemma good_symm
    {f : ℝ → ℝ}
    {x y : ℝ}
    (hx : 0 < x)
    (h : Good f x y) :
    Good f y x := by

  rcases h with ⟨hy, hxy⟩

  constructor

  · exact hx

  · nlinarith

/-!
============================================================
2. An elementary algebraic lemma
============================================================
-/

/--
If

    x f(x) > 1
    y f(y) > 1,

with x,y,f(x),f(y) positive, then

    x f(y) + y f(x) > 2.
-/
lemma cross_sum_gt_two
    {x y fx fy : ℝ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hfx : 0 < fx)
    (hfy : 0 < fy)
    (hxx : 1 < x * fx)
    (hyy : 1 < y * fy) :
    2 < x * fy + y * fx := by

  let A : ℝ := x * fy
  let B : ℝ := y * fx
  let U : ℝ := x * fx
  let V : ℝ := y * fy

  have hA :
      0 < A := by
    dsimp [A]
    positivity

  have hB :
      0 < B := by
    dsimp [B]
    positivity

  have hU :
      1 < U := by
    exact hxx

  have hV :
      1 < V := by
    exact hyy

  have hUVeq :
      A * B = U * V := by
    dsimp [A, B, U, V]
    ring

  have hU1 :
      0 < U - 1 := by
    linarith

  have hV1 :
      0 < V - 1 := by
    linarith

  have hprodAux :
      0 < (U - 1) * (V - 1) := by
    exact mul_pos hU1 hV1

  have hUV :
      1 < U * V := by
    nlinarith

  have hAB :
      1 < A * B := by
    rw [hUVeq]
    exact hUV

  by_contra hnot

  have hsum :
      A + B ≤ 2 := by
    linarith

  have hsum_nonneg :
      0 ≤ A + B := by
    linarith

  have hmul :
      0 ≤
        (A + B) *
          (2 - (A + B)) := by

    exact
      mul_nonneg
        hsum_nonneg
        (sub_nonneg.mpr hsum)

  have hsq :
      0 ≤ (A - B) ^ 2 :=
    sq_nonneg (A - B)

  nlinarith

/-!
============================================================
3. The unique partner must be x itself
============================================================
-/

/--
If y is the unique partner of x, then y = x.
-/
lemma unique_partner_eq_self
    (f : ℝ → ℝ)
    (hfpos :
      ∀ t : ℝ,
        0 < t →
        0 < f t)
    (huniq :
      ∀ t : ℝ,
        0 < t →
        ∃! u : ℝ,
          Good f t u)
    {x : ℝ}
    (hx : 0 < x) :
    Good f x x := by

  obtain
    ⟨y,
     hyGood,
     hyUnique⟩ :=
    huniq x hx

  rcases hyGood with
    ⟨hy, hxy⟩

  obtain
    ⟨z,
     hzGood,
     hzUnique⟩ :=
    huniq y hy

  have hyx :
      Good f y x := by

    constructor

    · exact hx

    · nlinarith

  have hxz :
      x = z :=
    hzUnique
      x
      hyx

  have hy_eq_x :
      y = x := by

    by_contra hne

    have hnot_xx :
        ¬ Good f x x := by

      intro hxxGood

      have hxeqy :
          x = y :=
        hyUnique
          x
          hxxGood

      exact
        hne
          hxeqy.symm

    have hnot_yy :
        ¬ Good f y y := by

      intro hyyGood

      have hyeqz :
          y = z :=
        hzUnique
          y
          hyyGood

      have hyx' :
          y = x := by
        calc
          y = z := hyeqz
          _ = x := hxz.symm

      exact hne hyx'

    have hxx_not_le :
        ¬
          x * f x +
              x * f x
            ≤
          2 := by

      intro hle

      apply hnot_xx

      exact
        ⟨hx, hle⟩

    have hyy_not_le :
        ¬
          y * f y +
              y * f y
            ≤
          2 := by

      intro hle

      apply hnot_yy

      exact
        ⟨hy, hle⟩

    have hxx :
        1 < x * f x := by
      nlinarith

    have hyy :
        1 < y * f y := by
      nlinarith

    have hfx :
        0 < f x :=
      hfpos x hx

    have hfy :
        0 < f y :=
      hfpos y hy

    have hcross :
        2 <
          x * f y +
          y * f x :=
      cross_sum_gt_two
        hx
        hy
        hfx
        hfy
        hxx
        hyy

    linarith

  rw [hy_eq_x] at hxy

  exact
    ⟨hx, hxy⟩

/-!
============================================================
4. First bound: x f(x) ≤ 1
============================================================
-/

lemma mul_f_le_one
    (f : ℝ → ℝ)
    (hfpos :
      ∀ t : ℝ,
        0 < t →
        0 < f t)
    (huniq :
      ∀ t : ℝ,
        0 < t →
        ∃! u : ℝ,
          Good f t u)
    {x : ℝ}
    (hx : 0 < x) :
    x * f x ≤ 1 := by

  have hself :
      Good f x x :=
    unique_partner_eq_self
      f
      hfpos
      huniq
      hx

  rcases hself with
    ⟨_, h⟩

  nlinarith

/-!
============================================================
5. Every valid partner is x
============================================================
-/

lemma good_implies_eq
    (f : ℝ → ℝ)
    (hfpos :
      ∀ t : ℝ,
        0 < t →
        0 < f t)
    (huniq :
      ∀ t : ℝ,
        0 < t →
        ∃! u : ℝ,
          Good f t u)
    {x y : ℝ}
    (hx : 0 < x)
    (hyGood :
      Good f x y) :
    y = x := by

  obtain
    ⟨u,
     huGood,
     huUnique⟩ :=
    huniq x hx

  have hxGood :
      Good f x x :=
    unique_partner_eq_self
      f
      hfpos
      huniq
      hx

  have hyu :
      y = u :=
    huUnique
      y
      hyGood

  have hxu :
      x = u :=
    huUnique
      x
      hxGood

  exact
    hyu.trans
      hxu.symm

/-!
============================================================
6. Final lower bound without limits
============================================================
-/

/--
Set

    y = 1 / f(x).

Since x f(x) ≤ 1, we have x ≤ y.

Also y f(y) ≤ 1, so

    x f(y) ≤ y f(y) ≤ 1,

while

    y f(x) = 1.

Hence y is another valid partner of x.
By uniqueness, y = x, so x f(x) = 1.
-/
lemma mul_f_eq_one
    (f : ℝ → ℝ)
    (hfpos :
      ∀ t : ℝ,
        0 < t →
        0 < f t)
    (huniq :
      ∀ t : ℝ,
        0 < t →
        ∃! u : ℝ,
          Good f t u)
    {x : ℝ}
    (hx : 0 < x) :
    x * f x = 1 := by

  have hfx :
      0 < f x :=
    hfpos x hx

  have hupper :
      x * f x ≤ 1 :=
    mul_f_le_one
      f
      hfpos
      huniq
      hx

  let y : ℝ :=
    1 / f x

  have hy :
      0 < y := by

    dsimp [y]

    exact
      one_div_pos.mpr
        hfx

  have hxy :
      x ≤ y := by

    dsimp [y]

    exact
      (le_div_iff₀ hfx).2
        hupper

  have hyupper :
      y * f y ≤ 1 :=
    mul_f_le_one
      f
      hfpos
      huniq
      hy

  have hfy :
      0 < f y :=
    hfpos y hy

  have hx_fy :
      x * f y
        ≤
      y * f y := by

    exact
      mul_le_mul_of_nonneg_right
        hxy
        (le_of_lt hfy)

  have hy_fx :
      y * f x = 1 := by

    dsimp [y]

    field_simp [ne_of_gt hfx]

  have hyGood :
      Good f x y := by

    constructor

    · exact hy

    · nlinarith

  have hyx :
      y = x :=
    good_implies_eq
      f
      hfpos
      huniq
      hx
      hyGood

  rw [hyx] at hy_fx

  exact hy_fx

/-!
============================================================
7. Main theorem
============================================================
-/

theorem imo2022_p2
    (f : ℝ → ℝ)
    (hfpos :
      ∀ x : ℝ,
        0 < x →
        0 < f x)
    (huniq :
      ∀ x : ℝ,
        0 < x →
        ∃! y : ℝ,
          Good f x y) :
    ∀ x : ℝ,
      0 < x →
      f x = 1 / x := by

  intro x hx

  have hprod :
      x * f x = 1 :=
    mul_f_eq_one
      f
      hfpos
      huniq
      hx

  have hx0 :
      x ≠ 0 :=
    ne_of_gt hx

  apply
    (eq_div_iff hx0).2

  calc
    f x * x
        =
      x * f x := by
        ring

    _ = 1 :=
      hprod

/-!
============================================================
8. Expanded statement
============================================================
-/

theorem imo2022_p2_expanded
    (f : ℝ → ℝ)

    (hfpos :
      ∀ x : ℝ,
        0 < x →
        0 < f x)

    (huniq :
      ∀ x : ℝ,
        0 < x →
        ∃! y : ℝ,
          0 < y ∧
          x * f y +
              y * f x
            ≤
          2) :

    ∀ x : ℝ,
      0 < x →
      f x = 1 / x := by

  apply
    imo2022_p2
      f
      hfpos

  intro x hx

  exact
    huniq
      x
      hx

end IMO2022P2
