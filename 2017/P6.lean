import Mathlib

open BigOperators

namespace IMO2017P6

noncomputable section

abbrev Poly := MvPolynomial (Fin 2) ℤ

def Primitive (p : ℤ × ℤ) : Prop :=
  Int.gcd p.1 p.2 = 1

def pointVal (p : ℤ × ℤ) : Fin 2 → ℤ
  | ⟨0, _⟩ => p.1
  | ⟨1, _⟩ => p.2

def X : Poly :=
  MvPolynomial.X 0

def Y : Poly :=
  MvPolynomial.X 1

def linearForm (p : ℤ × ℤ) : Poly :=
  MvPolynomial.C p.2 * X -
  MvPolynomial.C p.1 * Y

lemma eval_X (p : ℤ × ℤ) :
    MvPolynomial.eval (pointVal p) X = p.1 := by
  simp [X, pointVal]

lemma eval_Y (p : ℤ × ℤ) :
    MvPolynomial.eval (pointVal p) Y = p.2 := by
  simp [Y, pointVal]

lemma eval_linearForm
    (p q : ℤ × ℤ) :
    MvPolynomial.eval (pointVal q) (linearForm p)
      = p.2 * q.1 - p.1 * q.2 := by
  simp [linearForm, eval_X, eval_Y]

lemma linearForm_self
    (p : ℤ × ℤ) :
    MvPolynomial.eval (pointVal p) (linearForm p) = 0 := by
  rw [eval_linearForm]
  ring

/--
Bézout for a primitive point.

If gcd(x,y)=1, there are α,β ∈ ℤ such that

  α*x + β*y = 1.
-/
lemma primitive_bezout
    {p : ℤ × ℤ}
    (hp : Primitive p) :
    ∃ α β : ℤ,
      α * p.1 + β * p.2 = 1 := by

  refine ⟨Int.gcdA p.1 p.2,
          Int.gcdB p.1 p.2, ?_⟩

  have h :=
    Int.gcd_eq_gcd_ab p.1 p.2

  unfold Primitive at hp

  rw [hp] at h

  norm_num at h ⊢

  nlinarith [h]

/--
The linear polynomial supplied by Bézout evaluates to 1
at a primitive point.
-/
lemma exists_linear_eval_one
    {p : ℤ × ℤ}
    (hp : Primitive p) :
    ∃ L : Poly,
      MvPolynomial.eval (pointVal p) L = 1 := by

  obtain ⟨α, β, hαβ⟩ :=
    primitive_bezout hp

  refine
    ⟨MvPolynomial.C α * X +
      MvPolynomial.C β * Y, ?_⟩

  simp [X, Y, pointVal]

  exact hαβ

/--
The polynomial used in the PDF to vanish at one old point.
-/
def vanishAt (p : ℤ × ℤ) : Poly :=
  linearForm p

/--
`vanishAt p` vanishes at p.
-/
lemma vanishAt_self
    (p : ℤ × ℤ) :
    MvPolynomial.eval (pointVal p) (vanishAt p) = 0 := by
  exact linearForm_self p

/--
Product of the linear factors corresponding to a finite set.
-/
def vanishProduct
    (S : Finset (ℤ × ℤ)) : Poly :=
  ∏ p ∈ S, vanishAt p

/--
If `p ∈ S`, the product vanishes at `p`.
-/
lemma eval_vanishProduct_eq_zero
    (S : Finset (ℤ × ℤ))
    {p : ℤ × ℤ}
    (hp : p ∈ S) :
    MvPolynomial.eval (pointVal p) (vanishProduct S) = 0 := by

  unfold vanishProduct

  rw [MvPolynomial.eval_prod]

  apply Finset.prod_eq_zero hp

  exact vanishAt_self p

/--
The correction form used in the PDF:

  b*x - a*y.
-/
lemma correction_factor_eval
    (old new : ℤ × ℤ) :
    MvPolynomial.eval
        (pointVal new)
        (MvPolynomial.C old.2 * X -
         MvPolynomial.C old.1 * Y)
      =
      old.2 * new.1 -
      old.1 * new.2 := by
  simp [X, Y, pointVal]

/--
Evaluation respects powers.
-/
lemma eval_pow
    (p : ℤ × ℤ)
    (F : Poly)
    (k : ℕ) :
    MvPolynomial.eval (pointVal p) (F ^ k)
      =
      (MvPolynomial.eval (pointVal p) F) ^ k := by
  simp

/--
Evaluation respects products.
-/
lemma eval_mul
    (p : ℤ × ℤ)
    (F G : Poly) :
    MvPolynomial.eval (pointVal p) (F * G)
      =
      MvPolynomial.eval (pointVal p) F *
      MvPolynomial.eval (pointVal p) G := by
  simp

/--
Algebraic heart of the inductive construction in the PDF.

If

  g(p)^k + D*h(p) = 1,

then the corrected polynomial evaluates to 1 at p.
-/
lemma correction_at_new_point
    (p : ℤ × ℤ)
    (g h L : Poly)
    (k : ℕ)
    (H :
      (MvPolynomial.eval (pointVal p) g) ^ k
        +
      MvPolynomial.eval (pointVal p) L *
      MvPolynomial.eval (pointVal p) h
        = 1) :
    MvPolynomial.eval
        (pointVal p)
        (g ^ k + L * h) = 1 := by

  simp only [
    MvPolynomial.eval_add,
    MvPolynomial.eval_mul,
    MvPolynomial.eval_pow
  ]

  exact H

/--
At an old point where the correction factor is zero,
the correction term disappears.
-/
lemma correction_vanishes_at_old_point
    (p : ℤ × ℤ)
    (g h L : Poly)
    (k : ℕ)
    (hL :
      MvPolynomial.eval (pointVal p) L = 0) :
    MvPolynomial.eval
        (pointVal p)
        (g ^ k + L * h)
      =
      (MvPolynomial.eval (pointVal p) g) ^ k := by

  simp [hL]

/--
Hence if g(p)=1 at an old point, the corrected polynomial
still evaluates to 1.
-/
lemma correction_preserves_old_point
    (p : ℤ × ℤ)
    (g h L : Poly)
    (k : ℕ)
    (hg :
      MvPolynomial.eval (pointVal p) g = 1)
    (hL :
      MvPolynomial.eval (pointVal p) L = 0) :
    MvPolynomial.eval
        (pointVal p)
        (g ^ k + L * h) = 1 := by

  rw [correction_vanishes_at_old_point
        p g h L k hL]

  rw [hg]

  simp

/--
This is the final construction from the PDF:

  h(x,y) = M (αx + βy)^d,

where αa + βb = 1.

At the primitive point p=(a,b), it evaluates to M.
-/
lemma exists_homogeneous_value
    {p : ℤ × ℤ}
    (hp : Primitive p)
    (M : ℤ)
    (d : ℕ) :
    ∃ h : Poly,
      MvPolynomial.eval (pointVal p) h = M := by

  obtain ⟨α, β, hαβ⟩ :=
    primitive_bezout hp

  let L : Poly :=
    MvPolynomial.C α * X +
    MvPolynomial.C β * Y

  refine
    ⟨MvPolynomial.C M * L ^ d, ?_⟩

  have hL :
      MvPolynomial.eval (pointVal p) L = 1 := by
    dsimp [L]
    simp [X, Y, pointVal]
    exact hαβ

  simp [L, hL]

end

end IMO2017P6
