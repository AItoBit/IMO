import Mathlib

namespace IMO2018P1

/-
We work analytically in ℝ².



    DE ∥ II'
    II' ∥ HH'
    FG ∥ HH'

and concludes

    DE ∥ FG.

For vectors in ℝ², parallelism is represented by linear
dependence / scalar multiplication.
-/

abbrev Point := ℝ × ℝ

def vec (A B : Point) : Point :=
  (B.1 - A.1, B.2 - A.2)

/--
Two vectors in ℝ² are parallel iff their determinant is zero.
-/
def ParallelVec (u v : Point) : Prop :=
  u.1 * v.2 - u.2 * v.1 = 0

/--
Two lines AB and CD are parallel iff their direction
vectors are parallel.
-/
def Parallel (A B C D : Point) : Prop :=
  ParallelVec (vec A B) (vec C D)


/- ============================================================
   Elementary vector facts
   ============================================================ -/

lemma parallelVec_refl (u : Point) :
    ParallelVec u u := by
  unfold ParallelVec
  ring


lemma parallelVec_symm
    {u v : Point}
    (h : ParallelVec u v) :
    ParallelVec v u := by
  unfold ParallelVec at h ⊢
  linarith


/--
If u ∥ v and v ∥ w, and v is nonzero, then u ∥ w.

In ℝ² this follows from the determinant identities.
-/
lemma parallelVec_trans
    {u v w : Point}
    (hv : v ≠ (0, 0))
    (huv : ParallelVec u v)
    (hvw : ParallelVec v w) :
    ParallelVec u w := by

  rcases v with ⟨vx, vy⟩
  rcases u with ⟨ux, uy⟩
  rcases w with ⟨wx, wy⟩

  simp only [Prod.fst, Prod.snd] at huv hvw ⊢

  have hvcoord :
      vx ≠ 0 ∨ vy ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨hvx, hvy⟩
    apply hv
    simp [hvx, hvy]

  rcases hvcoord with hvx | hvy

  · have h1 :
        uy = ux * vy / vx := by
      field_simp [hvx]
      nlinarith [huv]

    have h2 :
        wy = wx * vy / vx := by
      field_simp [hvx]
      nlinarith [hvw]

    rw [h1, h2]

    field_simp [hvx]
    ring

  · have h1 :
        ux = uy * vx / vy := by
      field_simp [hvy]
      nlinarith [huv]

    have h2 :
        wx = wy * vx / vy := by
      field_simp [hvy]
      nlinarith [hvw]

    rw [h1, h2]

    field_simp [hvy]
    ring


lemma parallel_symm
    {A B C D : Point}
    (h : Parallel A B C D) :
    Parallel C D A B := by
  exact parallelVec_symm h


/- ============================================================
   Affine/scalar form of parallelism
   ============================================================ -/

/--
A scalar multiple of a vector is parallel to it.
-/
lemma parallelVec_smul
    (u : Point)
    (t : ℝ) :
    ParallelVec
      (t * u.1, t * u.2)
      u := by
  unfold ParallelVec
  ring


/--
If the direction vector CD is a scalar multiple of AB,
then AB ∥ CD.
-/
lemma parallel_of_vec_eq_smul
    {A B C D : Point}
    {t : ℝ}
    (h :
      vec C D =
        (t * (vec A B).1,
         t * (vec A B).2)) :
    Parallel A B C D := by

  unfold Parallel

  rw [h]

  unfold ParallelVec

  ring


/- ============================================================
   The PDF's chain of parallelisms
   ============================================================ -/

/--
This theorem formalizes the final logical chain in Solution 2:

    DE ∥ II'
    II' ∥ HH'
    FG ∥ HH'

therefore

    DE ∥ FG.

The nondegeneracy assumptions correspond to the intermediate
lines being genuine lines rather than zero direction vectors.
-/
theorem pdf_parallel_chain
    (D E I I' H H' F G : Point)
    (hII_ne :
      vec I I' ≠ (0, 0))
    (hHH_ne :
      vec H H' ≠ (0, 0))
    (hDEII :
      Parallel D E I I')
    (hIIHH :
      Parallel I I' H H')
    (hFGHH :
      Parallel F G H H') :
    Parallel D E F G := by

  have hDEHH :
      Parallel D E H H' := by

    unfold Parallel at hDEII hIIHH ⊢

    exact
      parallelVec_trans
        hII_ne
        hDEII
        hIIHH

  have hHHFG :
      Parallel H H' F G := by
    exact parallel_symm hFGHH

  unfold Parallel at hDEHH hHHFG ⊢

  exact
    parallelVec_trans
      hHH_ne
      hDEHH
      hHHFG


/- ============================================================
   Rhombus diagonal model
   ============================================================ -/

/--
A convenient coordinate model for a parallelogram/rhombus.

If

    Q = H + H' - O,

then OHQH' is a parallelogram.
-/
def parallelogramFourth
    (O H H' : Point) : Point :=
  (H.1 + H'.1 - O.1,
   H.2 + H'.2 - O.2)


lemma parallelogramFourth_vec_HQ
    (O H H' : Point) :
    vec H (parallelogramFourth O H H')
      = vec O H' := by

  unfold vec parallelogramFourth

  apply Prod.ext <;> simp <;> ring


lemma parallelogramFourth_vec_H'Q
    (O H H' : Point) :
    vec H' (parallelogramFourth O H H')
      = vec O H := by

  unfold vec parallelogramFourth

  apply Prod.ext <;> simp <;> ring


/--
Opposite sides of the constructed parallelogram are parallel.
-/
lemma parallelogramFourth_parallel₁
    (O H H' : Point) :
    Parallel
      H
      (parallelogramFourth O H H')
      O
      H' := by

  unfold Parallel

  rw [parallelogramFourth_vec_HQ]

  exact parallelVec_refl _


lemma parallelogramFourth_parallel₂
    (O H H' : Point) :
    Parallel
      H'
      (parallelogramFourth O H H')
      O
      H := by

  unfold Parallel

  rw [parallelogramFourth_vec_H'Q]

  exact parallelVec_refl _


/- ============================================================
   Similarity / same-ratio lemma used in the PDF
   ============================================================ -/

/--
If I and I' divide OH and OH' by the same ratio t, then

    II' ∥ HH'.

This is the analytic form of the similarity argument in
Solution 2.
-/
lemma same_ratio_parallel
    (O H H' : Point)
    (t : ℝ)
    (I I' : Point)
    (hI :
      I =
        (O.1 + t * (H.1 - O.1),
         O.2 + t * (H.2 - O.2)))
    (hI' :
      I' =
        (O.1 + t * (H'.1 - O.1),
         O.2 + t * (H'.2 - O.2))) :
    Parallel I I' H H' := by

  unfold Parallel ParallelVec vec

  rw [hI, hI']

  simp

  ring


/- ============================================================
   Homothety lemma used for F,G
   ============================================================ -/

/--
If F and G are obtained from H and H' by the same homothety
with centre Q and ratio t, then

    FG ∥ HH'.

This is exactly the homothety step described in the PDF.
-/
lemma homothety_parallel
    (Q H H' F G : Point)
    (t : ℝ)
    (hF :
      F =
        (Q.1 + t * (H.1 - Q.1),
         Q.2 + t * (H.2 - Q.2)))
    (hG :
      G =
        (Q.1 + t * (H'.1 - Q.1),
         Q.2 + t * (H'.2 - Q.2))) :
    Parallel F G H H' := by

  unfold Parallel ParallelVec vec

  rw [hF, hG]

  simp

  ring


/- ============================================================
   Combined analytic form of Solution 2
   ============================================================ -/

/--
Mathlib-only formalization of the final construction of the
second solution from the PDF.

* I and I' divide OH and OH' in the same ratio,
  therefore II' ∥ HH'.

* F and G are corresponding points under a homothety centred
  at Q,
  therefore FG ∥ HH'.

* If DE ∥ II', then DE ∥ FG.
-/
theorem imo2018_p1_solution2_core
    (D E O H H' Q I I' F G : Point)
    (t s : ℝ)

    (hI :
      I =
        (O.1 + t * (H.1 - O.1),
         O.2 + t * (H.2 - O.2)))

    (hI' :
      I' =
        (O.1 + t * (H'.1 - O.1),
         O.2 + t * (H'.2 - O.2)))

    (hF :
      F =
        (Q.1 + s * (H.1 - Q.1),
         Q.2 + s * (H.2 - Q.2)))

    (hG :
      G =
        (Q.1 + s * (H'.1 - Q.1),
         Q.2 + s * (H'.2 - Q.2)))

    (hDEII :
      Parallel D E I I')

    (hII_ne :
      vec I I' ≠ (0, 0))

    (hHH_ne :
      vec H H' ≠ (0, 0)) :

    Parallel D E F G := by

  have hIIHH :
      Parallel I I' H H' :=
    same_ratio_parallel
      O H H'
      t
      I I'
      hI hI'

  have hFGHH :
      Parallel F G H H' :=
    homothety_parallel
      Q H H'
      F G
      s
      hF hG

  exact
    pdf_parallel_chain
      D E I I' H H' F G
      hII_ne
      hHH_ne
      hDEII
      hIIHH
      hFGHH


end IMO2018P1
