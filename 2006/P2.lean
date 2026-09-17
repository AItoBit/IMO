import Mathlib

/-!
# IMO 2006, Problem 2 — combinatorial core

Let `P` be a regular 2006-gon.

A diagonal is called good if its endpoints divide the boundary into
two arcs containing an odd number of polygon sides. Polygon sides
themselves are also declared good.

The official argument proves that for every isosceles triangle having
two good sides one can select two boundary sides such that

* the two selected sides are distinct;
* no selected side is used by two different triangles.

Thus, if `T` is the finite type of such triangles, there is an
injection

    T × Fin 2 ↪ Fin 2006.

Cardinality immediately gives

    2 * #T ≤ 2006,

hence

    #T ≤ 1003.
-/

namespace IMO2006P2

/--
The abstract counting lemma underlying IMO 2006 Problem 2.

`Special` is the type of isosceles triangles having two good sides.

For each special triangle, the supplied solution assigns two boundary
sides.  If no boundary side is assigned twice, this gives an injection

`Special × Fin 2 → Fin 2006`.

Therefore there are at most `1003` special triangles.
-/
theorem iso_odd_triangle_bound
    (Special : Type)
    [Fintype Special]
    (assignedSide : Special × Fin 2 → Fin 2006)
    (hassigned : Function.Injective assignedSide) :
    Fintype.card Special ≤ 1003 := by
  have hcard :
      Fintype.card (Special × Fin 2) ≤ Fintype.card (Fin 2006) :=
    Fintype.card_le_of_injective assignedSide hassigned

  simp only [
    Fintype.card_prod,
    Fintype.card_fin
  ] at hcard

  omega


/--
A formulation closer to the wording of the supplied proof.

For each special triangle `t`, choose two boundary sides
`first t` and `second t`.

The hypotheses say:

* the two sides selected for one triangle differ;
* first sides of different triangles differ;
* second sides of different triangles differ;
* a first side is never a second side belonging to another triangle.

These conditions imply that all `2 * #Special` assigned sides are
different, so there are at most `1003` special triangles.
-/
theorem iso_odd_triangle_bound_of_pair_assignment
    (Special : Type)
    [Fintype Special]
    (first second : Special → Fin 2006)
    (hne : ∀ t, first t ≠ second t)
    (hfirst :
      ∀ ⦃s t⦄, first s = first t → s = t)
    (hsecond :
      ∀ ⦃s t⦄, second s = second t → s = t)
    (hcross :
      ∀ s t, first s ≠ second t) :
    Fintype.card Special ≤ 1003 := by

  let assigned : Special × Fin 2 → Fin 2006 :=
    fun x =>
      if x.2 = (0 : Fin 2) then
        first x.1
      else
        second x.1

  have hassigned : Function.Injective assigned := by
    intro x y hxy

    rcases x with ⟨x, i⟩
    rcases y with ⟨y, j⟩

    have hi : i = 0 ∨ i = 1 := by
      fin_cases i <;> simp

    have hj : j = 0 ∨ j = 1 := by
      fin_cases j <;> simp

    rcases hi with rfl | rfl <;>
      rcases hj with rfl | rfl

    · -- first x = first y
      simp only [assigned, if_pos rfl] at hxy
      have hxy' : x = y := hfirst hxy
      subst y
      rfl

    · -- first x = second y: impossible
      simp only [assigned] at hxy
      exact False.elim ((hcross x y) hxy)

    · -- second x = first y: impossible
      simp only [assigned] at hxy
      have hne' : first y ≠ second x := hcross y x
      exact False.elim (hne' hxy.symm)

    · -- second x = second y
      simp only [assigned] at hxy
      have hxy' : x = y := hsecond hxy
      subst y
      rfl

  exact
    iso_odd_triangle_bound
      Special
      assigned
      hassigned


/--
The numerical heart of the result:
if two distinct resources are required for each object and only
2006 resources are available, there can be at most 1003 objects.
-/
theorem two_times_card_le_2006
    (Special : Type)
    [Fintype Special]
    (assignedSide : Special × Fin 2 → Fin 2006)
    (hassigned : Function.Injective assignedSide) :
    2 * Fintype.card Special ≤ 2006 := by
  have hcard :
      Fintype.card (Special × Fin 2) ≤ Fintype.card (Fin 2006) :=
    Fintype.card_le_of_injective assignedSide hassigned

  simp only [
    Fintype.card_prod,
    Fintype.card_fin
  ] at hcard

  omega


/--
The numerical division step appearing at the end of the olympiad proof.
-/
theorem half_of_2006_bound
    (n : ℕ)
    (h : 2 * n ≤ 2006) :
    n ≤ 1003 := by
  omega

end IMO2006P2
