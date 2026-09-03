import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Imo1964P4

/-- Any finset with at least three elements contains three pairwise distinct elements. -/
private lemma exists_three_distinct {α : Type*} [DecidableEq α] {B : Finset α}
    (h : 3 ≤ B.card) :
    ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  have h1 : 2 ≤ (B.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (B.erase x).card)
  have h2 : 1 ≤ ((B.erase x).erase y).card := by rw [Finset.card_erase_of_mem hy]; omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((B.erase x).erase y).card)
  have hzx : z ∈ B.erase x := Finset.mem_of_mem_erase hz
  exact ⟨x, hx, y, Finset.mem_of_mem_erase hy, z, Finset.mem_of_mem_erase hzx,
    (Finset.ne_of_mem_erase hy).symm, (Finset.ne_of_mem_erase hzx).symm,
    (Finset.ne_of_mem_erase hz).symm⟩

/-- In `Fin 3`, two colours that both avoid the same two distinct colours are equal. -/
private lemma fin3_eq_of_ne {t1 t2 c d : Fin 3} (h : t1 ≠ t2)
    (hc1 : c ≠ t1) (hc2 : c ≠ t2) (hd1 : d ≠ t1) (hd2 : d ≠ t2) : c = d := by
  revert h hc1 hc2 hd1 hd2
  revert t1 t2 c d
  decide

/-- A monochromatic triangle gives the required set of three people. -/
private lemma triangle_solution {topic : Sym2 (Fin 17) → Fin 3} {a b c : Fin 17} {t : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : topic s(a, b) = t) (h2 : topic s(a, c) = t) (h3 : topic s(b, c) = t) :
    ∃ (s : Finset (Fin 17)) (t : Fin 3),
      3 ≤ s.card ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ (_ : x ≠ y), topic s(x, y) = t := by
  refine ⟨{a, b, c}, t, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | assumption
        | (rw [Sym2.eq_swap]; assumption)

end Imo1964P4

open Imo1964P4 in
/--
Each pair from $17$ people exchange letters on one of three topics. Prove that there are at least
$3$ people who write to each other on the same topic. [In other words, if we color the edges of the
complete graph $K_{17}$ with three colors, then we can find a triangle all the same color.]
-/
theorem imo_1964_p4
    -- a topic corresponding to each unordered pair of distinct people
    (topic : Sym2 (Fin 17) → Fin 3) :
    ∃ (s : Finset (Fin 17)) (t : Fin 3),
      3 ≤ s.card ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ (_h : x ≠ y), topic s(x, y) = t := by
  classical
  -- Pigeonhole at person `0`: some topic `t1` is used with at least six other people.
  obtain ⟨t1, -, ht1⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := (Finset.univ : Finset (Fin 17)).erase 0) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun u => topic s(0, u)) (n := 5) (fun a _ => Finset.mem_univ _)
      (by simp [Finset.card_erase_of_mem])
  set A : Finset (Fin 17) := {x ∈ (Finset.univ : Finset (Fin 17)).erase 0 | topic s(0, x) = t1}
    with hAdef
  have hA0 : ∀ x ∈ A, x ≠ 0 := by
    intro x hx
    rw [hAdef, Finset.mem_filter] at hx
    exact Finset.ne_of_mem_erase hx.1
  have hAt : ∀ x ∈ A, topic s(0, x) = t1 := by
    intro x hx
    rw [hAdef, Finset.mem_filter] at hx
    exact hx.2
  by_cases hedge1 : ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ topic s(x, y) = t1
  · obtain ⟨x, hx, y, hy, hxy, hcol⟩ := hedge1
    exact triangle_solution (Ne.symm (hA0 x hx)) (Ne.symm (hA0 y hy)) hxy
      (hAt x hx) (hAt y hy) hcol
  push Not at hedge1
  -- No edge inside `A` has colour `t1`.
  have hAne : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → topic s(x, y) ≠ t1 := by
    intro x hx y hy hxy
    exact hedge1 x hx y hy hxy
  -- Pick a person `a` in `A` and pigeonhole again with the two remaining topics.
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  have hcardA' : 5 ≤ (A.erase a).card := by
    rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨t2, ht2mem, ht2⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := A.erase a) (t := (Finset.univ : Finset (Fin 3)).erase t1)
      (f := fun u => topic s(a, u)) (n := 2)
      (by
        intro u hu
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        exact hAne a ha u (Finset.mem_of_mem_erase hu)
          (Ne.symm (Finset.ne_of_mem_erase hu)))
      (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
        simp only [Finset.card_univ, Fintype.card_fin]
        omega)
  have ht12 : t1 ≠ t2 := Ne.symm (Finset.ne_of_mem_erase ht2mem)
  set B : Finset (Fin 17) := {x ∈ A.erase a | topic s(a, x) = t2} with hBdef
  have hBA : ∀ x ∈ B, x ∈ A := by
    intro x hx
    rw [hBdef, Finset.mem_filter] at hx
    exact Finset.mem_of_mem_erase hx.1
  have hBa : ∀ x ∈ B, x ≠ a := by
    intro x hx
    rw [hBdef, Finset.mem_filter] at hx
    exact Finset.ne_of_mem_erase hx.1
  have hBt : ∀ x ∈ B, topic s(a, x) = t2 := by
    intro x hx
    rw [hBdef, Finset.mem_filter] at hx
    exact hx.2
  by_cases hedge2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ topic s(x, y) = t2
  · obtain ⟨x, hx, y, hy, hxy, hcol⟩ := hedge2
    exact triangle_solution (Ne.symm (hBa x hx)) (Ne.symm (hBa y hy)) hxy
      (hBt x hx) (hBt y hy) hcol
  push Not at hedge2
  -- Every edge inside `B` avoids both `t1` and `t2`, hence they all share the third colour.
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    exists_three_distinct (B := B) (by omega)
  have key : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → topic s(u, v) ≠ t1 ∧ topic s(u, v) ≠ t2 :=
    fun u hu v hv huv => ⟨hAne u (hBA u hu) v (hBA v hv) huv, hedge2 u hu v hv huv⟩
  obtain ⟨hxy1, hxy2⟩ := key x hx y hy hxy
  obtain ⟨hxz1, hxz2⟩ := key x hx z hz hxz
  obtain ⟨hyz1, hyz2⟩ := key y hy z hz hyz
  refine triangle_solution (topic := topic) (t := topic s(x, y)) hxy hxz hyz rfl ?_ ?_
  · exact (fin3_eq_of_ne ht12 hxz1 hxz2 hxy1 hxy2)
  · exact (fin3_eq_of_ne ht12 hyz1 hyz2 hxy1 hxy2)
