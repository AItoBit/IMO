import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# IMO 2003, Problem 1

For every 101-element subset A of {1, ..., 1000000}, there exist 100 distinct
shifts from the same interval whose translates of A are pairwise disjoint.

The proof bounds the difference set by 10101, then chooses the shifts greedily.
 
-/

namespace IMO2003P1

open Finset

/-- The permitted shifts. -/
def S : Finset ℤ := Icc 1 1000000

/-- Translation of a finite set by an integer. -/
def translate (A : Finset ℤ) (x : ℤ) : Finset ℤ := A.image (fun a => a + x)

/-- All nonzero differences, together with zero. -/
def differences (A : Finset ℤ) : Finset ℤ :=
  insert 0 (A.offDiag.image (fun p => p.1 - p.2))

lemma zero_mem_differences (A : Finset ℤ) : 0 ∈ differences A := by
  simp [differences]

lemma sub_mem_differences {A : Finset ℤ} {a b : ℤ} (ha : a ∈ A) (hb : b ∈ A) :
    a - b ∈ differences A := by
  by_cases hab : a = b
  · subst b
    simpa using zero_mem_differences A
  · apply mem_insert_of_mem
    exact mem_image.mpr ⟨(a, b), mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩

lemma card_differences_le {A : Finset ℤ} (hA : A.card = 101) :
    (differences A).card ≤ 10101 := by
  calc
    (differences A).card ≤ (A.offDiag.image (fun p => p.1 - p.2)).card + 1 :=
      card_insert_le _ _
    _ ≤ A.offDiag.card + 1 := Nat.add_le_add_right card_image_le 1
    _ = 10101 := by rw [offDiag_card, hA]

/-- The chosen translates are pairwise disjoint. -/
def Good (A T : Finset ℤ) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (translate A x) (translate A y)

/-- The greedy construction works for each number of shifts up to 100.
In fact, it works for any 101-element set of integers, regardless of its location. -/
lemma greedy (A : Finset ℤ) (hA : A.card = 101) :
    ∀ k : ℕ, k ≤ 100 → ∃ T : Finset ℤ, T ⊆ S ∧ T.card = k ∧ Good A T := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨∅, by simp, by simp, by simp [Good]⟩
  | succ k ih =>
    intro hk
    obtain ⟨T, hTS, hTk, hgood⟩ := ih (by omega)
    let F : Finset ℤ := T.biUnion (fun t => (differences A).image (fun d => t + d))
    have hFcard : F.card ≤ T.card * 10101 :=
      card_biUnion_le_card_mul T _ 10101
        (fun _ _ => card_image_le.trans (card_differences_le hA))
    have hScard : S.card = 1000000 := by norm_num [S]
    have hFlt : F.card < S.card := by
      rw [hTk] at hFcard
      rw [hScard]
      omega
    obtain ⟨x, hxS, hxF⟩ := exists_mem_notMem_of_card_lt_card hFlt
    have hxT : x ∉ T := by
      intro h
      apply hxF
      exact mem_biUnion.mpr ⟨x, h,
        mem_image.mpr ⟨0, zero_mem_differences A, by simp⟩⟩
    have hxdis (t : ℤ) (ht : t ∈ T) : Disjoint (translate A x) (translate A t) := by
      apply disjoint_left.mpr
      intro v hvx hvt
      obtain ⟨a, ha, hav⟩ := mem_image.mp hvx
      obtain ⟨b, hb, hbv⟩ := mem_image.mp hvt
      apply hxF
      apply mem_biUnion.mpr
      refine ⟨t, ht, mem_image.mpr ⟨b - a, sub_mem_differences hb ha, ?_⟩⟩
      omega
    refine ⟨insert x T, insert_subset hxS hTS, ?_, ?_⟩
    · simp [card_insert_of_notMem hxT, hTk]
    · intro u hu v hv huv
      rcases mem_insert.mp hu with rfl | huT
      · rcases mem_insert.mp hv with rfl | hvT
        · exact False.elim (huv rfl)
        · exact hxdis v hvT
      · rcases mem_insert.mp hv with rfl | hvT
        · exact (hxdis u huT).symm
        · exact hgood u huT v hvT huv

/-- IMO 2003, Problem 1, in finite-set form. A set of cardinality 100
encodes 100 distinct shifts. -/
theorem imo2003_p1_finset (A : Finset ℤ) (_hAS : A ⊆ S) (hA : A.card = 101) :
    ∃ T : Finset ℤ, T ⊆ S ∧ T.card = 100 ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
        Disjoint (A.image (fun a => a + x)) (A.image (fun a => a + y)) :=
  greedy A hA 100 (by omega)

/-- IMO 2003, Problem 1, with an explicit indexed family of 100 distinct shifts. -/
theorem imo2003_p1 (A : Finset ℤ) (hAS : A ⊆ Icc 1 1000000) (hA : A.card = 101) :
    ∃ x : Fin 100 → ℤ,
      Function.Injective x ∧
      (∀ i, x i ∈ Icc 1 1000000) ∧
      ∀ i j, i ≠ j →
        Disjoint (A.image (fun a => a + x i)) (A.image (fun a => a + x j)) := by
  obtain ⟨T, hTS, hTcard, hgood⟩ := imo2003_p1_finset A hAS hA
  let e : Fin 100 ≃ {t // t ∈ T} := (Finset.equivFinOfCardEq hTcard).symm
  refine ⟨fun i => (e i).val, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact hTS (e i).property
  · intro i j hij
    apply hgood (e i).val (e i).property (e j).val (e j).property
    intro heq
    exact hij (e.injective (Subtype.ext heq))

end IMO2003P1
