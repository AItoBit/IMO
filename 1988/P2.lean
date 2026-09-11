import Mathlib

/-!
# IMO 1988 Problem 2

Let `n` be a positive integer and let `A 0, …, A (2n)` (that is, `2n+1` sets) be subsets of a
set `B` such that

* (a) each `A i` has exactly `2n` elements,
* (b) each `A i ∩ A j` with `i ≠ j` contains exactly one element,
* (c) every element of `B` belongs to at least two of the `A i`.

For which `n` can one assign to every element of `B` one of the numbers `0` and `1` in such a way
that each `A i` has `0` assigned to exactly `n` of its elements?

**Answer: exactly the even `n`.**

Main results:

* `IMO1988P2.card_idx_eq_two`: under (a), (b), (c) every element of `B` lies in *exactly* two of
  the sets, so the configuration is the edge set of the complete graph on `2n+1` vertices;
* `IMO1988P2.even_of_exists_assignment`: a valid assignment forces `n` to be even (double
  counting: `(2n+1) * n` must be twice the number of `0`-labelled elements);
* `IMO1988P2.exists_assignment_of_even`: for even `n`, every configuration admits a valid
  assignment (label an element `0` exactly when the circular distance of the two indices
  containing it is at most `n / 2`);
* `IMO1988P2.imo1988_p2`: the resulting equivalence for a fixed configuration;
* `IMO1988P2.exists_config`: configurations exist for every `n`;
* `IMO1988P2.imo1988_p2_answer`: `HasAssignment n ↔ Even n`, the answer to the question.

The accompanying handwritten solution sketch concludes "`4 ∣ n`"; that sketch uses a different
scaling of the parameter (it works with `n + 1` sets of size `n`). For the problem exactly as
stated above the answer is `Even n`, and `IMO1988P2.answer_ne_four_dvd` records that "`4 ∣ n`" is
not a correct answer (for `n = 2` a valid assignment always exists).
-/

namespace IMO1988P2

open Finset

section Config

variable {n : ℕ} {B : Type*} [DecidableEq B]

/-- The set of indices `i` such that `b ∈ A i`. -/
def idx (A : Fin (2 * n + 1) → Finset B) (b : B) : Finset (Fin (2 * n + 1)) :=
  Finset.univ.filter fun i => b ∈ A i

@[simp] lemma mem_idx {A : Fin (2 * n + 1) → Finset B} {b : B} {i : Fin (2 * n + 1)} :
    i ∈ idx A b ↔ b ∈ A i := by
  simp [idx]

variable (A : Fin (2 * n + 1) → Finset B)
  (hcard : ∀ i, (A i).card = 2 * n)
  (hint : ∀ i j, i ≠ j → ((A i) ∩ (A j)).card = 1)
  (hmem : ∀ b : B, 2 ≤ (idx A b).card)

section InterElem

include hint

/-- Choice of the unique element of `A i ∩ A j` for `i ≠ j`. -/
lemma exists_inter_fun [Nonempty B] :
    ∃ e : Fin (2 * n + 1) → Fin (2 * n + 1) → B, ∀ i j, i ≠ j → A i ∩ A j = {e i j} := by
  classical
  have hex : ∀ i j : Fin (2 * n + 1), ∃ x : B, i ≠ j → A i ∩ A j = {x} := by
    intro i j
    by_cases h : i ≠ j
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hint i j h)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨Classical.arbitrary B, fun h' => absurd h' h⟩
  choose e he using hex
  exact ⟨e, he⟩

end InterElem

section Basic

variable {A}
variable {e : Fin (2 * n + 1) → Fin (2 * n + 1) → B}
  (he : ∀ i j, i ≠ j → A i ∩ A j = {e i j})

include he

lemma inter_elem_mem_left {i j : Fin (2 * n + 1)} (hij : i ≠ j) : e i j ∈ A i := by
  have : e i j ∈ A i ∩ A j := by rw [he i j hij]; simp
  exact (Finset.mem_inter.mp this).1

lemma inter_elem_mem_right {i j : Fin (2 * n + 1)} (hij : i ≠ j) : e i j ∈ A j := by
  have : e i j ∈ A i ∩ A j := by rw [he i j hij]; simp
  exact (Finset.mem_inter.mp this).2

include hmem in
/-- Every element of `A i` is of the form `e i j` for some `j ≠ i`. -/
lemma surj_inter_elem (i : Fin (2 * n + 1)) {x : B} (hx : x ∈ A i) :
    ∃ j, j ≠ i ∧ e i j = x := by
  have h1 : 1 < (idx A x).card := lt_of_lt_of_le one_lt_two (hmem x)
  rw [Finset.one_lt_card_iff_nontrivial] at h1
  obtain ⟨j, hj, hji⟩ := h1.exists_ne i
  refine ⟨j, hji, ?_⟩
  have hxj : x ∈ A j := mem_idx.mp hj
  have : x ∈ A i ∩ A j := Finset.mem_inter.mpr ⟨hx, hxj⟩
  rw [he i j (Ne.symm hji)] at this
  exact (Finset.mem_singleton.mp this).symm

include hcard hmem in
/-- For fixed `i`, the map `j ↦ e i j` is injective on the indices `j ≠ i`. -/
lemma injOn_inter_elem (i : Fin (2 * n + 1)) :
    Set.InjOn (e i) (Finset.univ.erase i) := by
  refine Finset.injOn_of_surjOn_of_card_le (t := A i) (e i) (fun j hj => ?_) (fun x hx => ?_) ?_
  · exact inter_elem_mem_left he (Ne.symm (Finset.ne_of_mem_erase (Finset.mem_coe.mp hj)))
  · obtain ⟨j, hj, hjx⟩ := surj_inter_elem (A := A) hmem he i (Finset.mem_coe.mp hx)
    exact ⟨j, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩), hjx⟩
  · rw [hcard i, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega

end Basic

include hcard hint hmem

/-- Every element of `B` lies in exactly two of the sets `A i` (condition (c) is an equality). -/
theorem card_idx_eq_two (b : B) : (idx A b).card = 2 := by
  classical
  haveI : Nonempty B := ⟨b⟩
  obtain ⟨e, he⟩ := exists_inter_fun A hint
  obtain ⟨i, hi⟩ : ∃ i, i ∈ idx A b := Finset.card_pos.mp (by have := hmem b; omega)
  obtain ⟨j, hji, hjb⟩ := surj_inter_elem (A := A) hmem he i (mem_idx.mp hi)
  have hsub : idx A b = {i, j} := by
    apply Finset.Subset.antisymm
    · intro k hk
      by_cases hki : k = i
      · simp [hki]
      · have hbk : b ∈ A k := mem_idx.mp hk
        have : b ∈ A i ∩ A k := Finset.mem_inter.mpr ⟨mem_idx.mp hi, hbk⟩
        rw [he i k (Ne.symm hki)] at this
        have hbe : e i k = b := (Finset.mem_singleton.mp this).symm
        have hkj : k = j :=
          injOn_inter_elem (A := A) hcard hmem he i (by simp [hki]) (by simp [hji])
            (by rw [hbe, hjb])
        simp [hkj]
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact mem_idx.mpr (by rw [← hjb]; exact inter_elem_mem_right he (Ne.symm hji))
  rw [hsub, Finset.card_insert_of_notMem (by simpa using Ne.symm hji), Finset.card_singleton]

/-- Double counting: summing over all indices the number of elements of `A i` labelled `0`
counts each `0`-labelled element exactly twice. -/
theorem sum_card_filter_eq (f : B → Fin 2) :
    ∑ i : Fin (2 * n + 1), ((A i).filter fun b => f b = 0).card
      = 2 * (((Finset.univ.biUnion A).filter fun b => f b = 0).card) := by
  classical
  set U : Finset B := Finset.univ.biUnion A with hUdef
  have hsubU : ∀ i, A i ⊆ U := fun i b hb => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hb⟩
  have h1 : ∀ i : Fin (2 * n + 1), ((A i).filter fun b => f b = 0).card
      = ∑ b ∈ U, (if b ∈ A i ∧ f b = 0 then 1 else 0) := by
    intro i
    rw [← Finset.card_filter]
    congr 1
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hsubU i h.1, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  calc ∑ i : Fin (2 * n + 1), ((A i).filter fun b => f b = 0).card
      = ∑ i : Fin (2 * n + 1), ∑ b ∈ U, (if b ∈ A i ∧ f b = 0 then 1 else 0) := by
        exact Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ b ∈ U, ∑ i : Fin (2 * n + 1), (if b ∈ A i ∧ f b = 0 then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ b ∈ U, (if f b = 0 then 2 else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : f b = 0
        · simp only [hb, and_true, if_true]
          rw [← Finset.card_filter]
          exact card_idx_eq_two A hcard hint hmem b
        · simp [hb]
    _ = 2 * ((U.filter fun b => f b = 0).card) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
        simp [Nat.mul_comm]

/-- If a valid `0`/`1` assignment exists, then `n` must be even. -/
theorem even_of_exists_assignment (f : B → Fin 2)
    (hf : ∀ i, ((A i).filter fun b => f b = 0).card = n) : Even n := by
  classical
  have h := sum_card_filter_eq A hcard hint hmem f
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hf i] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  have h2 : Even ((2 * n + 1) * n) := by rw [h]; exact even_two_mul _
  rcases Nat.even_mul.mp h2 with hodd | hn
  · exact absurd hodd (by simp)
  · exact hn

end Config

section Distance

/-- The circular distance from `0` of an element of `Fin (2n+1)`. -/
def cls (n : ℕ) (x : Fin (2 * n + 1)) : ℕ := min x.val (2 * n + 1 - x.val)

lemma cls_neg (n : ℕ) (x : Fin (2 * n + 1)) : cls n (-x) = cls n x := by
  by_cases h : x = 0
  · rw [h, neg_zero]
  · have hx : x.val < 2 * n + 1 := x.isLt
    have hx0 : x.val ≠ 0 := fun hv => h (Fin.eq_of_val_eq (by rw [hv, Fin.val_zero]))
    unfold cls
    rw [Fin.val_neg, if_neg h]
    omega

/-- For even `n`, exactly `n` of the nonzero elements of `Fin (2n+1)` are at circular distance
at most `n / 2` from `0`. -/
lemma card_filter_cls_zero {n : ℕ} (hn : Even n) :
    ((Finset.univ.erase (0 : Fin (2 * n + 1))).filter fun x => cls n x ≤ n / 2).card = n := by
  classical
  obtain ⟨k, hk⟩ := hn
  have hnk : n = 2 * k := by omega
  subst hnk
  have himg : (((Finset.univ.erase (0 : Fin (2 * (2 * k) + 1))).filter
      fun x => cls (2 * k) x ≤ (2 * k) / 2).image Fin.val)
      = (Finset.Icc 1 k) ∪ (Finset.Icc (3 * k + 1) (4 * k)) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_union, Finset.mem_Icc, cls]
    constructor
    · rintro ⟨x, ⟨hx0, hxc⟩, rfl⟩
      have h1 : x.val < 2 * (2 * k) + 1 := x.isLt
      have h2 : x.val ≠ 0 := fun hv => hx0 (Fin.eq_of_val_eq (by rw [hv, Fin.val_zero]))
      omega
    · intro ht
      refine ⟨⟨t, by omega⟩, ⟨?_, ?_⟩, rfl⟩
      · intro hc
        have : t = 0 := by simpa [Fin.ext_iff] using hc
        omega
      · simp only []
        omega
  have hcard := congrArg Finset.card himg
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  rw [hcard, Finset.card_union_of_disjoint, Nat.card_Icc, Nat.card_Icc]
  · omega
  · simp only [Finset.disjoint_left, Finset.mem_Icc]
    omega

/-- Translation invariance of the count of indices at small circular distance. -/
lemma card_filter_cls {n : ℕ} (i : Fin (2 * n + 1)) :
    ((Finset.univ.erase i).filter fun j => cls n (i - j) ≤ n / 2).card
      = ((Finset.univ.erase (0 : Fin (2 * n + 1))).filter fun x => cls n x ≤ n / 2).card := by
  classical
  refine Finset.card_bij (fun j _ => i - j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
    exact ⟨sub_ne_zero_of_ne (Ne.symm hj.1), hj.2⟩
  · intro a _ b _ hab
    have := congrArg (fun y => i - y) hab
    simpa [sub_sub_cancel] using this
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hx
    refine ⟨i - x, ?_, show i - (i - x) = x from sub_sub_cancel i x⟩
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun hc => hx.1 (sub_eq_self.mp hc), by rw [sub_sub_cancel]; exact hx.2⟩

end Distance

section Construction

variable {n : ℕ} {B : Type*} [DecidableEq B]
variable (A : Fin (2 * n + 1) → Finset B)
  (hcard : ∀ i, (A i).card = 2 * n)
  (hint : ∀ i j, i ≠ j → ((A i) ∩ (A j)).card = 1)
  (hmem : ∀ b : B, 2 ≤ (idx A b).card)

include hcard hint hmem

/-- If `n` is even, a valid `0`/`1` assignment exists. -/
theorem exists_assignment_of_even (hn : Even n) :
    ∃ f : B → Fin 2, ∀ i, ((A i).filter fun b => f b = 0).card = n := by
  classical
  rcases isEmpty_or_nonempty B with hB | hB
  · refine ⟨fun _ => 0, fun i => ?_⟩
    have h0 : A i = ∅ := Finset.eq_empty_of_isEmpty _
    have h1 := hcard i
    rw [h0] at h1
    simp only [Finset.card_empty] at h1
    simp [h0]
    omega
  · obtain ⟨e, he⟩ := exists_inter_fun A hint
    have hidx : ∀ p q : Fin (2 * n + 1), p ≠ q → idx A (e p q) = {p, q} := by
      intro p q hpq
      have h1 : ({p, q} : Finset (Fin (2 * n + 1))) ⊆ idx A (e p q) := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact mem_idx.mpr (inter_elem_mem_left he hpq)
        · exact mem_idx.mpr (inter_elem_mem_right he hpq)
      have h2 : ({p, q} : Finset (Fin (2 * n + 1))).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
      have h3 : (idx A (e p q)).card = 2 := card_idx_eq_two A hcard hint hmem _
      exact (Finset.eq_of_subset_of_card_le h1 (by rw [h2, h3])).symm
    refine ⟨fun b => if (∀ p ∈ idx A b, ∀ q ∈ idx A b, p ≠ q → cls n (p - q) ≤ n / 2)
      then 0 else 1, fun i => ?_⟩
    have hval : ∀ p q : Fin (2 * n + 1), p ≠ q →
        ((if (∀ r ∈ idx A (e p q), ∀ s ∈ idx A (e p q), r ≠ s → cls n (r - s) ≤ n / 2)
          then (0 : Fin 2) else 1) = 0 ↔ cls n (p - q) ≤ n / 2) := by
      intro p q hpq
      have hC : (∀ r ∈ idx A (e p q), ∀ s ∈ idx A (e p q), r ≠ s → cls n (r - s) ≤ n / 2)
          ↔ cls n (p - q) ≤ n / 2 := by
        rw [hidx p q hpq]
        constructor
        · intro h
          exact h p (by simp) q (by simp) hpq
        · intro h r hr s hs hrs
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr hs
          rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
          · exact absurd rfl hrs
          · exact h
          · rw [show r - s = -(s - r) from (neg_sub s r).symm, cls_neg]
            exact h
          · exact absurd rfl hrs
      by_cases hc : (∀ r ∈ idx A (e p q), ∀ s ∈ idx A (e p q), r ≠ s → cls n (r - s) ≤ n / 2)
      · rw [if_pos hc]
        exact iff_of_true rfl (hC.mp hc)
      · rw [if_neg hc]
        exact iff_of_false (by decide) (fun h => hc (hC.mpr h))
    have hbij : ((Finset.univ.erase i).filter fun j => cls n (i - j) ≤ n / 2).card
        = ((A i).filter fun b =>
            (if (∀ p ∈ idx A b, ∀ q ∈ idx A b, p ≠ q → cls n (p - q) ≤ n / 2)
              then (0 : Fin 2) else 1) = 0).card := by
      refine Finset.card_bij (fun j _ => e i j) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hj
        refine Finset.mem_filter.mpr ⟨inter_elem_mem_left he (Ne.symm hj.1), ?_⟩
        exact (hval i j (Ne.symm hj.1)).mpr hj.2
      · intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at ha hb
        exact injOn_inter_elem (A := A) hcard hmem he i
          (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨ha.1, Finset.mem_univ a⟩))
          (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hb.1, Finset.mem_univ b⟩)) hab
      · intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨j, hj, hjx⟩ := surj_inter_elem (A := A) hmem he i hx.1
        refine ⟨j, ?_, hjx⟩
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
        refine ⟨hj, ?_⟩
        exact (hval i j (Ne.symm hj)).mp (by rw [hjx]; exact hx.2)
    rw [← hbij, card_filter_cls i, card_filter_cls_zero hn]

/-- **IMO 1988, Problem 2.** For a configuration as in the problem, an assignment of `0`/`1` to
the elements of `B` such that each `A i` carries exactly `n` zeros exists if and only if `n` is
even. -/
theorem imo1988_p2 :
    (∃ f : B → Fin 2, ∀ i, ((A i).filter fun b => f b = 0).card = n) ↔ Even n := by
  constructor
  · rintro ⟨f, hf⟩
    exact even_of_exists_assignment A hcard hint hmem f hf
  · intro hn
    exact exists_assignment_of_even A hcard hint hmem hn

end Construction

section Existence

/-- The edges of the complete graph on `2n+1` vertices. -/
def Edge (n : ℕ) : Type := {p : Fin (2 * n + 1) × Fin (2 * n + 1) // p.1 < p.2}

instance (n : ℕ) : DecidableEq (Edge n) := Subtype.instDecidableEq
instance (n : ℕ) : Fintype (Edge n) := Subtype.fintype _

/-- The family of "stars": `star n i` is the set of edges incident to the vertex `i`. -/
def star (n : ℕ) (i : Fin (2 * n + 1)) : Finset (Edge n) :=
  Finset.univ.filter fun p => p.val.1 = i ∨ p.val.2 = i

@[simp] lemma mem_star {n : ℕ} {i : Fin (2 * n + 1)} {p : Edge n} :
    p ∈ star n i ↔ p.val.1 = i ∨ p.val.2 = i := by
  simp [star]

/-- The edge joining two distinct vertices. -/
def edgeOf {n : ℕ} {i j : Fin (2 * n + 1)} (hij : i ≠ j) : Edge n :=
  ⟨(min i j, max i j), by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h⟩

lemma star_card (n : ℕ) (i : Fin (2 * n + 1)) : (star n i).card = 2 * n := by
  classical
  have h : (Finset.univ.erase i).card = 2 * n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  rw [← h]
  refine (Finset.card_bij (fun (j : Fin (2 * n + 1)) (hj : j ∈ Finset.univ.erase i) =>
    edgeOf (i := i) (j := j) (Ne.symm (Finset.ne_of_mem_erase hj))) ?_ ?_ ?_).symm
  · intro j hj
    have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
    rw [mem_star]
    rcases lt_or_gt_of_ne hij with h | h
    · left; simp [edgeOf, min_eq_left h.le]
    · right; simp [edgeOf, max_eq_left h.le]
  · intro a ha b hb hab
    have hia : i ≠ a := Ne.symm (Finset.ne_of_mem_erase ha)
    have hib : i ≠ b := Ne.symm (Finset.ne_of_mem_erase hb)
    have h1 : min i a = min i b := congrArg (fun p => p.val.1) hab
    have h2 : max i a = max i b := congrArg (fun p => p.val.2) hab
    rcases lt_or_gt_of_ne hia with h | h <;> rcases lt_or_gt_of_ne hib with h' | h'
    · rw [max_eq_right h.le, max_eq_right h'.le] at h2; exact h2
    · rw [min_eq_left h.le, min_eq_right h'.le] at h1; omega
    · rw [min_eq_right h.le, min_eq_left h'.le] at h1; omega
    · rw [min_eq_right h.le, min_eq_right h'.le] at h1; exact h1
  · intro p hp
    rw [mem_star] at hp
    have hlt : p.val.1 < p.val.2 := p.2
    rcases hp with h | h
    · refine ⟨p.val.2, Finset.mem_erase.mpr ⟨fun hc => by omega, Finset.mem_univ _⟩, ?_⟩
      have h1 : i < p.val.2 := by rw [← h]; exact hlt
      apply Subtype.ext
      rw [Prod.ext_iff]
      exact ⟨by simp [edgeOf, min_eq_left h1.le, h], by simp [edgeOf, max_eq_right h1.le]⟩
    · refine ⟨p.val.1, Finset.mem_erase.mpr ⟨fun hc => by omega, Finset.mem_univ _⟩, ?_⟩
      have h1 : p.val.1 < i := by rw [← h]; exact hlt
      apply Subtype.ext
      rw [Prod.ext_iff]
      exact ⟨by simp [edgeOf, min_eq_right h1.le], by simp [edgeOf, max_eq_left h1.le, h]⟩

lemma star_inter (n : ℕ) {i j : Fin (2 * n + 1)} (hij : i ≠ j) :
    (star n i ∩ star n j) = {edgeOf hij} := by
  classical
  ext p
  simp only [Finset.mem_inter, mem_star, Finset.mem_singleton]
  have hlt : p.val.1 < p.val.2 := p.2
  constructor
  · rintro ⟨hi | hi, hj | hj⟩
    · exact absurd (hi ▸ hj : i = j) hij
    · have h1 : i < j := by rw [← hi, ← hj]; exact hlt
      apply Subtype.ext
      rw [Prod.ext_iff]
      exact ⟨by simp [edgeOf, min_eq_left h1.le, hi], by simp [edgeOf, max_eq_right h1.le, hj]⟩
    · have h1 : j < i := by rw [← hj, ← hi]; exact hlt
      apply Subtype.ext
      rw [Prod.ext_iff]
      exact ⟨by simp [edgeOf, min_eq_right h1.le, hj], by simp [edgeOf, max_eq_left h1.le, hi]⟩
    · exact absurd (hi ▸ hj : i = j) hij
  · rintro rfl
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨Or.inl (by simp [edgeOf, min_eq_left h.le]),
        Or.inr (by simp [edgeOf, max_eq_right h.le])⟩
    · exact ⟨Or.inr (by simp [edgeOf, max_eq_left h.le]),
        Or.inl (by simp [edgeOf, min_eq_right h.le])⟩

lemma star_mem (n : ℕ) (p : Edge n) : 2 ≤ (idx (star n) p).card := by
  classical
  have hsub : ({p.val.1, p.val.2} : Finset (Fin (2 * n + 1))) ⊆ idx (star n) p := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact mem_idx.mpr (mem_star.mpr (Or.inl rfl))
    · exact mem_idx.mpr (mem_star.mpr (Or.inr rfl))
  have hne : p.val.1 ≠ p.val.2 := ne_of_lt p.2
  have hc : ({p.val.1, p.val.2} : Finset (Fin (2 * n + 1))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  calc 2 = ({p.val.1, p.val.2} : Finset (Fin (2 * n + 1))).card := hc.symm
    _ ≤ (idx (star n) p).card := Finset.card_le_card hsub

/-- Configurations satisfying (a), (b), (c) exist for every `n`: take for `B` the set of edges of
the complete graph on `2n+1` vertices, and for `A i` the set of edges through the vertex `i`. -/
theorem exists_config (n : ℕ) :
    (∀ i, (star n i).card = 2 * n) ∧ (∀ i j, i ≠ j → ((star n i) ∩ (star n j)).card = 1) ∧
      (∀ p : Edge n, 2 ≤ (idx (star n) p).card) :=
  ⟨star_card n, fun i j hij => by rw [star_inter n hij, Finset.card_singleton], star_mem n⟩

/-- `HasAssignment n` states that *every* family `A 0, …, A (2n)` of subsets of a set `B`
satisfying (a), (b), (c) admits an assignment of `0`/`1` to the elements of `B` for which each
`A i` has `0` assigned to exactly `n` of its elements. -/
def HasAssignment (n : ℕ) : Prop :=
  ∀ (B : Type) [DecidableEq B] (A : Fin (2 * n + 1) → Finset B),
    (∀ i, (A i).card = 2 * n) → (∀ i j, i ≠ j → ((A i) ∩ (A j)).card = 1) →
    (∀ b : B, 2 ≤ (idx A b).card) →
    ∃ f : B → Fin 2, ∀ i, ((A i).filter fun b => f b = 0).card = n

/-- **IMO 1988, Problem 2, final answer.** The values of `n` for which *every* configuration as in
the problem admits an assignment of `0`/`1` making each `A i` carry exactly `n` zeros are exactly
the even ones. (The forward implication uses that configurations do exist for every `n`.) -/
theorem imo1988_p2_answer (n : ℕ) : HasAssignment n ↔ Even n := by
  obtain ⟨h1, h2, h3⟩ := exists_config n
  constructor
  · intro h
    obtain ⟨f, hf⟩ := h (Edge n) (star n) h1 h2 h3
    exact even_of_exists_assignment (star n) h1 h2 h3 f hf
  · intro hn B _ A hA1 hA2 hA3
    exact exists_assignment_of_even A hA1 hA2 hA3 hn

/-- The answer is *not* "`4 ∣ n`": for `n = 2` every configuration admits a valid assignment,
although `4` does not divide `2`. -/
theorem answer_ne_four_dvd : ¬ (∀ n : ℕ, HasAssignment n ↔ 4 ∣ n) := by
  intro h
  have h2 : HasAssignment 2 := (imo1988_p2_answer 2).mpr (by decide)
  have : (4 : ℕ) ∣ 2 := (h 2).mp h2
  omega

end Existence

end IMO1988P2
