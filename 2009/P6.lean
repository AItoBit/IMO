import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

/-!
# IMO 2009, Problem 6 (the grasshopper problem)

Let `a₁, a₂, …, aₙ` be distinct positive integers and let `M` be a set of `n - 1` positive
integers not containing `s = a₁ + a₂ + ⋯ + aₙ`.  A grasshopper is to jump along the real axis,
starting at the point `0` and making `n` jumps to the right with lengths `a₁, a₂, …, aₙ` in some
order.  Prove that the order can be chosen in such a way that the grasshopper never lands on any
point in `M`.

The jump lengths are modelled by a list `l : List ℕ` of distinct positive integers, and choosing
an order means choosing a permutation `l'` of `l`.  The points the grasshopper visits are the
partial sums `(l'.take k).sum` for `k ≥ 1`.
-/

namespace IMO2009P6

open List

/-- `SafeFrom M p l` says that a grasshopper standing at the point `p` and performing the jumps
of `l` in order never lands on a point of `M`; if `l` is empty this asserts that `p` itself is
not in `M`. -/
def SafeFrom (M : Finset ℕ) : ℕ → List ℕ → Prop
  | p, [] => p ∉ M
  | p, a :: t => p + a ∉ M ∧ SafeFrom M (p + a) t

@[simp] lemma safeFrom_nil (M : Finset ℕ) (p : ℕ) : SafeFrom M p [] ↔ p ∉ M := Iff.rfl

@[simp] lemma safeFrom_cons (M : Finset ℕ) (p a : ℕ) (t : List ℕ) :
    SafeFrom M p (a :: t) ↔ p + a ∉ M ∧ SafeFrom M (p + a) t := Iff.rfl

/-- If every obstacle lies strictly below the current position, the grasshopper is safe
whatever it does (all its future positions are at least the current one). -/
lemma safeFrom_of_all_lt (M : Finset ℕ) :
    ∀ (l : List ℕ) (p : ℕ), (∀ z ∈ M, z < p) → (∀ x ∈ l, 0 < x) → SafeFrom M p l := by
  intro l
  induction l with
  | nil => intro p h _; exact fun hp => absurd (h p hp) (lt_irrefl p)
  | cons b v ih =>
      intro p h hposl
      have hb : 0 < b := hposl b (List.mem_cons_self ..)
      refine ⟨fun hmem => absurd (h _ hmem) (by omega), ?_⟩
      exact ih (p + b) (fun z hz => by have := h z hz; omega)
        (fun x hx => hposl x (List.mem_cons_of_mem _ hx))

/-- Being safe for `M.erase m` is the same as being safe for `M` once we are past `m`. -/
lemma safeFrom_of_erase (M : Finset ℕ) (m : ℕ) :
    ∀ (t : List ℕ) (q : ℕ), m < q → (∀ x ∈ t, 0 < x) →
      SafeFrom (M.erase m) q t → SafeFrom M q t := by
  intro t
  induction t with
  | nil =>
      intro q hq _ h
      simp only [safeFrom_nil] at h ⊢
      intro hmem
      exact h (Finset.mem_erase.2 ⟨by omega, hmem⟩)
  | cons b v ih =>
      intro q hq hposl h
      have hb : 0 < b := hposl b (List.mem_cons_self ..)
      obtain ⟨h1, h2⟩ := h
      refine ⟨fun hmem => h1 (Finset.mem_erase.2 ⟨by omega, hmem⟩), ?_⟩
      exact ih (q + b) (by omega) (fun x hx => hposl x (List.mem_cons_of_mem _ hx)) h2

/-- Safety in terms of partial sums. -/
lemma safeFrom_take (M : Finset ℕ) :
    ∀ (l : List ℕ) (p : ℕ), SafeFrom M p l → ∀ k, 0 < k → p + (l.take k).sum ∉ M := by
  intro l
  induction l with
  | nil => intro p h k _; simpa using h
  | cons b v ih =>
      intro p h k hk
      obtain ⟨h1, h2⟩ := h
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using h1
      · have := ih (p + b) h2 j hj
        simpa [List.take_succ_cons, ← Nat.add_assoc] using this

/-- **Repair lemma.**  Suppose the grasshopper at `q` plans to jump `a` first and then the jumps
of `t` (all of which are smaller than `a`), and that this plan avoids all obstacles except
possibly the obstacle `m₁`, below which there is no obstacle above `q`.  Then the plan can be
repaired: if the plan does land on `m₁`, the jump `a` is delayed by one step. -/
lemma repair (M : Finset ℕ) (m₁ a : ℕ) :
    ∀ (t : List ℕ) (q : ℕ), (∀ x ∈ t, 0 < x ∧ x < a) →
      (∀ z ∈ M, z ≤ q ∨ m₁ ≤ z) → SafeFrom (M.erase m₁) q (a :: t) →
      q + a + t.sum ∉ M → ∃ t', t' ~ a :: t ∧ SafeFrom M q t' := by
  intro t
  induction t with
  | nil =>
      intro q _ _ _ hfinal
      exact ⟨[a], List.Perm.refl _, by simpa using hfinal, by simpa using hfinal⟩
  | cons b v ih =>
      intro q hlt hgap hsafe hfinal
      obtain ⟨h1, h3, h4⟩ := hsafe
      obtain ⟨hb0, hba⟩ : 0 < b ∧ b < a := hlt b (List.mem_cons_self ..)
      have hvpos : ∀ x ∈ v, 0 < x ∧ x < a := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
      have hvpos' : ∀ x ∈ v, 0 < x := fun x hx => (hvpos x hx).1
      rcases lt_trichotomy (q + a) m₁ with hcase | hcase | hcase
      · -- `m₁` is still ahead:  jump `b` now and keep `a` in reserve
        have hqb : q + b ∉ M := by
          intro hmem; rcases hgap _ hmem with h | h <;> omega
        have hsafe' : SafeFrom (M.erase m₁) (q + b) (a :: v) := by
          refine ⟨?_, ?_⟩
          · rw [show q + b + a = q + a + b by omega]; exact h3
          · rw [show q + b + a = q + a + b by omega]; exact h4
        have hfinal' : q + b + a + v.sum ∉ M := by
          rw [show q + b + a + v.sum = q + a + (b :: v).sum by simp; omega]; exact hfinal
        obtain ⟨t', hperm, hs⟩ := ih (q + b) hvpos
          (fun z hz => by
            rcases hgap z hz with h | h
            exacts [Or.inl (by omega), Or.inr h])
          hsafe' hfinal'
        exact ⟨b :: t', (hperm.cons b).trans (List.Perm.swap a b v), hqb, hs⟩
      · -- the plan lands on `m₁`:  swap the jumps `a` and `b`
        have hqb : q + b ∉ M := by
          intro hmem; rcases hgap _ hmem with h | h <;> omega
        have hab : q + b + a ∉ M := by
          rw [show q + b + a = q + a + b by omega]
          intro hmem; exact h3 (Finset.mem_erase.2 ⟨by omega, hmem⟩)
        refine ⟨b :: a :: v, List.Perm.swap a b v, hqb, hab, ?_⟩
        refine safeFrom_of_erase M m₁ v (q + b + a) (by omega) hvpos' ?_
        rw [show q + b + a = q + a + b by omega]; exact h4
      · -- the plan is already past `m₁`, so it is safe
        refine ⟨a :: b :: v, List.Perm.refl _, ?_, ?_⟩
        · intro hmem; exact h1 (Finset.mem_erase.2 ⟨by omega, hmem⟩)
        · exact safeFrom_of_erase M m₁ (b :: v) (q + a) hcase
            (fun x hx => by rcases List.mem_cons.1 hx with rfl | hx
                            · exact hb0
                            · exact hvpos' x hx) ⟨h3, h4⟩

/-- Every nonempty list of naturals has a greatest element. -/
lemma exists_max_mem : ∀ (l : List ℕ), l ≠ [] → ∃ a ∈ l, ∀ x ∈ l, x ≤ a := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons b v ih =>
      intro _
      rcases v with _ | ⟨c, w⟩
      · exact ⟨b, by simp, by simp⟩
      · obtain ⟨a, ha, hmax⟩ := ih (by simp)
        rcases le_total a b with h | h
        · refine ⟨b, by simp, ?_⟩
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact le_refl _
          · exact (hmax x hx).trans h
        · refine ⟨a, List.mem_cons_of_mem _ ha, ?_⟩
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact h
          · exact hmax x hx

/-- The main induction:  a grasshopper standing at `p`, with jumps `l` (distinct, positive) still
to perform, can avoid the obstacle set `M` provided that fewer than `l.length` obstacles lie
beyond `p` and that its final landing point is not an obstacle. -/
theorem main_aux : ∀ n : ℕ, ∀ (l : List ℕ) (M : Finset ℕ) (p : ℕ), l.length = n →
    (∀ x ∈ l, 0 < x) → l.Nodup → (M.filter (fun m => p < m)).card < n → p + l.sum ∉ M →
    ∃ l', l' ~ l ∧ SafeFrom M p l' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro l M p hlen hpos hnd hcard hsum
    rcases Finset.eq_empty_or_nonempty (M.filter (fun m => p < m)) with hMp | hMp
    · -- no obstacle lies beyond `p`:  any order will do
      have hle : ∀ z ∈ M, z ≤ p := by
        intro z hz
        by_contra h
        have : z ∈ M.filter (fun m => p < m) := Finset.mem_filter.2 ⟨hz, by omega⟩
        rw [hMp] at this
        exact absurd this (Finset.notMem_empty z)
      refine ⟨l, List.Perm.refl _, ?_⟩
      rcases l with _ | ⟨b, v⟩
      · simp at hlen; omega
      · have hb : 0 < b := hpos b (by simp)
        refine ⟨fun hmem => by have := hle _ hmem; omega, ?_⟩
        exact safeFrom_of_all_lt M v (p + b) (fun z hz => by have := hle z hz; omega)
          (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
    · -- there is an obstacle beyond `p`
      have hMpcard : 0 < (M.filter (fun m => p < m)).card := Finset.card_pos.2 hMp
      have hn : 2 ≤ n := by omega
      have hlne : l ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      obtain ⟨a, haL, hamax⟩ := exists_max_mem l hlne
      have ha0 : 0 < a := hpos a haL
      have hperm_l : l ~ a :: l.erase a := List.perm_cons_erase haL
      have hLlen : (l.erase a).length = n - 1 := by
        rw [List.length_erase_of_mem haL, hlen]
      have hLnd : (l.erase a).Nodup := hnd.erase a
      have hLmem : ∀ x ∈ l.erase a, x ∈ l ∧ x ≠ a := by
        intro x hx
        have := (List.Nodup.mem_erase_iff hnd).1 hx
        exact ⟨this.2, this.1⟩
      have hLpos : ∀ x ∈ l.erase a, 0 < x := fun x hx => hpos x (hLmem x hx).1
      have hLlt : ∀ x ∈ l.erase a, x < a := by
        intro x hx
        have := hamax x (hLmem x hx).1
        have := (hLmem x hx).2
        omega
      have hLsum : l.sum = a + (l.erase a).sum := by
        have := hperm_l.sum_eq
        simpa using this
      by_cases hA : p + a ∈ M
      · -- the largest jump is blocked
        have hpaMp : p + a ∈ M.filter (fun m => p < m) := Finset.mem_filter.2 ⟨hA, by omega⟩
        by_cases hB : ∀ b ∈ l.erase a, p + b ∉ M
        · -- no other single jump is blocked
          have hcard' : (M.filter (fun m => p + a < m)).card < n - 1 := by
            have hsub : M.filter (fun m => p + a < m) ⊆
                (M.filter (fun m => p < m)).erase (p + a) := by
              intro z hz
              rw [Finset.mem_filter] at hz
              exact Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨hz.1, by omega⟩⟩
            have h1 := Finset.card_le_card hsub
            have h2 : ((M.filter (fun m => p < m)).erase (p + a)).card =
                (M.filter (fun m => p < m)).card - 1 := Finset.card_erase_of_mem hpaMp
            omega
          obtain ⟨t, htperm, htsafe⟩ := IH (n - 1) (by omega) (l.erase a) M (p + a) hLlen
            hLpos hLnd hcard' (by rw [show p + a + (l.erase a).sum = p + l.sum by omega]; exact hsum)
          have htlen : t.length = n - 1 := by rw [htperm.length_eq, hLlen]
          rcases t with _ | ⟨b, v⟩
          · simp at htlen; omega
          · obtain ⟨h1, h2⟩ := htsafe
            have hbL : b ∈ l.erase a := htperm.mem_iff.1 (List.mem_cons_self ..)
            refine ⟨b :: a :: v, ?_, hB b hbL, ?_, ?_⟩
            · exact ((List.Perm.swap a b v).trans ((htperm.cons a).trans hperm_l.symm))
            · rw [show p + b + a = p + a + b by omega]; exact h1
            · rw [show p + b + a = p + a + b by omega]; exact h2
        · -- some other single jump is blocked
          push_neg at hB
          obtain ⟨b₀, hb₀L, hb₀M⟩ := hB
          have hb₀lt : b₀ < a := hLlt b₀ hb₀L
          have hb₀0 : 0 < b₀ := hLpos b₀ hb₀L
          have hb₀Mp : p + b₀ ∈ (M.filter (fun m => p < m)).erase (p + a) :=
            Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨hb₀M, by omega⟩⟩
          -- a pigeonhole argument produces a jump `b` with both `p + b` and `p + b + a` free
          obtain ⟨b, hbL, hbM1, hbM2⟩ : ∃ b ∈ l.erase a, p + b ∉ M ∧ p + b + a ∉ M := by
            by_contra hcon
            push_neg at hcon
            have hmap : ∀ x ∈ (l.erase a).toFinset,
                (fun b => if p + b ∈ M then p + b else p + b + a) x ∈
                  (M.filter (fun m => p < m)).erase (p + a) := by
              intro x hx
              rw [List.mem_toFinset] at hx
              have hx0 : 0 < x := hLpos x hx
              have hxa : x < a := hLlt x hx
              by_cases h : p + x ∈ M
              · simp only [h, if_pos]
                exact Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨h, by omega⟩⟩
              · simp only [h, if_neg, if_false]
                exact Finset.mem_erase.2
                  ⟨by omega, Finset.mem_filter.2 ⟨hcon x hx h, by omega⟩⟩
            have hinj : Set.InjOn (fun b => if p + b ∈ M then p + b else p + b + a)
                ((l.erase a).toFinset : Set ℕ) := by
              intro x hx y hy hxy
              simp only [Finset.coe_sort_coe, Finset.mem_coe, List.mem_toFinset] at hx hy
              have hx0 : 0 < x := hLpos x hx
              have hxa : x < a := hLlt x hx
              have hy0 : 0 < y := hLpos y hy
              have hya : y < a := hLlt y hy
              by_cases h1 : p + x ∈ M <;> by_cases h2 : p + y ∈ M <;>
                simp only [h1, h2, if_pos, if_neg, if_false, if_true] at hxy <;> omega
            have hcard1 := Finset.card_le_card_of_injOn _ hmap hinj
            have hcard2 : ((l.erase a).toFinset).card = n - 1 := by
              rw [List.toFinset_card_of_nodup hLnd, hLlen]
            have hcard3 : ((M.filter (fun m => p < m)).erase (p + a)).card =
                (M.filter (fun m => p < m)).card - 1 := Finset.card_erase_of_mem hpaMp
            omega
          have hb0 : 0 < b := hLpos b hbL
          have hblt : b < a := hLlt b hbL
          have hEsum : (l.erase a).sum = b + ((l.erase a).erase b).sum := by
            have := (List.perm_cons_erase hbL).sum_eq
            simpa using this
          have hcard' : (M.filter (fun m => p + b + a < m)).card < n - 2 := by
            have hsub : M.filter (fun m => p + b + a < m) ⊆
                (((M.filter (fun m => p < m)).erase (p + a)).erase (p + b₀)) := by
              intro z hz
              rw [Finset.mem_filter] at hz
              refine Finset.mem_erase.2 ⟨by omega, Finset.mem_erase.2 ⟨by omega, ?_⟩⟩
              exact Finset.mem_filter.2 ⟨hz.1, by omega⟩
            have h1 := Finset.card_le_card hsub
            have h2 : ((M.filter (fun m => p < m)).erase (p + a)).card =
                (M.filter (fun m => p < m)).card - 1 := Finset.card_erase_of_mem hpaMp
            have h3 : (((M.filter (fun m => p < m)).erase (p + a)).erase (p + b₀)).card =
                ((M.filter (fun m => p < m)).erase (p + a)).card - 1 :=
              Finset.card_erase_of_mem hb₀Mp
            have h4 : 0 < ((M.filter (fun m => p < m)).erase (p + a)).card :=
              Finset.card_pos.2 ⟨p + b₀, hb₀Mp⟩
            omega
          obtain ⟨t, htperm, htsafe⟩ := IH (n - 2) (by omega) ((l.erase a).erase b) M (p + b + a)
            (by rw [List.length_erase_of_mem hbL, hLlen]; omega)
            (fun x hx => hLpos x (List.mem_of_mem_erase hx))
            (hLnd.erase b) hcard'
            (by rw [show p + b + a + ((l.erase a).erase b).sum = p + l.sum by omega]; exact hsum)
          refine ⟨b :: a :: t, ?_, hbM1, hbM2, htsafe⟩
          refine ((htperm.cons a).cons b).trans ?_
          refine (List.Perm.swap a b ((l.erase a).erase b)).trans ?_
          exact (((List.perm_cons_erase hbL).symm).cons a).trans hperm_l.symm
      · -- the largest jump is free:  use the repair lemma
        have hm₁mem := Finset.min'_mem _ hMp
        set m₁ := (M.filter (fun m => p < m)).min' hMp with hm₁def
        have hm₁M : m₁ ∈ M := (Finset.mem_filter.1 hm₁mem).1
        have hm₁p : p < m₁ := (Finset.mem_filter.1 hm₁mem).2
        have hgap : ∀ z ∈ M, z ≤ p ∨ m₁ ≤ z := by
          intro z hz
          by_cases h : p < z
          · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hz, h⟩))
          · exact Or.inl (by omega)
        have hcard' : ((M.erase m₁).filter (fun m => p + a < m)).card < n - 1 := by
          have hsub : (M.erase m₁).filter (fun m => p + a < m) ⊆
              (M.filter (fun m => p < m)).erase m₁ := by
            intro z hz
            rw [Finset.mem_filter, Finset.mem_erase] at hz
            exact Finset.mem_erase.2 ⟨hz.1.1, Finset.mem_filter.2 ⟨hz.1.2, by omega⟩⟩
          have h1 := Finset.card_le_card hsub
          have h2 : ((M.filter (fun m => p < m)).erase m₁).card =
              (M.filter (fun m => p < m)).card - 1 := Finset.card_erase_of_mem hm₁mem
          omega
        obtain ⟨t, htperm, htsafe⟩ := IH (n - 1) (by omega) (l.erase a) (M.erase m₁) (p + a)
          hLlen hLpos hLnd hcard'
          (by
            rw [show p + a + (l.erase a).sum = p + l.sum by omega]
            exact fun hmem => hsum (Finset.mem_of_mem_erase hmem))
        have htsum : t.sum = (l.erase a).sum := htperm.sum_eq
        obtain ⟨t', hperm', hsafe'⟩ := repair M m₁ a t p
          (fun x hx => ⟨hLpos x (htperm.mem_iff.1 hx), hLlt x (htperm.mem_iff.1 hx)⟩)
          hgap
          ⟨fun hmem => hA (Finset.mem_of_mem_erase hmem), htsafe⟩
          (by rw [show p + a + t.sum = p + l.sum by omega]; exact hsum)
        exact ⟨t', hperm'.trans ((htperm.cons a).trans hperm_l.symm), hsafe'⟩
