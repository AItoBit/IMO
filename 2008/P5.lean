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

set_option grind.warning false

/-!
# IMO 2008 Problem 5

Let `n` and `k` be positive integers with `k ≥ n` and `k - n` even.  There are `2 * n` lamps,
labelled `1, …, 2n`, all initially off.  A *sequence of steps* of length `k` is a list of `k`
lamps, the `i`-th entry being the lamp switched at step `i`.

* `N` is the number of such sequences ending in the state where lamps `1, …, n` are on and
  lamps `n+1, …, 2n` are off;
* `M` is the number of such sequences ending in the same state in which, moreover, none of the
  lamps `n+1, …, 2n` is ever switched.

The answer is `N / M = 2 ^ (k - n)`.

Since a lamp starts off, it is on at the end iff it has been switched an odd number of times;
so the final state condition says exactly that each of the first `n` lamps is switched an odd
number of times and each of the last `n` lamps an even number of times.  A lamp among
`n+1, …, 2n` is never switched on iff it is never switched at all.  This is how the two counts
are formalised below, sequences being modelled as functions `Fin k → Fin (2 * n)`.
-/

namespace Imo2008P5

/-- The number of steps at which the lamp `i` is switched, in the sequence of steps `a`. -/
def cnt {k : ℕ} {L : Type} [DecidableEq L] (a : Fin k → L) (i : L) : ℕ :=
  (Finset.univ.filter fun t => a t = i).card

/-- The set of sequences of `k` steps on `2 * n` lamps ending in the state where the lamps
`1, …, n` (indices `0, …, n-1`) are on and the lamps `n+1, …, 2n` (indices `n, …, 2n-1`)
are off.  `N` is the cardinality of this set. -/
def Nset (n k : ℕ) : Finset (Fin k → Fin (2 * n)) :=
  Finset.univ.filter fun a =>
    (∀ i : Fin (2 * n), (i : ℕ) < n → Odd (cnt a i)) ∧
      (∀ i : Fin (2 * n), n ≤ (i : ℕ) → Even (cnt a i))

/-- The subset of `Nset n k` consisting of those sequences in which none of the last `n` lamps
is ever switched.  `M` is the cardinality of this set. -/
def Mset (n k : ℕ) : Finset (Fin k → Fin (2 * n)) :=
  (Nset n k).filter fun a => ∀ t, (a t : ℕ) < n

/-! ### Reformulation with lamps indexed by `Fin n ⊕ Fin n` -/

/-- The identification of the `2 * n` lamps with two copies of `Fin n`: the first copy is the
set `A = {1, …, n}` of lamps that must end up on, the second copy is the set
`B = {n+1, …, 2n}`. -/
def lampEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
  (finCongr (two_mul n)).trans finSumFinEquiv.symm

/-- `Nset` transported along `lampEquiv`. -/
def NsetS (n k : ℕ) : Finset (Fin k → Fin n ⊕ Fin n) :=
  Finset.univ.filter fun a =>
    (∀ i : Fin n, Odd (cnt a (Sum.inl i))) ∧ (∀ i : Fin n, Even (cnt a (Sum.inr i)))

/-- `Mset` transported along `lampEquiv`. -/
def MsetS (n k : ℕ) : Finset (Fin k → Fin n ⊕ Fin n) :=
  (NsetS n k).filter fun a => ∀ t, (a t).isLeft

/-- Sequences using only the lamps of `A`, each an odd number of times. -/
def Aset (n k : ℕ) : Finset (Fin k → Fin n) :=
  Finset.univ.filter fun y => ∀ i : Fin n, Odd (cnt y i)

/-- Forgetting which copy of `Fin n` a lamp belongs to. -/
def proj {n k : ℕ} (a : Fin k → Fin n ⊕ Fin n) : Fin k → Fin n := fun t => Sum.elim id id (a t)

/-! ### Basic lemmas on `cnt` -/

lemma cnt_comp_equiv {k : ℕ} {L L' : Type} [DecidableEq L] [DecidableEq L'] (e : L ≃ L')
    (a : Fin k → L) (i : L) : cnt (fun t => e (a t)) (e i) = cnt a i := by
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro t _
  simp [e.injective.eq_iff]

lemma cnt_proj {n k : ℕ} (a : Fin k → Fin n ⊕ Fin n) (i : Fin n) :
    cnt (proj a) i = cnt a (Sum.inl i) + cnt a (Sum.inr i) := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and, proj]
    cases h : a t <;> simp
  · simp only [Finset.disjoint_left, Finset.mem_filter]
    rintro t ⟨-, h1⟩ ⟨-, h2⟩
    rw [h1] at h2
    exact Sum.inl_ne_inr h2

/-! ### Transfer between the two models -/

lemma lampEquiv_symm_inl (n : ℕ) (j : Fin n) :
    (((lampEquiv n).symm (Sum.inl j) : Fin (2 * n)) : ℕ) = (j : ℕ) := by
  simp [lampEquiv]

lemma lampEquiv_symm_inr (n : ℕ) (j : Fin n) :
    (((lampEquiv n).symm (Sum.inr j) : Fin (2 * n)) : ℕ) = (j : ℕ) + n := by
  simp [lampEquiv]

lemma lampEquiv_isLeft {n : ℕ} (i : Fin (2 * n)) : (lampEquiv n i).isLeft ↔ (i : ℕ) < n := by
  rcases h : lampEquiv n i with j | j
  · have : i = (lampEquiv n).symm (Sum.inl j) := by rw [← h]; simp
    rw [this]
    simp [lampEquiv_symm_inl, j.2]
  · have : i = (lampEquiv n).symm (Sum.inr j) := by rw [← h]; simp
    rw [this]
    simp [lampEquiv_symm_inr]

lemma mem_NsetS_iff {n k : ℕ} (a : Fin k → Fin (2 * n)) :
    (fun t => lampEquiv n (a t)) ∈ NsetS n k ↔ a ∈ Nset n k := by
  simp only [NsetS, Nset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h1 ⟨i, hi⟩
      rwa [show (Sum.inl ⟨(i : ℕ), hi⟩ : Fin n ⊕ Fin n) = lampEquiv n i by
        apply (lampEquiv n).symm.injective; apply Fin.ext; simp [lampEquiv_symm_inl],
        cnt_comp_equiv] at this
    · have := h2 ⟨(i : ℕ) - n, by omega⟩
      rwa [show (Sum.inr ⟨(i : ℕ) - n, by omega⟩ : Fin n ⊕ Fin n) = lampEquiv n i by
        apply (lampEquiv n).symm.injective; apply Fin.ext; simp [lampEquiv_symm_inr]; omega,
        cnt_comp_equiv] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [show (Sum.inl i : Fin n ⊕ Fin n) = lampEquiv n ((lampEquiv n).symm (Sum.inl i)) by simp,
        cnt_comp_equiv]
      exact h1 _ (by rw [lampEquiv_symm_inl]; exact i.2)
    · rw [show (Sum.inr i : Fin n ⊕ Fin n) = lampEquiv n ((lampEquiv n).symm (Sum.inr i)) by simp,
        cnt_comp_equiv]
      exact h2 _ (by rw [lampEquiv_symm_inr]; omega)

lemma card_Nset_eq (n k : ℕ) : (Nset n k).card = (NsetS n k).card := by
  apply Finset.card_nbij' (fun a t => lampEquiv n (a t)) (fun b t => (lampEquiv n).symm (b t))
  · intro a ha
    exact (mem_NsetS_iff a).2 ha
  · intro b hb
    refine (mem_NsetS_iff _).1 ?_
    simpa using hb
  · intro a _; funext t; simp
  · intro b _; funext t; simp

lemma card_Mset_eq (n k : ℕ) : (Mset n k).card = (MsetS n k).card := by
  apply Finset.card_nbij' (fun a t => lampEquiv n (a t)) (fun b t => (lampEquiv n).symm (b t))
  · intro a ha
    simp only [Mset, Finset.coe_filter, Set.mem_setOf_eq] at ha
    simp only [MsetS, Finset.mem_coe, Finset.mem_filter]
    exact ⟨(mem_NsetS_iff a).2 ha.1, fun t => (lampEquiv_isLeft _).2 (ha.2 t)⟩
  · intro b hb
    simp only [MsetS, Finset.coe_filter, Set.mem_setOf_eq] at hb
    simp only [Mset, Finset.mem_coe, Finset.mem_filter]
    refine ⟨(mem_NsetS_iff _).1 (by simpa using hb.1), fun t => ?_⟩
    rw [← lampEquiv_isLeft]
    simpa using hb.2 t
  · intro a _; funext t; simp
  · intro b _; funext t; simp

lemma card_MsetS_eq (n k : ℕ) : (MsetS n k).card = (Aset n k).card := by
  apply Finset.card_nbij' proj (fun y t => Sum.inl (y t))
  · intro a ha
    simp only [MsetS, NsetS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha
    simp only [Aset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    have h0 : cnt a (Sum.inr i) = 0 := by
      simp only [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t _
      have hl := ha.2 t
      rcases h : a t with j | j
      · simp
      · rw [h] at hl; simp at hl
    rw [cnt_proj, h0, add_zero]
    exact ha.1.1 i
  · intro y hy
    simp only [Aset, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hy
    simp only [MsetS, NsetS, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, fun t => rfl⟩
    · have h : cnt (fun t => (Sum.inl (y t) : Fin n ⊕ Fin n)) (Sum.inl i) = cnt y i := by
        unfold cnt
        congr 1
        apply Finset.filter_congr
        intro t _
        simp
      rw [h]
      exact hy i
    · have h : cnt (fun t => (Sum.inl (y t) : Fin n ⊕ Fin n)) (Sum.inr i) = 0 := by
        simp [cnt]
      rw [h]
      exact ⟨0, rfl⟩
  · intro a ha
    simp only [MsetS, Finset.coe_filter, Set.mem_setOf_eq] at ha
    funext t
    have hl := ha.2 t
    rcases h : a t with j | j
    · simp [proj, h]
    · rw [h] at hl; simp at hl
  · intro y _; funext t; simp [proj]

/-! ### Counting the fibres -/

/-- The set of `ZMod 2`-valued functions that sum to zero on every fibre of `y`. -/
def Kset {n k : ℕ} (y : Fin k → Fin n) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter fun s => ∀ i : Fin n, ∑ t ∈ Finset.univ.filter fun t => y t = i, s t = 0

/-- Summing a `ZMod 2`-valued function over the fibres of `y`, as a linear map. -/
def fibreSum {n k : ℕ} (y : Fin k → Fin n) : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun s := fun i => ∑ t ∈ Finset.univ.filter fun t => y t = i, s t
  map_add' := by
    intro s s'
    funext i
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c s
    funext i
    simp [Finset.mul_sum]

lemma fibreSum_surjective {n k : ℕ} (y : Fin k → Fin n) (hy : Function.Surjective y) :
    Function.Surjective (fibreSum y) := by
  intro c
  choose rep hrep using hy
  refine ⟨fun t => if rep (y t) = t then c (y t) else 0, ?_⟩
  funext i
  show ∑ t ∈ Finset.univ.filter (fun t => y t = i), (if rep (y t) = t then c (y t) else 0) = c i
  rw [Finset.sum_eq_single (rep i)]
  · simp [hrep i]
  · intro t ht htne
    have hyt : y t = i := (Finset.mem_filter.1 ht).2
    have hne : rep (y t) ≠ t := by rw [hyt]; exact htne.symm
    simp [hne]
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ (rep i), hrep i⟩) h

lemma card_Kset {n k : ℕ} (y : Fin k → Fin n) (hy : Function.Surjective y) :
    (Kset y).card = 2 ^ (k - n) := by
  have hrange : LinearMap.range (fibreSum y) = ⊤ :=
    LinearMap.range_eq_top.2 (fibreSum_surjective y hy)
  have h1 : Module.finrank (ZMod 2) (LinearMap.ker (fibreSum y)) = k - n := by
    have h2 := LinearMap.finrank_range_add_finrank_ker (fibreSum y)
    rw [hrange] at h2
    simp [Module.finrank_fintype_fun_eq_card] at h2
    omega
  have h3 : Fintype.card (LinearMap.ker (fibreSum y)) = 2 ^ (k - n) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker (fibreSum y)), h1]
    simp
  have hker : Kset y = Finset.univ.filter (fun s => s ∈ LinearMap.ker (fibreSum y)) := by
    apply Finset.filter_congr
    intro s _
    simp only [LinearMap.mem_ker, funext_iff]
    rfl
  rw [hker, ← Fintype.card_subtype]
  exact h3

lemma surjective_of_mem_Aset {n k : ℕ} {y : Fin k → Fin n} (hy : y ∈ Aset n k) :
    Function.Surjective y := by
  intro i
  simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  have h := hy i
  have hne : cnt y i ≠ 0 := by
    rintro h0
    rw [h0] at h
    simp at h
  have hpos : 0 < (Finset.univ.filter fun t => y t = i).card := Nat.pos_of_ne_zero hne
  obtain ⟨t, ht⟩ := Finset.card_pos.1 hpos
  exact ⟨t, (Finset.mem_filter.1 ht).2⟩

lemma mem_NsetS_iff_of_proj {n k : ℕ} {y : Fin k → Fin n} (hy : y ∈ Aset n k)
    {a : Fin k → Fin n ⊕ Fin n} (h : proj a = y) :
    a ∈ NsetS n k ↔ ∀ i : Fin n, Even (cnt a (Sum.inr i)) := by
  simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  simp only [NsetS, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h2⟩
    exact h2
  · intro h2
    refine ⟨fun i => ?_, h2⟩
    have hodd := hy i
    rw [← h, cnt_proj] at hodd
    have hz := h2 i
    rw [Nat.even_iff] at hz
    rw [Nat.odd_iff] at hodd ⊢
    omega

/-- For a sequence lying over `y`, the fibre sums of the associated `ZMod 2`-valued function
vanish exactly when the lamps of `B` are switched an even number of times. -/
lemma sum_fibre_eq_zero_iff {n k : ℕ} {y : Fin k → Fin n} {a : Fin k → Fin n ⊕ Fin n}
    (h : proj a = y) (i : Fin n) :
    (∑ t ∈ Finset.univ.filter fun t => y t = i, (if (a t).isRight then (1 : ZMod 2) else 0)) = 0
      ↔ Even (cnt a (Sum.inr i)) := by
  rw [Finset.sum_boole]
  have hset : ((Finset.univ.filter fun t => y t = i).filter fun t => (a t).isRight = true) =
      (Finset.univ.filter fun t => a t = Sum.inr i) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    subst h
    cases ht : a t with
    | inl j => simp [proj, ht]
    | inr j => simp [proj, ht, eq_comm]
  rw [hset]
  exact ZMod.natCast_eq_zero_iff_even

lemma card_fibre {n k : ℕ} {y : Fin k → Fin n} (hy : y ∈ Aset n k) :
    ((NsetS n k).filter fun a => proj a = y).card = 2 ^ (k - n) := by
  rw [← card_Kset y (surjective_of_mem_Aset hy)]
  have hzo : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  apply Finset.card_nbij' (fun a t => if (a t).isRight then (1 : ZMod 2) else 0)
    (fun s t => if s t = 1 then Sum.inr (y t) else Sum.inl (y t))
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
    simp only [Kset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    exact (sum_fibre_eq_zero_iff ha.2 i).2 (((mem_NsetS_iff_of_proj hy ha.2).1 ha.1) i)
  · intro s hs
    simp only [Kset, Finset.coe_filter, Set.mem_setOf_eq] at hs
    set a : Fin k → Fin n ⊕ Fin n := fun t => if s t = 1 then Sum.inr (y t) else Sum.inl (y t)
      with ha
    have hproj : proj a = y := by
      funext t
      by_cases h : s t = 1 <;> simp [proj, ha, h]
    have hs' : ∀ t, (if (a t).isRight then (1 : ZMod 2) else 0) = s t := by
      intro t
      by_cases h : s t = 1
      · simp [ha, h]
      · rcases hzo (s t) with h0 | h1
        · simp [ha, h0]
        · exact absurd h1 h
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨(mem_NsetS_iff_of_proj hy hproj).2 (fun i => ?_), hproj⟩
    refine (sum_fibre_eq_zero_iff hproj i).1 ?_
    rw [Finset.sum_congr rfl (fun t _ => hs' t)]
    exact hs.2 i
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
    funext t
    have hp := ha.2
    cases ht : a t with
    | inl j =>
      have hj : y t = j := by rw [← hp]; simp [proj, ht]
      simp [ht, hj]
    | inr j =>
      have hj : y t = j := by rw [← hp]; simp [proj, ht]
      simp [ht, hj]
  · intro s _
    funext t
    by_cases h : s t = 1
    · simp [h]
    · rcases hzo (s t) with h0 | h1
      · simp [h0]
      · exact absurd h1 h

lemma card_NsetS (n k : ℕ) : (NsetS n k).card = 2 ^ (k - n) * (Aset n k).card := by
  have hmaps : Set.MapsTo (proj : (Fin k → Fin n ⊕ Fin n) → Fin k → Fin n) (NsetS n k) (Aset n k) := by
    intro a ha
    simp only [NsetS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha
    simp only [Aset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [cnt_proj]
    exact (ha.1 i).add_even (ha.2 i)
  rw [Finset.card_eq_sum_card_fiberwise hmaps,
    Finset.sum_congr rfl (fun y hy => card_fibre hy), Finset.sum_const, smul_eq_mul, mul_comm]

lemma card_filter_ge (n k : ℕ) :
    (Finset.univ.filter fun t : Fin k => n ≤ (t : ℕ)).card = k - n := by
  rw [← Nat.card_Ico n k]
  apply Finset.card_nbij (fun t : Fin k => (t : ℕ))
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ht
    simp [ht, t.2]
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro m hm
    simp only [Finset.coe_Ico, Set.mem_Ico] at hm
    exact ⟨⟨m, hm.2⟩, by simp [hm.1], rfl⟩

lemma Aset_nonempty {n k : ℕ} (hn : 0 < n) (hk : n ≤ k) (he : Even (k - n)) :
    (Aset n k).Nonempty := by
  refine ⟨fun t => if h : (t : ℕ) < n then ⟨t, h⟩ else ⟨0, hn⟩, ?_⟩
  simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  by_cases hi : (i : ℕ) = 0
  · have hset : (Finset.univ.filter fun t : Fin k =>
        (if h : (t : ℕ) < n then (⟨t, h⟩ : Fin n) else ⟨0, hn⟩) = i) =
        insert (⟨0, by omega⟩ : Fin k) (Finset.univ.filter fun t : Fin k => n ≤ (t : ℕ)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases h : (t : ℕ) < n
      · rw [dif_pos h]
        simp only [Fin.ext_iff]
        omega
      · rw [dif_neg h]
        simp only [Fin.ext_iff]
        omega
    have hnotmem : (⟨0, by omega⟩ : Fin k) ∉
        (Finset.univ.filter fun t : Fin k => n ≤ (t : ℕ)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [cnt, hset, Finset.card_insert_of_notMem hnotmem, card_filter_ge]
    rcases he with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  · have hik : (i : ℕ) < k := lt_of_lt_of_le i.2 hk
    have hset : (Finset.univ.filter fun t : Fin k =>
        (if h : (t : ℕ) < n then (⟨t, h⟩ : Fin n) else ⟨0, hn⟩) = i) = {(⟨i, hik⟩ : Fin k)} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      by_cases h : (t : ℕ) < n
      · rw [dif_pos h]
        simp only [Fin.ext_iff]
      · rw [dif_neg h]
        simp only [Fin.ext_iff]
        have := i.2
        omega
    rw [cnt, hset]
    simp

/-! ### The answer -/

/-- **IMO 2008 Problem 5.**  The number `N` of sequences of `k` steps ending with the lamps
`1, …, n` on and the lamps `n+1, …, 2n` off equals `2 ^ (k - n)` times the number `M` of such
sequences that never switch any of the lamps `n+1, …, 2n`. -/
theorem card_Nset_eq_mul_card_Mset (n k : ℕ) :
    (Nset n k).card = 2 ^ (k - n) * (Mset n k).card := by
  rw [card_Nset_eq, card_Mset_eq, card_NsetS, card_MsetS_eq]

/-- Under the hypotheses of the problem, `M ≠ 0`. -/
theorem card_Mset_pos {n k : ℕ} (hn : 0 < n) (hk : n ≤ k) (he : Even (k - n)) :
    0 < (Mset n k).card := by
  rw [card_Mset_eq, card_MsetS_eq, Finset.card_pos]
  exact Aset_nonempty hn hk he

/-- **IMO 2008 Problem 5**: the ratio `N / M` equals `2 ^ (k - n)`. -/
theorem ratio_eq {n k : ℕ} (hn : 0 < n) (hk : n ≤ k) (he : Even (k - n)) :
    ((Nset n k).card : ℚ) / (Mset n k).card = 2 ^ (k - n) := by
  have hM : ((Mset n k).card : ℚ) ≠ 0 := by
    exact_mod_cast (card_Mset_pos hn hk he).ne'
  rw [card_Nset_eq_mul_card_Mset]
  push_cast
  field_simp

end Imo2008P5
