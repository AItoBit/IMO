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

namespace Imo1976P5

/-- The "number of `-1` coefficients" in row `i`, as an integer. -/
noncomputable def negCount {p q : ℕ} (a : Fin p → Fin q → ℤ) (i : Fin p) : ℤ :=
  ∑ j : Fin q, (if a i j = -1 then (1 : ℤ) else 0)

/-- The "number of `+1` coefficients" in row `i`, as an integer. -/
noncomputable def posCount {p q : ℕ} (a : Fin p → Fin q → ℤ) (i : Fin p) : ℤ :=
  ∑ j : Fin q, (if a i j = 1 then (1 : ℤ) else 0)

/-- A row cannot have more than `q` coefficients equal to `±1`. -/
lemma posCount_add_negCount_le {p q : ℕ} (a : Fin p → Fin q → ℤ) (i : Fin p) :
    posCount a i + negCount a i ≤ (q : ℤ) := by
  unfold posCount negCount
  rw [← Finset.sum_add_distrib]
  calc ∑ j : Fin q, ((if a i j = 1 then (1 : ℤ) else 0) + (if a i j = -1 then (1 : ℤ) else 0))
      ≤ ∑ _j : Fin q, (1 : ℤ) := by
        refine Finset.sum_le_sum ?_
        intro j _
        by_cases h1 : a i j = 1
        · simp [h1]
        · simp only [h1, if_false, zero_add]
          split <;> norm_num
    _ = (q : ℤ) := by simp

/-- Lower bound for a row sum when all entries `x j` lie in `[0, q]`. -/
lemma row_sum_lower {p q : ℕ} (a : Fin p → Fin q → ℤ)
    (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    (x : Fin q → ℤ) (hx0 : ∀ j, 0 ≤ x j) (hxq : ∀ j, x j ≤ (q : ℤ)) (i : Fin p) :
    -(q : ℤ) * negCount a i ≤ ∑ j : Fin q, a i j * x j := by
  unfold negCount
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j _
  rcases ha i j with h | h | h
  · have := hx0 j
    have := hxq j
    simp [h]
    linarith
  · simp [h]
  · have := hx0 j
    have h1 : (1 : ℤ) ≠ -1 := by norm_num
    simp [h, h1]
    linarith

/-- Upper bound for a row sum when all entries `x j` lie in `[0, q]`. -/
lemma row_sum_upper {p q : ℕ} (a : Fin p → Fin q → ℤ)
    (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    (x : Fin q → ℤ) (hx0 : ∀ j, 0 ≤ x j) (hxq : ∀ j, x j ≤ (q : ℤ)) (i : Fin p) :
    ∑ j : Fin q, a i j * x j ≤ (q : ℤ) * posCount a i := by
  unfold posCount
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j _
  rcases ha i j with h | h | h
  · have := hx0 j
    have h1 : (-1 : ℤ) ≠ 1 := by norm_num
    simp [h, h1]
    linarith
  · simp [h]
  · have := hxq j
    simp [h]
    linarith

/-- Every row sum lies in an interval of length `q ^ 2`. -/
lemma row_sum_mem_Icc {p q : ℕ} (a : Fin p → Fin q → ℤ)
    (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    (x : Fin q → ℤ) (hx0 : ∀ j, 0 ≤ x j) (hxq : ∀ j, x j ≤ (q : ℤ)) (i : Fin p) :
    (∑ j : Fin q, a i j * x j) ∈
      Finset.Icc (-(q : ℤ) * negCount a i) (-(q : ℤ) * negCount a i + (q : ℤ) ^ 2) := by
  have hlow := row_sum_lower a ha x hx0 hxq i
  have hup := row_sum_upper a ha x hx0 hxq i
  have hcount := posCount_add_negCount_le a i
  have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  refine Finset.mem_Icc.mpr ⟨hlow, ?_⟩
  have : (q : ℤ) * posCount a i ≤ -(q : ℤ) * negCount a i + (q : ℤ) ^ 2 := by
    nlinarith [hcount, hq]
  linarith

/-- **IMO 1976, Problem 5.**  For a homogeneous linear system of `p` equations in `q = 2p`
unknowns whose coefficients all lie in `{-1, 0, 1}`, there is a nontrivial integer solution
all of whose entries are bounded in absolute value by `q`. -/
theorem imo1976_p5 (p q : ℕ) (hp : 0 < p) (hq : q = 2 * p)
    (a : Fin p → Fin q → ℤ) (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1) :
    ∃ x : Fin q → ℤ,
      (∀ i : Fin p, ∑ j : Fin q, a i j * x j = 0) ∧ (∃ j : Fin q, x j ≠ 0) ∧
        (∀ j : Fin q, |x j| ≤ (q : ℤ)) := by
  classical
  -- the box of candidate vectors, encoded as functions into `Fin (q+1)`
  set S : Finset (Fin q → Fin (q + 1)) := Finset.univ with hS
  set f : (Fin q → Fin (q + 1)) → (Fin p → ℤ) :=
    fun x i => ∑ j : Fin q, a i j * ((x j : ℕ) : ℤ) with hf
  set T : Finset (Fin p → ℤ) :=
    Fintype.piFinset fun i : Fin p =>
      Finset.Icc (-(q : ℤ) * negCount a i) (-(q : ℤ) * negCount a i + (q : ℤ) ^ 2) with hT
  have hmaps : ∀ x ∈ S, f x ∈ T := by
    intro x _
    rw [hT, Fintype.mem_piFinset]
    intro i
    have hb : ∀ j : Fin q, ((x j : ℕ) : ℤ) ≤ (q : ℤ) := by
      intro j
      exact_mod_cast Nat.lt_succ_iff.mp (x j).isLt
    have h0 : ∀ j : Fin q, (0 : ℤ) ≤ ((x j : ℕ) : ℤ) := fun j => Int.natCast_nonneg _
    exact row_sum_mem_Icc a ha (fun j => ((x j : ℕ) : ℤ)) h0 hb i
  have hTcard : T.card = (q ^ 2 + 1) ^ p := by
    rw [hT, Fintype.card_piFinset]
    have : ∀ i : Fin p,
        (Finset.Icc (-(q : ℤ) * negCount a i)
          (-(q : ℤ) * negCount a i + (q : ℤ) ^ 2)).card = q ^ 2 + 1 := by
      intro i
      rw [Int.card_Icc]
      have : -(q : ℤ) * negCount a i + (q : ℤ) ^ 2 + 1 - -(q : ℤ) * negCount a i
          = ((q ^ 2 + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [Finset.prod_congr rfl fun i _ => this i]
    simp
  have hScard : S.card = (q + 1) ^ q := by
    rw [hS]
    simp
  have hlt : T.card < S.card := by
    rw [hTcard, hScard, hq]
    have h2 : (2 * p + 1) ^ (2 * p) = ((2 * p + 1) ^ 2) ^ p := by
      rw [← pow_mul, mul_comm 2 p]
    rw [h2]
    apply Nat.pow_lt_pow_left _ hp.ne'
    nlinarith [hp]
  obtain ⟨u, -, v, -, huv, hfuv⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨fun j => ((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ), ?_, ?_, ?_⟩
  · intro i
    have := congrFun hfuv i
    rw [hf] at this
    simp only at this
    calc ∑ j : Fin q, a i j * (((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ))
        = (∑ j : Fin q, a i j * ((u j : ℕ) : ℤ)) - ∑ j : Fin q, a i j * ((v j : ℕ) : ℤ) := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this]; ring
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp huv
    refine ⟨j, ?_⟩
    show ((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ) ≠ 0
    have : ((u j : ℕ) : ℤ) ≠ ((v j : ℕ) : ℤ) := by
      simpa [Fin.val_inj] using fun h : (u j : ℕ) = (v j : ℕ) => hj (Fin.ext h)
    omega
  · intro j
    show |((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ)| ≤ (q : ℤ)
    have hu : ((u j : ℕ) : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (u j).isLt
    have hv : ((v j : ℕ) : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (v j).isLt
    have hu0 : (0 : ℤ) ≤ ((u j : ℕ) : ℤ) := Int.natCast_nonneg _
    have hv0 : (0 : ℤ) ≤ ((v j : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [abs_le]
    omega

end Imo1976P5
