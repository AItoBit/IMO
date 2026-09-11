import Mathlib

/-!
# IMO 1987, Problem 1

Let `p n k` be the number of permutations of an `n`-element set with exactly `k`
fixed points. Prove that `∑_{k=0}^{n} k * p n k = n!`  (for `n ≥ 1`).

We model `{1, …, n}` as `Fin n`.

Proof (double counting):
  ∑ k * p n k = ∑_σ #fix(σ) = ∑_i #{σ | σ i = i} = ∑_i #{σ | σ a = i} = #Perm = n!,
where the third step uses the bijection `σ ↦ σ * swap a i`.
-/

open Finset
open scoped Nat

namespace Imo1987P1

/-- Number of fixed points of a permutation of `Fin n`. -/
def numFixed {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter fun i => σ i = i).card

/-- `p n k` : number of permutations of `Fin n` with exactly `k` fixed points. -/
def p (n k : ℕ) : ℕ :=
  (univ.filter fun σ : Equiv.Perm (Fin n) => numFixed σ = k).card

/-- Permutations fixing `i` are in bijection with permutations sending `a` to `i`. -/
lemma card_fix_eq (n : ℕ) (a i : Fin n) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card =
      (univ.filter fun σ : Equiv.Perm (Fin n) => σ a = i).card := by
  refine card_nbij' (fun σ => σ * Equiv.swap a i) (fun σ => σ * Equiv.swap a i)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hσ]
  · intro σ hσ
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hσ]
  · intro σ _
    exact Equiv.mul_swap_mul_self a i σ
  · intro σ _
    exact Equiv.mul_swap_mul_self a i σ

theorem imo1987_p1 (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), k * p n k = n ! := by
  -- Step 1: the sum counts all fixed points of all permutations.
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin n))), numFixed σ ∈ range (n + 1) := by
    intro σ _
    rw [mem_range]
    unfold numFixed
    exact Nat.lt_succ_of_le ((card_filter_le _ _).trans_eq (card_fin n))
  have h1 : ∑ k ∈ range (n + 1), k * p n k = ∑ σ : Equiv.Perm (Fin n), numFixed σ := by
    rw [← sum_fiberwise_of_maps_to hmaps numFixed]
    refine sum_congr rfl fun k _ => ?_
    have hk : ∀ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => numFixed σ = k),
        numFixed σ = k :=
      fun σ hσ => (mem_filter.mp hσ).2
    rw [sum_const_nat hk, p, mul_comm]
  -- Step 2: swap the order of summation.
  have h2 : ∑ σ : Equiv.Perm (Fin n), numFixed σ =
      ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card := by
    simp only [numFixed, card_filter]
    exact sum_comm
  -- Step 3: each point is fixed by the same number of permutations; total is `n!`.
  have h3 : ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card = n ! := by
    have a : Fin n := ⟨0, by omega⟩
    calc ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card
        = ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ a = i).card :=
          sum_congr rfl fun i _ => card_fix_eq n a i
      _ = (univ : Finset (Equiv.Perm (Fin n))).card :=
          (card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin n) => σ a)
            (s := univ) (t := univ) (by intro σ _; simp)).symm
      _ = n ! := by simp [Fintype.card_perm]
  exact h1.trans (h2.trans h3)

end Imo1987P1
