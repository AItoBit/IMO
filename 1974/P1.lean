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

/-!
# IMO 1974, Problem 1

Three players `A`, `B`, `C` play the following game.  On each of three cards an integer is
written; these three numbers `p, q, r` satisfy `0 < p < q < r`.  The three cards are shuffled
and one is dealt to each player; each player then receives the number of counters indicated by
the card he holds.  Then the cards are shuffled again, and this is repeated for `n ≥ 2` rounds.

After the last round `A` has `20` counters in all, `B` has `10` and `C` has `9`.  In the last
round `B` received `r` counters.  Who received `q` counters in the first round?

Answer: player `C`.

Formalisation.  Rounds are indexed by `i < n`.  `a i`, `b i`, `c i` denote the numbers of
counters received by `A`, `B`, `C` in round `i`; the fact that in each round the three cards
`p, q, r` are distributed among the three players is expressed by the equality of multisets
`{a i, b i, c i} = {p, q, r}`.
-/

namespace IMO1974P1

/-- In each round the three players together receive `p + q + r` counters. -/
theorem round_sum {n p q r : ℕ} {a b c : ℕ → ℕ}
    (hdeal : ∀ i < n, ({a i, b i, c i} : Multiset ℕ) = {p, q, r}) :
    ∀ i < n, a i + b i + c i = p + q + r := by
  intro i hi
  have h := congrArg Multiset.sum (hdeal i hi)
  simpa [add_assoc] using h

/-- In each round every player receives one of the three amounts `p`, `q`, `r`. -/
theorem mem_cards {n p q r : ℕ} {a b c : ℕ → ℕ}
    (hdeal : ∀ i < n, ({a i, b i, c i} : Multiset ℕ) = {p, q, r}) :
    ∀ i < n, (a i = p ∨ a i = q ∨ a i = r) ∧ (b i = p ∨ b i = q ∨ b i = r) ∧
      (c i = p ∨ c i = q ∨ c i = r) := by
  intro i hi
  have ha : a i ∈ ({p, q, r} : Multiset ℕ) := by rw [← hdeal i hi]; simp
  have hb : b i ∈ ({p, q, r} : Multiset ℕ) := by rw [← hdeal i hi]; simp
  have hc : c i ∈ ({p, q, r} : Multiset ℕ) := by rw [← hdeal i hi]; simp
  refine ⟨by simpa using ha, by simpa using hb, by simpa using hc⟩

/-- There were exactly three rounds, and `p + q + r = 13`. -/
theorem three_rounds {n p q r : ℕ} {a b c : ℕ → ℕ}
    (hn : 2 ≤ n) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hdeal : ∀ i < n, ({a i, b i, c i} : Multiset ℕ) = {p, q, r})
    (hA : ∑ i ∈ Finset.range n, a i = 20)
    (hB : ∑ i ∈ Finset.range n, b i = 10)
    (hC : ∑ i ∈ Finset.range n, c i = 9) :
    n = 3 ∧ p + q + r = 13 := by
  have key : n * (p + q + r) = 39 := by
    have h : ∑ i ∈ Finset.range n, (a i + b i + c i) = n * (p + q + r) := by
      rw [Finset.sum_congr rfl (fun i hi => round_sum hdeal i (Finset.mem_range.mp hi))]
      simp [Finset.sum_const]
    rw [← h]
    simp only [Finset.sum_add_distrib, hA, hB, hC]
  have hs : 6 ≤ p + q + r := by omega
  have hn6 : n ≤ 6 := by nlinarith
  interval_cases n <;> omega

/-- **IMO 1974, Problem 1.**  Under the conditions of the problem, player `C` received `q`
counters in the first round. -/
theorem imo1974_p1 {n p q r : ℕ} {a b c : ℕ → ℕ}
    (hn : 2 ≤ n) (hp : 0 < p) (hpq : p < q) (hqr : q < r)
    (hdeal : ∀ i < n, ({a i, b i, c i} : Multiset ℕ) = {p, q, r})
    (hA : ∑ i ∈ Finset.range n, a i = 20)
    (hB : ∑ i ∈ Finset.range n, b i = 10)
    (hC : ∑ i ∈ Finset.range n, c i = 9)
    (hlast : b (n - 1) = r) :
    c 0 = q := by
  obtain ⟨hn3, hsum⟩ := three_rounds hn hp hpq hqr hdeal hA hB hC
  subst hn3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hA hB hC
  have hs0 := round_sum hdeal 0 (by norm_num)
  have hs1 := round_sum hdeal 1 (by norm_num)
  have hs2 := round_sum hdeal 2 (by norm_num)
  obtain ⟨ha0, hb0, -⟩ := mem_cards hdeal 0 (by norm_num)
  obtain ⟨ha1, hb1, -⟩ := mem_cards hdeal 1 (by norm_num)
  obtain ⟨ha2, -, -⟩ := mem_cards hdeal 2 (by norm_num)
  norm_num at hlast
  rcases ha0 with h | h | h <;> rcases ha1 with h' | h' | h' <;>
    rcases ha2 with h'' | h'' | h'' <;> rcases hb0 with k | k | k <;>
      rcases hb1 with k' | k' | k' <;> omega

end IMO1974P1
