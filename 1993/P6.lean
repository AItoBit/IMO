import Mathlib

namespace IMO1993P6A

variable {n : ℕ} (hn : 2 ≤ n)

/-- We use `Fin n` to represent the lamps in a circle. 
    The state of the lamps is a function from `Fin n` to `Bool`. -/
abbrev LampState (n : ℕ) := Fin n → Bool

/-- The index of the previous lamp, wrapping around to n - 1 if i is 0. -/
def prev (i : Fin n) : Fin n :=
  if h : (i : ℕ) = 0 then ⟨n - 1, by omega⟩ else ⟨(i : ℕ) - 1, by omega⟩

/-- The previous lamp is never the current lamp, since n ≥ 2. -/
lemma prev_ne (i : Fin n) : prev hn i ≠ i := by
  intro hc
  -- Project the Fin n equality down to ℕ for omega to reason about
  have hc' : (prev hn i).val = i.val := congrArg Fin.val hc
  unfold prev at hc'
  split_ifs at hc' with h
  · -- Unwrap the Fin constructor so omega sees (n - 1) = i
    simp only [Fin.val_mk] at hc'
    omega
  · -- Unwrap the Fin constructor so omega sees (i - 1) = i
    simp only [Fin.val_mk] at hc'
    omega

/-- 
The state update at step `i`:
If the previous lamp is lit (true), we toggle the current lamp `i` via XOR.
Otherwise, we do nothing.
-/
def step (i : Fin n) (s : LampState n) : LampState n :=
  fun j => if j = i then xor (s i) (s (prev hn i)) else s j

/-- 
Crucial observation: the operation at step `i` is an involution 
(it is its own inverse). This rigorously proves the step is deterministic 
and perfectly reversible.
-/
theorem step_involutive (i : Fin n) (s : LampState n) :
    step hn i (step hn i s) = s := by
  ext j
  by_cases h : j = i
  · -- Replace j with i in the goal, without destroying i in the context
    rw [h]
    dsimp [step]
    simp only [ite_true]
    -- Because prev i ≠ i, the previous lamp's state isn't touched
    have h_prev : prev hn i = i ↔ False := iff_false_intro (prev_ne hn i)
    simp only [h_prev, ite_false]
    -- Verify the XOR toggling natively evaluates to the identity
    cases s i <;> cases s (prev hn i) <;> rfl
  · -- For all other lamps, they are untouched
    dsimp [step]
    have hj : j = i ↔ False := iff_false_intro h
    simp only [hj, ite_false]

/-- Each individual step is uniquely reversible, forming a bijection (permutation). -/
def stepEquiv (i : Fin n) : Equiv.Perm (LampState n) where
  toFun := step hn i
  invFun := step hn i
  left_inv s := step_involutive hn i s
  right_inv s := step_involutive hn i s

/-- 
A full round consists of applying the step operation sequentially 
for each lamp from 0 to n - 1. We construct this by folding over `Fin n`.
-/
def roundEquiv : Equiv.Perm (LampState n) :=
  (List.finRange n).foldr (fun i eq => eq.trans (stepEquiv hn i)) (Equiv.refl _)

/-- 
IMO 1993 Problem 6, Part (A):
Because a full round is a permutation on a finite state space,
it must have a finite mathematical order. Thus, applying it a certain number 
of times (`k`) acts as the identity mapping, returning the system to its 
exact initial state ("all lamps are on").
-/
theorem imo1993_p6_part_a :
    ∃ k : ℕ, k > 0 ∧ (roundEquiv hn) ^ k = 1 := by
  -- In Mathlib, any element of a finite group has finite order, meaning 
  -- some strictly positive power of it is the identity element.
  have h : IsOfFinOrder (roundEquiv hn) := isOfFinOrder_of_finite (roundEquiv hn)
  exact h.exists_pow_eq_one

end IMO1993P6A
