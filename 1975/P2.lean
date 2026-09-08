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

/-- **IMO 1975, Problem 2.**

Let `a 1, a 2, a 3, …` be an infinite increasing sequence of positive integers.
Then for every `p ≥ 1` there are infinitely many `a m` which can be written in the form
`a m = x * a p + y * a q` with `x`, `y` positive integers and `q > p`.

The sequence is modelled as a function `a : ℕ → ℕ` which is strictly increasing and takes
positive values.  The conclusion says that the set of indices `m` for which such a
representation exists is infinite (equivalently, since `a` is injective, that infinitely
many terms `a m` are of that form).

The hypothesis `1 ≤ p` is part of the original statement (the sequence is indexed starting
from `1`); it is not needed for the proof. -/
theorem imo1975_p2 (a : ℕ → ℕ) (hmono : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℕ) (hp : 1 ≤ p) :
    {m : ℕ | ∃ x y q : ℕ, 0 < x ∧ 0 < y ∧ p < q ∧ a m = x * a p + y * a q}.Infinite := by
  clear hp
  have hap : 0 < a p := hpos p
  -- Pigeonhole: infinitely many terms with index `> p` share the same residue mod `a p`.
  set f : ℕ → Fin (a p) := fun n => ⟨a (p + 1 + n) % a p, Nat.mod_lt _ hap⟩ with hf
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber f
  have hS : (f ⁻¹' {r}).Infinite := Set.infinite_coe_iff.mp hr
  obtain ⟨n₀, hn₀⟩ := hS.nonempty
  -- `q` is the index of a fixed term in this residue class.
  set q : ℕ := p + 1 + n₀ with hq
  have hpq : p < q := by omega
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hnS, hn⟩ := hS.exists_gt (max n₀ N)
  refine ⟨p + 1 + n, ?_, by omega⟩
  have hmod : a (p + 1 + n) % a p = a q % a p := by
    have h1 : f n = r := hnS
    have h2 : f n₀ = r := hn₀
    have := h1.trans h2.symm
    simpa [hf, Fin.ext_iff, hq] using this
  have hlt : a q < a (p + 1 + n) := hmono (by omega)
  -- The difference is a positive multiple of `a p`.
  have hdvd : a p ∣ a (p + 1 + n) - a q :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  obtain ⟨x, hx⟩ := hdvd
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h, Nat.mul_zero] at hx; omega
    · exact h
  exact ⟨x, 1, q, hxpos, Nat.one_pos, hpq, by rw [Nat.mul_comm] at hx; omega⟩
