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

set_option maxRecDepth 40000 in
/-- Bounded verification: for every `n < 1000`, the three-digit / divisibility /
digit-square condition holds exactly for `n = 550` and `n = 803`. -/
lemma imo_1960_p1_bounded :
    ∀ n ∈ Finset.range 1000,
      (((Nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧
        ((Nat.digits 10 n).map (· ^ 2)).sum = (n / 11 : ℕ)) ↔ (n = 550 ∨ n = 803)) := by
  decide

/--
Determine all three digit numbers $N$ which are divisible by $11$ and where $N/11$ is equal to
the sum of the squares of the digits of $N$.  The answer is $\{550, 803\}$.
-/
theorem imo_1960_p1 :
    {n : ℕ | (Nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧
      ((Nat.digits 10 n).map (· ^ 2)).sum = (n / 11 : ℕ)} = {550, 803} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hlen, hdvd, hsum⟩
    have hn : n < 1000 := by
      have := (Nat.digits_length_le_iff (b := 10) (k := 3) (by norm_num) n).mp hlen.le
      simpa using this
    exact (imo_1960_p1_bounded n (Finset.mem_range.mpr hn)).mp ⟨hlen, hdvd, hsum⟩
  · rintro (rfl | rfl)
    · exact (imo_1960_p1_bounded 550 (by decide)).mpr (Or.inl rfl)
    · exact (imo_1960_p1_bounded 803 (by decide)).mpr (Or.inr rfl)
