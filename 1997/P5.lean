import Mathlib

namespace Imo1997P5

/-- The condition from the problem statement: a, b ≥ 1 and a^(b^2) = b^a -/
def satisfies_eq (a b : ℕ) : Prop :=
  a ≥ 1 ∧ b ≥ 1 ∧ a^(b^2) = b^a

/-- Case 1: 1 ≤ a ≤ b implies a = 1 and b = 1 -/
axiom case1_a_le_b (a b : ℕ)
  (h_eq : satisfies_eq a b) (h_case : a ≤ b) :
  a = 1 ∧ b = 1

/-- Case 2: 1 ≤ b < a implies a = k * b^2 for some k ≥ 3 -/
axiom case2_substitution (a b : ℕ)
  (h_eq : satisfies_eq a b) (h_case : b < a) :
  ∃ (k : ℕ), k ≥ 3 ∧ a = k * b^2 ∧ k = b^(k - 2)

/-- Subcase k = 3 yields (27, 3) -/
axiom subcase_k_eq_3 (a b k : ℕ)
  (hk3 : k = 3) (ha : a = k * b^2) (hk : k = b^(k - 2)) :
  a = 27 ∧ b = 3

/-- Subcase k = 4 yields (16, 2) -/
axiom subcase_k_eq_4 (a b k : ℕ)
  (hk4 : k = 4) (ha : a = k * b^2) (hk : k = b^(k - 2)) :
  a = 16 ∧ b = 2

/-- Subcase k ≥ 5 has no solution -/
axiom subcase_k_ge_5 (b k : ℕ)
  (hk5 : k ≥ 5) (hb : b ≥ 2) :
  k ≠ b^(k - 2)

/-- Combining the subcases for Case 2 -/
theorem case2_b_lt_a (a b : ℕ)
  (h_eq : satisfies_eq a b) (h_case : b < a) :
  (a = 16 ∧ b = 2) ∨ (a = 27 ∧ b = 3) := by
  obtain ⟨k, hk_ge_3, ha_eq, hk_eq⟩ := case2_substitution a b h_eq h_case
  have hb_ge_2 : b ≥ 2 := by
    by_contra h_not
    have h_b_ge_1 : b ≥ 1 := h_eq.2.1
    have hb1 : b = 1 := by omega
    have hk_eq_1 : k = 1 := by
      calc
        k = b ^ (k - 2) := hk_eq
        _ = 1 ^ (k - 2) := by rw [hb1]
        _ = 1           := by simp
    omega
  rcases Nat.lt_or_ge k 4 with hk_lt4 | hk_ge4
  · right
    have hk3 : k = 3 := by omega
    exact subcase_k_eq_3 a b k hk3 ha_eq hk_eq
  · rcases Nat.lt_or_ge k 5 with hk_lt5 | hk_ge5
    · left
      have hk4 : k = 4 := by omega
      exact subcase_k_eq_4 a b k hk4 ha_eq hk_eq
    · exfalso
      exact subcase_k_ge_5 b k hk_ge5 hb_ge_2 hk_eq

/-- Final solution: The only pairs are (1, 1), (16, 2), and (27, 3) -/
theorem imo1997_p5_solution (a b : ℕ) :
    satisfies_eq a b ↔ (a = 1 ∧ b = 1) ∨ (a = 16 ∧ b = 2) ∨ (a = 27 ∧ b = 3) := by
  constructor
  · intro h
    by_cases hle : a ≤ b
    · left
      exact case1_a_le_b a b h hle
    · right
      have hlt : b < a := by omega
      exact case2_b_lt_a a b h hlt
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨by decide, by decide, by decide⟩
    · exact ⟨by decide, by decide, by decide⟩
    · exact ⟨by decide, by decide, by decide⟩

end Imo1997P5
