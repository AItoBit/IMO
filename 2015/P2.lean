import Mathlib

namespace IMO2015P2

/-!
# IMO 2015 Problem 2

Determine all positive integers `(a,b,c)` such that

    a*b - c
    b*c - a
    c*a - b

are powers of two.

We work over `ℤ` so that subtraction has its ordinary
integer meaning.
-/

/-!
## Powers of two
-/

def IsPowerOfTwo (z : ℤ) : Prop :=
  ∃ m : ℕ, z = 2 ^ m

lemma powerOfTwo_pos
    {z : ℤ}
    (h : IsPowerOfTwo z) :
    0 < z := by
  rcases h with ⟨m, rfl⟩
  positivity

lemma pow2_1 :
    IsPowerOfTwo 1 := by
  refine ⟨0, ?_⟩
  norm_num

lemma pow2_2 :
    IsPowerOfTwo 2 := by
  refine ⟨1, ?_⟩
  norm_num

lemma pow2_4 :
    IsPowerOfTwo 4 := by
  refine ⟨2, ?_⟩
  norm_num

lemma pow2_8 :
    IsPowerOfTwo 8 := by
  refine ⟨3, ?_⟩
  norm_num

lemma pow2_16 :
    IsPowerOfTwo 16 := by
  refine ⟨4, ?_⟩
  norm_num

lemma pow2_32 :
    IsPowerOfTwo 32 := by
  refine ⟨5, ?_⟩
  norm_num

lemma pow2_64 :
    IsPowerOfTwo 64 := by
  refine ⟨6, ?_⟩
  norm_num

/-!
## The condition in the problem
-/

def Good
    (a b c : ℤ) : Prop :=
  0 < a ∧
  0 < b ∧
  0 < c ∧
  IsPowerOfTwo (a * b - c) ∧
  IsPowerOfTwo (b * c - a) ∧
  IsPowerOfTwo (c * a - b)

/-!
## Symmetry
-/

/--
Swapping `a` and `b` preserves the condition.
-/
lemma Good.swap_ab
    {a b c : ℤ}
    (h : Good a b c) :
    Good b a c := by

  rcases h with
    ⟨ha, hb, hc, h₁, h₂, h₃⟩

  refine
    ⟨hb, ha, hc, ?_, ?_, ?_⟩

  · simpa [mul_comm] using h₁

  · simpa [mul_comm] using h₃

  · simpa [mul_comm] using h₂

/--
Swapping `b` and `c` preserves the condition.
-/
lemma Good.swap_bc
    {a b c : ℤ}
    (h : Good a b c) :
    Good a c b := by

  rcases h with
    ⟨ha, hb, hc, h₁, h₂, h₃⟩

  refine
    ⟨ha, hc, hb, ?_, ?_, ?_⟩

  · simpa [mul_comm] using h₃

  · simpa [mul_comm] using h₂

  · simpa [mul_comm] using h₁

/--
Cyclically permuting the variables preserves the condition.
-/
lemma Good.cycle
    {a b c : ℤ}
    (h : Good a b c) :
    Good b c a := by

  rcases h with
    ⟨ha, hb, hc, h₁, h₂, h₃⟩

  exact
    ⟨hb, hc, ha, h₂, h₃, h₁⟩

/--
Reverse cyclic permutation.
-/
lemma Good.cycle_rev
    {a b c : ℤ}
    (h : Good a b c) :
    Good c a b := by
  exact h.cycle.cycle

/-!
## Canonical solutions
-/

/--
`(2,2,2)` is a solution.
-/
lemma good_222 :
    Good 2 2 2 := by

  refine
    ⟨by norm_num,
     by norm_num,
     by norm_num,
     ?_,
     ?_,
     ?_⟩

  · norm_num
    exact pow2_2

  · norm_num
    exact pow2_2

  · norm_num
    exact pow2_2

/--
`(2,2,3)` is a solution.
-/
lemma good_223 :
    Good 2 2 3 := by

  refine
    ⟨by norm_num,
     by norm_num,
     by norm_num,
     ?_,
     ?_,
     ?_⟩

  · norm_num
    exact pow2_1

  · norm_num
    exact pow2_4

  · norm_num
    exact pow2_4

/--
`(2,6,11)` is a solution.
-/
lemma good_2_6_11 :
    Good 2 6 11 := by

  refine
    ⟨by norm_num,
     by norm_num,
     by norm_num,
     ?_,
     ?_,
     ?_⟩

  · norm_num
    exact pow2_1

  · norm_num
    exact pow2_64

  · norm_num
    exact pow2_16

/--
`(3,5,7)` is a solution.
-/
lemma good_3_5_7 :
    Good 3 5 7 := by

  refine
    ⟨by norm_num,
     by norm_num,
     by norm_num,
     ?_,
     ?_,
     ?_⟩

  · norm_num
    exact pow2_8

  · norm_num
    exact pow2_32

  · norm_num
    exact pow2_16

/-!
## Permutations of (2,2,3)
-/

lemma good_232 :
    Good 2 3 2 := by
  exact good_223.swap_bc

lemma good_322 :
    Good 3 2 2 := by
  exact good_223.cycle_rev

/-!
## Six permutations of (2,6,11)
-/

lemma good_6_11_2 :
    Good 6 11 2 := by
  exact good_2_6_11.cycle

lemma good_11_2_6 :
    Good 11 2 6 := by
  exact good_2_6_11.cycle_rev

lemma good_6_2_11 :
    Good 6 2 11 := by
  exact good_2_6_11.swap_ab

lemma good_2_11_6 :
    Good 2 11 6 := by
  exact good_2_6_11.swap_bc

lemma good_11_6_2 :
    Good 11 6 2 := by
  exact good_6_11_2.swap_ab

/-!
## Six permutations of (3,5,7)
-/

lemma good_5_7_3 :
    Good 5 7 3 := by
  exact good_3_5_7.cycle

lemma good_7_3_5 :
    Good 7 3 5 := by
  exact good_3_5_7.cycle_rev

lemma good_5_3_7 :
    Good 5 3 7 := by
  exact good_3_5_7.swap_ab

lemma good_3_7_5 :
    Good 3 7 5 := by
  exact good_3_5_7.swap_bc

lemma good_7_5_3 :
    Good 7 5 3 := by
  exact good_5_7_3.swap_ab

/-!
## The sixteen solutions from the official answer
-/

def IsListed
    (a b c : ℤ) : Prop :=
  (a = 2 ∧ b = 2 ∧ c = 2) ∨
  (a = 2 ∧ b = 2 ∧ c = 3) ∨
  (a = 2 ∧ b = 3 ∧ c = 2) ∨
  (a = 3 ∧ b = 2 ∧ c = 2) ∨
  (a = 2 ∧ b = 6 ∧ c = 11) ∨
  (a = 6 ∧ b = 11 ∧ c = 2) ∨
  (a = 11 ∧ b = 2 ∧ c = 6) ∨
  (a = 6 ∧ b = 2 ∧ c = 11) ∨
  (a = 2 ∧ b = 11 ∧ c = 6) ∨
  (a = 11 ∧ b = 6 ∧ c = 2) ∨
  (a = 3 ∧ b = 5 ∧ c = 7) ∨
  (a = 5 ∧ b = 7 ∧ c = 3) ∨
  (a = 7 ∧ b = 3 ∧ c = 5) ∨
  (a = 5 ∧ b = 3 ∧ c = 7) ∨
  (a = 3 ∧ b = 7 ∧ c = 5) ∨
  (a = 7 ∧ b = 5 ∧ c = 3)

/--
Every triple appearing in the official answer really satisfies
the required condition.
-/
theorem listed_solution_is_good
    {a b c : ℤ}
    (h : IsListed a b c) :
    Good a b c := by

  rcases h with
    h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_222

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_223

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_232

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_322

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_2_6_11

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_6_11_2

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_11_2_6

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_6_2_11

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_2_11_6

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_11_6_2

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_3_5_7

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_5_7_3

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_7_3_5

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_5_3_7

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_3_7_5

  · rcases h with ⟨rfl, rfl, rfl⟩
    exact good_7_5_3

/-!
## First reduction in the official proof
-/

/--
After using symmetry to assume

    a ≤ b ≤ c,

the smallest entry must satisfy `a ≥ 2`.

Indeed, if `a = 1`, then

    a*b - c = b-c ≤ 0,

whereas a power of two is strictly positive.
-/
lemma smallest_at_least_two
    {a b c : ℤ}
    (hgood : Good a b c)
    (hab : a ≤ b)
    (hbc : b ≤ c) :
    2 ≤ a := by

  rcases hgood with
    ⟨ha, _hb, _hc, hp, _h₂, _h₃⟩

  have hp_pos :
      0 < a * b - c :=
    powerOfTwo_pos hp

  by_contra h

  have ha1 :
      a = 1 := by
    omega

  rw [ha1] at hp_pos

  norm_num at hp_pos

  linarith

/-!
## Ordering the three power-of-two expressions
-/

/--
If `a ≤ b ≤ c`, then

    ab-c ≤ ac-b.
-/
lemma first_le_second
    {a b c : ℤ}
    (ha : 0 < a)
    (hbc : b ≤ c) :
    a * b - c ≤
      c * a - b := by

  have hnonneg :
      0 ≤
        (a + 1) * (c - b) := by
    positivity

  nlinarith

/--
If `a ≤ b ≤ c`, then

    ac-b ≤ bc-a.
-/
lemma second_le_third
    {a b c : ℤ}
    (hc : 0 < c)
    (hab : a ≤ b) :
    c * a - b ≤
      b * c - a := by

  have hnonneg :
      0 ≤
        (c + 1) * (b - a) := by
    positivity

  nlinarith

/--
Thus after sorting the variables, the three powers of two occur
in nondecreasing order, exactly as in the source proof.
-/
lemma ordered_power_values
    {a b c : ℤ}
    (hgood : Good a b c)
    (hab : a ≤ b)
    (hbc : b ≤ c) :
    a * b - c ≤
      c * a - b ∧
    c * a - b ≤
      b * c - a := by

  rcases hgood with
    ⟨ha, _hb, hc, _h₁, _h₂, _h₃⟩

  constructor

  · exact
      first_le_second
        ha
        hbc

  · exact
      second_le_third
        hc
        hab

end IMO2015P2
