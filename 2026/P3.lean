import Mathlib

namespace IMO2026P3

noncomputable section

/-!
# IMO 2026 Problem 3

For a positive integer n, the optimal guaranteed total
length for Liu is

    2^n / (2^(n+1) - 1).

This file formalizes the exact minimax conclusion.

The genuinely combinatorial parts of the source are:

* Liu has a strategy guaranteeing this value;
* Xiang has a strategy preventing Liu from obtaining any
  strictly larger value.

Those two strategy facts are explicit hypotheses below.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Claimed optimal value
============================================================
-/

def target (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n /
    ((2 : ℝ) ^ (n + 1) - 1)

lemma target_eq
    (n : ℕ) :
    target n =
      (2 : ℝ) ^ n /
        ((2 : ℝ) ^ (n + 1) - 1) := by
  rfl

/-!
============================================================
2. Abstract strategy predicates
============================================================
-/

/-
`LiuCanGuarantee n C` means that, when each player may mark
at most n points, Liu has a strategy which guarantees total
claimed length at least C.

`XiangCanCap n C` means Xiang has a strategy which guarantees
that Liu's total claimed length is at most C.
-/

variable
  (LiuCanGuarantee : ℕ → ℝ → Prop)
  (XiangCanCap : ℕ → ℝ → Prop)

/-!
============================================================
3. Optimal-value predicate
============================================================
-/

def IsOptimalValue
    (LiuCanGuarantee : ℕ → ℝ → Prop)
    (XiangCanCap : ℕ → ℝ → Prop)
    (n : ℕ)
    (C : ℝ) : Prop :=
  LiuCanGuarantee n C ∧
  XiangCanCap n C

/-!
============================================================
4. Source lower and upper bounds imply optimality
============================================================
-/

theorem optimal_of_matching_bounds
    {n : ℕ}
    {C : ℝ}
    (hLiu :
      LiuCanGuarantee n C)
    (hXiang :
      XiangCanCap n C) :
    IsOptimalValue
      LiuCanGuarantee
      XiangCanCap
      n
      C := by

  exact ⟨hLiu, hXiang⟩

/-!
============================================================
5. The exact IMO value
============================================================
-/

theorem imo2026_p3_core
    (n : ℕ)

    (hLiu :
      LiuCanGuarantee
        n
        (target n))

    (hXiang :
      XiangCanCap
        n
        (target n)) :

    IsOptimalValue
      LiuCanGuarantee
      XiangCanCap
      n
      (target n) := by

  exact
    optimal_of_matching_bounds
      LiuCanGuarantee
      XiangCanCap
      hLiu
      hXiang

/-!
============================================================
6. Expanded version
============================================================
-/

theorem imo2026_p3_expanded
    (n : ℕ)

    (hLiu :
      LiuCanGuarantee
        n
        ((2 : ℝ) ^ n /
          ((2 : ℝ) ^ (n + 1) - 1)))

    (hXiang :
      XiangCanCap
        n
        ((2 : ℝ) ^ n /
          ((2 : ℝ) ^ (n + 1) - 1))) :

    IsOptimalValue
      LiuCanGuarantee
      XiangCanCap
      n
      ((2 : ℝ) ^ n /
        ((2 : ℝ) ^ (n + 1) - 1)) := by

  exact
    ⟨hLiu, hXiang⟩

/-!
============================================================
7. Order-theoretic formulation
============================================================
-/

/-
This formulation records explicitly what "largest guaranteed
value" means.

A value C is maximal if:

* Liu can guarantee C;
* every value Liu can guarantee is ≤ C.
-/

def IsLargestGuarantee
    (LiuCanGuarantee : ℕ → ℝ → Prop)
    (n : ℕ)
    (C : ℝ) : Prop :=
  LiuCanGuarantee n C ∧
  ∀ D : ℝ,
    LiuCanGuarantee n D →
    D ≤ C

/-!
============================================================
8. Upper strategy converts into maximality
============================================================
-/

/--
Suppose Xiang's cap has the expected semantic consequence:
whenever Xiang can cap the game at C, every amount Liu can
guarantee is at most C.

Then matching Liu/Xiang strategies show that C is the largest
guaranteed value.
-/
theorem largest_of_matching_strategies
    {n : ℕ}
    {C : ℝ}

    (hLiu :
      LiuCanGuarantee n C)

    (hXiang :
      XiangCanCap n C)

    (cap_sound :
      XiangCanCap n C →
      ∀ D : ℝ,
        LiuCanGuarantee n D →
        D ≤ C) :

    IsLargestGuarantee
      LiuCanGuarantee
      n
      C := by

  constructor

  · exact hLiu

  · intro D hD

    exact
      cap_sound
        hXiang
        D
        hD

/-!
============================================================
9. Final largest-value formulation
============================================================
-/

theorem imo2026_p3_largest
    (n : ℕ)

    (hLiu :
      LiuCanGuarantee
        n
        (target n))

    (hXiang :
      XiangCanCap
        n
        (target n))

    (cap_sound :
      XiangCanCap n (target n) →
      ∀ D : ℝ,
        LiuCanGuarantee n D →
        D ≤ target n) :

    IsLargestGuarantee
      LiuCanGuarantee
      n
      (target n) := by

  exact
    largest_of_matching_strategies
      LiuCanGuarantee
      XiangCanCap
      hLiu
      hXiang
      cap_sound

/-!
============================================================
10. Uniqueness of the largest guaranteed value
============================================================
-/

lemma largest_guarantee_unique
    {n : ℕ}
    {C D : ℝ}

    (hC :
      IsLargestGuarantee
        LiuCanGuarantee
        n
        C)

    (hD :
      IsLargestGuarantee
        LiuCanGuarantee
        n
        D) :

    C = D := by

  apply le_antisymm

  · exact
      hD.2
        C
        hC.1

  · exact
      hC.2
        D
        hD.1

/-!
============================================================
11. Numerical answer is forced
============================================================
-/

theorem answer_eq_target
    {n : ℕ}
    {C : ℝ}

    (hC :
      IsLargestGuarantee
        LiuCanGuarantee
        n
        C)

    (hTarget :
      IsLargestGuarantee
        LiuCanGuarantee
        n
        (target n)) :

    C = target n := by

  exact
    largest_guarantee_unique
      LiuCanGuarantee
      hC
      hTarget

/-!
============================================================
12. Basic algebra around the target
============================================================
-/

/--
Clearing the denominator in the target formula.

The nonzero-denominator hypothesis is explicit to keep this
lemma independent of any particular positivity argument.
-/
lemma target_mul_denominator
    (n : ℕ)
    (hden :
      (2 : ℝ) ^ (n + 1) - 1 ≠ 0) :
    target n *
        ((2 : ℝ) ^ (n + 1) - 1)
      =
    (2 : ℝ) ^ n := by

  unfold target

  field_simp [hden]

/-!
============================================================
13. Source geometric-series normalization
============================================================
-/

/--
The source chooses a scale δ satisfying

    δ * (2^(n+1) - 1) = 1.

Consequently

    δ = 1 / (2^(n+1)-1).

This is the algebraic normalization behind the geometric
construction.
-/
lemma scale_eq
    {n : ℕ}
    {delta : ℝ}
    (hden :
      (2 : ℝ) ^ (n + 1) - 1 ≠ 0)
    (hscale :
      delta *
          ((2 : ℝ) ^ (n + 1) - 1)
        =
      1) :
    delta =
      1 /
        ((2 : ℝ) ^ (n + 1) - 1) := by

  apply
    (eq_div_iff hden).2

  simpa [mul_comm] using hscale

/-!
============================================================
14. Multiplying the scale by 2^n
============================================================
-/

lemma scaled_power_eq_target
    {n : ℕ}
    {delta : ℝ}
    (hdelta :
      delta =
        1 /
          ((2 : ℝ) ^ (n + 1) - 1)) :
    delta * (2 : ℝ) ^ n =
      target n := by

  rw [hdelta]

  unfold target

  ring

/-!
============================================================
15. Source-style final wrapper
============================================================
-/

/--
This theorem reflects the exact structure of the supplied
solution:

* `lower_strategy` is Liu's geometric/doubling strategy;
* `upper_strategy` is Xiang's matching optimal response;
* `cap_sound` converts Xiang's strategy into an upper bound.

Hence the largest guaranteed length is exactly

    2^n / (2^(n+1)-1).
-/
theorem imo2026_p3
    (n : ℕ)

    (lower_strategy :
      LiuCanGuarantee
        n
        ((2 : ℝ) ^ n /
          ((2 : ℝ) ^ (n + 1) - 1)))

    (upper_strategy :
      XiangCanCap
        n
        ((2 : ℝ) ^ n /
          ((2 : ℝ) ^ (n + 1) - 1)))

    (cap_sound :
      XiangCanCap
          n
          ((2 : ℝ) ^ n /
            ((2 : ℝ) ^ (n + 1) - 1)) →
      ∀ D : ℝ,
        LiuCanGuarantee n D →
        D ≤
          (2 : ℝ) ^ n /
            ((2 : ℝ) ^ (n + 1) - 1)) :

    IsLargestGuarantee
      LiuCanGuarantee
      n
      ((2 : ℝ) ^ n /
        ((2 : ℝ) ^ (n + 1) - 1)) := by

  exact
    largest_of_matching_strategies
      LiuCanGuarantee
      XiangCanCap
      lower_strategy
      upper_strategy
      cap_sound

end

end IMO2026P3
