import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace GoldenRatioFunction

/-- The golden ratio. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- The required function, defined by nearest-integer rounding of `phi * n`. -/
noncomputable def goldenFunction (n : ℕ) : ℕ :=
  ⌊phi * (n : ℝ) + 1 / 2⌋₊

private lemma phi_spec :
    1 < phi ∧ phi < 2 ∧ phi ^ 2 = phi + 1 := by
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs2 : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  constructor
  · unfold phi
    nlinarith
  constructor
  · unfold phi
    nlinarith
  · unfold phi
    nlinarith

private lemma goldenFunction_bounds (n : ℕ) :
    (goldenFunction n : ℝ) ≤ phi * (n : ℝ) + 1 / 2 ∧
      phi * (n : ℝ) + 1 / 2 < (goldenFunction n : ℝ) + 1 := by
  have hnonneg : 0 ≤ phi * (n : ℝ) + 1 / 2 := by
    have hphi := phi_spec.1
    positivity
  exact ⟨Nat.floor_le hnonneg, Nat.lt_floor_add_one _⟩

private lemma goldenFunction_strictMono : StrictMono goldenFunction := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hphi := phi_spec.1
  have hn := (goldenFunction_bounds n).1
  have harg : 0 ≤ phi * ((n + 1 : ℕ) : ℝ) + 1 / 2 := by
    positivity
  have hstep :
      ((goldenFunction n + 1 : ℕ) : ℝ) ≤
        phi * ((n + 1 : ℕ) : ℝ) + 1 / 2 := by
    push_cast
    nlinarith
  exact Nat.lt_iff_add_one_le.mpr ((Nat.le_floor_iff harg).mpr hstep)

private lemma goldenFunction_one : goldenFunction 1 = 2 := by
  have hphi := phi_spec
  unfold goldenFunction
  norm_num only [Nat.cast_one, mul_one]
  apply (Nat.floor_eq_iff (show 0 ≤ phi + 1 / 2 by nlinarith [hphi.1])).2
  norm_num only [Nat.cast_ofNat]
  constructor <;> nlinarith

private lemma goldenFunction_iterate (n : ℕ) :
    goldenFunction (goldenFunction n) = goldenFunction n + n := by
  have hphi := phi_spec
  have hk := goldenFunction_bounds n
  let k := goldenFunction n
  have hk_lower : (k : ℝ) ≤ phi * (n : ℝ) + 1 / 2 := by
    simpa [k] using hk.1
  have hk_upper : phi * (n : ℝ) + 1 / 2 < (k : ℝ) + 1 := by
    simpa [k] using hk.2
  have hlow :
      ((k + n : ℕ) : ℝ) ≤ phi * (k : ℝ) + 1 / 2 := by
    push_cast
    nlinarith [mul_lt_mul_of_pos_left
      (show phi * (n : ℝ) - 1 / 2 < (k : ℝ) by linarith) (sub_pos.mpr hphi.1)]
  have hupp :
      phi * (k : ℝ) + 1 / 2 < ((k + n : ℕ) : ℝ) + 1 := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hk_lower (sub_nonneg.mpr hphi.1.le)]
  change ⌊phi * (k : ℝ) + 1 / 2⌋₊ = k + n
  apply (Nat.floor_eq_iff (by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith)).2
  exact ⟨hlow, hupp⟩

/--
There exists a strictly increasing `f : ℕ → ℕ` such that `f 1 = 2` and
`f (f n) = f n + n`.  This is slightly stronger than the problem, whose
natural numbers start at `1`, because the identity is also proved at `0`.
-/
theorem exists_strictMono_function :
    ∃ f : ℕ → ℕ, StrictMono f ∧ f 1 = 2 ∧ ∀ n, f (f n) = f n + n := by
  exact ⟨goldenFunction, goldenFunction_strictMono, goldenFunction_one,
    goldenFunction_iterate⟩

end GoldenRatioFunction
