import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# IMO 2002, Problem 5

The only functions satisfying the functional equation are the constant zero
function, the constant one-half function, and the squaring function.

Verified with Lean 4.34.0 and mathlib commit
7801e8406155c31b340d28e2762f754d02b5e9b0.
-/

namespace IMO2002P5

/-- The functional equation in the problem. -/
def Satisfies (f : ℝ → ℝ) : Prop :=
  ∀ x y z t : ℝ,
    (f x + f z) * (f y + f t) = f (x * y - z * t) + f (x * t + y * z)

/-- The nonconstant, normalized case is the squaring function. -/
lemma normalized_square (f : ℝ → ℝ) (hf : Satisfies f)
    (h0 : f 0 = 0) (h1 : f 1 = 1) : ∀ x, f x = x ^ 2 := by
  have hmul (x y : ℝ) : f (x * y) = f x * f y := by
    simpa [h0] using (hf x y 0 0).symm
  have heven (x : ℝ) : f (-x) = f x := by
    have h := hf 0 0 x 1
    simpa [h0, h1] using h.symm
  have hsq (x : ℝ) : f (x ^ 2) = (f x) ^ 2 := by
    simpa only [pow_two] using hmul x x
  have hnonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
    have h := hsq (Real.sqrt x)
    rw [Real.sq_sqrt hx] at h
    rw [h]
    exact sq_nonneg _
  have hsum (u v : ℝ) : f (u ^ 2 + v ^ 2) = (f u + f v) ^ 2 := by
    have h := hf u u v (-v)
    rw [heven v] at h
    have hleft : u * u - v * -v = u ^ 2 + v ^ 2 := by ring
    have hright : u * -v + u * v = 0 := by ring
    rw [hleft, hright, h0, add_zero] at h
    nlinarith [h]
  have hmono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : f a ≤ f b := by
    have h := hsum (Real.sqrt a) (Real.sqrt (b - a))
    rw [Real.sq_sqrt ha, Real.sq_sqrt (sub_nonneg.mpr hab)] at h
    have harg : a + (b - a) = b := by ring
    rw [harg] at h
    have hs := hsq (Real.sqrt a)
    rw [Real.sq_sqrt ha] at hs
    have hu := hnonneg (Real.sqrt a) (Real.sqrt_nonneg a)
    have hv := hnonneg (Real.sqrt (b - a)) (Real.sqrt_nonneg (b - a))
    nlinarith [mul_nonneg hu hv, sq_nonneg (f (Real.sqrt (b - a)))]
  have hnat (n : ℕ) : f (n : ℝ) = (n : ℝ) ^ 2 := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using h0
    | one => simpa using h1
    | more n ih0 ih1 =>
      have h := hf ((n : ℝ) + 1) 1 1 1
      simp only [h1, mul_one] at h
      have harg : (n : ℝ) + 1 - 1 = n := by ring
      rw [harg, show (n : ℝ) + 1 + 1 = n + 2 by ring] at h
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at ih1 ⊢
      nlinarith
  have hint (z : ℤ) : f (z : ℝ) = (z : ℝ) ^ 2 := by
    cases z with
    | ofNat n => simpa using hnat n
    | negSucc n =>
      have h := hnat (n + 1)
      simpa only [Int.cast_negSucc, heven, neg_sq, Nat.cast_add, Nat.cast_one] using h
  have hrat (q : ℚ) : f (q : ℝ) = (q : ℝ) ^ 2 := by
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    have hqd : (q : ℝ) * q.den = q.num := by
      rw [Rat.cast_def, div_mul_cancel₀ _ hd]
    apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    calc
      f (q : ℝ) * (q.den : ℝ) ^ 2 = f ((q : ℝ) * q.den) := by
        rw [hmul, hnat]
      _ = (q.num : ℝ) ^ 2 := by rw [hqd, hint]
      _ = (q : ℝ) ^ 2 * (q.den : ℝ) ^ 2 := by rw [← hqd, mul_pow]
  have hpositive (x : ℝ) (hx : 0 ≤ x) : f x = x ^ 2 := by
    have hfpos := hnonneg x hx
    have hr := Real.sqrt_nonneg (f x)
    have hrsq := Real.sq_sqrt hfpos
    have heq : Real.sqrt (f x) = x := by
      apply le_antisymm
      · by_contra! hlt
        obtain ⟨q, hxq, hqr⟩ := exists_rat_btwn hlt
        have hfx : f x ≤ (q : ℝ) ^ 2 := by
          simpa only [hrat] using hmono hx hxq.le
        nlinarith
      · by_contra! hlt
        obtain ⟨q, hrq, hqx⟩ := exists_rat_btwn hlt
        have hq : 0 ≤ (q : ℝ) := by linarith
        have hfx : (q : ℝ) ^ 2 ≤ f x := by
          simpa only [hrat] using hmono hq hqx.le
        nlinarith
    rw [heq] at hrsq
    exact hrsq.symm
  intro x
  by_cases hx : 0 ≤ x
  · exact hpositive x hx
  · have h := hpositive (-x) (by linarith)
    simpa only [heven, neg_sq] using h

/-- Complete classification, including verification of all three solutions. -/
theorem imo2002_p5 (f : ℝ → ℝ) :
    Satisfies f ↔
      f = (fun _ => 0) ∨ f = (fun _ => (1 / 2 : ℝ)) ∨ f = (fun x => x ^ 2) := by
  constructor
  · intro hf
    have hz := hf 0 0 0 0
    norm_num only [mul_zero, sub_zero, add_zero] at hz
    have hfactor : f 0 * (2 * f 0 - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h0 | hhalf
    · have hmul (x y : ℝ) : f (x * y) = f x * f y := by
        simpa [h0] using (hf x y 0 0).symm
      have hone := hmul 1 1
      simp only [one_mul] at hone
      have hfactor1 : f 1 * (f 1 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor1 with h1 | h1
      · left
        funext x
        have h := hmul x 1
        simpa [h1] using h
      · right; right
        have h1' : f 1 = 1 := by linarith
        exact funext (normalized_square f hf h0 h1')
    · right; left
      have h0 : f 0 = 1 / 2 := by linarith
      funext x
      have h := hf x 0 0 0
      norm_num [h0] at h
      linarith
  · rintro (rfl | rfl | rfl)
    · intro x y z t
      norm_num
    · intro x y z t
      norm_num
    · intro x y z t
      dsimp
      ring

end IMO2002P5
