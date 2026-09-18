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
# IMO 2008, Problem 4

Find all functions `f : (0, ∞) → (0, ∞)` such that
`(f w ^ 2 + f x ^ 2) / (f (y ^ 2) + f (z ^ 2)) = (w ^ 2 + x ^ 2) / (y ^ 2 + z ^ 2)`
for all positive reals `w, x, y, z` with `w * x = y * z`.

The answer is `f x = x` for all `x > 0`, or `f x = 1 / x` for all `x > 0`.
-/

namespace Imo2008P4

/-- The functional equation, for a function `f : ℝ → ℝ` (only its values on the
positive reals are constrained). -/
def FE (f : ℝ → ℝ) : Prop :=
  ∀ w x y z : ℝ, 0 < w → 0 < x → 0 < y → 0 < z → w * x = y * z →
    (f w ^ 2 + f x ^ 2) / (f (y ^ 2) + f (z ^ 2)) = (w ^ 2 + x ^ 2) / (y ^ 2 + z ^ 2)

/-- A solution of the functional equation satisfies `f 1 = 1`. -/
theorem value_at_one (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x) (hf : FE f) :
    f 1 = 1 := by
  have h1 : (0:ℝ) < f 1 := hpos 1 one_pos
  have h := hf 1 1 1 1 one_pos one_pos one_pos one_pos (by norm_num)
  norm_num at h
  have hne : f 1 + f 1 ≠ 0 := by positivity
  field_simp at h
  nlinarith [h, h1]

/-- Pointwise, a solution takes the value `x` or the value `1 / x`. -/
theorem pointwise (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x) (hf : FE f)
    (x : ℝ) (hx : 0 < x) : f x = x ∨ f x = 1 / x := by
  have h1 : f 1 = 1 := value_at_one f hpos hf
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have h := hf 1 x (Real.sqrt x) (Real.sqrt x) one_pos hx hs hs (by
    rw [← sq, hsq]; ring)
  rw [hsq, h1] at h
  have hfx : 0 < f x := hpos x hx
  have hden : f x + f x ≠ 0 := by positivity
  have hden2 : x + x ≠ 0 := by positivity
  rw [div_eq_div_iff hden hden2] at h
  have hfac : (f x - x) * (x * f x - 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hfac with h' | h'
  · left; linarith
  · right
    field_simp
    linarith [h']

/-- The two pointwise alternatives cannot be mixed. -/
theorem no_mixing (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x) (hf : FE f)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hfa : f a = a) (hfb : f b = 1 / b) :
    a = 1 ∨ b = 1 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr hab
  have hsq : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt hab.le
  have h := hf a b (Real.sqrt (a * b)) (Real.sqrt (a * b)) ha hb hs hs (by
    rw [← sq, hsq])
  rw [hsq, hfa, hfb] at h
  have hfab : 0 < f (a * b) := hpos _ hab
  have hden : f (a * b) + f (a * b) ≠ 0 := by positivity
  have hden2 : a * b + a * b ≠ 0 := by positivity
  rw [div_eq_div_iff hden hden2] at h
  have hbne : b ≠ 0 := ne_of_gt hb
  have habne : a * b ≠ 0 := ne_of_gt hab
  rcases pointwise f hpos hf (a * b) hab with hc | hc
  · rw [hc] at h
    right
    have key : a ^ 2 + (1 / b) ^ 2 = a ^ 2 + b ^ 2 := mul_right_cancel₀ hden2 h
    have hb4 : b ^ 4 = 1 := by
      field_simp at key
      linarith [key]
    have hfac : (b - 1) * ((b + 1) * (b ^ 2 + 1)) = 0 := by linear_combination hb4
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · nlinarith [h', hb]
  · rw [hc] at h
    left
    have ha4 : a ^ 4 = 1 := by
      field_simp at h
      have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hbne
      have hfac0 : (a ^ 4 - 1) * b ^ 2 = 0 := by linear_combination h
      rcases mul_eq_zero.mp hfac0 with h' | h'
      · linarith
      · exact absurd h' hb2
    have hfac : (a - 1) * ((a + 1) * (a ^ 2 + 1)) = 0 := by linear_combination ha4
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · nlinarith [h', ha]

/-- **IMO 2008, Problem 4.** For `f` positive on the positive reals, `f` satisfies the
functional equation if and only if `f x = x` for all `x > 0` or `f x = 1 / x` for all
`x > 0`. -/
theorem imo2008_p4 (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x) :
    FE f ↔ ((∀ x : ℝ, 0 < x → f x = x) ∨ (∀ x : ℝ, 0 < x → f x = 1 / x)) := by
  constructor
  · intro hf
    by_cases hid : ∀ x : ℝ, 0 < x → f x = x
    · exact Or.inl hid
    · right
      push_neg at hid
      obtain ⟨b, hb, hbne⟩ := hid
      have hfb : f b = 1 / b := (pointwise f hpos hf b hb).resolve_left hbne
      have hb1 : b ≠ 1 := by
        rintro rfl
        exact hbne (by simpa using value_at_one f hpos hf)
      intro x hx
      rcases pointwise f hpos hf x hx with hc | hc
      · rcases no_mixing f hpos hf x b hx hb hc hfb with h1 | h1
        · rw [h1] at hc ⊢; norm_num [hc, h1]
        · exact absurd h1 hb1
      · exact hc
  · rintro (h | h) w x y z hw hx hy hz hcon
    · rw [h w hw, h x hx, h (y ^ 2) (by positivity), h (z ^ 2) (by positivity)]
    · rw [h w hw, h x hx, h (y ^ 2) (by positivity), h (z ^ 2) (by positivity)]
      have hw' : w ≠ 0 := ne_of_gt hw
      have hx' : x ≠ 0 := ne_of_gt hx
      have hy' : y ≠ 0 := ne_of_gt hy
      have hz' : z ≠ 0 := ne_of_gt hz
      have hyz : (0:ℝ) < y ^ 2 + z ^ 2 := by positivity
      have hwx : (0:ℝ) < w ^ 2 + x ^ 2 := by positivity
      have h2 : w ^ 2 * x ^ 2 = y ^ 2 * z ^ 2 := by rw [← mul_pow, ← mul_pow, hcon]
      rw [div_eq_div_iff (by positivity) (ne_of_gt hyz)]
      field_simp
      linear_combination (-(x ^ 2 + w ^ 2) * (y ^ 2 + z ^ 2)) * h2

end Imo2008P4
