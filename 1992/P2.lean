import Mathlib

/-!
# IMO 1992, Problem 2

Find all `f : ℝ → ℝ` with `f (x² + f y) = y + (f x)²` for all real `x, y`.

Answer: `f = id`.

## Proof

* `f` is injective: `x = 0` gives `f (f u) = u + (f 0)²`, so `f u = f v` forces `u = v`.
* `f` is surjective onto `0`: `t := f (-(f 0)²)` satisfies `f t = 0`.
* Then `x = t, y = 0` gives `f (t² + f 0) = 0 = f t`, so `t² + f 0 = t`; and `x = 0, y = t`
  gives `f 0 = t + (f 0)²`. Eliminating `t` yields `(f 0)²·((f 0 - 1)² + 1) = 0`, and the
  second factor is positive, so `f 0 = 0`.
* Hence `f (f y) = y`, and substituting `y ↦ f y` in the original equation gives
  `f (x² + y) = f y + (f x)²`.
* So `f` is monotone: for `v ≤ u`, take `s = √(u - v)` and get `f u = f v + (f s)² ≥ f v`.
* Finally `f (f y) = y` with `f` monotone forces `f y = y`: `f y < y` would give `y ≤ f y`,
  and `y < f y` would give `f y ≤ y`.
-/

namespace Imo1992P2

theorem imo1992_p2 (f : ℝ → ℝ) :
    (∀ x y : ℝ, f (x ^ 2 + f y) = y + (f x) ^ 2) ↔ ∀ x, f x = x := by
  constructor
  · intro h
    -- `f` is injective
    have hinj : Function.Injective f := by
      intro u v huv
      have h1 := h 0 u
      have h2 := h 0 v
      rw [huv] at h1
      linarith
    -- a point sent to `0`
    obtain ⟨t, ht⟩ : ∃ t, f t = 0 := by
      refine ⟨f (-(f 0 ^ 2)), ?_⟩
      have h1 := h 0 (-(f 0 ^ 2))
      have h2 : (0 : ℝ) ^ 2 + f (-(f 0 ^ 2)) = f (-(f 0 ^ 2)) := by ring
      rw [h2] at h1
      linarith
    -- two equations for `t`
    have ht1 : t ^ 2 + f 0 = t := by
      refine hinj ?_
      have h1 := h t 0
      rw [ht] at h1
      rw [ht, h1]
      norm_num
    have ht2 : f 0 = t + (f 0) ^ 2 := by
      have h1 := h 0 t
      rw [ht] at h1
      have h2 : (0 : ℝ) ^ 2 + 0 = 0 := by ring
      rw [h2] at h1
      exact h1
    -- `f 0 = 0`
    have htv : t = f 0 - (f 0) ^ 2 := by linarith
    have hpoly : (f 0) ^ 2 * ((f 0 - 1) ^ 2 + 1) = 0 := by
      rw [htv] at ht1
      linear_combination ht1
    have hd0 : f 0 = 0 := by
      have hq : (0 : ℝ) < (f 0 - 1) ^ 2 + 1 := by positivity
      have hsq : (f 0) ^ 2 = 0 := by
        rcases mul_eq_zero.1 hpoly with h' | h'
        · exact h'
        · linarith
      exact sq_eq_zero_iff.mp hsq
    -- `f` is an involution
    have hff : ∀ y, f (f y) = y := by
      intro y
      have h1 := h 0 y
      rw [hd0] at h1
      have h2 : (0 : ℝ) ^ 2 + f y = f y := by ring
      rw [h2] at h1
      simpa using h1
    -- the shifted equation
    have hadd : ∀ x y : ℝ, f (x ^ 2 + y) = f y + (f x) ^ 2 := by
      intro x y
      have h1 := h x (f y)
      rw [hff y] at h1
      exact h1
    -- `f` is monotone
    have hmono : ∀ u v : ℝ, v ≤ u → f v ≤ f u := by
      intro u v huv
      have hs : Real.sqrt (u - v) ^ 2 = u - v := Real.sq_sqrt (by linarith)
      have h1 := hadd (Real.sqrt (u - v)) v
      rw [hs] at h1
      have h2 : u - v + v = u := by ring
      rw [h2] at h1
      nlinarith [sq_nonneg (f (Real.sqrt (u - v)))]
    -- conclude
    intro y
    rcases lt_trichotomy (f y) y with hlt | heq | hgt
    · exfalso
      have hge := hmono y (f y) hlt.le
      rw [hff y] at hge
      linarith
    · exact heq
    · exfalso
      have hle := hmono (f y) y hgt.le
      rw [hff y] at hle
      linarith
  · intro hf x y
    simp only [hf]
    ring

end Imo1992P2
