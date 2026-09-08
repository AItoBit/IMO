/-
# IMO 1973, Problem 5

`G` is a set of non-constant real functions of the form `f x = a x + b` such
that

* (a) `f, g ∈ G → g ∘ f ∈ G`;
* (b) `f ∈ G → f⁻¹ ∈ G`;
* (c) every `f ∈ G` has a fixed point.

Prove that there is a real `k` with `f k = k` for every `f ∈ G`.

## Modelling

`G : Set (ℝ → ℝ)`, with

* `hform` : every `f ∈ G` is `x ↦ a x + b` with `a ≠ 0` ("non-constant");
* `hcomp` : closure under composition;
* `hinv`  : every `f ∈ G` has a two-sided inverse lying in `G`;
* `hfix`  : every `f ∈ G` has a fixed point.

## Proof

Two observations, following the AoPS solution.

*Translations are trivial.*  If `h ∈ G` and `h x = x + β` for all `x`, then a
fixed point of `h` gives `β = 0` (`htrans` below).

*The key relation.*  For `f, g ∈ G` with `f x = a₁ x + b₁` and `g x = a₂ x + b₂`,
the element `h = (f ∘ g)⁻¹ ∘ (g ∘ f)` is in `G` by (a) and (b), and satisfies
`(f ∘ g) (h x) = (g ∘ f) x`.  Comparing coefficients at `x = 0` and `x = 1`
forces the linear coefficient of `h` to be `1`, so `h` is a translation, so its
constant term vanishes, which is exactly

  `a₂ b₁ + b₂ - a₁ b₂ - b₁ = 0`.   (`key` below)

*Conclusion.*  If every element of `G` is the identity, any `k` works.
Otherwise pick `f₀ ∈ G` that is not the identity; then its linear coefficient
`a₀ ≠ 1`, and (c) gives it a fixed point `x₀`.  For any `f ∈ G` with
coefficients `(a, b)`, the key relation together with `a₀ x₀ + b₀ = x₀` gives

  `(1 - a₀) · (x₀ (1 - a) - b) = 0`,

and `a₀ ≠ 1` yields `a x₀ + b = x₀`, i.e. `f x₀ = x₀`.

(Working with the fixed point `x₀` of `f₀` instead of `b₀ / (1 - a₀)` avoids
division entirely.)
-/

import Mathlib

namespace Imo1973P5

/-- **IMO 1973, Problem 5.** -/
theorem imo1973_p5 (G : Set (ℝ → ℝ))
    (hform : ∀ f ∈ G, ∃ a b : ℝ, a ≠ 0 ∧ ∀ x, f x = a * x + b)
    (hcomp : ∀ f ∈ G, ∀ g ∈ G, (f ∘ g) ∈ G)
    (hinv : ∀ f ∈ G, ∃ g ∈ G, (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x))
    (hfix : ∀ f ∈ G, ∃ x, f x = x) :
    ∃ k : ℝ, ∀ f ∈ G, f k = k := by
  -- a translation in `G` is the identity
  have htrans : ∀ h ∈ G, ∀ β : ℝ, (∀ x, h x = x + β) → β = 0 := by
    intro h hhG β hb
    obtain ⟨x, hx⟩ := hfix h hhG
    rw [hb] at hx
    linarith
  -- the key relation between the coefficients of any two elements
  have key : ∀ f ∈ G, ∀ g ∈ G, ∀ a₁ b₁ a₂ b₂ : ℝ, a₁ ≠ 0 → a₂ ≠ 0 →
      (∀ x, f x = a₁ * x + b₁) → (∀ x, g x = a₂ * x + b₂) →
      a₂ * b₁ + b₂ - a₁ * b₂ - b₁ = 0 := by
    intro f hfG g hgG a₁ b₁ a₂ b₂ ha₁ ha₂ hf hg
    have hFG : (f ∘ g) ∈ G := hcomp f hfG g hgG
    have hKG : (g ∘ f) ∈ G := hcomp g hgG f hfG
    obtain ⟨Finv, hFinvG, hR, -⟩ := hinv (f ∘ g) hFG
    have hhG : (Finv ∘ (g ∘ f)) ∈ G := hcomp Finv hFinvG (g ∘ f) hKG
    obtain ⟨α, β, hα, hh⟩ := hform _ hhG
    -- `(f ∘ g) (h x) = (g ∘ f) x`, written out in coefficients
    have hExp : ∀ x : ℝ,
        a₁ * (a₂ * (α * x + β) + b₂) + b₁ = a₂ * (a₁ * x + b₁) + b₂ := by
      intro x
      have h := hR ((g ∘ f) x)
      have hval := hh x
      simp only [Function.comp_apply] at h hval
      rw [hval] at h
      simp only [hf, hg] at h
      exact h
    have h0 := hExp 0
    have h1 := hExp 1
    -- the linear coefficient of `h` is `1`
    have hprod : a₁ * a₂ * (α - 1) = 0 := by linear_combination h1 - h0
    have hα1 : α = 1 := by
      rcases mul_eq_zero.mp hprod with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' ha₁
        · exact absurd h' ha₂
      · linarith
    -- so `h` is a translation, hence its constant term vanishes
    have hβ : β = 0 := by
      refine htrans _ hhG β ?_
      intro x
      rw [hh, hα1]
      ring
    rw [hβ] at h0
    linear_combination -h0
  -- either every element is the identity, or we can pick a non-identity one
  by_cases hex : ∃ f₀ ∈ G, ∃ y, f₀ y ≠ y
  · obtain ⟨f₀, hf₀G, y, hy⟩ := hex
    obtain ⟨a₀, b₀, ha₀0, hf₀⟩ := hform f₀ hf₀G
    have ha₀ : a₀ ≠ 1 := by
      intro h
      apply hy
      have hb₀ : b₀ = 0 := by
        refine htrans f₀ hf₀G b₀ ?_
        intro x
        rw [hf₀, h]
        ring
      rw [hf₀, h, hb₀]
      ring
    obtain ⟨x₀, hx₀⟩ := hfix f₀ hf₀G
    rw [hf₀] at hx₀
    refine ⟨x₀, ?_⟩
    intro f hfG
    obtain ⟨a, b, ha0, hf⟩ := hform f hfG
    have hrel := key f hfG f₀ hf₀G a b a₀ b₀ ha0 ha₀0 hf hf₀
    have h1 : (1 : ℝ) - a₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm ha₀)
    have hfact : (1 - a₀) * (x₀ * (1 - a) - b) = 0 := by
      linear_combination hrel - (1 - a) * hx₀
    have h2 : x₀ * (1 - a) - b = 0 := by
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd h h1
      · exact h
    rw [hf]
    linear_combination -h2
  · refine ⟨0, ?_⟩
    intro f hfG
    by_contra hcon
    exact hex ⟨f, hfG, 0, hcon⟩

end Imo1973P5
