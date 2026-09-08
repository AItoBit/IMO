/-
# IMO 1973, Problem 1

`O` lies on a line `g`; `OP₁, …, OPₙ` are unit vectors with all `Pᵢ` in a plane
containing `g` and on one side of `g`.  Prove that if `n` is odd then
`‖OP₁ + ⋯ + OPₙ‖ ≥ 1`.

## Modelling

Take the plane to be `ℂ`, `O` the origin and `g` the real axis.  "Unit vector"
is `‖v i‖ = 1`, "on one side of `g`" is `0 ≤ (v i).im`.

## Proof

The AoPS solution is an induction that discards the two outermost vectors.  The
argument below is a one-shot version of the same idea, which is much easier to
formalize because it needs no induction — only a sorting step.

Write `v i = (cos θᵢ, sin θᵢ)` with `θᵢ = arccos (v i).re ∈ [0, π]`.  Sort the
indices so that `θ` is monotone, and let `m` be the middle index (`n = 2r+1`, so
`m = r`).  For every `j`, the reversed index `rev j` sits on the other side of
`m`, so `θ_j - θ_m` and `θ_{rev j} - θ_m` have opposite signs and their absolute
values add up to at most `π`.  Since

  `cos x + cos y = 2 cos((x+y)/2) cos((x-y)/2) ≥ 0`  for `x, y ≥ 0`, `x + y ≤ π`,

we get `cos (θ_j - θ_m) + cos (θ_{rev j} - θ_m) ≥ 0` for **every** `j`, and the
term at `j = m` equals `2` because `rev m = m`.  Summing,

  `2 ≤ ∑_j (cos (θ_j - θ_m) + cos (θ_{rev j} - θ_m)) = 2 ∑_j cos (θ_j - θ_m)`,

so `⟪v m, S⟫ = ∑_j cos (θ_j - θ_m) ≥ 1`, and Cauchy–Schwarz with `‖v m‖ = 1`
gives `‖S‖ ≥ 1`.
-/

import Mathlib

namespace Imo1973P1

/-- If `x, y ≥ 0` and `x + y ≤ π`, then `cos x + cos y ≥ 0`. -/
private lemma cos_add_cos_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ Real.pi) : 0 ≤ Real.cos x + Real.cos y := by
  rw [Real.cos_add_cos]
  have hpi := Real.pi_pos
  have h1 : 0 ≤ Real.cos ((x + y) / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h2 : 0 ≤ Real.cos ((x - y) / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  exact mul_nonneg (by linarith) h2

/-- **IMO 1973, Problem 1.** -/
theorem imo1973_p1 (n : ℕ) (hodd : Odd n) (v : Fin n → ℂ)
    (hunit : ∀ i, ‖v i‖ = 1) (hside : ∀ i, 0 ≤ (v i).im) :
    1 ≤ ‖∑ i, v i‖ := by
  -- the norm in coordinates
  have hnorm : ∀ z : ℂ, ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    intro z
    rw [← dist_zero_right z, Complex.dist_eq_re_im]
    simp
  have hsq : ∀ i, (v i).re ^ 2 + (v i).im ^ 2 = 1 := by
    intro i
    have h := hunit i
    rw [hnorm] at h
    have h2 : Real.sqrt ((v i).re ^ 2 + (v i).im ^ 2) ^ 2 = 1 ^ 2 := by rw [h]
    rwa [Real.sq_sqrt (by positivity), one_pow] at h2
  -- polar angles in `[0, π]`
  obtain ⟨θ, hcos, hsin, hθ0, hθpi⟩ :
      ∃ θ : Fin n → ℝ, (∀ i, Real.cos (θ i) = (v i).re) ∧
        (∀ i, Real.sin (θ i) = (v i).im) ∧ (∀ i, 0 ≤ θ i) ∧ (∀ i, θ i ≤ Real.pi) := by
    refine ⟨fun i => Real.arccos ((v i).re), ?_, ?_, ?_, ?_⟩
    · intro i
      exact Real.cos_arccos
        (by nlinarith [hsq i, sq_nonneg ((v i).im), sq_nonneg ((v i).re + 1)])
        (by nlinarith [hsq i, sq_nonneg ((v i).im), sq_nonneg ((v i).re - 1)])
    · intro i
      show Real.sin (Real.arccos ((v i).re)) = (v i).im
      rw [Real.sin_arccos, show 1 - (v i).re ^ 2 = (v i).im ^ 2 by linarith [hsq i]]
      exact Real.sqrt_sq (hside i)
    · intro i; exact Real.arccos_nonneg _
    · intro i; exact Real.arccos_le_pi _
  -- write `n = 2r + 1`
  obtain ⟨r, hr⟩ : ∃ r, n = 2 * r + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  subst hr
  -- sort the indices so that the angles increase
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin (2 * r + 1)), Monotone (θ ∘ σ) :=
    ⟨Tuple.sort θ, Tuple.monotone_sort θ⟩
  -- the middle index
  obtain ⟨m, hmval⟩ : ∃ m : Fin (2 * r + 1), (m : ℕ) = r := ⟨⟨r, by omega⟩, rfl⟩
  have hrevm : Fin.rev m = m := by
    apply Fin.ext
    rw [Fin.val_rev, hmval]
    omega
  -- the pairing estimate
  have hkey : ∀ j : Fin (2 * r + 1),
      0 ≤ Real.cos (θ (σ j) - θ (σ m)) + Real.cos (θ (σ (Fin.rev j)) - θ (σ m)) := by
    intro j
    have hrv : ((Fin.rev j : Fin (2 * r + 1)) : ℕ) = 2 * r + 1 - ((j : ℕ) + 1) := Fin.val_rev j
    have hjlt : (j : ℕ) < 2 * r + 1 := j.isLt
    by_cases hj : (j : ℕ) ≤ r
    · have h1 : θ (σ j) ≤ θ (σ m) := hmono (by rw [Fin.le_def, hmval]; exact hj)
      have h2 : θ (σ m) ≤ θ (σ (Fin.rev j)) := hmono (by rw [Fin.le_def, hmval, hrv]; omega)
      rw [show θ (σ j) - θ (σ m) = -(θ (σ m) - θ (σ j)) by ring, Real.cos_neg]
      refine cos_add_cos_nonneg (by linarith) (by linarith) ?_
      have ha := hθ0 (σ j)
      have hb := hθpi (σ (Fin.rev j))
      linarith
    · have h1 : θ (σ m) ≤ θ (σ j) := hmono (by rw [Fin.le_def, hmval]; omega)
      have h2 : θ (σ (Fin.rev j)) ≤ θ (σ m) := hmono (by rw [Fin.le_def, hmval, hrv]; omega)
      rw [show θ (σ (Fin.rev j)) - θ (σ m) = -(θ (σ m) - θ (σ (Fin.rev j))) by ring,
        Real.cos_neg]
      refine cos_add_cos_nonneg (by linarith) (by linarith) ?_
      have ha := hθ0 (σ (Fin.rev j))
      have hb := hθpi (σ j)
      linarith
  -- reversing the index does not change the sum
  have hsum1 : ∑ j : Fin (2 * r + 1), Real.cos (θ (σ (Fin.rev j)) - θ (σ m))
      = ∑ j : Fin (2 * r + 1), Real.cos (θ (σ j) - θ (σ m)) :=
    Fintype.sum_bijective Fin.rev
      (Function.Involutive.bijective (fun i => Fin.rev_rev i)) _ _ (fun _ => rfl)
  have hsum2 : ∑ j : Fin (2 * r + 1),
      (Real.cos (θ (σ j) - θ (σ m)) + Real.cos (θ (σ (Fin.rev j)) - θ (σ m)))
      = 2 * ∑ j : Fin (2 * r + 1), Real.cos (θ (σ j) - θ (σ m)) := by
    rw [Finset.sum_add_distrib, hsum1]
    ring
  have hterm : Real.cos (θ (σ m) - θ (σ m))
      + Real.cos (θ (σ (Fin.rev m)) - θ (σ m)) = 2 := by
    rw [hrevm, sub_self, Real.cos_zero]
    norm_num
  have hbig : (2 : ℝ) ≤ ∑ j : Fin (2 * r + 1),
      (Real.cos (θ (σ j) - θ (σ m)) + Real.cos (θ (σ (Fin.rev j)) - θ (σ m))) := by
    rw [← hterm]
    exact Finset.single_le_sum (fun j _ => hkey j) (Finset.mem_univ m)
  have hC : (1 : ℝ) ≤ ∑ j : Fin (2 * r + 1), Real.cos (θ (σ j) - θ (σ m)) := by
    rw [hsum2] at hbig
    linarith
  -- rewrite the sum of cosines as an inner product with the total sum
  have hSre : (∑ i, v i).re = ∑ j : Fin (2 * r + 1), (v (σ j)).re := by
    rw [Equiv.sum_comp σ (fun i => (v i).re)]
    simp
  have hSim : (∑ i, v i).im = ∑ j : Fin (2 * r + 1), (v (σ j)).im := by
    rw [Equiv.sum_comp σ (fun i => (v i).im)]
    simp
  have hexpand : ∑ j : Fin (2 * r + 1), Real.cos (θ (σ j) - θ (σ m))
      = (v (σ m)).re * (∑ i, v i).re + (v (σ m)).im * (∑ i, v i).im := by
    have h1 : ∀ j : Fin (2 * r + 1), Real.cos (θ (σ j) - θ (σ m))
        = (v (σ m)).re * (v (σ j)).re + (v (σ m)).im * (v (σ j)).im := by
      intro j
      rw [Real.cos_sub, hcos, hcos, hsin, hsin]
      ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hSre, hSim]
  -- Cauchy–Schwarz
  set S := ∑ i, v i with hS
  have hu : (v (σ m)).re ^ 2 + (v (σ m)).im ^ 2 = 1 := hsq (σ m)
  have hT : (1 : ℝ) ≤ (v (σ m)).re * S.re + (v (σ m)).im * S.im := by
    rw [← hexpand]; exact hC
  have hCS : ((v (σ m)).re * S.re + (v (σ m)).im * S.im) ^ 2 ≤ S.re ^ 2 + S.im ^ 2 := by
    nlinarith [sq_nonneg ((v (σ m)).re * S.im - (v (σ m)).im * S.re), hu]
  have hSsq : (1 : ℝ) ≤ S.re ^ 2 + S.im ^ 2 := by nlinarith [hT, hCS]
  rw [hnorm]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (S.re ^ 2 + S.im ^ 2) := Real.sqrt_le_sqrt hSsq

end Imo1973P1
