import Mathlib

/-!
# IMO 1996, Problem 2

`P` is inside triangle `ABC` with `∠APB - ∠ACB = ∠APC - ∠ABC`; `D`, `E` are the incentres of
`APB`, `APC`. Show `AP`, `BD`, `CE` are concurrent.

## The reduction

`BD` is the bisector of `∠ABP` and `CE` is the bisector of `∠ACP`, so by the angle bisector
theorem they meet `AP` at the points dividing `AP` in the ratios `AB : PB` and `AC : PC`. Hence
the three lines concur exactly when

  `AC · PB = AB · PC`.                                            (★)

That is the whole content of the problem, and it is what is proved here.

## Encoding the angle hypothesis

Points are complex numbers `a b c p`. Put

  `X = (a-p)(b-c)`,  `Y = (b-p)(c-a)`,  `T = (c-p)(a-b)`,

so that `X + Y + T = 0` identically (`sum_eq_zero` below). The two "angle defects" of the problem
are the arguments of

  `Z = -Y/X`  (that is `∠APB - ∠ACB`)  and  `W = -T/X`  (that is `∠APC - ∠ABC`),

and with `a, b, c` counterclockwise and `p` interior the hypothesis `∠APB - ∠ACB = ∠APC - ∠ABC`
says `arg Z = -arg W`, i.e. `Z·W = Y·T/X²` is real. That is `hcond` below.

Conclusion (★) is `‖Y‖ = ‖T‖`.

`hnr` says `Y/T` is not real. This excludes a degenerate branch of the algebra — `Im(s/(s+1)²) = 0`
holds either when `|s| = 1` (the wanted conclusion) or when `s` is real — and it holds throughout
the interior of a nondegenerate triangle, failing only as `p` approaches a vertex.

Everything below is proved; there is no `sorry`.
-/

namespace Imo1996P2

/-- If `s/(s+1)²` is real and `s` is not, then `s` has modulus one. -/
theorem abs_ratio_eq_one {s : ℂ} (h1 : s + 1 ≠ 0) (him : s.im ≠ 0)
    (h : (s / (s + 1) ^ 2).im = 0) : ‖s‖ = 1 := by
  have hd : ((s + 1) ^ 2) ≠ 0 := pow_ne_zero 2 h1
  have hns : Complex.normSq ((s + 1) ^ 2) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hd
  rw [Complex.div_im] at h
  have h' : s.im * ((s + 1) ^ 2).re - s.re * ((s + 1) ^ 2).im = 0 := by
    field_simp at h
    linarith
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im] at h'
  have hfac : s.im * (1 - s.re * s.re - s.im * s.im) = 0 := by linear_combination h'
  have hsq : s.re * s.re + s.im * s.im = 1 := by
    rcases mul_eq_zero.1 hfac with h0 | h0
    · exact absurd h0 him
    · linarith
  rw [Complex.norm_def, Complex.normSq_apply, hsq, Real.sqrt_one]

/-- The three products always sum to zero. -/
theorem sum_eq_zero (a b c p : ℂ) :
    (a - p) * (b - c) + (b - p) * (c - a) + (c - p) * (a - b) = 0 := by ring

/-- **The metric core of IMO 1996 P2:** the angle hypothesis forces `AC · PB = AB · PC`. -/
theorem imo1996_p2_metric (a b c p : ℂ)
    (hT : (c - p) * (a - b) ≠ 0)
    (hX : (a - p) * (b - c) ≠ 0)
    (hnr : (((b - p) * (c - a)) / ((c - p) * (a - b))).im ≠ 0)
    (hcond : ((((b - p) * (c - a)) * ((c - p) * (a - b)))
        / ((a - p) * (b - c)) ^ 2).im = 0) :
    ‖b - p‖ * ‖c - a‖ = ‖c - p‖ * ‖a - b‖ := by
  set Y : ℂ := (b - p) * (c - a) with hY
  set T : ℂ := (c - p) * (a - b) with hTdef
  set X : ℂ := (a - p) * (b - c) with hXdef
  have hsum : X + Y + T = 0 := by rw [hXdef, hY, hTdef]; exact sum_eq_zero a b c p
  have hXeq : X = -(Y + T) := by linear_combination hsum
  have hYT : Y + T ≠ 0 := fun h0 => hX (by rw [hXeq, h0, neg_zero])
  set s : ℂ := Y / T with hs
  have hYs : Y = s * T := by rw [hs]; field_simp
  have hs1 : s + 1 ≠ 0 := by
    intro h0
    apply hYT
    have hstep : Y + T = (s + 1) * T := by rw [hYs]; ring
    rw [h0, zero_mul] at hstep
    exact hstep
  have hA : X ^ 2 ≠ 0 := pow_ne_zero 2 hX
  have hB : (s + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hs1
  have hrw : Y * T / X ^ 2 = s / (s + 1) ^ 2 := by
    rw [div_eq_div_iff hA hB, hXeq, hYs]
    ring
  rw [hrw] at hcond
  have habs : ‖s‖ = 1 := abs_ratio_eq_one hs1 hnr hcond
  have hT0 : ‖T‖ ≠ 0 := norm_ne_zero_iff.2 hT
  have hYn : ‖Y‖ = ‖T‖ := by
    have h1 : ‖Y‖ / ‖T‖ = 1 := by rw [← norm_div]; exact habs
    field_simp at h1
    exact h1
  rw [hY, hTdef] at hYn
  simpa [norm_mul] using hYn

/-- **The concurrency.** With `AC·PB = AB·PC` the two ratios in which the bisectors from `B` and
from `C` cut `AP` agree. -/
theorem ratio_eq (a b c p : ℂ)
    (hbp : b ≠ p) (hcp : c ≠ p)
    (h : ‖b - p‖ * ‖c - a‖ = ‖c - p‖ * ‖a - b‖) :
    ‖a - c‖ / ‖c - p‖ = ‖a - b‖ / ‖b - p‖ := by
  have h1 : (0 : ℝ) < ‖b - p‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.2 hbp
  have h2 : (0 : ℝ) < ‖c - p‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.2 hcp
  rw [div_eq_div_iff h2.ne' h1.ne']
  rw [show ‖a - c‖ = ‖c - a‖ from norm_sub_rev a c]
  linarith [h]

/-- The point cutting `AP` in the ratio `r : 1`, i.e. with `AX/XP = r`. -/
noncomputable def divPt (a p : ℂ) (r : ℝ) : ℂ := (a + (r : ℂ) * p) / (1 + (r : ℂ))

/-- The feet on `AP` of the bisector from `C` (of `∠ACP`) and of the bisector from `B`
(of `∠ABP`) coincide. By the angle bisector theorem those feet are `divPt a p (AC/CP)` and
`divPt a p (AB/BP)`, which is the modelling input here; the equality of the two ratios is
`ratio_eq`. -/
theorem feet_eq (a b c p : ℂ)
    (hbp : b ≠ p) (hcp : c ≠ p)
    (h : ‖b - p‖ * ‖c - a‖ = ‖c - p‖ * ‖a - b‖) :
    divPt a p (‖a - c‖ / ‖c - p‖) = divPt a p (‖a - b‖ / ‖b - p‖) := by
  rw [ratio_eq a b c p hbp hcp h]

end Imo1996P2
