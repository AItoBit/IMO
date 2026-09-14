import Mathlib

open scoped BigOperators
open scoped Real
open scoped RealInnerProductSpace

set_option maxHeartbeats 1000000

namespace Imo1998P5

/-! ### Scalar algebra -/

/-- The Gram determinant identity forces this factorization identity. -/
theorem key_identity (r p q w : ℝ)
    (hGram : r ^ 2 * (p ^ 2 + q ^ 2 + w ^ 2) = r ^ 6 + 2 * p * q * w) :
    2 * (w * p - r ^ 2 * q) * (q * p - r ^ 2 * w) =
      -(r ^ 2 * (r ^ 2 + p) * ((q + p - w - r ^ 2) * (q + r ^ 2 - w - p))) := by
  linear_combination (r ^ 2 - p) * hGram

theorem gram_aux (r p q w : ℝ)
    (hGram : r ^ 2 * (p ^ 2 + q ^ 2 + w ^ 2) = r ^ 6 + 2 * p * q * w) :
    r ^ 2 * (q - w) ^ 2 = (r ^ 2 - p) * (r ^ 2 * (r ^ 2 + p) - 2 * q * w) := by
  linear_combination hGram

theorem D1_ne_zero (r p q w : ℝ)
    (hGram : r ^ 2 * (p ^ 2 + q ^ 2 + w ^ 2) = r ^ 6 + 2 * p * q * w)
    (hp' : p < r ^ 2) (hq' : q < r ^ 2) (hw : -r ^ 2 < w) :
    q + p - w - r ^ 2 ≠ 0 := by
  intro h
  have hrp : r ^ 2 - p ≠ 0 := by linarith
  have hid := gram_aux r p q w hGram
  have h2 : (r ^ 2 - p) * (2 * q * w - 2 * r ^ 2 * p) = 0 := by
    linear_combination hid - r ^ 2 * (r ^ 2 - p + q - w) * h
  have hqw : q * w = r ^ 2 * p := by
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hrp
    · linarith
  have hsq : (q + w - (r ^ 2 + p)) * (q + w + (r ^ 2 + p)) = 0 := by
    linear_combination (q - w + r ^ 2 - p) * h + 4 * hqw
  rcases mul_eq_zero.1 hsq with h4 | h4
  · linarith
  · linarith

theorem D2_ne_zero (r p q w : ℝ)
    (hGram : r ^ 2 * (p ^ 2 + q ^ 2 + w ^ 2) = r ^ 6 + 2 * p * q * w)
    (hp' : p < r ^ 2) (hw' : w < r ^ 2) (hq : -r ^ 2 < q) :
    q + r ^ 2 - w - p ≠ 0 := by
  intro h
  have hrp : r ^ 2 - p ≠ 0 := by linarith
  have hid := gram_aux r p q w hGram
  have h2 : (r ^ 2 - p) * (2 * q * w - 2 * r ^ 2 * p) = 0 := by
    linear_combination hid + r ^ 2 * (r ^ 2 - p - q + w) * h
  have hqw : q * w = r ^ 2 * p := by
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hrp
    · linarith
  have hsq : (q + w - (r ^ 2 + p)) * (q + w + (r ^ 2 + p)) = 0 := by
    linear_combination (q - w - r ^ 2 + p) * h + 4 * hqw
  rcases mul_eq_zero.1 hsq with h4 | h4
  · linarith
  · linarith

/-- The heart of the matter, in scalar form. -/
theorem scalar_core (r p q w beta B2 s t : ℝ)
    (hGram : r ^ 2 * (p ^ 2 + q ^ 2 + w ^ 2) = r ^ 6 + 2 * p * q * w)
    (hp : -r ^ 2 < p) (hq : -r ^ 2 < q) (hw : -r ^ 2 < w)
    (hp' : p < r ^ 2) (hq' : q < r ^ 2) (hw' : w < r ^ 2)
    (hs : s * (q + p - w - r ^ 2) = w - beta)
    (ht : t * (q + r ^ 2 - w - p) = q - beta)
    (hbeta : beta * (r ^ 2 + p) = r ^ 2 * (q + w))
    (hB2 : B2 * (r ^ 2 + p) = 2 * r ^ 4) :
    B2 + 2 * s * t * (r ^ 2 - p) = r ^ 2 := by
  have hc : (0:ℝ) < r ^ 2 + p := by linarith
  have hD1 := D1_ne_zero r p q w hGram hp' hq' hw
  have hD2 := D2_ne_zero r p q w hGram hp' hw' hq
  have e1 : (w - beta) * (r ^ 2 + p) = w * p - r ^ 2 * q := by linear_combination -hbeta
  have e2 : (q - beta) * (r ^ 2 + p) = q * p - r ^ 2 * w := by linear_combination -hbeta
  have h4 : (s * (q + p - w - r ^ 2)) * (t * (q + r ^ 2 - w - p)) = (w - beta) * (q - beta) := by
    rw [hs, ht]
  have h6 : ((w - beta) * (r ^ 2 + p)) * ((q - beta) * (r ^ 2 + p)) =
      (w * p - r ^ 2 * q) * (q * p - r ^ 2 * w) := by rw [e1, e2]
  have hst : s * t * ((q + p - w - r ^ 2) * (q + r ^ 2 - w - p) * (r ^ 2 + p) ^ 2) =
      (w * p - r ^ 2 * q) * (q * p - r ^ 2 * w) := by
    linear_combination (r ^ 2 + p) ^ 2 * h4 + h6
  have hkey := key_identity r p q w hGram
  have hX : ((q + p - w - r ^ 2) * (q + r ^ 2 - w - p) * (r ^ 2 + p) ^ 3) *
      (B2 + 2 * s * t * (r ^ 2 - p) - r ^ 2) = 0 := by
    linear_combination ((q + p - w - r ^ 2) * (q + r ^ 2 - w - p) * (r ^ 2 + p) ^ 2) * hB2 +
      (2 * (r ^ 2 - p) * (r ^ 2 + p)) * hst + ((r ^ 2 - p) * (r ^ 2 + p)) * hkey
  have hne : ((q + p - w - r ^ 2) * (q + r ^ 2 - w - p) * (r ^ 2 + p) ^ 3) ≠ 0 := by
    have : (r ^ 2 + p) ^ 3 ≠ 0 := by positivity
    exact mul_ne_zero (mul_ne_zero hD1 hD2) this
  have := (mul_eq_zero.1 hX).resolve_left hne
  linarith

/-! ### Coordinate form -/

/-- Everything happens in the plane, with the incentre at the origin:
`k, l, m` are the touch points, `b` is the vertex `B`. -/
theorem coord_core (r k0 k1 l0 l1 m0 m1 b0 b1 s t u v : ℝ)
    (hk : k0 ^ 2 + k1 ^ 2 = r ^ 2) (hl : l0 ^ 2 + l1 ^ 2 = r ^ 2) (hm : m0 ^ 2 + m1 ^ 2 = r ^ 2)
    (hbk : b0 * k0 + b1 * k1 = r ^ 2) (hbm : b0 * m0 + b1 * m1 = r ^ 2)
    (hp : -r ^ 2 < k0 * m0 + k1 * m1) (hq : -r ^ 2 < k0 * l0 + k1 * l1)
    (hw : -r ^ 2 < l0 * m0 + l1 * m1)
    (hp' : k0 * m0 + k1 * m1 < r ^ 2) (hq' : k0 * l0 + k1 * l1 < r ^ 2)
    (hw' : l0 * m0 + l1 * m1 < r ^ 2)
    (hR0 : b0 + s * (k0 - m0) = l0 + u * (m0 - l0))
    (hR1 : b1 + s * (k1 - m1) = l1 + u * (m1 - l1))
    (hS0 : b0 + t * (k0 - m0) = l0 + v * (k0 - l0))
    (hS1 : b1 + t * (k1 - m1) = l1 + v * (k1 - l1)) :
    (b0 + s * (k0 - m0)) * (b0 + t * (k0 - m0)) +
      (b1 + s * (k1 - m1)) * (b1 + t * (k1 - m1)) = r ^ 2 := by
  -- abbreviations
  have hGram : r ^ 2 * ((k0 * m0 + k1 * m1) ^ 2 + (k0 * l0 + k1 * l1) ^ 2 +
      (l0 * m0 + l1 * m1) ^ 2) = r ^ 6 + 2 * (k0 * m0 + k1 * m1) * (k0 * l0 + k1 * l1) *
        (l0 * m0 + l1 * m1) := by
    have h : (k0 ^ 2 + k1 ^ 2) * ((l0 ^ 2 + l1 ^ 2) * (m0 ^ 2 + m1 ^ 2)) +
        2 * (k0 * m0 + k1 * m1) * (k0 * l0 + k1 * l1) * (l0 * m0 + l1 * m1) =
        (k0 ^ 2 + k1 ^ 2) * (l0 * m0 + l1 * m1) ^ 2 +
        (l0 ^ 2 + l1 ^ 2) * (k0 * m0 + k1 * m1) ^ 2 +
        (m0 ^ 2 + m1 ^ 2) * (k0 * l0 + k1 * l1) ^ 2 := by ring
    rw [hk, hl, hm] at h
    linear_combination -h
  -- `b` is determined by the two tangency conditions
  have hdet : (k0 * m1 - k1 * m0) ^ 2 = (r ^ 2 - (k0 * m0 + k1 * m1)) *
      (r ^ 2 + (k0 * m0 + k1 * m1)) := by
    linear_combination (m0 ^ 2 + m1 ^ 2) * hk + r ^ 2 * hm
  have hdetne : k0 * m1 - k1 * m0 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    nlinarith [hdet]
  have he0 : (b0 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k0 + m0)) * (k0 * m1 - k1 * m0) = 0 := by
    have hk' : (b0 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k0 + m0)) * k0 +
        (b1 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k1 + m1)) * k1 = 0 := by
      linear_combination (r ^ 2 + (k0 * m0 + k1 * m1)) * hbk - r ^ 2 * hk
    have hm' : (b0 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k0 + m0)) * m0 +
        (b1 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k1 + m1)) * m1 = 0 := by
      linear_combination (r ^ 2 + (k0 * m0 + k1 * m1)) * hbm - r ^ 2 * hm
    linear_combination m1 * hk' - k1 * hm'
  have he1 : (b1 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k1 + m1)) * (k0 * m1 - k1 * m0) = 0 := by
    have hk' : (b0 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k0 + m0)) * k0 +
        (b1 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k1 + m1)) * k1 = 0 := by
      linear_combination (r ^ 2 + (k0 * m0 + k1 * m1)) * hbk - r ^ 2 * hk
    have hm' : (b0 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k0 + m0)) * m0 +
        (b1 * (r ^ 2 + (k0 * m0 + k1 * m1)) - r ^ 2 * (k1 + m1)) * m1 = 0 := by
      linear_combination (r ^ 2 + (k0 * m0 + k1 * m1)) * hbm - r ^ 2 * hm
    linear_combination k0 * hm' - m0 * hk'
  have hb0 : b0 * (r ^ 2 + (k0 * m0 + k1 * m1)) = r ^ 2 * (k0 + m0) := by
    have := (mul_eq_zero.1 he0).resolve_right hdetne
    linarith
  have hb1 : b1 * (r ^ 2 + (k0 * m0 + k1 * m1)) = r ^ 2 * (k1 + m1) := by
    have := (mul_eq_zero.1 he1).resolve_right hdetne
    linarith
  have hbeta : (b0 * l0 + b1 * l1) * (r ^ 2 + (k0 * m0 + k1 * m1)) =
      r ^ 2 * ((k0 * l0 + k1 * l1) + (l0 * m0 + l1 * m1)) := by
    linear_combination l0 * hb0 + l1 * hb1
  have hB2 : (b0 ^ 2 + b1 ^ 2) * (r ^ 2 + (k0 * m0 + k1 * m1)) = 2 * r ^ 4 := by
    linear_combination b0 * hb0 + b1 * hb1 + r ^ 2 * hbk + r ^ 2 * hbm
  have hs : s * ((k0 * l0 + k1 * l1) + (k0 * m0 + k1 * m1) - (l0 * m0 + l1 * m1) - r ^ 2) =
      (l0 * m0 + l1 * m1) - (b0 * l0 + b1 * l1) := by
    linear_combination (l0 + m0) * hR0 + (l1 + m1) * hR1 - hbm + u * hm - u * hl + s * hm + hl
  have ht : t * ((k0 * l0 + k1 * l1) + r ^ 2 - (l0 * m0 + l1 * m1) - (k0 * m0 + k1 * m1)) =
      (k0 * l0 + k1 * l1) - (b0 * l0 + b1 * l1) := by
    linear_combination (l0 + k0) * hS0 + (l1 + k1) * hS1 - hbk + v * hk - v * hl - t * hk + hl
  have main := scalar_core r (k0 * m0 + k1 * m1) (k0 * l0 + k1 * l1) (l0 * m0 + l1 * m1)
    (b0 * l0 + b1 * l1) (b0 ^ 2 + b1 ^ 2) s t hGram hp hq hw hp' hq' hw' hs ht hbeta hB2
  linear_combination main + (s + t) * hbk - (s + t) * hbm + s * t * hk + s * t * hm

/-! ### Plane geometry helpers -/

/-- Coordinates of the inner product on the Euclidean plane. -/
theorem inner_coord (x y : EuclideanSpace ℝ (Fin 2)) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- Coordinates of the inner product of two differences. -/
theorem inner_sub_coord (x y z : EuclideanSpace ℝ (Fin 2)) :
    ⟪x - z, y - z⟫ = (x 0 - z 0) * (y 0 - z 0) + (x 1 - z 1) * (y 1 - z 1) := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- Two vectors orthogonal to a common nonzero vector of the plane are parallel. -/
theorem cross_eq_zero_of_perp (n x y : EuclideanSpace ℝ (Fin 2)) (hn : n ≠ 0)
    (h1 : ⟪n, x⟫ = 0) (h2 : ⟪n, y⟫ = 0) : x 0 * y 1 - x 1 * y 0 = 0 := by
  rw [inner_coord] at h1 h2
  have hn' : ¬ (n 0 = 0 ∧ n 1 = 0) := by
    rintro ⟨h0, h1'⟩
    exact hn (by ext i; fin_cases i <;> simpa)
  have e0 : n 0 * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination y 1 * h1 - x 1 * h2
  have e1 : n 1 * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination x 0 * h2 - y 0 * h1
  rcases not_and_or.1 hn' with h | h
  · exact (mul_eq_zero.1 e0).resolve_left h
  · exact (mul_eq_zero.1 e1).resolve_left h

/-- If the cross product of `B - A` and `C - A` vanishes, the three points are collinear. -/
theorem collinear_of_cross_eq_zero (A B C : EuclideanSpace ℝ (Fin 2))
    (h : (B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0) = 0) :
    Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
  by_cases hBA : B = A
  · subst hBA
    have hset : ({B, B, C} : Set (EuclideanSpace ℝ (Fin 2))) = {B, C} := by simp
    rw [hset]; exact collinear_pair ℝ B C
  · rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
    refine ⟨B - A, ?_⟩
    have hne : ¬ (B 0 - A 0 = 0 ∧ B 1 - A 1 = 0) := by
      rintro ⟨h0, h1⟩
      exact hBA (by ext i; fin_cases i <;> simp <;> linarith)
    intro p hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · rcases not_and_or.1 hne with h0 | h0
      · refine ⟨(p 0 - A 0) / (B 0 - A 0), ?_⟩
        ext i
        fin_cases i <;> simp [vadd_eq_add] <;> field_simp <;> nlinarith [h]
      · refine ⟨(p 1 - A 1) / (B 1 - A 1), ?_⟩
        ext i
        fin_cases i <;> simp [vadd_eq_add] <;> field_simp <;> nlinarith [h]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If the tangent line at `X` to the circle of centre `I` and radius `r` passes through `P`,
then `⟪P - I, X - I⟫ = r ^ 2`. -/
theorem inner_vertex_touch {I P Q X : E} {r : ℝ} (hdist : dist I X = r)
    (hperp : ⟪X - I, Q - P⟫ = 0) (hseg : ∃ α : ℝ, X - P = α • (Q - P)) :
    ⟪P - I, X - I⟫ = r ^ 2 := by
  obtain ⟨α, hα⟩ := hseg
  have hXI : ⟪X - I, X - I⟫ = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hdist]
  have hPI : P - I = (X - I) - α • (Q - P) := by rw [← hα]; abel
  have hperp' : ⟪Q - P, X - I⟫ = 0 := by rw [real_inner_comm]; exact hperp
  rw [hPI, inner_sub_left, real_inner_smul_left, hXI, hperp']
  ring

/-- Two touch points of the same circle whose tangent lines meet are not antipodal. -/
theorem neg_sq_lt_inner {b k m : E} {r : ℝ} (hr : 0 < r)
    (hk : ⟪k, k⟫ = r ^ 2) (hm : ⟪m, m⟫ = r ^ 2) (hbk : ⟪b, k⟫ = r ^ 2) (hbm : ⟪b, m⟫ = r ^ 2) :
    -r ^ 2 < ⟪k, m⟫ := by
  by_contra hcon
  push_neg at hcon
  have h1 : ⟪k + m, k + m⟫ = 2 * r ^ 2 + 2 * ⟪k, m⟫ := by
    rw [real_inner_add_add_self, hk, hm]; ring
  have h2 : k + m = 0 := by
    have hnn := real_inner_self_nonneg (x := k + m)
    have h0 : ⟪k + m, k + m⟫ = 0 := le_antisymm (by linarith) hnn
    exact inner_self_eq_zero.mp h0
  have h3 : m = -k := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
  rw [h3, inner_neg_right, hbk] at hbm
  nlinarith

theorem inner_lt_sq {k m : E} {r : ℝ} (hk : ⟪k, k⟫ = r ^ 2) (hm : ⟪m, m⟫ = r ^ 2) (hne : k ≠ m) :
    ⟪k, m⟫ < r ^ 2 := by
  have h1 : ⟪k - m, k - m⟫ = 2 * r ^ 2 - 2 * ⟪k, m⟫ := by
    rw [real_inner_sub_sub_self, hk, hm]; ring
  have h2 : (0:ℝ) < ⟪k - m, k - m⟫ := real_inner_self_pos.2 (sub_ne_zero.2 hne)
  linarith

/-- An angle with positive inner product is acute. -/
theorem angle_lt_pi_div_two_of_inner_pos {x y : E} (h : 0 < ⟪x, y⟫) :
    InnerProductGeometry.angle x y < π / 2 := by
  have hx : x ≠ 0 := by rintro rfl; simp at h
  have hy : y ≠ 0 := by rintro rfl; simp at h
  rw [InnerProductGeometry.angle, Real.arccos_lt_pi_div_two]
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hny : 0 < ‖y‖ := norm_pos_iff.2 hy
  positivity

/-- Membership in a line, in vector form. -/
theorem eq_add_smul_of_mem_line {P Q X : EuclideanSpace ℝ (Fin 2)} (h : X ∈ line[ℝ, P, Q]) :
    ∃ u : ℝ, X = P + u • (Q - P) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at h
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [← hu, AffineMap.lineMap_apply]; simp [vsub_eq_sub]; abel⟩

/-- A point of an open segment, written relative to either endpoint. -/
theorem sub_eq_smul_of_mem_openSegment {P Q X : EuclideanSpace ℝ (Fin 2)}
    (h : X ∈ openSegment ℝ P Q) :
    (∃ α : ℝ, X - P = α • (Q - P)) ∧ (∃ β : ℝ, X - Q = β • (P - Q)) := by
  rw [openSegment_eq_image] at h
  obtain ⟨α, -, rfl⟩ := h
  exact ⟨⟨α, by module⟩, ⟨1 - α, by module⟩⟩

/-- If a nonzero vector is orthogonal to `B - A` and to `C - A`, then `A`, `B`, `C`
are collinear. -/
theorem collinear_of_perp {A B C n : EuclideanSpace ℝ (Fin 2)} (hn : n ≠ 0)
    (h1 : ⟪n, B - A⟫ = 0) (h2 : ⟪n, C - A⟫ = 0) :
    Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
  have hcross := cross_eq_zero_of_perp n (B - A) (C - A) hn h1 h2
  refine collinear_of_cross_eq_zero A B C ?_
  simpa using hcross

/-! ### The problem -/

/-- **IMO 1998, Problem 5.**
Let `I` be the incentre of the triangle `ABC`, and let its incircle (centre `I`, radius `r`)
touch the sides `BC`, `CA`, `AB` at `K`, `L`, `M` respectively (tangency being expressed by
saying that each touch point lies on the corresponding open side and that the radius to it is
orthogonal to that side).  The line through `B` parallel to `MK` meets the lines `LM` and `LK`
at `R` and `S` respectively.  Then the angle `RIS` is acute.

In fact the proof shows the sharper statement `⟪R - I, S - I⟫ = r ^ 2`. -/
theorem imo1998_p5 (A B C I K L M R S : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hIK : dist I K = r) (hIL : dist I L = r) (hIM : dist I M = r)
    (hK : K ∈ openSegment ℝ B C) (hL : L ∈ openSegment ℝ C A) (hM : M ∈ openSegment ℝ A B)
    (hKt : ⟪K - I, C - B⟫ = 0) (hLt : ⟪L - I, A - C⟫ = 0) (hMt : ⟪M - I, B - A⟫ = 0)
    (hRline : R ∈ line[ℝ, L, M]) (hSline : S ∈ line[ℝ, L, K])
    (hRB : ∃ s : ℝ, R = B + s • (K - M)) (hSB : ∃ t : ℝ, S = B + t • (K - M)) :
    EuclideanGeometry.angle R I S < π / 2 := by
  obtain ⟨s, rfl⟩ := hRB
  obtain ⟨t, rfl⟩ := hSB
  obtain ⟨u, hu⟩ := eq_add_smul_of_mem_line hRline
  obtain ⟨v, hv⟩ := eq_add_smul_of_mem_line hSline
  obtain ⟨⟨aK, hKB⟩, ⟨bK, hKC⟩⟩ := sub_eq_smul_of_mem_openSegment hK
  obtain ⟨⟨aL, hLC⟩, ⟨bL, hLA⟩⟩ := sub_eq_smul_of_mem_openSegment hL
  obtain ⟨⟨aM, hMA⟩, ⟨bM, hMB⟩⟩ := sub_eq_smul_of_mem_openSegment hM
  -- self inner products
  have hkk : ⟪K - I, K - I⟫ = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hIK]
  have hll : ⟪L - I, L - I⟫ = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hIL]
  have hmm : ⟪M - I, M - I⟫ = r ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm, hIM]
  have hknz : K - I ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hkk; nlinarith
  have hlnz : L - I ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hll; nlinarith
  have hmnz : M - I ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hmm; nlinarith
  -- the reversed tangency conditions
  have hKt' : ⟪K - I, B - C⟫ = 0 := by
    rw [show B - C = -(C - B) by abel, inner_neg_right, hKt, neg_zero]
  have hLt' : ⟪L - I, C - A⟫ = 0 := by
    rw [show C - A = -(A - C) by abel, inner_neg_right, hLt, neg_zero]
  have hMt' : ⟪M - I, A - B⟫ = 0 := by
    rw [show A - B = -(B - A) by abel, inner_neg_right, hMt, neg_zero]
  -- the six vertex-to-touch-point relations
  have hbk : ⟪B - I, K - I⟫ = r ^ 2 := inner_vertex_touch hIK hKt ⟨aK, hKB⟩
  have hck : ⟪C - I, K - I⟫ = r ^ 2 := inner_vertex_touch hIK hKt' ⟨bK, hKC⟩
  have hcl : ⟪C - I, L - I⟫ = r ^ 2 := inner_vertex_touch hIL hLt ⟨aL, hLC⟩
  have hal : ⟪A - I, L - I⟫ = r ^ 2 := inner_vertex_touch hIL hLt' ⟨bL, hLA⟩
  have ham : ⟪A - I, M - I⟫ = r ^ 2 := inner_vertex_touch hIM hMt ⟨aM, hMA⟩
  have hbm : ⟪B - I, M - I⟫ = r ^ 2 := inner_vertex_touch hIM hMt' ⟨bM, hMB⟩
  -- the touch points are pairwise distinct
  have hKM : K ≠ M := by
    intro h
    refine hABC (collinear_of_perp (n := K - I) hknz ?_ ?_)
    · rw [h]; exact hMt
    · rw [show C - A = (C - B) + (B - A) by abel, inner_add_right, hKt, h, hMt]; ring
  have hKL : K ≠ L := by
    intro h
    refine hABC (collinear_of_perp (n := K - I) hknz ?_ ?_)
    · rw [show B - A = -((C - B) + (A - C)) by abel, inner_neg_right, inner_add_right, hKt,
        h, hLt]; ring
    · rw [h]; exact hLt'
  have hLM : L ≠ M := by
    intro h
    refine hABC (collinear_of_perp (n := L - I) hlnz ?_ ?_)
    · rw [h]; exact hMt
    · exact hLt'
  -- the inner product bounds
  have hp : -r ^ 2 < ⟪K - I, M - I⟫ := neg_sq_lt_inner hr hkk hmm hbk hbm
  have hq : -r ^ 2 < ⟪K - I, L - I⟫ := neg_sq_lt_inner hr hkk hll hck hcl
  have hw : -r ^ 2 < ⟪L - I, M - I⟫ := neg_sq_lt_inner hr hll hmm hal ham
  have hp' : ⟪K - I, M - I⟫ < r ^ 2 :=
    inner_lt_sq hkk hmm (fun h => hKM (by simpa [sub_left_inj] using h))
  have hq' : ⟪K - I, L - I⟫ < r ^ 2 :=
    inner_lt_sq hkk hll (fun h => hKL (by simpa [sub_left_inj] using h))
  have hw' : ⟪L - I, M - I⟫ < r ^ 2 :=
    inner_lt_sq hll hmm (fun h => hLM (by simpa [sub_left_inj] using h))
  -- pass to coordinates
  rw [inner_sub_coord] at hbk hck hcl hal ham hbm hp hq hw hp' hq' hw' hkk hll hmm
  have hk2 : (K 0 - I 0) ^ 2 + (K 1 - I 1) ^ 2 = r ^ 2 := by linear_combination hkk
  have hl2 : (L 0 - I 0) ^ 2 + (L 1 - I 1) ^ 2 = r ^ 2 := by linear_combination hll
  have hm2 : (M 0 - I 0) ^ 2 + (M 1 - I 1) ^ 2 = r ^ 2 := by linear_combination hmm
  have hR0 : (B 0 - I 0) + s * ((K 0 - I 0) - (M 0 - I 0)) =
      (L 0 - I 0) + u * ((M 0 - I 0) - (L 0 - I 0)) := by
    have h := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hu) 0
    simp at h
    linear_combination h
  have hR1 : (B 1 - I 1) + s * ((K 1 - I 1) - (M 1 - I 1)) =
      (L 1 - I 1) + u * ((M 1 - I 1) - (L 1 - I 1)) := by
    have h := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hu) 1
    simp at h
    linear_combination h
  have hS0 : (B 0 - I 0) + t * ((K 0 - I 0) - (M 0 - I 0)) =
      (L 0 - I 0) + v * ((K 0 - I 0) - (L 0 - I 0)) := by
    have h := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hv) 0
    simp at h
    linear_combination h
  have hS1 : (B 1 - I 1) + t * ((K 1 - I 1) - (M 1 - I 1)) =
      (L 1 - I 1) + v * ((K 1 - I 1) - (L 1 - I 1)) := by
    have h := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hv) 1
    simp at h
    linear_combination h
  have hcore := coord_core r (K 0 - I 0) (K 1 - I 1) (L 0 - I 0) (L 1 - I 1)
    (M 0 - I 0) (M 1 - I 1) (B 0 - I 0) (B 1 - I 1) s t u v hk2 hl2 hm2
    (by linear_combination hbk) (by linear_combination hbm)
    (by linear_combination hp) (by linear_combination hq) (by linear_combination hw)
    (by linear_combination hp') (by linear_combination hq') (by linear_combination hw')
    hR0 hR1 hS0 hS1
  -- conclude
  have hang : EuclideanGeometry.angle (B + s • (K - M)) I (B + t • (K - M)) =
      InnerProductGeometry.angle ((B + s • (K - M)) - I) ((B + t • (K - M)) - I) := by
    simp [EuclideanGeometry.angle, vsub_eq_sub]
  rw [hang]
  refine angle_lt_pi_div_two_of_inner_pos ?_
  rw [inner_sub_coord]
  have hval : ((B + s • (K - M)) 0 - I 0) * ((B + t • (K - M)) 0 - I 0) +
      ((B + s • (K - M)) 1 - I 1) * ((B + t • (K - M)) 1 - I 1) = r ^ 2 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linear_combination hcore
  rw [hval]
  positivity

/-! ### The hypotheses are consistent

We exhibit an explicit configuration satisfying all the hypotheses of `imo1998_p5`:
the isosceles triangle `A = (0, 5/3)`, `B = (-2, -1)`, `C = (2, -1)`, whose incircle is the
unit circle centred at the origin, touching the sides at `K = (0, -1)`, `L = (4/5, 3/5)` and
`M = (-4/5, 3/5)`.  Here `R = (-14/5, 3/5)` and `S = (-1, -3)`. -/

theorem not_collinear_of_cross_ne_zero (A B C : EuclideanSpace ℝ (Fin 2))
    (h : (B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0) ≠ 0) :
    ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert A {B, C})] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨a, ha⟩ := hv B (by simp)
  obtain ⟨b, hb⟩ := hv C (by simp)
  apply h
  have ha0 := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) ha) 0
  have ha1 := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) ha) 1
  have hb0 := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hb) 0
  have hb1 := congrFun (congrArg (fun z => (z : EuclideanSpace ℝ (Fin 2)).ofLp) hb) 1
  simp [vadd_eq_add] at ha0 ha1 hb0 hb1
  rw [ha0, ha1, hb0, hb1]
  ring

example :
    EuclideanGeometry.angle (!₂[(-14/5 : ℝ), 3/5] : EuclideanSpace ℝ (Fin 2)) !₂[0, 0]
      !₂[-1, -3] < π / 2 := by
  refine imo1998_p5 !₂[0, 5/3] !₂[-2, -1] !₂[2, -1] !₂[0, 0] !₂[0, -1] !₂[4/5, 3/5]
    !₂[-4/5, 3/5] !₂[-14/5, 3/5] !₂[-1, -3] 1 one_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine not_collinear_of_cross_ne_zero _ _ _ ?_
    norm_num
  · rw [EuclideanSpace.dist_eq]; norm_num [Fin.sum_univ_two]
  · rw [EuclideanSpace.dist_eq]; norm_num [Fin.sum_univ_two]
  · rw [EuclideanSpace.dist_eq]; norm_num [Fin.sum_univ_two]
  · rw [openSegment_eq_image]
    refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
    ext i; fin_cases i <;> norm_num
  · rw [openSegment_eq_image]
    refine ⟨3/5, ⟨by norm_num, by norm_num⟩, ?_⟩
    ext i; fin_cases i <;> norm_num
  · rw [openSegment_eq_image]
    refine ⟨2/5, ⟨by norm_num, by norm_num⟩, ?_⟩
    ext i; fin_cases i <;> norm_num
  · simp [PiLp.inner_apply, Fin.sum_univ_two]
  · simp [PiLp.inner_apply, Fin.sum_univ_two]; norm_num
  · simp [PiLp.inner_apply, Fin.sum_univ_two]; norm_num
  · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨9/4, ?_⟩
    rw [AffineMap.lineMap_apply]
    ext i; fin_cases i <;> norm_num [vsub_eq_sub, vadd_eq_add]
  · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨9/4, ?_⟩
    rw [AffineMap.lineMap_apply]
    ext i; fin_cases i <;> norm_num [vsub_eq_sub, vadd_eq_add]
  · refine ⟨-1, ?_⟩
    ext i; fin_cases i <;> norm_num
  · refine ⟨5/4, ?_⟩
    ext i; fin_cases i <;> norm_num

end Imo1998P5
