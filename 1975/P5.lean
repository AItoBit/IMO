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

set_option grind.warning false

/-!
# IMO 1975 Problem 5

Determine, with proof, whether or not one can find `1975` points on the circumference of a
circle with unit radius such that the distance between any two of them is a rational number.

The answer is **yes**.  We use the classical construction: let `z = (3 + 4i)/5`, a point of the
unit circle which is not a root of unity, and take the points `z ^ (2 * k)` for `k < 1975`.
The distance between `z ^ (2 * j)` and `z ^ (2 * k)` equals `2 * |Im (z ^ (j - k))|`, which is
rational.
-/

namespace IMO1975P5

/-- The Gaussian integer `(3 + 4i)^n`, recorded as the pair of its real and imaginary parts. -/
def gp : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | (n + 1) => (3 * (gp n).1 - 4 * (gp n).2, 4 * (gp n).1 + 3 * (gp n).2)

@[simp] lemma gp_zero : gp 0 = (1, 0) := rfl

lemma gp_succ (n : ℕ) :
    gp (n + 1) = (3 * (gp n).1 - 4 * (gp n).2, 4 * (gp n).1 + 3 * (gp n).2) := rfl

/-- `(3 + 4i)^n` really is `gp n`. -/
lemma gp_cast (n : ℕ) :
    ((gp n).1 : ℂ) + ((gp n).2 : ℂ) * Complex.I = (3 + 4 * Complex.I) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← ih, gp_succ]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring

/-- For `n ≥ 1`, modulo `5` the real part of `(3+4i)^n` is `3` and its imaginary part is `4`. -/
lemma gp_mod_five (n : ℕ) : (gp (n + 1)).1 % 5 = 3 ∧ (gp (n + 1)).2 % 5 = 4 := by
  induction n with
  | zero => decide
  | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [gp_succ]
      refine ⟨?_, ?_⟩ <;> simp only <;> omega

/-- The base point of the construction: a point of the unit circle with rational coordinates. -/
noncomputable def z : ℂ := (3 + 4 * Complex.I) / 5

lemma z_norm : ‖z‖ = 1 := by
  have h : ‖(3 : ℂ) + 4 * Complex.I‖ = 5 := by
    simp [Complex.norm_def, Complex.normSq_apply]
    norm_num
  rw [z, norm_div, h]
  norm_num

lemma z_ne_zero : z ≠ 0 := by
  intro h
  have h1 := z_norm
  rw [h] at h1
  simp at h1

lemma z_pow (n : ℕ) : z ^ n = (((gp n).1 : ℂ) + ((gp n).2 : ℂ) * Complex.I) / 5 ^ n := by
  rw [gp_cast, z, div_pow]

lemma z_pow_norm (n : ℕ) : ‖z ^ n‖ = 1 := by
  rw [norm_pow, z_norm, one_pow]

lemma z_pow_im (n : ℕ) : (z ^ n).im = ((gp n).2 : ℝ) / 5 ^ n := by
  rw [z_pow]
  have h5 : ((5 : ℂ) ^ n) = ((5 ^ n : ℝ) : ℂ) := by push_cast; ring
  rw [h5, Complex.div_ofReal_im]
  simp

/-- The base point is not a root of unity. -/
lemma z_pow_ne_one {n : ℕ} (hn : n ≠ 0) : z ^ n ≠ 1 := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [z_pow] at h
  have h5 : ((5 : ℂ) ^ (m + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_eq_one_iff_eq h5] at h
  have hRim : ((5 : ℂ) ^ (m + 1)).im = 0 := by
    rw [show ((5 : ℂ) ^ (m + 1)) = ((5 ^ (m + 1) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_im _
  have him : ((gp (m + 1)).2 : ℝ) = 0 := by
    have h2 := congrArg Complex.im h
    rw [hRim] at h2
    simpa using h2
  have hz : (gp (m + 1)).2 = 0 := by exact_mod_cast him
  have h2 := (gp_mod_five m).2
  omega

/-- The points of the construction. -/
noncomputable def pt (k : ℕ) : ℂ := z ^ (2 * k)

lemma pt_norm (k : ℕ) : ‖pt k‖ = 1 := z_pow_norm _

lemma pt_injective : Function.Injective pt := by
  have key : ∀ j k : ℕ, k ≤ j → pt j = pt k → j = k := by
    intro j k hkj h
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
    have hm : m ≠ 0 := by omega
    have hz : z ^ (2 * (k + m)) = z ^ (2 * k) * z ^ (2 * m) := by
      rw [← pow_add]; ring_nf
    rw [pt, pt, hz] at h
    have hzk : z ^ (2 * k) ≠ 0 := pow_ne_zero _ z_ne_zero
    have h' : z ^ (2 * k) * z ^ (2 * m) = z ^ (2 * k) * 1 := by rw [mul_one]; exact h
    have hone : z ^ (2 * m) = 1 := mul_left_cancel₀ hzk h'
    exact z_pow_ne_one (by omega) hone
  intro j k h
  rcases le_total k j with hkj | hjk
  · exact key j k hkj h
  · exact (key k j hjk h.symm).symm

/-- The key computation: `‖u ^ 2 - 1‖ = 2 * |Im u|` for `u` on the unit circle. -/
lemma norm_sq_sub_one {u : ℂ} (hu : ‖u‖ = 1) : ‖u ^ 2 - 1‖ = 2 * |u.im| := by
  have hns : Complex.normSq u = 1 := by simp [Complex.normSq_eq_norm_sq, hu]
  have hconj : (starRingEnd ℂ) u = u⁻¹ := by
    rw [Complex.inv_def, hns]
    simp
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h1 : u ^ 2 - 1 = u * (u - (starRingEnd ℂ) u) := by
    rw [hconj]
    field_simp
  have h2 : u - (starRingEnd ℂ) u = ((2 * u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [two_mul]
  rw [h1, h2, norm_mul, hu, one_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

lemma dist_pt_rat (j k : ℕ) : ∃ q : ℚ, dist (pt j) (pt k) = (q : ℝ) := by
  have key : ∀ a b : ℕ, b ≤ a → ∃ q : ℚ, dist (pt a) (pt b) = (q : ℝ) := by
    intro a b hba
    obtain ⟨m, rfl⟩ : ∃ m, a = b + m := ⟨a - b, by omega⟩
    refine ⟨2 * |((gp m).2 : ℚ)| / 5 ^ m, ?_⟩
    have hsplit : pt (b + m) - pt b = z ^ (2 * b) * ((z ^ m) ^ 2 - 1) := by
      rw [pt, pt, ← pow_mul, show 2 * (b + m) = 2 * b + m * 2 by ring, pow_add]
      ring
    rw [Complex.dist_eq, hsplit, norm_mul, z_pow_norm, one_mul,
      norm_sq_sub_one (z_pow_norm m), z_pow_im, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < 5 ^ m)]
    push_cast
    ring
  rcases le_total k j with h | h
  · exact key j k h
  · obtain ⟨q, hq⟩ := key k j h
    exact ⟨q, by rw [dist_comm]; exact hq⟩

/-- **Yes**: for every `n` there are `n` points on the unit circle whose pairwise distances
are all rational. -/
theorem exists_points_unit_circle_rat_dist (n : ℕ) :
    ∃ S : Finset ℂ, S.card = n ∧ (∀ w ∈ S, ‖w‖ = 1) ∧
      ∀ w ∈ S, ∀ v ∈ S, ∃ q : ℚ, dist w v = (q : ℝ) := by
  refine ⟨(Finset.range n).image pt, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ pt_injective, Finset.card_range]
  · intro w hw
    simp only [Finset.mem_image] at hw
    obtain ⟨k, -, rfl⟩ := hw
    exact pt_norm k
  · intro w hw v hv
    simp only [Finset.mem_image] at hw hv
    obtain ⟨j, -, rfl⟩ := hw
    obtain ⟨k, -, rfl⟩ := hv
    exact dist_pt_rat j k

/-- **IMO 1975, Problem 5.**  One *can* find `1975` points on the circumference of a circle of
unit radius such that the distance between any two of them is a rational number. -/
theorem imo1975_p5 :
    ∃ S : Finset ℂ, S.card = 1975 ∧ (∀ w ∈ S, ‖w‖ = 1) ∧
      ∀ w ∈ S, ∀ v ∈ S, ∃ q : ℚ, dist w v = (q : ℝ) :=
  exists_points_unit_circle_rat_dist 1975

end IMO1975P5
