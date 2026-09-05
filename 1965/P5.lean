import Mathlib

/-!
# IMO 1965, Problem 5

Consider the triangle `OAB` with acute angle `AOB`.  Through a point `M ≠ O`
perpendiculars are drawn to `OA` and `OB`, the feet of which are `P` and `Q`
respectively.  The point of intersection of the altitudes of the triangle `OPQ`
is `H`.  What is the locus of `H` if `M` is permitted to range over

* (a) the side `AB`,
* (b) the interior of the triangle `OAB`?

We work in coordinates: `O = (0,0)`, `A = (a,0)`, `B = (b,c)` with `a, b, c > 0`
(this is exactly the situation of an acute angle `AOB`, after choosing the
`x`-axis along `OA`).

The answers are:

* (a) the segment joining the point `(b, 0)` of the line `OA` and the point
  `(a*b/(b²+c²)) • B` of the line `OB`; moreover every such `H` satisfies the
  line equation `a*c*x + (b² + c² - a*b)*y = a*b*c`;
* (b) the interior of the triangle with vertices `O`, `(a*b/(b²+c²)) • B` and
  `(b, 0)`.
-/

namespace IMO1965P5

noncomputable section

/-- The Euclidean dot product on the coordinate plane `ℝ × ℝ`. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- The foot of the perpendicular dropped from `M` to the `x`-axis, i.e. to the
line `OA` with `O = (0,0)` and `A = (a, 0)`, `a ≠ 0`. -/
def footX (M : ℝ × ℝ) : ℝ × ℝ := (M.1, 0)

/-- The foot of the perpendicular dropped from `M` to the line `OB`
(with `O = (0,0)` and `B ≠ 0`). -/
def footLine (B M : ℝ × ℝ) : ℝ × ℝ := (dot M B / dot B B) • B

/-- `H` is the point of intersection of the altitudes (the orthocenter) of the
triangle `O P Q`: each of the three lines `OH`, `PH`, `QH` is perpendicular to
the opposite side. -/
def IsOrthocenter (O P Q H : ℝ × ℝ) : Prop :=
  dot (H - O) (P - Q) = 0 ∧ dot (H - P) (Q - O) = 0 ∧ dot (H - Q) (O - P) = 0

/-- The explicit formula for the orthocenter `H` of the triangle `OPQ`, as a
function of the point `M`, where `B = (b, c)`. -/
def Hpt (b c : ℝ) (M : ℝ × ℝ) : ℝ × ℝ :=
  (b * (M.1 * b + M.2 * c) / (b ^ 2 + c ^ 2), b * (M.1 * c - M.2 * b) / (b ^ 2 + c ^ 2))

/-- The "open triangle" with vertices `0`, `X`, `Y`: the set of strictly
positive convex combinations, i.e. the interior of the triangle `0 X Y` when
`X` and `Y` are linearly independent. -/
def openTriangle (X Y : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β < 1 ∧ p = α • X + β • Y}

/-! ### The feet of the perpendiculars are what they should be -/

/-- `footX M` lies on the line `OA`. -/
theorem footX_mem_line (a : ℝ) (ha : a ≠ 0) (M : ℝ × ℝ) :
    footX M = (M.1 / a) • (a, (0 : ℝ)) := by
  simp [footX, ha]

/-- `M - footX M` is perpendicular to `OA`. -/
theorem footX_perp (a : ℝ) (M : ℝ × ℝ) : dot (M - footX M) (a, (0 : ℝ)) = 0 := by
  simp [dot, footX]

/-- `footLine B M` lies on the line `OB`. -/
theorem footLine_mem_line (B M : ℝ × ℝ) : ∃ t : ℝ, footLine B M = t • B :=
  ⟨dot M B / dot B B, rfl⟩

/-- `M - footLine B M` is perpendicular to `OB`. -/
theorem footLine_perp (B M : ℝ × ℝ) (hB : B ≠ 0) : dot (M - footLine B M) B = 0 := by
  have hBB : B.1 ^ 2 + B.2 ^ 2 ≠ 0 := by
    intro h
    have h1 : B.1 = 0 := by nlinarith [sq_nonneg B.1, sq_nonneg B.2]
    have h2 : B.2 = 0 := by nlinarith [sq_nonneg B.1, sq_nonneg B.2]
    exact hB (by simp [Prod.ext_iff, h1, h2])
  have hBB' : B.1 * B.1 + B.2 * B.2 ≠ 0 := by
    intro h; exact hBB (by nlinarith)
  simp only [dot, footLine, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  field_simp
  ring

/-! ### The orthocenter of `OPQ` -/

/-- The point `Hpt b c M` is indeed the orthocenter of the triangle `O P Q`,
where `P = footX M` and `Q = footLine (b,c) M`. -/
theorem isOrthocenter_Hpt (b c : ℝ) (hd : b ^ 2 + c ^ 2 ≠ 0) (M : ℝ × ℝ) :
    IsOrthocenter 0 (footX M) (footLine (b, c) M) (Hpt b c M) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [dot, footX, footLine, Hpt, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, sub_zero, zero_sub, Prod.fst_neg, Prod.snd_neg, neg_zero]
    field_simp
    ring

/-- Uniqueness of the orthocenter: under the non-degeneracy assumptions `c ≠ 0`
(so `B` is not on the line `OA`), `M.1 ≠ 0` (so `P ≠ O`) and
`dot M (b,c) ≠ 0` (so `Q ≠ O`), the orthocenter of `O P Q` is `Hpt b c M`. -/
theorem eq_Hpt_of_isOrthocenter (b c : ℝ) (hc : c ≠ 0) (M H : ℝ × ℝ) (hM : M.1 ≠ 0)
    (hQ : dot M (b, c) ≠ 0) (h : IsOrthocenter 0 (footX M) (footLine (b, c) M) H) :
    H = Hpt b c M := by
  have hd : b ^ 2 + c ^ 2 ≠ 0 := by positivity
  have hQ' : M.1 * b + M.2 * c ≠ 0 := by simpa [dot] using hQ
  obtain ⟨h1, h2, -⟩ := h
  simp only [dot, footX, footLine, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, sub_zero, zero_sub] at h1 h2
  field_simp at h1 h2
  have e2 : b * H.1 + c * H.2 - b * M.1 = 0 := by
    have hz : (M.1 * b + M.2 * c) * (b * H.1 + c * H.2 - b * M.1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hQ'
    · exact h
  have e1 : (M.1 * c - M.2 * b) * H.1 - (M.1 * b + M.2 * c) * H.2 = 0 := by
    have hz : c * ((M.1 * c - M.2 * b) * H.1 - (M.1 * b + M.2 * c) * H.2) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hc
    · exact h
  have hx : H.1 * (b ^ 2 + c ^ 2) = b * (M.1 * b + M.2 * c) := by
    have key : M.1 * (H.1 * (b ^ 2 + c ^ 2) - b * (M.1 * b + M.2 * c)) = 0 := by
      linear_combination c * e1 + (M.1 * b + M.2 * c) * e2
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hM
    · linarith
  have hy : H.2 * (b ^ 2 + c ^ 2) = b * (M.1 * c - M.2 * b) := by
    have key : M.1 * (H.2 * (b ^ 2 + c ^ 2) - b * (M.1 * c - M.2 * b)) = 0 := by
      linear_combination (-b) * e1 + (M.1 * c - M.2 * b) * e2
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hM
    · linarith
  refine Prod.ext ?_ ?_ <;> simp only [Hpt] <;> field_simp <;> linarith

/-! ### The map `M ↦ H` is linear -/

theorem Hpt_add_smul (b c : ℝ) (α β : ℝ) (M N : ℝ × ℝ) :
    Hpt b c (α • M + β • N) = α • Hpt b c M + β • Hpt b c N := by
  simp only [Hpt, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  constructor <;> ring

/-- The image of the vertex `A = (a, 0)`: a point of the ray `OB`. -/
theorem Hpt_A (a b c : ℝ) : Hpt b c (a, 0) = (a * b / (b ^ 2 + c ^ 2)) • (b, c) := by
  simp only [Hpt, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

/-- The image of the vertex `B = (b, c)`: the point `(b, 0)` of the ray `OA`. -/
theorem Hpt_B (b c : ℝ) (hd : b ^ 2 + c ^ 2 ≠ 0) : Hpt b c (b, c) = (b, 0) := by
  simp only [Hpt, Prod.ext_iff]
  refine ⟨?_, ?_⟩ <;> field_simp
  ring

/-! ### (a) `M` ranges over the side `AB` -/

/-- Every `H` obtained from a point `M` of the line `AB` lies on the line
`a*c*x + (b² + c² - a*b)*y = a*b*c`. -/
theorem line_equation (a b c : ℝ) (hd : b ^ 2 + c ^ 2 ≠ 0) (t : ℝ)
    (M : ℝ × ℝ) (hM : M = (1 - t) • (a, (0 : ℝ)) + t • (b, c)) :
    a * c * (Hpt b c M).1 + (b ^ 2 + c ^ 2 - a * b) * (Hpt b c M).2 = a * b * c := by
  subst hM
  simp only [Hpt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  field_simp
  ring

/-- **Answer to (a).**  As `M` ranges over the side `AB`, the orthocenter `H`
ranges over the segment joining the point `(a*b/(b²+c²)) • B` of the line `OB`
to the point `(b, 0)` of the line `OA`. -/
theorem locus_side (a b c : ℝ) (hd : b ^ 2 + c ^ 2 ≠ 0) :
    Hpt b c '' (segment ℝ (a, 0) (b, c)) =
      segment ℝ ((a * b / (b ^ 2 + c ^ 2)) • (b, c)) (b, 0) := by
  ext p
  constructor
  · rintro ⟨M, ⟨α, β, hα, hβ, hαβ, rfl⟩, rfl⟩
    exact ⟨α, β, hα, hβ, hαβ, by rw [Hpt_add_smul, Hpt_A, Hpt_B b c hd]⟩
  · rintro ⟨α, β, hα, hβ, hαβ, rfl⟩
    exact ⟨α • (a, 0) + β • (b, c), ⟨α, β, hα, hβ, hαβ, rfl⟩, by
      rw [Hpt_add_smul, Hpt_A, Hpt_B b c hd]⟩

/-- The endpoint `(b, 0)` of the locus lies on the ray `OA` (and on the segment
`OA` exactly when `b ≤ a`). -/
theorem endpoint_on_OA (a b : ℝ) (ha : a ≠ 0) : ((b : ℝ), (0 : ℝ)) = (b / a) • (a, (0 : ℝ)) := by
  simp [ha]

/-! ### (b) `M` ranges over the interior of the triangle `OAB` -/

/-- **Answer to (b).**  As `M` ranges over the interior of the triangle `OAB`,
the orthocenter `H` ranges over the interior of the triangle with vertices `O`,
`(a*b/(b²+c²)) • B` (on `OB`) and `(b, 0)` (on `OA`). -/
theorem locus_interior (a b c : ℝ) (hd : b ^ 2 + c ^ 2 ≠ 0) :
    Hpt b c '' (openTriangle (a, 0) (b, c)) =
      openTriangle ((a * b / (b ^ 2 + c ^ 2)) • (b, c)) (b, 0) := by
  ext p
  constructor
  · rintro ⟨M, ⟨α, β, hα, hβ, hαβ, rfl⟩, rfl⟩
    exact ⟨α, β, hα, hβ, hαβ, by rw [Hpt_add_smul, Hpt_A, Hpt_B b c hd]⟩
  · rintro ⟨α, β, hα, hβ, hαβ, rfl⟩
    exact ⟨α • (a, 0) + β • (b, c), ⟨α, β, hα, hβ, hαβ, rfl⟩, by
      rw [Hpt_add_smul, Hpt_A, Hpt_B b c hd]⟩

/-! ### The full statement of the locus -/

/-- Non-degeneracy: for a point `M = α • A + β • B` with `α, β ≥ 0` not both
zero (and `a, b, c > 0`), the feet `P` and `Q` are both different from `O`. -/
theorem nondegenerate (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (M : ℝ × ℝ)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : 0 < α + β)
    (hM : M = α • (a, (0 : ℝ)) + β • (b, c)) : 0 < M.1 ∧ 0 < dot M (b, c) := by
  subst hM
  have h1 : 0 < α * a + β * b := by
    rcases lt_or_ge 0 α with h | h
    · nlinarith
    · have : 0 < β := by linarith
      nlinarith
  refine ⟨by simpa using h1, ?_⟩
  have h2 : 0 ≤ β * c := by positivity
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_zero, zero_add]
  nlinarith

/-- **The locus, part (a).**  For a triangle `OAB` with `O = (0,0)`, `A = (a,0)`,
`B = (b,c)` and `a, b, c > 0` (an acute angle at `O`), the set of orthocenters
`H` of the triangles `OPQ`, as `M` ranges over the side `AB`, is exactly the
segment joining `(a*b/(b²+c²)) • B ∈ OB` and `(b, 0) ∈ OA`. -/
theorem locus_of_side (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    {H : ℝ × ℝ | ∃ M ∈ segment ℝ ((a : ℝ), (0 : ℝ)) (b, c),
        IsOrthocenter 0 (footX M) (footLine (b, c) M) H} =
      segment ℝ ((a * b / (b ^ 2 + c ^ 2)) • (b, c)) (b, 0) := by
  have hd : b ^ 2 + c ^ 2 ≠ 0 := by positivity
  rw [← locus_side a b c hd]
  ext H
  constructor
  · rintro ⟨M, hMseg, hH⟩
    obtain ⟨α, β, hα, hβ, hαβ, hM⟩ := hMseg
    obtain ⟨hM1, hMQ⟩ := nondegenerate a b c ha hb hc M α β hα hβ (by linarith) hM.symm
    exact ⟨M, ⟨α, β, hα, hβ, hαβ, hM⟩,
      (eq_Hpt_of_isOrthocenter b c hc.ne' M H hM1.ne' hMQ.ne' hH).symm⟩
  · rintro ⟨M, hMseg, rfl⟩
    exact ⟨M, hMseg, isOrthocenter_Hpt b c hd M⟩

/-- **The locus, part (b).**  With the same conventions, the set of orthocenters
`H`, as `M` ranges over the interior of the triangle `OAB`, is exactly the
interior of the triangle with vertices `O`, `(a*b/(b²+c²)) • B ∈ OB` and
`(b, 0) ∈ OA`. -/
theorem locus_of_interior (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    {H : ℝ × ℝ | ∃ M ∈ openTriangle ((a : ℝ), (0 : ℝ)) (b, c),
        IsOrthocenter 0 (footX M) (footLine (b, c) M) H} =
      openTriangle ((a * b / (b ^ 2 + c ^ 2)) • (b, c)) (b, 0) := by
  have hd : b ^ 2 + c ^ 2 ≠ 0 := by positivity
  rw [← locus_interior a b c hd]
  ext H
  constructor
  · rintro ⟨M, hMint, hH⟩
    obtain ⟨α, β, hα, hβ, hαβ, hM⟩ := hMint
    obtain ⟨hM1, hMQ⟩ :=
      nondegenerate a b c ha hb hc M α β hα.le hβ.le (by linarith) hM
    exact ⟨M, ⟨α, β, hα, hβ, hαβ, hM⟩,
      (eq_Hpt_of_isOrthocenter b c hc.ne' M H hM1.ne' hMQ.ne' hH).symm⟩
  · rintro ⟨M, hMint, rfl⟩
    exact ⟨M, hMint, isOrthocenter_Hpt b c hd M⟩

/-- Every orthocenter arising from a point `M` of the side `AB` lies on the line
`a*c*x + (b² + c² - a*b)*y = a*b*c`. -/
theorem locus_line_equation (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (M : ℝ × ℝ) (hMseg : M ∈ segment ℝ ((a : ℝ), (0 : ℝ)) (b, c)) (H : ℝ × ℝ)
    (hH : IsOrthocenter 0 (footX M) (footLine (b, c) M) H) :
    a * c * H.1 + (b ^ 2 + c ^ 2 - a * b) * H.2 = a * b * c := by
  have hd : b ^ 2 + c ^ 2 ≠ 0 := by positivity
  obtain ⟨α, β, hα, hβ, hαβ, hM⟩ := hMseg
  obtain ⟨hM1, hMQ⟩ := nondegenerate a b c ha hb hc M α β hα hβ (by linarith) hM.symm
  rw [eq_Hpt_of_isOrthocenter b c hc.ne' M H hM1.ne' hMQ.ne' hH]
  refine line_equation a b c hd β M ?_
  rw [← hM]
  have hα1 : α = 1 - β := by linarith
  rw [hα1]

end

end IMO1965P5
