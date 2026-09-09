import Mathlib

/-!
# IMO 1981, Problem 1

`P` is a point inside a given triangle `ABC`, and `D`, `E`, `F` are the feet of the
perpendiculars from `P` to the lines `BC`, `CA`, `AB` respectively.  Find all `P` for which

  `BC / PD + CA / PE + AB / PF`

is least.

The answer is: the expression is minimised exactly when `P` is the incenter of the triangle,
i.e. when `(a + b + c) • P = a • A + b • B + c • C` with `a = BC`, `b = CA`, `c = AB`
(equivalently, exactly when `PD = PE = PF`), and the minimal value is `(a+b+c)^2 / (2 * area)`.

The formalisation works in an arbitrary real inner product space; the "doubled area" of a
triangle `A B C` is defined through the Gram determinant of the two edge vectors,
`areaDoubled A B C = √(‖B-A‖²‖C-A‖² - ⟪B-A, C-A⟫²)`, which is the usual `2 · area`.
-/

namespace Imo1981P1

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gram determinant of two vectors, `‖u‖²‖v‖² - ⟪u, v⟫²`. -/
noncomputable def gram (u v : V) : ℝ := ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2

/-- Twice the area of the triangle with vertices `A`, `B`, `C`. -/
noncomputable def areaDoubled (A B C : V) : ℝ := Real.sqrt (gram (B - A) (C - A))

/-! ### Basic properties of the Gram determinant -/

lemma gram_nonneg (u v : V) : 0 ≤ gram u v := by
  have h := real_inner_mul_inner_self_le u v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  simp only [gram]
  nlinarith [h]

lemma gram_comm (u v : V) : gram u v = gram v u := by
  simp [gram, real_inner_comm u v]; ring

/-- The Gram determinant transforms by the square of the determinant of a linear change of
coordinates. -/
lemma gram_smul_comb (x₁ y₁ x₂ y₂ : ℝ) (u v : V) :
    gram (x₁ • u + y₁ • v) (x₂ • u + y₂ • v) = (x₁ * y₂ - x₂ * y₁) ^ 2 * gram u v := by
  simp only [gram, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v u]
  ring

lemma gram_self (u : V) : gram u u = 0 := by
  simp only [gram, ← real_inner_self_eq_norm_sq]; ring

lemma areaDoubled_nonneg (A B C : V) : 0 ≤ areaDoubled A B C := Real.sqrt_nonneg _

/-- Sanity check: the right triangle with legs of length one has doubled area `1`. -/
example : areaDoubled (0 : EuclideanSpace ℝ (Fin 2)) !₂[1, 0] !₂[0, 1] = 1 := by
  simp [areaDoubled, gram, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    EuclideanSpace.inner_eq_star_dotProduct]

/-- `areaDoubled` is invariant under cyclic rotation of the vertices. -/
lemma areaDoubled_rotate (A B C : V) : areaDoubled A B C = areaDoubled B C A := by
  have h : gram (C - B) (A - B) = gram (B - A) (C - A) := by
    have h1 : C - B = (-1 : ℝ) • (B - A) + (1 : ℝ) • (C - A) := by module
    have h2 : A - B = (-1 : ℝ) • (B - A) + (0 : ℝ) • (C - A) := by module
    rw [h1, h2, gram_smul_comb]
    norm_num
  simp [areaDoubled, h]

/-- `areaDoubled` is invariant under swapping the last two vertices. -/
lemma areaDoubled_swap (A B C : V) : areaDoubled A B C = areaDoubled A C B := by
  simp [areaDoubled, gram_comm]

/-! ### Nondegeneracy -/

/-- If two vectors have vanishing Gram determinant and the first is nonzero, the second is a
multiple of the first. -/
lemma exists_smul_of_gram_eq_zero {u v : V} (hu : u ≠ 0) (h : gram u v = 0) :
    ∃ r : ℝ, v = r • u := by
  refine ⟨⟪u, v⟫ / ‖u‖ ^ 2, ?_⟩
  have hu2 : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  have h' : ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 = 0 := h
  have e1 : ‖(‖u‖ ^ 2) • v‖ ^ 2 = (‖u‖ ^ 2) ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow]
  have e2 : ‖⟪u, v⟫ • u‖ ^ 2 = ⟪u, v⟫ ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow, sq_abs]
  have e3 : ⟪(‖u‖ ^ 2) • v, ⟪u, v⟫ • u⟫ = ‖u‖ ^ 2 * ⟪u, v⟫ * ⟪v, u⟫ := by
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  have key : ‖(‖u‖ ^ 2) • v - ⟪u, v⟫ • u‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, e1, e2, e3, real_inner_comm u v]
    linear_combination (‖u‖ ^ 2) * h'
  have hzero : (‖u‖ ^ 2) • v - ⟪u, v⟫ • u = 0 :=
    norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp key)
  rw [sub_eq_zero] at hzero
  rw [eq_comm, div_eq_inv_mul, mul_smul, ← hzero, smul_smul, inv_mul_cancel₀ (ne_of_gt hu2),
    one_smul]

/-- For a nondegenerate triangle, the Gram determinant of the edge vectors is positive. -/
lemma gram_pos_of_not_collinear {A B C : V} (h : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    0 < gram (B - A) (C - A) := by
  rcases lt_or_eq_of_le (gram_nonneg (B - A) (C - A)) with hlt | heq
  · exact hlt
  · exfalso
    apply h
    by_cases hu : B - A = 0
    · have hBA : B = A := by rwa [sub_eq_zero] at hu
      subst hBA
      simpa [Set.insert_comm, Set.insert_eq_self] using collinear_pair ℝ B C
    · obtain ⟨r, hr⟩ := exists_smul_of_gram_eq_zero hu heq.symm
      rw [collinear_iff_of_mem (Set.mem_insert A {B, C})]
      refine ⟨B - A, ?_⟩
      rintro p (rfl | rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨r, by rw [← hr]; simp⟩

lemma gram_pos_ne {u v : V} (h : 0 < gram u v) : u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; simp [gram] at h
  · rintro rfl; simp [gram] at h
  · rintro rfl; rw [gram_self] at h; exact lt_irrefl _ h

/-- Barycentric coordinates are unique in a nondegenerate triangle. -/
lemma eq_zero_of_gram_pos {u v : V} (h : 0 < gram u v) {X Y : ℝ} (hw : X • u + Y • v = 0) :
    X = 0 ∧ Y = 0 := by
  have h1 : ⟪X • u + Y • v, u⟫ = 0 := by rw [hw]; simp
  have h2 : ⟪X • u + Y • v, v⟫ = 0 := by rw [hw]; simp
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h1 h2
  rw [real_inner_comm u v] at h1
  -- h1 : X * ‖u‖² + Y * ⟪u,v⟫ = 0, h2 : X * ⟪u,v⟫ + Y * ‖v‖² = 0
  have hg : ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 > 0 := h
  constructor
  · have hX : X * (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) = 0 := by
      linear_combination ‖v‖ ^ 2 * h1 - ⟪u, v⟫ * h2
    exact (mul_eq_zero.mp hX).resolve_right (ne_of_gt hg)
  · have hY : Y * (‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2) = 0 := by
      linear_combination ‖u‖ ^ 2 * h2 - ⟪u, v⟫ * h1
    exact (mul_eq_zero.mp hY).resolve_right (ne_of_gt hg)

/-! ### The foot of a perpendicular -/

/-- If `u - t • v` is orthogonal to `v`, then the Gram determinant of `u` and `v` factors. -/
lemma gram_eq_of_perp (u v : V) (t : ℝ) (h : ⟪u - t • v, v⟫ = 0) :
    gram u v = ‖u - t • v‖ ^ 2 * ‖v‖ ^ 2 := by
  simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, sub_eq_zero] at h
  rw [norm_sub_sq_real]
  simp only [norm_smul, real_inner_smul_right, Real.norm_eq_abs, gram, mul_pow, sq_abs]
  rw [h]; ring

/-- The distance from a point to the foot of the perpendicular on a line, multiplied by the
length of the segment defining the line, equals twice the area of the corresponding triangle. -/
lemma dist_foot_mul (P B C D : V) (hD : D ∈ line[ℝ, B, C]) (hperp : ⟪P - D, C - B⟫ = 0) :
    dist P D * dist B C = areaDoubled B P C := by
  obtain ⟨t, rfl⟩ : ∃ t : ℝ, D = B + t • (C - B) := by
    have h2 : (D - B) +ᵥ B ∈ line[ℝ, B, C] := by simpa using hD
    obtain ⟨r, hr⟩ := (vadd_left_mem_affineSpan_pair (k := ℝ)).mp h2
    simp only [vsub_eq_sub] at hr
    exact ⟨r, by rw [hr]; abel⟩
  have hPD : P - (B + t • (C - B)) = (P - B) - t • (C - B) := by abel
  have hkey : gram (P - B) (C - B) = ‖(P - B) - t • (C - B)‖ ^ 2 * ‖C - B‖ ^ 2 :=
    gram_eq_of_perp _ _ t (by rw [← hPD]; exact hperp)
  have hd1 : dist P (B + t • (C - B)) = ‖(P - B) - t • (C - B)‖ := by
    rw [dist_eq_norm, hPD]
  have hd2 : dist B C = ‖C - B‖ := by rw [dist_comm, dist_eq_norm]
  rw [areaDoubled, hd1, hd2, hkey, ← mul_pow, Real.sqrt_sq (by positivity)]

/-! ### The area decomposition -/

/-- Twice the area of the triangle `P B C` where `P = α A + β B + γ C` is an affine
combination. -/
lemma areaDoubled_comb (A B C : V) {α β γ : ℝ} (hs : α + β + γ = 1) (hα : 0 ≤ α) :
    areaDoubled (α • A + β • B + γ • C) B C = α * areaDoubled A B C := by
  have hβ : β = 1 - α - γ := by linarith
  subst hβ
  have h1 : B - (α • A + (1 - α - γ) • B + γ • C) = (α + γ) • (B - A) + (-γ) • (C - A) := by
    module
  have h2 : C - (α • A + (1 - α - γ) • B + γ • C) = (-(1 - α - γ)) • (B - A)
      + (α + (1 - α - γ)) • (C - A) := by module
  rw [areaDoubled, areaDoubled, h1, h2, gram_smul_comb]
  have hdet : ((α + γ) * (α + (1 - α - γ)) - (-(1 - α - γ)) * (-γ)) = α := by ring
  rw [hdet, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα]

/-! ### The optimisation lemma -/

lemma min_lemma {a b c x y z T : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : a * x + b * y + c * z = T) :
    (a + b + c) ^ 2 / T ≤ a / x + b / y + c / z ∧
      (a / x + b / y + c / z = (a + b + c) ^ 2 / T ↔ x = y ∧ y = z) := by
  have hT : 0 < T := by rw [← h]; positivity
  have key : (a / x + b / y + c / z) * T - (a + b + c) ^ 2 =
      a * b * (x - y) ^ 2 / (x * y) + b * c * (y - z) ^ 2 / (y * z)
        + a * c * (x - z) ^ 2 / (x * z) := by
    rw [← h]; field_simp; ring
  have hnn : 0 ≤ a * b * (x - y) ^ 2 / (x * y) + b * c * (y - z) ^ 2 / (y * z)
      + a * c * (x - z) ^ 2 / (x * z) := by positivity
  have hge : (a + b + c) ^ 2 ≤ (a / x + b / y + c / z) * T := by linarith
  refine ⟨(div_le_iff₀ hT).2 hge, ?_⟩
  constructor
  · intro heq
    have h0 : (a / x + b / y + c / z) * T - (a + b + c) ^ 2 = 0 := by
      rw [heq, div_mul_cancel₀ _ (ne_of_gt hT)]; ring
    rw [key] at h0
    have t1 : 0 ≤ a * b * (x - y) ^ 2 / (x * y) := by positivity
    have t2 : 0 ≤ b * c * (y - z) ^ 2 / (y * z) := by positivity
    have t3 : 0 ≤ a * c * (x - z) ^ 2 / (x * z) := by positivity
    have e1 : a * b * (x - y) ^ 2 / (x * y) = 0 := by linarith
    have e2 : b * c * (y - z) ^ 2 / (y * z) = 0 := by linarith
    constructor
    · have := (div_eq_zero_iff.mp e1).resolve_right (by positivity)
      have hxy : (x - y) ^ 2 = 0 := by
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' (by positivity)
        · exact h'
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hxy
      linarith
    · have := (div_eq_zero_iff.mp e2).resolve_right (by positivity)
      have hyz : (y - z) ^ 2 = 0 := by
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' (by positivity)
        · exact h'
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hyz
      linarith
  · rintro ⟨rfl, rfl⟩
    rw [← h]
    field_simp

/-! ### The main theorem -/

/-- **IMO 1981, Problem 1.**  Let `P` be a point inside the triangle `ABC` (given by strictly
positive barycentric coordinates `α, β, γ`), and let `D`, `E`, `F` be the feet of the
perpendiculars from `P` to the lines `BC`, `CA`, `AB`.  Then

  `BC/PD + CA/PE + AB/PF ≥ (BC + CA + AB)² / (2·area ABC)`,

with equality if and only if `P` is the incenter of the triangle, i.e.
`(a + b + c) • P = a • A + b • B + c • C` with `a = BC`, `b = CA`, `c = AB`; equivalently,
if and only if `PD = PE = PF`. -/
theorem imo1981_p1 {A B C P D E F : V}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set V))
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = 1)
    (hP : P = α • A + β • B + γ • C)
    (hD : D ∈ line[ℝ, B, C]) (hD' : ⟪P - D, C - B⟫ = 0)
    (hE : E ∈ line[ℝ, C, A]) (hE' : ⟪P - E, A - C⟫ = 0)
    (hF : F ∈ line[ℝ, A, B]) (hF' : ⟪P - F, B - A⟫ = 0) :
    (dist B C + dist C A + dist A B) ^ 2 / areaDoubled A B C
        ≤ dist B C / dist P D + dist C A / dist P E + dist A B / dist P F ∧
      (dist B C / dist P D + dist C A / dist P E + dist A B / dist P F
          = (dist B C + dist C A + dist A B) ^ 2 / areaDoubled A B C ↔
        (dist B C + dist C A + dist A B) • P = dist B C • A + dist C A • B + dist A B • C) ∧
      (dist B C / dist P D + dist C A / dist P E + dist A B / dist P F
          = (dist B C + dist C A + dist A B) ^ 2 / areaDoubled A B C ↔
        dist P D = dist P E ∧ dist P E = dist P F) := by
  have hgram : 0 < gram (B - A) (C - A) := gram_pos_of_not_collinear hABC
  obtain ⟨hu0, hv0, huv⟩ := gram_pos_ne hgram
  have hT : 0 < areaDoubled A B C := Real.sqrt_pos.mpr hgram
  have hapos : 0 < dist B C := dist_pos.mpr (fun h => huv (by rw [h]))
  have hbpos : 0 < dist C A := dist_pos.mpr (fun h => hv0 (by rw [h]; simp))
  have hcpos : 0 < dist A B := dist_pos.mpr (fun h => hu0 (by rw [← h]; simp))
  -- the three "area" identities
  have hx : dist P D * dist B C = α * areaDoubled A B C := by
    rw [dist_foot_mul P B C D hD hD', areaDoubled_rotate B P C, areaDoubled_swap P C B, hP,
      areaDoubled_comb A B C hsum hα.le]
  have hy : dist P E * dist C A = β * areaDoubled A B C := by
    have h1 := dist_foot_mul P C A E hE hE'
    rw [areaDoubled_rotate C P A, areaDoubled_swap P A C] at h1
    have hPcomb : P = β • B + γ • C + α • A := by rw [hP]; module
    have h2 : areaDoubled P C A = β * areaDoubled B C A := by
      rw [hPcomb, areaDoubled_comb B C A (by linarith) hβ.le]
    rw [h1, h2, areaDoubled_rotate A B C]
  have hz : dist P F * dist A B = γ * areaDoubled A B C := by
    have h1 := dist_foot_mul P A B F hF hF'
    rw [areaDoubled_rotate A P B, areaDoubled_swap P B A] at h1
    have hPcomb : P = γ • C + α • A + β • B := by rw [hP]; module
    have h2 : areaDoubled P A B = γ * areaDoubled C A B := by
      rw [hPcomb, areaDoubled_comb C A B (by linarith) hγ.le]
    rw [h1, h2, areaDoubled_rotate A B C, areaDoubled_rotate B C A]
  have hxpos : 0 < dist P D := by
    nlinarith [dist_nonneg (x := P) (y := D), mul_pos hα hT]
  have hypos : 0 < dist P E := by
    nlinarith [dist_nonneg (x := P) (y := E), mul_pos hβ hT]
  have hzpos : 0 < dist P F := by
    nlinarith [dist_nonneg (x := P) (y := F), mul_pos hγ hT]
  have hsum2 : dist B C * dist P D + dist C A * dist P E + dist A B * dist P F
      = areaDoubled A B C := by
    linear_combination hx + hy + hz + areaDoubled A B C * hsum
  obtain ⟨hle, hiff⟩ := min_lemma hapos hbpos hcpos hxpos hypos hzpos hsum2
  refine ⟨hle, hiff.trans ⟨?_, ?_⟩, hiff⟩
  · -- equal distances to the three sides force `P` to be the incenter
    rintro ⟨hxy, hyz⟩
    have hy' : dist P E * dist C A = β * areaDoubled A B C := hy
    rw [← hxy] at hy'
    have hz' : dist P F * dist A B = γ * areaDoubled A B C := hz
    rw [← hyz, ← hxy] at hz'
    have hsumr : dist P D * (dist B C + dist C A + dist A B) = areaDoubled A B C := by
      linear_combination hx + hy' + hz' + areaDoubled A B C * hsum
    have e1 : (dist B C + dist C A + dist A B) * α = dist B C :=
      mul_left_cancel₀ (ne_of_gt hT)
        (by linear_combination (-(dist B C + dist C A + dist A B)) * hx + dist B C * hsumr)
    have e2 : (dist B C + dist C A + dist A B) * β = dist C A :=
      mul_left_cancel₀ (ne_of_gt hT)
        (by linear_combination (-(dist B C + dist C A + dist A B)) * hy' + dist C A * hsumr)
    have e3 : (dist B C + dist C A + dist A B) * γ = dist A B :=
      mul_left_cancel₀ (ne_of_gt hT)
        (by linear_combination (-(dist B C + dist C A + dist A B)) * hz' + dist A B * hsumr)
    rw [hP, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e1, e2, e3]
  · -- conversely, the incenter is equidistant from the three sides
    intro hkey
    have hα3 : α = 1 - β - γ := by linarith
    have expand : ((dist B C + dist C A + dist A B) * β - dist C A) • (B - A)
        + ((dist B C + dist C A + dist A B) * γ - dist A B) • (C - A)
        = (dist B C + dist C A + dist A B) • P
          - (dist B C • A + dist C A • B + dist A B • C) := by
      rw [hP, hα3]; module
    have hzero : ((dist B C + dist C A + dist A B) * β - dist C A) • (B - A)
        + ((dist B C + dist C A + dist A B) * γ - dist A B) • (C - A) = 0 := by
      rw [expand, hkey, sub_self]
    obtain ⟨hb', hc'⟩ := eq_zero_of_gram_pos hgram hzero
    have ha' : (dist B C + dist C A + dist A B) * α = dist B C := by
      linear_combination (dist B C + dist C A + dist A B) * hsum - hb' - hc'
    have hb'' : (dist B C + dist C A + dist A B) * β = dist C A := by linarith
    have hc'' : (dist B C + dist C A + dist A B) * γ = dist A B := by linarith
    have hs : 0 < dist B C + dist C A + dist A B := by linarith
    have hxs : dist P D * (dist B C + dist C A + dist A B) = areaDoubled A B C :=
      mul_left_cancel₀ (ne_of_gt hα) (by linear_combination hx + dist P D * ha')
    have hys : dist P E * (dist B C + dist C A + dist A B) = areaDoubled A B C :=
      mul_left_cancel₀ (ne_of_gt hβ) (by linear_combination hy + dist P E * hb'')
    have hzs : dist P F * (dist B C + dist C A + dist A B) = areaDoubled A B C :=
      mul_left_cancel₀ (ne_of_gt hγ) (by linear_combination hz + dist P F * hc'')
    exact ⟨mul_right_cancel₀ (ne_of_gt hs) (by rw [hxs, hys]),
      mul_right_cancel₀ (ne_of_gt hs) (by rw [hys, hzs])⟩

end Imo1981P1
