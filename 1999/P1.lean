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
# IMO 1999, Problem 1

Determine all finite sets `S` of at least three points in the plane which satisfy the following
condition: for any two distinct points `A` and `B` in `S`, the perpendicular bisector of the
segment `AB` is an axis of symmetry of `S`.

The answer: `S` is the set of vertices of a regular `n`-gon, where `n = |S|`.

The plane is modelled by `ℂ`.  The reflection in the perpendicular bisector of a segment `AB`
(with `A ≠ B`) is the map `reflBis A B`, defined below; the lemmas `reflBis_dist`,
`reflBis_involutive` and `reflBis_fixed_iff` justify this name: `reflBis A B` is an isometric
involution of the plane whose set of fixed points is exactly the perpendicular bisector
`{z | dist z A = dist z B}` of `A` and `B`.
-/

namespace IMO1999Q1

open ComplexConjugate

/-- Reflection of the plane `ℂ` in the perpendicular bisector of the segment joining `A` to `B`
(for `A ≠ B`). -/
noncomputable def reflBis (A B z : ℂ) : ℂ :=
  (A + B) / 2 - ((B - A) / conj (B - A)) * conj (z - (A + B) / 2)

section Basic

variable {A B z z' : ℂ}

lemma conj_ne_zero_of_ne_zero {x : ℂ} (hx : x ≠ 0) : conj x ≠ 0 := by
  intro hh; apply hx; simpa using congrArg conj hh

/-- `reflBis A B` is an isometry of the plane. -/
theorem reflBis_dist (h : A ≠ B) (z z' : ℂ) :
    dist (reflBis A B z) (reflBis A B z') = dist z z' := by
  have hd : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have key : reflBis A B z - reflBis A B z' = -((B - A) / conj (B - A)) * conj (z - z') := by
    unfold reflBis
    simp only [map_sub]
    ring
  have hk : ‖(B - A) / conj (B - A)‖ = 1 := by
    rw [norm_div, RCLike.norm_conj]
    exact div_self (by simpa using hd)
  rw [Complex.dist_eq, Complex.dist_eq, key, norm_mul, norm_neg, hk, RCLike.norm_conj, one_mul]

/-- `reflBis A B` is injective. -/
theorem reflBis_injective (h : A ≠ B) : Function.Injective (reflBis A B) := by
  intro x y hxy
  have := reflBis_dist h x y
  rw [hxy, dist_self] at this
  exact dist_eq_zero.mp this.symm

/-- `reflBis A B` is an involution. -/
theorem reflBis_involutive (h : A ≠ B) (z : ℂ) : reflBis A B (reflBis A B z) = z := by
  have hd : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hcd : conj B - conj A ≠ 0 := by
    rw [← map_sub]; exact conj_ne_zero_of_ne_zero hd
  unfold reflBis
  simp only [map_sub, map_add, map_mul, map_div₀, map_ofNat, Complex.conj_conj]
  field_simp
  ring

/-- A point is equidistant from `A` and `B` exactly when `(z - (A+B)/2) * conj (B - A)` is purely
imaginary. -/
theorem dist_eq_iff_re (A B z : ℂ) :
    dist z A = dist z B ↔ ((z - (A + B) / 2) * conj (B - A)).re = 0 := by
  rw [Complex.dist_eq, Complex.dist_eq]
  rw [show (‖z - A‖ = ‖z - B‖ ↔ Complex.normSq (z - A) = Complex.normSq (z - B)) from by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    constructor
    · intro hh; rw [hh]
    · intro hh; nlinarith [norm_nonneg (z - A), norm_nonneg (z - B)]]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.div_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.div_im]
  norm_num
  constructor <;> intro hh <;> nlinarith [hh]

/-- The displacement produced by the reflection. -/
theorem reflBis_sub_self (h : A ≠ B) (z : ℂ) :
    reflBis A B z - z = -(((z - (A + B) / 2) * conj (B - A))
      + conj ((z - (A + B) / 2) * conj (B - A))) / conj (B - A) := by
  have hd : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hcd' : conj B - conj A ≠ 0 := by rw [← map_sub]; exact conj_ne_zero_of_ne_zero hd
  unfold reflBis
  simp only [map_sub, map_add, map_mul, map_div₀, map_ofNat, Complex.conj_conj]
  field_simp
  ring

/-- The fixed points of `reflBis A B` are exactly the points of the perpendicular bisector of
`A` and `B`. -/
theorem reflBis_fixed_iff (h : A ≠ B) (z : ℂ) : reflBis A B z = z ↔ dist z A = dist z B := by
  have hd : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hcd : conj (B - A) ≠ 0 := conj_ne_zero_of_ne_zero hd
  set s : ℂ := (z - (A + B) / 2) * conj (B - A) with hs
  have key1 : reflBis A B z = z ↔ s.re = 0 := by
    rw [← sub_eq_zero, reflBis_sub_self h z, ← hs, div_eq_zero_iff]
    simp only [hcd, or_false, neg_eq_zero]
    rw [Complex.add_conj]
    norm_cast
    simp
  rw [key1, dist_eq_iff_re, hs]

/-- The reflection in the perpendicular bisector of `AB` exchanges `A` and `B`. -/
theorem reflBis_left (h : A ≠ B) : reflBis A B A = B := by
  have hd : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hcd' : conj B - conj A ≠ 0 := by
    rw [← map_sub]; exact conj_ne_zero_of_ne_zero hd
  unfold reflBis
  simp only [map_sub, map_add, map_div₀, map_ofNat]
  field_simp
  ring

instance perpBisector_nonempty_complex (A B : ℂ) :
    Nonempty (AffineSubspace.perpBisector A B) :=
  ⟨⟨midpoint ℝ A B, AffineSubspace.midpoint_mem_perpBisector A B⟩⟩

/-- `reflBis A B` really is Mathlib's reflection in the perpendicular bisector of `A` and `B`. -/
theorem reflBis_eq_reflection (h : A ≠ B) (z : ℂ) :
    reflBis A B z
      = EuclideanGeometry.reflection (𝕜 := ℝ) (AffineSubspace.perpBisector A B) z := by
  have hd : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hcd : conj (B - A) ≠ 0 := conj_ne_zero_of_ne_zero hd
  have hmc : (B - A) * conj (B - A) = (Complex.normSq (B - A) : ℂ) := Complex.mul_conj _
  have hN : Complex.normSq (B - A) ≠ 0 := by simpa using hd
  set s : ℂ := (z - (A + B) / 2) * conj (B - A) with hs
  set c : ℝ := -s.re / Complex.normSq (B - A) with hc
  set q : ℂ := (z + reflBis A B z) / 2 with hq
  have hqz : q - z = (c : ℂ) * (B - A) := by
    have h1 : reflBis A B z - z = -(s + conj s) / conj (B - A) := reflBis_sub_self h z
    have h2 : q - z = (reflBis A B z - z) / 2 := by rw [hq]; ring
    rw [h2, h1, Complex.add_conj, hc]
    push_cast
    rw [← hmc]
    field_simp
  have hqmem : q ∈ AffineSubspace.perpBisector A B := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq, dist_eq_iff_re]
    have hqm : (q - (A + B) / 2) * conj (B - A)
        = s + ((c * Complex.normSq (B - A) : ℝ) : ℂ) := by
      have hsplit : q - (A + B) / 2 = (z - (A + B) / 2) + (q - z) := by ring
      rw [hsplit, add_mul, hqz, ← hs]
      push_cast
      rw [mul_assoc, hmc]
    rw [hqm]
    simp only [Complex.add_re, Complex.ofReal_re]
    rw [hc]
    field_simp
    ring
  have hqmem2 : q ∈ AffineSubspace.mk' z (AffineSubspace.perpBisector A B).directionᗮ := by
    rw [AffineSubspace.mem_mk']
    have hv : q -ᵥ z = (c : ℂ) * (B - A) := hqz
    rw [hv, AffineSubspace.direction_perpBisector]
    apply Submodule.le_orthogonal_orthogonal
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by rw [Complex.real_smul]; simp⟩
  have hproj : (EuclideanGeometry.orthogonalProjection
      (AffineSubspace.perpBisector A B) z : ℂ) = q := by
    have hmem : q ∈ (AffineSubspace.perpBisector A B : Set ℂ)
        ∩ AffineSubspace.mk' z (AffineSubspace.perpBisector A B).directionᗮ := ⟨hqmem, hqmem2⟩
    rw [EuclideanGeometry.inter_eq_singleton_orthogonalProjection z] at hmem
    exact (Set.mem_singleton_iff.mp hmem).symm
  rw [EuclideanGeometry.reflection_apply', hproj]
  simp only [vsub_eq_sub, vadd_eq_add]
  rw [hq]
  ring

end Basic

/-- If `‖a‖ = 1` then `conj a = a⁻¹`. -/
lemma conj_of_norm_one {a : ℂ} (h : ‖a‖ = 1) : conj a = a⁻¹ := by
  have ha : a ≠ 0 := by intro h0; rw [h0] at h; simp at h
  have hmul : a * conj a = 1 := by
    rw [Complex.mul_conj]; norm_cast; simp [Complex.normSq_eq_norm_sq, h]
  field_simp at hmul ⊢
  linear_combination hmul

lemma norm_eq_one_of_pow_eq_one {u : ℂ} {n : ℕ} (hn : n ≠ 0) (hu : u ^ n = 1) : ‖u‖ = 1 := by
  have h : ‖u‖ ^ n = 1 := by rw [← norm_pow, hu, norm_one]
  rcases lt_trichotomy ‖u‖ 1 with h1 | h1 | h1
  · have := pow_lt_one₀ (norm_nonneg u) h1 hn
    linarith
  · exact h1
  · have := one_lt_pow₀ h1 hn
    linarith

/-- Reflections in perpendicular bisectors of chords of a circle, in terms of the circle
parametrisation `u ↦ c + w * u` by the unit circle. -/
lemma reflBis_circle {c w a b u : ℂ} (hw : w ≠ 0) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hu : ‖u‖ = 1)
    (hab : a ≠ b) : reflBis (c + w * a) (c + w * b) (c + w * u) = c + w * (a * b / u) := by
  have ha0 : a ≠ 0 := by intro h0; rw [h0] at ha; simp at ha
  have hb0 : b ≠ 0 := by intro h0; rw [h0] at hb; simp at hb
  have hu0 : u ≠ 0 := by intro h0; rw [h0] at hu; simp at hu
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hcw : conj w ≠ 0 := conj_ne_zero_of_ne_zero hw
  unfold reflBis
  have h1 : ((c + w * b) - (c + w * a)) = w * (b - a) := by ring
  rw [h1]
  have h2 : conj (w * (b - a)) = conj w * (a - b) / (a * b) := by
    simp only [map_sub, map_mul, conj_of_norm_one ha, conj_of_norm_one hb]
    field_simp
  have h3 : (w * (b - a)) / conj (w * (b - a)) = -(w * a * b) / conj w := by
    rw [h2, div_div_eq_mul_div, div_eq_div_iff (by simp [hcw, hab']) hcw]
    ring
  rw [h3]
  have h4 : conj (c + w * u - (c + w * a + (c + w * b)) / 2)
      = conj w * (u⁻¹ - (a⁻¹ + b⁻¹) / 2) := by
    simp only [map_sub, map_add, map_mul, map_div₀, map_ofNat,
      conj_of_norm_one ha, conj_of_norm_one hb, conj_of_norm_one hu]
    ring
  rw [h4]
  field_simp
  ring

section Forward

variable {S : Finset ℂ}

/-- The symmetry hypothesis of the problem. -/
def IsSymmetric (S : Finset ℂ) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ z ∈ S, reflBis A B z ∈ S

/-- A reflection in the perpendicular bisector of two points of `S` permutes `S`. -/
lemma image_reflBis_eq (hsym : IsSymmetric S) {A B : ℂ} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    S.image (reflBis A B) = S := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact hsym A hA B hB hAB z hz
  · rw [Finset.card_image_of_injective _ (reflBis_injective hAB)]

lemma sum_reflBis (A B : ℂ) (S : Finset ℂ) (hcard : (S.card : ℂ) ≠ 0) :
    ∑ z ∈ S, reflBis A B z = (S.card : ℂ) * reflBis A B ((∑ z ∈ S, z) / S.card) := by
  have hconj : conj ((S.card : ℂ)) = (S.card : ℂ) := by simp
  simp only [reflBis, map_sub, map_div₀, map_add, map_ofNat, hconj, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, map_sum]
  field_simp

/-- The centroid of `S` is fixed by every reflection in a perpendicular bisector of two of its
points. -/
lemma centroid_fixed (hsym : IsSymmetric S) {A B : ℂ} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B)
    (hcard : (S.card : ℂ) ≠ 0) :
    reflBis A B ((∑ z ∈ S, z) / S.card) = (∑ z ∈ S, z) / S.card := by
  have h1 : ∑ z ∈ S, reflBis A B z = ∑ z ∈ S, z := by
    conv_rhs => rw [← image_reflBis_eq hsym hA hB hAB]
    rw [Finset.sum_image (fun x _ y _ hxy => reflBis_injective hAB hxy)]
  rw [sum_reflBis A B S hcard] at h1
  have : (S.card : ℂ) * reflBis A B ((∑ z ∈ S, z) / S.card)
      = (S.card : ℂ) * ((∑ z ∈ S, z) / S.card) := by
    rw [h1]; field_simp
  exact mul_left_cancel₀ hcard this

/-- All points of `S` lie on a circle centred at the centroid of `S`. -/
lemma concyclic (hsym : IsSymmetric S) (hS : 3 ≤ S.card) {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) :
    dist ((∑ z ∈ S, z) / S.card) x = dist ((∑ z ∈ S, z) / S.card) y := by
  have hcard : (S.card : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  · have := centroid_fixed hsym hx hy hxy hcard
    rw [reflBis_fixed_iff hxy] at this
    exact this

/-- A finite subset `U` of the unit circle which contains `1`, has at least three elements and is
closed under the operations `u ↦ a * b / u` (for distinct `a, b ∈ U`) is closed under
multiplication. -/
lemma unitCircle_mul_closed (U : Finset ℂ) (hnorm : ∀ u ∈ U, ‖u‖ = 1) (h1 : (1 : ℂ) ∈ U)
    (hcard : 3 ≤ U.card) (hop : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → ∀ u ∈ U, a * b / u ∈ U) :
    ∀ a ∈ U, ∀ u ∈ U, a * u ∈ U := by
  intro a ha u hu
  have hne : ∀ x ∈ U, x ≠ 0 := by
    intro x hx h0
    have := hnorm x hx
    rw [h0] at this; simp at this
  obtain ⟨c, hc, hca, hc1⟩ : ∃ c ∈ U, c ≠ a ∧ c ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : U ⊆ {a, 1} := by
      intro x hx
      rcases eq_or_ne x a with rfl | hxa
      · simp
      · have := hcon x hx hxa
        simp [this]
    have h1' := Finset.card_le_card hsub
    have h2 : ({a, 1} : Finset ℂ).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hc0 : c ≠ 0 := hne c hc
  have hu0 : u ≠ 0 := hne u hu
  have step1 : c / u ∈ U := by
    have := hop 1 h1 c hc (Ne.symm hc1) u hu
    simpa using this
  have step2 := hop a ha c hc (Ne.symm hca) (c / u) step1
  have hrw : a * c / (c / u) = a * u := by field_simp
  rwa [hrw] at step2

/-- A finite subset of the unit circle with at least three elements that is closed under
multiplication is the set of `n`-th roots of unity, `n` being its cardinality. -/
lemma eq_nthRootsFinset_of_mul_closed (U : Finset ℂ) (hnorm : ∀ u ∈ U, ‖u‖ = 1)
    (hcard : 3 ≤ U.card) (hmul : ∀ a ∈ U, ∀ u ∈ U, a * u ∈ U) :
    U = Polynomial.nthRootsFinset U.card (1 : ℂ) := by
  have hne : ∀ x ∈ U, x ≠ 0 := by
    intro x hx h0
    have := hnorm x hx
    rw [h0] at this; simp at this
  have hn : 0 < U.card := by omega
  have hpow : ∀ u ∈ U, u ^ U.card = 1 := by
    intro u hu
    have hu0 : u ≠ 0 := hne u hu
    have himg : U.image (fun x => u * x) = U := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact hmul u hu y hy
      · rw [Finset.card_image_of_injective _ (mul_right_injective₀ hu0)]
    have hP : ∏ x ∈ U, x ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
    have h2 : ∏ x ∈ U, (u * x) = ∏ x ∈ U, x := by
      conv_rhs => rw [← himg]
      rw [Finset.prod_image (fun x _ y _ hxy => mul_right_injective₀ hu0 hxy)]
    rw [Finset.prod_mul_distrib, Finset.prod_const] at h2
    exact mul_right_cancel₀ hP (h2.trans (one_mul _).symm)
  have hsub : U ⊆ Polynomial.nthRootsFinset U.card (1 : ℂ) := by
    intro x hx
    rw [Polynomial.mem_nthRootsFinset hn]
    exact hpow x hx
  apply Finset.eq_of_subset_of_card_le hsub
  rw [IsPrimitiveRoot.card_nthRootsFinset (Complex.isPrimitiveRoot_exp U.card (by omega))]

/-- The hard direction of the problem: a symmetric set is the vertex set of a regular polygon. -/
lemma regular_of_isSymmetric (S : Finset ℂ) (hS : 3 ≤ S.card) (hsym : IsSymmetric S) :
    ∃ c w : ℂ, w ≠ 0 ∧ (S : Set ℂ) = {z | ∃ u : ℂ, u ^ S.card = 1 ∧ z = c + w * u} := by
  classical
  set O : ℂ := (∑ z ∈ S, z) / S.card with hO
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  set w : ℂ := z₀ - O with hwdef
  have hr : ∀ x ∈ S, ‖x - O‖ = ‖w‖ := by
    intro x hx
    have h := concyclic hsym hS hx hz₀
    rw [Complex.dist_eq, Complex.dist_eq] at h
    rw [hwdef, ← norm_neg (x - O), ← norm_neg (z₀ - O)]
    simpa [neg_sub] using h
  have hw : w ≠ 0 := by
    intro h0
    have hall : ∀ x ∈ S, x = O := by
      intro x hx
      have h := hr x hx
      rw [h0, norm_zero, norm_eq_zero, sub_eq_zero] at h
      exact h
    have hsub : S ⊆ {O} := fun x hx => by simp [hall x hx]
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  set U : Finset ℂ := S.image (fun z => (z - O) / w) with hU
  have hUmem : ∀ x ∈ S, (x - O) / w ∈ U := fun x hx => Finset.mem_image_of_mem _ hx
  have hUmem' : ∀ u ∈ U, O + w * u ∈ S := by
    intro u hu
    rw [hU, Finset.mem_image] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have h : O + w * ((x - O) / w) = x := by field_simp; ring
    rwa [h]
  have hnorm : ∀ u ∈ U, ‖u‖ = 1 := by
    intro u hu
    rw [hU, Finset.mem_image] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    rw [norm_div, hr x hx, div_self (by simpa using hw)]
  have hUcard : U.card = S.card := by
    rw [hU, Finset.card_image_of_injective]
    intro x y hxy
    field_simp at hxy
    linear_combination hxy
  have h1U : (1 : ℂ) ∈ U := by
    have h := hUmem z₀ hz₀
    rwa [← hwdef, div_self hw] at h
  have hop : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → ∀ u ∈ U, a * b / u ∈ U := by
    intro a ha b hb hab u hu
    have hA := hUmem' a ha
    have hB := hUmem' b hb
    have hz := hUmem' u hu
    have hAB : O + w * a ≠ O + w * b := by
      intro h
      exact hab (mul_left_cancel₀ hw (add_left_cancel h))
    have hmem := hsym _ hA _ hB hAB _ hz
    rw [reflBis_circle hw (hnorm a ha) (hnorm b hb) (hnorm u hu) hab] at hmem
    have h2 := hUmem _ hmem
    simpa [hw] using h2
  have hmul := unitCircle_mul_closed U hnorm h1U (by omega) hop
  have hUeq := eq_nthRootsFinset_of_mul_closed U hnorm (by omega) hmul
  rw [hUcard] at hUeq
  refine ⟨O, w, hw, ?_⟩
  ext x
  simp only [Finset.mem_coe, Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨(x - O) / w, ?_, ?_⟩
    · have h := hUmem x hx
      rw [hUeq] at h
      exact (Polynomial.mem_nthRootsFinset (by omega) 1).mp h
    · field_simp
      ring
  · rintro ⟨u, hu, rfl⟩
    apply hUmem'
    rw [hUeq]
    exact (Polynomial.mem_nthRootsFinset (by omega) 1).mpr hu

/-- The easy direction: the vertex set of a regular polygon is symmetric. -/
lemma isSymmetric_of_regular (S : Finset ℂ) (hS : 3 ≤ S.card) {c w : ℂ} (hw : w ≠ 0)
    (hEq : (S : Set ℂ) = {z | ∃ u : ℂ, u ^ S.card = 1 ∧ z = c + w * u}) : IsSymmetric S := by
  have hn : S.card ≠ 0 := by omega
  have hmem : ∀ x, x ∈ S ↔ ∃ u : ℂ, u ^ S.card = 1 ∧ x = c + w * u := by
    intro x
    constructor
    · intro hx
      have : x ∈ (S : Set ℂ) := by exact_mod_cast hx
      rw [hEq] at this
      exact this
    · intro hx
      have : x ∈ (S : Set ℂ) := by rw [hEq]; exact hx
      exact_mod_cast this
  intro A hA B hB hAB z hz
  obtain ⟨a, ha, rfl⟩ := (hmem A).mp hA
  obtain ⟨b, hb, rfl⟩ := (hmem B).mp hB
  obtain ⟨u, hu, rfl⟩ := (hmem z).mp hz
  have hna : ‖a‖ = 1 := norm_eq_one_of_pow_eq_one hn ha
  have hnb : ‖b‖ = 1 := norm_eq_one_of_pow_eq_one hn hb
  have hnu : ‖u‖ = 1 := norm_eq_one_of_pow_eq_one hn hu
  have hab : a ≠ b := by
    intro h
    exact hAB (by rw [h])
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0] at hnu; simp at hnu
  rw [reflBis_circle hw hna hnb hnu hab]
  rw [hmem]
  exact ⟨a * b / u, by rw [div_pow, mul_pow, ha, hb, hu]; norm_num, rfl⟩

end Forward

/-- **IMO 1999, Problem 1.**  A finite set `S` of at least three points of the plane has the
property that for any two distinct points `A, B ∈ S` the perpendicular bisector of `AB` is an
axis of symmetry of `S` if and only if `S` is the set of vertices of a regular `n`-gon, where
`n = |S|`: that is, `S = {c + w * u | u ^ n = 1}` for some centre `c` and some `w ≠ 0`. -/
theorem imo1999_q1 (S : Finset ℂ) (hS : 3 ≤ S.card) :
    (∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ z ∈ S, reflBis A B z ∈ S) ↔
      ∃ c w : ℂ, w ≠ 0 ∧ (S : Set ℂ) = {z | ∃ u : ℂ, u ^ S.card = 1 ∧ z = c + w * u} := by
  constructor
  · intro hsym
    exact regular_of_isSymmetric S hS hsym
  · rintro ⟨c, w, hw, hEq⟩
    exact isSymmetric_of_regular S hS hw hEq

end IMO1999Q1
