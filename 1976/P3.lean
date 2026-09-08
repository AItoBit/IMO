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

/-!
# IMO 1976, Problem 3

A rectangular box with integer edge lengths `a`, `b`, `c` can be completely filled with unit cubes.
If one places into it, with edges parallel to the edges of the box, as many cubes of volume `2` as
possible (each such cube has edge length `∛2`), then exactly `40 %` of the volume of the box is
filled.  Determine all possible dimensions of the box.

The number of cubes of edge `∛2` that fit is `⌊a/∛2⌋ * ⌊b/∛2⌋ * ⌊c/∛2⌋`, so the hypothesis reads
`2 * ⌊a/∛2⌋ * ⌊b/∛2⌋ * ⌊c/∛2⌋ = (2/5) * a * b * c`.

The answer is `{a, b, c} = {2, 3, 5}` or `{a, b, c} = {2, 5, 6}` (as unordered triples).
-/

namespace Imo1976P3

/-- The real number `∛2`, the edge length of a cube of volume `2`. -/
noncomputable def cbrt2 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

lemma cbrt2_pos : 0 < cbrt2 := Real.rpow_pos_of_pos (by norm_num) _

lemma cbrt2_cube : cbrt2 ^ 3 = 2 := by
  rw [cbrt2, ← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma cube_le_cube_iff {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : u ^ 3 ≤ v ^ 3 ↔ u ≤ v :=
  ⟨fun h => le_of_not_gt fun hlt => absurd h (not_le.2 (pow_lt_pow_left₀ hlt hv three_ne_zero)),
   fun h => pow_le_pow_left₀ hu h 3⟩

lemma cube_lt_cube_iff {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : u ^ 3 < v ^ 3 ↔ u < v := by
  rw [← not_le, ← not_le, cube_le_cube_iff hv hu]

/-- Arithmetic characterisation of `⌊n / ∛2⌋`. -/
lemma floor_cbrt2_spec (n k : ℕ) :
    ⌊(n : ℝ) / cbrt2⌋₊ = k ↔ (2 * k ^ 3 ≤ n ^ 3 ∧ n ^ 3 < 2 * (k + 1) ^ 3) := by
  have hc := cbrt2_pos
  rw [Nat.floor_eq_iff (by positivity), le_div_iff₀ hc, div_lt_iff₀ hc,
      ← cube_le_cube_iff (by positivity) (by positivity),
      ← cube_lt_cube_iff (by positivity) (by positivity), mul_pow, mul_pow, cbrt2_cube]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · exact_mod_cast (by push_cast; linarith : ((2 * k ^ 3 : ℕ) : ℝ) ≤ ((n ^ 3 : ℕ) : ℝ))
    · exact_mod_cast (by push_cast; linarith : ((n ^ 3 : ℕ) : ℝ) < ((2 * (k + 1) ^ 3 : ℕ) : ℝ))
  · rintro ⟨h1, h2⟩
    have h1' : ((2 * k ^ 3 : ℕ) : ℝ) ≤ ((n ^ 3 : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : ((n ^ 3 : ℕ) : ℝ) < ((2 * (k + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h1' h2'
    constructor <;> linarith

lemma nat_cube_lt {a m : ℕ} (h : a ^ 3 < m ^ 3) : a < m :=
  (Nat.pow_lt_pow_iff_left (by norm_num)).mp h

/-- If the ratio `a / ⌊a/∛2⌋` is at least `∛5`, then `a = 2`. -/
lemma one_var_large {a x : ℕ} (h2 : a ^ 3 < 2 * (x + 1) ^ 3) (h3 : 5 * x ^ 3 ≤ a ^ 3)
    (hx : 0 < x) : a = 2 ∧ x = 1 := by
  have hxle : x ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t, rfl⟩ : ∃ t, x = t + 3 := ⟨x - 3, by omega⟩
    have key : 2 * (t + 3 + 1) ^ 3 ≤ 5 * (t + 3) ^ 3 := by
      calc 2 * (t + 3 + 1) ^ 3
          ≤ 2 * (t + 3 + 1) ^ 3 + (3 * t ^ 3 + 21 * t ^ 2 + 39 * t + 7) := Nat.le_add_right _ _
        _ = 5 * (t + 3) ^ 3 := by ring
    omega
  interval_cases x
  · have ha1 : a < 3 := nat_cube_lt (m := 3) (by omega)
    have ha2 : 1 < a := nat_cube_lt (a := 1) (m := a) (by omega)
    omega
  · exfalso
    have ha1 : a < 4 := nat_cube_lt (m := 4) (by omega)
    have ha2 : 3 < a := nat_cube_lt (a := 3) (m := a) (by omega)
    omega

/-- If the ratio `b / ⌊b/∛2⌋` is at least `√(5/2)`, then `b = 2` or `b = 5`. -/
lemma one_var_mid {b y : ℕ} (h1 : 2 * y ^ 3 ≤ b ^ 3) (h2 : b ^ 3 < 2 * (y + 1) ^ 3)
    (h3 : 5 * y ^ 2 ≤ 2 * b ^ 2) (hy : 0 < y) : (b = 2 ∧ y = 1) ∨ (b = 5 ∧ y = 3) := by
  have hsix1 : 125 * y ^ 6 ≤ 8 * b ^ 6 := by
    calc 125 * y ^ 6 = (5 * y ^ 2) ^ 3 := by ring
      _ ≤ (2 * b ^ 2) ^ 3 := Nat.pow_le_pow_left h3 3
      _ = 8 * b ^ 6 := by ring
  have hsix2 : b ^ 6 < 4 * (y + 1) ^ 6 := by
    calc b ^ 6 = (b ^ 3) ^ 2 := by ring
      _ < (2 * (y + 1) ^ 3) ^ 2 := Nat.pow_lt_pow_left h2 (n := 2) (by norm_num)
      _ = 4 * (y + 1) ^ 6 := by ring
  have hyle : y ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t, rfl⟩ : ∃ t, y = t + 4 := ⟨y - 4, by omega⟩
    have key : 32 * (t + 4 + 1) ^ 6 ≤ 125 * (t + 4) ^ 6 := by
      calc 32 * (t + 4 + 1) ^ 6
          ≤ 32 * (t + 4 + 1) ^ 6 + (93 * t ^ 6 + 2040 * t ^ 5 + 18000 * t ^ 4 + 80000 * t ^ 3 +
              180000 * t ^ 2 + 168000 * t + 12000) := Nat.le_add_right _ _
        _ = 125 * (t + 4) ^ 6 := by ring
    omega
  interval_cases y
  · have hb1 : b < 3 := nat_cube_lt (m := 3) (by omega)
    have hb2 : 1 < b := nat_cube_lt (a := 1) (m := b) (by omega)
    omega
  · exfalso
    have hb1 : b < 4 := nat_cube_lt (m := 4) (by omega)
    have hb2 : 2 < b := nat_cube_lt (a := 2) (m := b) (by omega)
    interval_cases b
    omega
  · have hb1 : b < 6 := nat_cube_lt (m := 6) (by omega)
    have hb2 : 3 < b := nat_cube_lt (a := 3) (m := b) (by omega)
    interval_cases b <;> omega

/-- The case of ratio exactly `3/2`. -/
lemma ratio_three_halves {c z : ℕ} (h1 : 2 * z ^ 3 ≤ c ^ 3) (h2 : c ^ 3 < 2 * (z + 1) ^ 3)
    (h : 3 * z = 2 * c) (hz : 0 < z) : c = 3 ∨ c = 6 := by
  obtain ⟨t, rfl⟩ : ∃ t, z = 2 * t := ⟨z / 2, by omega⟩
  have hct : c = 3 * t := by omega
  subst hct
  have htpos : 0 < t := by omega
  have htle : t ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 3 := ⟨t - 3, by omega⟩
    have key : 2 * (2 * (s + 3) + 1) ^ 3 ≤ 27 * (s + 3) ^ 3 := by
      calc 2 * (2 * (s + 3) + 1) ^ 3
          ≤ 2 * (2 * (s + 3) + 1) ^ 3 + (11 * s ^ 3 + 75 * s ^ 2 + 141 * s + 43) :=
            Nat.le_add_right _ _
        _ = 27 * (s + 3) ^ 3 := by ring
    have : (3 * (s + 3)) ^ 3 = 27 * (s + 3) ^ 3 := by ring
    omega
  interval_cases t <;> omega

/-- The ratio `5/4` is impossible. -/
lemma ratio_five_fourths {c z : ℕ} (h1 : 2 * z ^ 3 ≤ c ^ 3) (h : 5 * z = 4 * c) (hz : 0 < z) :
    False := by
  have h64 : 64 * c ^ 3 = 125 * z ^ 3 := by
    have : (4 * c) ^ 3 = (5 * z) ^ 3 := by rw [h]
    nlinarith [this]
  have : 128 * z ^ 3 ≤ 64 * c ^ 3 := by nlinarith [h1]
  have hzp : 0 < z ^ 3 := Nat.pow_pos hz
  omega

/-- Two remaining sides, once the first side has been identified as `2`. -/
lemma pair_case {b y c z : ℕ} (hyb1 : 2 * y ^ 3 ≤ b ^ 3) (hyb2 : b ^ 3 < 2 * (y + 1) ^ 3)
    (hzc1 : 2 * z ^ 3 ≤ c ^ 3) (hzc2 : c ^ 3 < 2 * (z + 1) ^ 3)
    (h : 5 * (y * z) = 2 * (b * c)) (hmid : 5 * y ^ 2 ≤ 2 * b ^ 2) (hy : 0 < y) (hz : 0 < z) :
    b = 5 ∧ (c = 3 ∨ c = 6) := by
  rcases one_var_mid hyb1 hyb2 hmid hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (ratio_five_fourths hzc1 (by omega) hz) (by simp)
  · exact ⟨rfl, ratio_three_halves hzc1 hzc2 (by omega) hz⟩

/-- Core step: if the first side has the largest ratio, the triple is determined. -/
lemma core {a b c x y z : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hax1 : 2 * x ^ 3 ≤ a ^ 3) (hax2 : a ^ 3 < 2 * (x + 1) ^ 3)
    (hby1 : 2 * y ^ 3 ≤ b ^ 3) (hby2 : b ^ 3 < 2 * (y + 1) ^ 3)
    (hcz1 : 2 * z ^ 3 ≤ c ^ 3) (hcz2 : c ^ 3 < 2 * (z + 1) ^ 3)
    (hvol : 5 * (x * y * z) = a * b * c) (hbig : 5 * x ^ 3 ≤ a ^ 3) :
    ({a, b, c} : Multiset ℕ) = {2, 3, 5} ∨ ({a, b, c} : Multiset ℕ) = {2, 5, 6} := by
  have habc : 0 < a * b * c := by positivity
  have hxyz : 0 < x * y * z := by
    rcases Nat.eq_zero_or_pos (x * y * z) with h | h
    · rw [h] at hvol; omega
    · exact h
  have hx : 0 < x := Nat.pos_of_ne_zero fun h => by subst h; simp at hxyz
  have hy : 0 < y := Nat.pos_of_ne_zero fun h => by subst h; simp at hxyz
  have hz : 0 < z := Nat.pos_of_ne_zero fun h => by subst h; simp at hxyz
  obtain ⟨rfl, rfl⟩ := one_var_large hax2 hbig hx
  have hvol' : 5 * (y * z) = 2 * (b * c) := by
    have : 5 * (1 * y * z) = 2 * b * c := hvol
    ring_nf at this ⊢
    linarith [this]
  have hsplit : 5 * y ^ 2 ≤ 2 * b ^ 2 ∨ 5 * z ^ 2 ≤ 2 * c ^ 2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hsq : (5 * (y * z)) ^ 2 = (2 * (b * c)) ^ 2 := by rw [hvol']
    nlinarith [hsq, h1, h2, Nat.zero_le (y * z), Nat.zero_le (b * c)]
  rcases hsplit with hmid | hmid
  · obtain ⟨rfl, hcc⟩ := pair_case hby1 hby2 hcz1 hcz2 hvol' hmid hy hz
    rcases hcc with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  · have hvol'' : 5 * (z * y) = 2 * (c * b) := by rw [mul_comm z y, mul_comm c b]; exact hvol'
    obtain ⟨rfl, hbb⟩ := pair_case hcz1 hcz2 hby1 hby2 hvol'' hmid hz hy
    rcases hbb with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)

/-- The purely arithmetic form of the problem. -/
theorem arith_solution {a b c x y z : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hax1 : 2 * x ^ 3 ≤ a ^ 3) (hax2 : a ^ 3 < 2 * (x + 1) ^ 3)
    (hby1 : 2 * y ^ 3 ≤ b ^ 3) (hby2 : b ^ 3 < 2 * (y + 1) ^ 3)
    (hcz1 : 2 * z ^ 3 ≤ c ^ 3) (hcz2 : c ^ 3 < 2 * (z + 1) ^ 3)
    (hvol : 5 * (x * y * z) = a * b * c) :
    ({a, b, c} : Multiset ℕ) = {2, 3, 5} ∨ ({a, b, c} : Multiset ℕ) = {2, 5, 6} := by
  have hbig : 5 * x ^ 3 ≤ a ^ 3 ∨ 5 * y ^ 3 ≤ b ^ 3 ∨ 5 * z ^ 3 ≤ c ^ 3 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hcube : (a * b * c) ^ 3 = 125 * (x ^ 3 * y ^ 3 * z ^ 3) := by
      rw [← hvol]; ring
    have e1 : (a * b * c) ^ 3 = a ^ 3 * b ^ 3 * c ^ 3 := by ring
    have hlt : a ^ 3 * b ^ 3 * c ^ 3 < (5 * x ^ 3) * (5 * y ^ 3) * (5 * z ^ 3) :=
      Nat.mul_lt_mul_of_lt_of_lt (Nat.mul_lt_mul_of_lt_of_lt h1 h2) h3
    have : (5 * x ^ 3) * (5 * y ^ 3) * (5 * z ^ 3) = 125 * (x ^ 3 * y ^ 3 * z ^ 3) := by ring
    omega
  rcases hbig with h | h | h
  · exact core ha hb hc hax1 hax2 hby1 hby2 hcz1 hcz2 hvol h
  · have hvol' : 5 * (y * x * z) = b * a * c := by
      rw [show y * x * z = x * y * z by ring, show b * a * c = a * b * c by ring]; exact hvol
    have := core hb ha hc hby1 hby2 hax1 hax2 hcz1 hcz2 hvol' h
    have hperm : ({b, a, c} : Multiset ℕ) = ({a, b, c} : Multiset ℕ) := by
      simp only [Multiset.insert_eq_cons]
      exact Multiset.cons_swap b a {c}
    rwa [hperm] at this
  · have hvol' : 5 * (z * y * x) = c * b * a := by
      rw [show z * y * x = x * y * z by ring, show c * b * a = a * b * c by ring]; exact hvol
    have := core hc hb ha hcz1 hcz2 hby1 hby2 hax1 hax2 hvol' h
    have hperm : ({c, b, a} : Multiset ℕ) = ({a, b, c} : Multiset ℕ) := by
      show c ::ₘ b ::ₘ a ::ₘ 0 = a ::ₘ b ::ₘ c ::ₘ 0
      rw [Multiset.cons_swap b a, Multiset.cons_swap c a, Multiset.cons_swap c b]
    rwa [hperm] at this

/-- The floor values of `n / ∛2` for the relevant side lengths. -/
lemma floor_two : ⌊((2 : ℕ) : ℝ) / cbrt2⌋₊ = 1 := (floor_cbrt2_spec 2 1).mpr (by norm_num)

lemma floor_three : ⌊((3 : ℕ) : ℝ) / cbrt2⌋₊ = 2 := (floor_cbrt2_spec 3 2).mpr (by norm_num)

lemma floor_five : ⌊((5 : ℕ) : ℝ) / cbrt2⌋₊ = 3 := (floor_cbrt2_spec 5 3).mpr (by norm_num)

lemma floor_six : ⌊((6 : ℕ) : ℝ) / cbrt2⌋₊ = 4 := (floor_cbrt2_spec 6 4).mpr (by norm_num)

/-- **IMO 1976, Problem 3.**  A box with positive integer sides `a`, `b`, `c` is filled with as
many cubes of volume `2` (i.e. of edge `∛2`) as possible, their edges parallel to the edges of the
box; the number of such cubes is `⌊a/∛2⌋ * ⌊b/∛2⌋ * ⌊c/∛2⌋`.  Exactly `40 %` of the volume of the
box is filled precisely when the sides are, in some order, `2, 3, 5` or `2, 5, 6`. -/
theorem imo1976_p3 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * ((⌊(a : ℝ) / cbrt2⌋₊ : ℝ) * (⌊(b : ℝ) / cbrt2⌋₊ : ℝ) * (⌊(c : ℝ) / cbrt2⌋₊ : ℝ))
        = (2 / 5) * ((a : ℝ) * (b : ℝ) * (c : ℝ)) ↔
      ({a, b, c} : Multiset ℕ) = {2, 3, 5} ∨ ({a, b, c} : Multiset ℕ) = {2, 5, 6} := by
  set x := ⌊(a : ℝ) / cbrt2⌋₊ with hxdef
  set y := ⌊(b : ℝ) / cbrt2⌋₊ with hydef
  set z := ⌊(c : ℝ) / cbrt2⌋₊ with hzdef
  have hnat : (2 * ((x : ℝ) * (y : ℝ) * (z : ℝ)) = (2 / 5) * ((a : ℝ) * (b : ℝ) * (c : ℝ))) ↔
      5 * (x * y * z) = a * b * c := by
    constructor
    · intro h
      have : ((5 * (x * y * z) : ℕ) : ℝ) = ((a * b * c : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · intro h
      have : ((5 * (x * y * z) : ℕ) : ℝ) = ((a * b * c : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this
      linarith
  rw [hnat]
  obtain ⟨hax1, hax2⟩ := (floor_cbrt2_spec a x).mp hxdef.symm
  obtain ⟨hby1, hby2⟩ := (floor_cbrt2_spec b y).mp hydef.symm
  obtain ⟨hcz1, hcz2⟩ := (floor_cbrt2_spec c z).mp hzdef.symm
  constructor
  · intro hvol
    exact arith_solution ha hb hc hax1 hax2 hby1 hby2 hcz1 hcz2 hvol
  · intro hmul
    have hcases :
        (a = 2 ∧ b = 3 ∧ c = 5) ∨ (a = 2 ∧ b = 5 ∧ c = 3) ∨ (a = 3 ∧ b = 2 ∧ c = 5) ∨
          (a = 3 ∧ b = 5 ∧ c = 2) ∨ (a = 5 ∧ b = 2 ∧ c = 3) ∨ (a = 5 ∧ b = 3 ∧ c = 2) ∨
          (a = 2 ∧ b = 5 ∧ c = 6) ∨ (a = 2 ∧ b = 6 ∧ c = 5) ∨ (a = 5 ∧ b = 2 ∧ c = 6) ∨
          (a = 5 ∧ b = 6 ∧ c = 2) ∨ (a = 6 ∧ b = 2 ∧ c = 5) ∨ (a = 6 ∧ b = 5 ∧ c = 2) := by
      rcases hmul with h | h
      · simp [Multiset.cons_eq_cons] at h
        rcases h with ⟨rfl, h⟩ | ⟨hne, cs, h1, h2⟩
        · omega
        · rcases h1 with ⟨rfl, rfl⟩ | ⟨h3, rfl, rfl⟩ <;> simp_all <;> omega
      · simp [Multiset.cons_eq_cons] at h
        rcases h with ⟨rfl, h⟩ | ⟨hne, cs, h1, h2⟩
        · omega
        · rcases h1 with ⟨rfl, rfl⟩ | ⟨h3, rfl, rfl⟩ <;> simp_all <;> omega
    have hx2 : x = ⌊((a : ℕ) : ℝ) / cbrt2⌋₊ := hxdef
    have hy2 : y = ⌊((b : ℕ) : ℝ) / cbrt2⌋₊ := hydef
    have hz2 : z = ⌊((c : ℕ) : ℝ) / cbrt2⌋₊ := hzdef
    rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp only [hx2, hy2, hz2, floor_two, floor_three, floor_five, floor_six] <;>
      norm_num

end Imo1976P3
