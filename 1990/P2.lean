import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# IMO 1990, Problem 2

Let `n ≥ 3` and consider a set `E` of `2n - 1` distinct points on a circle.  Suppose that exactly
`k` of these points are to be coloured black.  Such a colouring is *good* if there is at least one
pair of black points such that the interior of one of the arcs between them contains exactly `n`
points from `E`.  Find the smallest value of `k` such that every such colouring of `k` points of
`E` is good.

We label the `2n - 1` points of `E` by `ZMod (2 * n - 1)`, in cyclic order along the circle; the
number of points of `E` in the interior of the arc going (say) clockwise from `x` to `y` is then
`(y - x).val - 1`.

The answer is `n` when `3 ∤ 2n - 1` and `3 * ⌊(2n-1)/6⌋ + 1` when `3 ∣ 2n - 1`.
-/

namespace Imo1990P2

/-- `gcd3 n` is `gcd (2n-1) 3`; it is `3` if `3 ∣ 2n - 1` and `1` otherwise.  It is the number of
cycles into which the "arc containing exactly `n` points" relation splits the `2n-1` points. -/
def gcd3 (n : ℕ) : ℕ := Nat.gcd (2 * n - 1) 3

/-- The common length of these cycles. -/
def cyclen (n : ℕ) : ℕ := (2 * n - 1) / gcd3 n

/-- Two points of `E` are joined when they differ by this step. -/
def step (n : ℕ) : ZMod (2 * n - 1) := ((n + 1 : ℕ) : ZMod (2 * n - 1))

/-- A colouring, given by the set `S` of black points, is *good* if some pair of distinct black
points bounds an arc whose interior contains exactly `n` points of `E`. -/
def IsGood (n : ℕ) (S : Finset (ZMod (2 * n - 1))) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ((y - x).val - 1 = n ∨ (x - y).val - 1 = n)

/-- The answer to the problem. -/
def answer (n : ℕ) : ℕ := if 3 ∣ (2 * n - 1) then 3 * ((2 * n - 1) / 6) + 1 else n

/-! ### Elementary arithmetic facts -/

lemma gcd3_dvd_m (n : ℕ) : gcd3 n ∣ 2 * n - 1 := Nat.gcd_dvd_left _ _

lemma gcd3_dvd_three (n : ℕ) : gcd3 n ∣ 3 := Nat.gcd_dvd_right _ _

lemma gcd3_eq_one_or_three (n : ℕ) : gcd3 n = 1 ∨ gcd3 n = 3 :=
  (Nat.prime_three.eq_one_or_self_of_dvd _ (gcd3_dvd_three n))

lemma gcd3_pos (n : ℕ) : 0 < gcd3 n := by
  rcases gcd3_eq_one_or_three n with h | h <;> omega

lemma m_eq_mul (n : ℕ) : 2 * n - 1 = gcd3 n * cyclen n :=
  (Nat.mul_div_cancel' (gcd3_dvd_m n)).symm

lemma cyclen_pos (n : ℕ) (hn : 3 ≤ n) : 0 < cyclen n := by
  have h := m_eq_mul n
  rcases Nat.eq_zero_or_pos (cyclen n) with h0 | h0
  · rw [h0, Nat.mul_zero] at h; omega
  · exact h0

lemma cyclen_odd (n : ℕ) (hn : 3 ≤ n) : Odd (cyclen n) := by
  have h := m_eq_mul n
  rcases Nat.even_or_odd (cyclen n) with he | ho
  · exfalso
    obtain ⟨c, hc⟩ := he
    rcases gcd3_eq_one_or_three n with hg | hg <;> rw [hg, hc] at h <;> omega
  · exact ho

lemma gcd3_dvd_succ (n : ℕ) (hn : 3 ≤ n) : gcd3 n ∣ n + 1 := by
  rcases gcd3_eq_one_or_three n with hg | hg
  · rw [hg]; exact one_dvd _
  · have h : (3 : ℕ) ∣ 2 * n - 1 := hg ▸ gcd3_dvd_m n
    rw [hg]
    omega

lemma three_dvd_iff (n : ℕ) : gcd3 n = 3 ↔ 3 ∣ 2 * n - 1 := by
  constructor
  · intro h; exact h ▸ gcd3_dvd_m n
  · intro h
    have : (3 : ℕ) ∣ gcd3 n := Nat.dvd_gcd h dvd_rfl
    rcases gcd3_eq_one_or_three n with hg | hg <;> omega

lemma answer_eq (n : ℕ) (hn : 3 ≤ n) : answer n = (2 * n - 1 - gcd3 n) / 2 + 1 := by
  have hm := m_eq_mul n
  obtain ⟨t, ht⟩ := cyclen_odd n hn
  unfold answer
  rcases gcd3_eq_one_or_three n with hg | hg
  · have h3 : ¬ (3 ∣ 2 * n - 1) := by
      intro h
      have := (three_dvd_iff n).2 h
      omega
    rw [ite_eq_right h3, hg]
    omega
  · have h3 : (3 ∣ 2 * n - 1) := (three_dvd_iff n).1 hg
    rw [ite_eq_left h3, hg]
    rw [hg, ht] at hm
    omega

/-- The key divisibility step: if `2n-1` divides `3 * k` then the cycle length divides `k`. -/
lemma cyclen_dvd_of_dvd_three_mul (n : ℕ) (k : ℤ)
    (h : ((2 * n - 1 : ℕ) : ℤ) ∣ 3 * k) : ((cyclen n : ℕ) : ℤ) ∣ k := by
  have hm := m_eq_mul n
  rcases gcd3_eq_one_or_three n with hg | hg
  · have hmc : cyclen n = 2 * n - 1 := by rw [hg] at hm; omega
    have hcop : Nat.Coprime (2 * n - 1) 3 := by
      unfold gcd3 at hg; exact hg
    have : IsCoprime ((2 * n - 1 : ℕ) : ℤ) ((3 : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      rw [Int.gcd_natCast_natCast]
      exact hcop
    rw [hmc]
    refine this.dvd_of_dvd_mul_left ?_
    simpa [mul_comm] using h
  · have hm3 : ((2 * n - 1 : ℕ) : ℤ) = 3 * (cyclen n : ℕ) := by
      rw [hg] at hm; exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hm
    rw [hm3] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).1 h

lemma m_cast (n : ℕ) (hn : 3 ≤ n) : ((2 * n - 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := by
  have : 1 ≤ 2 * n := by omega
  push_cast [Nat.cast_sub this]
  ring

/-! ### Reformulation of goodness -/

lemma val_step (n : ℕ) (hn : 3 ≤ n) [NeZero (2 * n - 1)] : (step n).val = n + 1 := by
  unfold step
  exact ZMod.val_cast_of_lt (by omega)

lemma good_iff (n : ℕ) (hn : 3 ≤ n) (S : Finset (ZMod (2 * n - 1))) :
    IsGood n S ↔ ∃ x ∈ S, x + step n ∈ S := by
  have : NeZero (2 * n - 1) := ⟨by omega⟩
  constructor
  · rintro ⟨x, hx, y, hy, hne, h | h⟩
    · have hv : (y - x).val = n + 1 := by
        have h0 : y - x ≠ 0 := sub_ne_zero_of_ne (Ne.symm hne)
        have : (y - x).val ≠ 0 := fun hc => h0 ((ZMod.val_eq_zero _).1 hc)
        omega
      refine ⟨x, hx, ?_⟩
      have : y - x = step n := by
        have := ZMod.natCast_rightInverse (n := 2 * n - 1) (y - x)
        rw [← this, hv]; rfl
      have hxy : x + step n = y := by rw [← this]; ring
      rw [hxy]; exact hy
    · have hv : (x - y).val = n + 1 := by
        have h0 : x - y ≠ 0 := sub_ne_zero_of_ne hne
        have : (x - y).val ≠ 0 := fun hc => h0 ((ZMod.val_eq_zero _).1 hc)
        omega
      refine ⟨y, hy, ?_⟩
      have : x - y = step n := by
        have := ZMod.natCast_rightInverse (n := 2 * n - 1) (x - y)
        rw [← this, hv]; rfl
      have hxy : y + step n = x := by rw [← this]; ring
      rw [hxy]; exact hx
  · rintro ⟨x, hx, hx'⟩
    refine ⟨x, hx, x + step n, hx', ?_, ?_⟩
    · intro hc
      have : step n = 0 := by
        have := congrArg (fun z => z - x) hc
        simpa using this.symm
      have hv := val_step n hn
      rw [this, ZMod.val_zero] at hv
      omega
    · left
      have hxx : x + step n - x = step n := by ring
      rw [hxx, val_step n hn]
      omega

/-! ### Upper bound for bad colourings -/

lemma val_add_step_mod (n : ℕ) (hn : 3 ≤ n) [NeZero (2 * n - 1)] (x : ZMod (2 * n - 1)) :
    (x + step n).val % gcd3 n = x.val % gcd3 n := by
  rw [ZMod.val_add, val_step n hn]
  rw [Nat.mod_mod_of_dvd _ (gcd3_dvd_m n)]
  obtain ⟨c, hc⟩ := gcd3_dvd_succ n hn
  rw [hc, Nat.add_mul_mod_self_left]

lemma fiber_card (n : ℕ) (hn : 3 ≤ n) [NeZero (2 * n - 1)] (r : ℕ) (hr : r < gcd3 n) :
    ({x : ZMod (2 * n - 1) | x.val % gcd3 n = r} : Finset _).card = cyclen n := by
  have hg : 0 < gcd3 n := gcd3_pos n
  have hg3 : gcd3 n ≤ 3 := Nat.le_of_dvd (by norm_num) (gcd3_dvd_three n)
  have hm := m_eq_mul n
  have key : ∀ i : ℕ, i < cyclen n → r + gcd3 n * i < 2 * n - 1 := by
    intro i hi
    have h1 : gcd3 n * i ≤ gcd3 n * (cyclen n - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : gcd3 n * (cyclen n - 1) = gcd3 n * cyclen n - gcd3 n := by
      rw [Nat.mul_sub, Nat.mul_one]
    omega
  symm
  rw [← Finset.card_range (cyclen n)]
  refine Finset.card_nbij' (fun i => ((r + gcd3 n * i : ℕ) : ZMod (2 * n - 1)))
    (fun x => x.val / gcd3 n) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and]
    rw [ZMod.val_cast_of_lt (key i hi)]
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hx
    simp only [Finset.coe_range, Set.mem_Iio]
    have hv : x.val < gcd3 n * cyclen n := by rw [← hm]; exact ZMod.val_lt x
    exact Nat.div_lt_of_lt_mul hv
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    show ((((r + gcd3 n * i : ℕ) : ZMod (2 * n - 1))).val) / gcd3 n = i
    rw [ZMod.val_cast_of_lt (key i hi), Nat.add_mul_div_left _ _ hg, Nat.div_eq_of_lt hr]
    omega
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hx
    show (((r + gcd3 n * (x.val / gcd3 n) : ℕ) : ZMod (2 * n - 1))) = x
    have h : r + gcd3 n * (x.val / gcd3 n) = x.val := by
      rw [← hx]; exact Nat.mod_add_div _ _
    rw [h]
    exact ZMod.natCast_rightInverse x

lemma bad_fiber_card (n : ℕ) (hn : 3 ≤ n) [NeZero (2 * n - 1)] (S : Finset (ZMod (2 * n - 1)))
    (hS : ∀ x ∈ S, x + step n ∉ S) (r : ℕ) (hr : r < gcd3 n) :
    2 * ({x ∈ S | x.val % gcd3 n = r}).card ≤ cyclen n := by
  classical
  set T : Finset (ZMod (2 * n - 1)) := {x ∈ S | x.val % gcd3 n = r} with hT
  set F : Finset (ZMod (2 * n - 1)) := {x : ZMod (2 * n - 1) | x.val % gcd3 n = r} with hF
  have hTF : T ⊆ F := by
    intro x hx
    simp only [hT, Finset.mem_filter] at hx
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx.2
  have himg : T.image (fun x => x + step n) ⊆ F := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [hT, Finset.mem_filter] at hx
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [val_add_step_mod n hn]
    exact hx.2
  have hdisj : Disjoint T (T.image (fun x => x + step n)) := by
    rw [Finset.disjoint_right]
    intro y hy hyT
    simp only [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [hT, Finset.mem_filter] at hx hyT
    exact hS x hx.1 hyT.1
  have hcard : (T.image (fun x => x + step n)).card = T.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hunion : (T ∪ T.image (fun x => x + step n)).card ≤ F.card :=
    Finset.card_le_card (Finset.union_subset hTF himg)
  rw [Finset.card_union_of_disjoint hdisj, hcard] at hunion
  rw [fiber_card n hn r hr] at hunion
  omega

lemma bad_card_le (n : ℕ) (hn : 3 ≤ n) (S : Finset (ZMod (2 * n - 1)))
    (hS : ∀ x ∈ S, x + step n ∉ S) : 2 * S.card ≤ 2 * n - 1 - gcd3 n := by
  classical
  have : NeZero (2 * n - 1) := ⟨by omega⟩
  have hg : 0 < gcd3 n := gcd3_pos n
  have hpart : S.card = ∑ r ∈ Finset.range (gcd3 n), ({x ∈ S | x.val % gcd3 n = r}).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_range.2 (Nat.mod_lt _ hg))
  have hsum : 2 * S.card ≤ ∑ _r ∈ Finset.range (gcd3 n), (cyclen n - 1) := by
    rw [hpart, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro r hr
    have h := bad_fiber_card n hn S hS r (Finset.mem_range.1 hr)
    obtain ⟨t, ht⟩ := cyclen_odd n hn
    omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have hm := m_eq_mul n
  have h2 : gcd3 n * (cyclen n - 1) = 2 * n - 1 - gcd3 n := by
    rw [Nat.mul_sub, Nat.mul_one, ← hm]
  omega

/-! ### A maximal bad colouring -/

/-- A colouring which is not good and has the maximal possible number of black points: in each of
the `gcd3 n` cycles, take every other point. -/
def badSet (n : ℕ) : Finset (ZMod (2 * n - 1)) :=
  (Finset.range (gcd3 n) ×ˢ Finset.range ((cyclen n - 1) / 2)).image
    (fun p => ((p.1 + 3 * p.2 : ℕ) : ZMod (2 * n - 1)))

lemma badSet_card (n : ℕ) (hn : 3 ≤ n) : (badSet n).card = (2 * n - 1 - gcd3 n) / 2 := by
  have hm := m_eq_mul n
  obtain ⟨t, ht⟩ := cyclen_odd n hn
  have hinj : Set.InjOn (fun p : ℕ × ℕ => ((p.1 + 3 * p.2 : ℕ) : ZMod (2 * n - 1)))
      ↑(Finset.range (gcd3 n) ×ˢ Finset.range ((cyclen n - 1) / 2)) := by
    rintro ⟨r, i⟩ hp ⟨r', i'⟩ hp' h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hp'
    simp only at h
    have hdvd : ((2 * n - 1 : ℕ) : ℤ) ∣ ((r' + 3 * i' : ℕ) : ℤ) - ((r + 3 * i : ℕ) : ℤ) :=
      Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h)
    push_cast at hdvd
    have hg3 : (gcd3 n : ℤ) ∣ ((r' : ℤ) - r) := by
      have h1 : (gcd3 n : ℤ) ∣ ((2 * n - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (gcd3_dvd_m n)
      have h2 : (gcd3 n : ℤ) ∣ ((r' : ℤ) + 3 * i' - ((r : ℤ) + 3 * i)) := h1.trans hdvd
      have h3 : (gcd3 n : ℤ) ∣ (3 : ℤ) := Int.natCast_dvd_natCast.2 (gcd3_dvd_three n)
      have heq : ((r' : ℤ) - r)
          = ((r' : ℤ) + 3 * i' - ((r : ℤ) + 3 * i)) - 3 * ((i' : ℤ) - i) := by ring
      rw [heq]
      exact dvd_sub h2 (h3.mul_right _)
    have hrr : r = r' := by
      have hlt : |((r' : ℤ) - r)| < (gcd3 n : ℤ) := by
        rw [abs_lt]; constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hg3 hlt
      omega
    subst hrr
    have hdvd3 : ((2 * n - 1 : ℕ) : ℤ) ∣ 3 * ((i' : ℤ) - i) := by
      have heq : (3 : ℤ) * ((i' : ℤ) - i) = ((r : ℤ) + 3 * i' - ((r : ℤ) + 3 * i)) := by ring
      rw [heq]; exact hdvd
    have hc := cyclen_dvd_of_dvd_three_mul n _ hdvd3
    have hlt : |((i' : ℤ) - i)| < (cyclen n : ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have h0 := Int.eq_zero_of_abs_lt_dvd hc hlt
    have : i = i' := by omega
    simp [this]
  rw [badSet, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
    Finset.card_range]
  rcases gcd3_eq_one_or_three n with hg | hg <;> rw [hg] <;> rw [hg] at hm <;> omega

lemma badSet_bad (n : ℕ) (hn : 3 ≤ n) : ∀ x ∈ badSet n, x + step n ∉ badSet n := by
  intro x hx hx'
  have hm := m_eq_mul n
  obtain ⟨t, ht⟩ := cyclen_odd n hn
  simp only [badSet, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists] at hx hx'
  obtain ⟨r, i, ⟨hr, hi⟩, hxeq⟩ := hx
  obtain ⟨r', i', ⟨hr', hi'⟩, hxeq'⟩ := hx'
  have hcast : ((r + 3 * i + (n + 1) : ℕ) : ZMod (2 * n - 1))
      = ((r' + 3 * i' : ℕ) : ZMod (2 * n - 1)) := by
    have hsplit : ((r + 3 * i + (n + 1) : ℕ) : ZMod (2 * n - 1))
        = ((r + 3 * i : ℕ) : ZMod (2 * n - 1)) + step n := by
      unfold step; push_cast; ring
    rw [hsplit, hxeq]
    exact hxeq'.symm
  have hdvd : ((2 * n - 1 : ℕ) : ℤ) ∣ ((r' + 3 * i' : ℕ) : ℤ) - ((r + 3 * i + (n + 1) : ℕ) : ℤ) :=
    Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 hcast)
  push_cast at hdvd
  have hmc := m_cast n hn
  have hg3 : (gcd3 n : ℤ) ∣ ((r' : ℤ) - r) := by
    have h1 : (gcd3 n : ℤ) ∣ ((2 * n - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (gcd3_dvd_m n)
    have h2 : (gcd3 n : ℤ) ∣ ((r' : ℤ) + 3 * i' - ((r : ℤ) + 3 * i + ((n : ℤ) + 1))) := h1.trans hdvd
    have h3 : (gcd3 n : ℤ) ∣ (3 : ℤ) := Int.natCast_dvd_natCast.2 (gcd3_dvd_three n)
    have h5 : (gcd3 n : ℤ) ∣ ((n : ℤ) + 1) := by
      have h6 := Int.natCast_dvd_natCast.2 (gcd3_dvd_succ n hn)
      push_cast at h6
      exact h6
    have heq : ((r' : ℤ) - r)
        = ((r' : ℤ) + 3 * i' - ((r : ℤ) + 3 * i + ((n : ℤ) + 1))) - 3 * ((i' : ℤ) - i)
          + ((n : ℤ) + 1) := by ring
    rw [heq]
    exact dvd_add (dvd_sub h2 (h3.mul_right _)) h5
  have hrr : r = r' := by
    have hlt : |((r' : ℤ) - r)| < (gcd3 n : ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hg3 hlt
    omega
  subst hrr
  have hdvd2 : ((2 * n - 1 : ℕ) : ℤ) ∣ 3 * (2 * (i' : ℤ) - 2 * i - 1) := by
    have h2 := hdvd.mul_left 2
    have heq : (2 : ℤ) * ((r : ℤ) + 3 * i' - ((r : ℤ) + 3 * i + ((n : ℤ) + 1)))
        = 3 * (2 * (i' : ℤ) - 2 * i - 1) - (2 * (n : ℤ) - 1) := by ring
    rw [heq] at h2
    have h3 : ((2 * n - 1 : ℕ) : ℤ) ∣ (2 * (n : ℤ) - 1) := by rw [hmc]
    have h4 := dvd_add h2 h3
    simpa using h4
  have hc := cyclen_dvd_of_dvd_three_mul n _ hdvd2
  have hlt : |(2 * (i' : ℤ) - 2 * i - 1)| < (cyclen n : ℤ) := by
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hc hlt
  omega

/-! ### The answer -/

/-- **IMO 1990, Problem 2.**  For `n ≥ 3`, the smallest `k` such that every colouring of `k` of
the `2n-1` points is good is `n` if `3 ∤ 2n-1`, and `3 * ⌊(2n-1)/6⌋ + 1` if `3 ∣ 2n-1`. -/
theorem imo1990_p2 (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {k | ∀ S : Finset (ZMod (2 * n - 1)), S.card = k → IsGood n S} (answer n) := by
  have hm := m_eq_mul n
  obtain ⟨t, ht⟩ := cyclen_odd n hn
  have hgc : gcd3 n * (cyclen n - 1) = 2 * n - 1 - gcd3 n := by
    rw [Nat.mul_sub, Nat.mul_one, ← hm]
  have heven : 2 * ((2 * n - 1 - gcd3 n) / 2) = 2 * n - 1 - gcd3 n := by
    rw [← hgc, ht]
    have h1 : 2 * t + 1 - 1 = 2 * t := by omega
    rw [h1]
    have h2 : gcd3 n * (2 * t) = 2 * (gcd3 n * t) := by ring
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
  constructor
  · intro S hS
    by_contra hbad
    rw [good_iff n hn] at hbad
    push Not at hbad
    have hle := bad_card_le n hn S hbad
    rw [hS, answer_eq n hn] at hle
    omega
  · intro k hk
    by_contra hlt
    push Not at hlt
    rw [answer_eq n hn] at hlt
    have hcard := badSet_card n hn
    have hle : k ≤ (badSet n).card := by rw [hcard]; omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hle
    have hgood := hk B hBcard
    rw [good_iff n hn] at hgood
    obtain ⟨x, hx, hx'⟩ := hgood
    exact badSet_bad n hn x (hBsub hx) (hBsub hx')

end Imo1990P2
