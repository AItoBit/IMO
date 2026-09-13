import Mathlib

/-!
# IMO 1995, Problem 4

The positive real numbers `x 0, x 1, …, x 1995` satisfy `x 0 = x 1995` and

  `x (i-1) + 2 / x (i-1) = 2 * x i + 1 / x i`  for `i = 1, 2, …, 1995`.

The maximum value that `x 0` can have is `2 ^ 997`.

The proof rewrites the recursion as `(2 * x i - x (i-1)) * (1 - x (i-1) * x i) = 0`, so each
step either halves or inverts the previous term.  Passing to `y i = logb 2 (x i)`, each step
is `y i = y (i-1) - 1` or `y i = -y (i-1)`, and after `N` steps one has
`y N = (-1) ^ (c + N) * y 0 + c` for an integer `c` with `|c| ≤ N`; the parity coupling between
the sign and `c + N` is what forces the answer.  With `N = 1995` and `y 1995 = y 0`, the sign
must be `-1` (otherwise `c = 0` while `c + 1995` is even), so `c` is even, `c ≤ 1994` and
`y 0 = c / 2 ≤ 997`.
-/

namespace IMO1995P4

open Real

/-- The constraints of the problem on a sequence `x : ℕ → ℝ`. -/
def Constraint (x : ℕ → ℝ) : Prop :=
  (∀ i ≤ 1995, 0 < x i) ∧ x 0 = x 1995 ∧
    ∀ i, 1 ≤ i → i ≤ 1995 → x (i - 1) + 2 / x (i - 1) = 2 * x i + 1 / x i

/-- The recursion forces each step to either halve the previous term or invert it. -/
lemma step_dichotomy {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a + 2 / a = 2 * b + 1 / b) : b = a / 2 ∨ b = 1 / a := by
  have ha' := ha.ne'
  have hb' := hb.ne'
  have key : (2 * b - a) * (1 - a * b) = 0 := by field_simp at h; nlinarith [h]
  rcases mul_eq_zero.1 key with h1 | h1
  · left; linarith
  · right; field_simp; nlinarith

/-- Sign/shift tracking: if each step either subtracts `1` or flips the sign, then after `N`
steps `y N = (-1) ^ (c + N) * y 0 + c` for some integer `c` with `|c| ≤ N`.  The coupling
between the sign and the parity of `c + N` is the crucial point. -/
lemma sign_track (y : ℕ → ℝ) (N : ℕ)
    (h : ∀ i < N, y (i + 1) = y i - 1 ∨ y (i + 1) = -y i) :
    ∃ c : ℤ, |c| ≤ (N : ℤ) ∧ y N = (-1 : ℝ) ^ (c + (N : ℤ)) * y 0 + c := by
  induction N with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc, hy⟩ := ih fun i hi => h i (by omega)
    rw [abs_le] at hc
    have hne : (-1 : ℝ) ≠ 0 := by norm_num
    rcases h n (by omega) with hstep | hstep
    · refine ⟨c - 1, by rw [abs_le]; push_cast; omega, ?_⟩
      have e1 : (c - 1) + (((n + 1 : ℕ)) : ℤ) = c + (n : ℤ) := by push_cast; ring
      rw [hstep, hy, e1]
      push_cast
      ring
    · refine ⟨-c, by rw [abs_le]; push_cast; omega, ?_⟩
      have hodd : Odd ((1 : ℤ) - 2 * c) := ⟨-c, by ring⟩
      have e1 : (-c) + (((n + 1 : ℕ)) : ℤ) = (c + (n : ℤ)) + (1 - 2 * c) := by push_cast; ring
      have hsign : (-1 : ℝ) ^ ((c + (n : ℤ)) + (1 - 2 * c)) = -((-1 : ℝ) ^ (c + (n : ℤ))) := by
        rw [zpow_add₀ hne, hodd.neg_one_zpow]; ring
      rw [hstep, e1, hsign, hy]
      push_cast
      ring

/-- The extremal sequence: `x i = 2 ^ (997 - i)` for `i ≤ 1994`, and `x 1995 = 2 ^ 997`. -/
noncomputable def witness : ℕ → ℝ :=
  fun i => if i ≤ 1994 then (2 : ℝ) ^ (997 - (i : ℤ)) else (2 : ℝ) ^ (997 : ℤ)

lemma witness_pos (i : ℕ) : 0 < witness i := by
  unfold witness; split <;> positivity

lemma witness_zero : witness 0 = (2 : ℝ) ^ (997 : ℕ) := by
  unfold witness
  norm_num

lemma witness_constraint : Constraint witness := by
  refine ⟨fun i _ => witness_pos i, ?_, ?_⟩
  · unfold witness
    norm_num
  · intro i h1 h2
    have hpos := witness_pos (i - 1)
    rcases Nat.lt_or_ge i 1995 with hi | hi
    · -- halving step
      have hprev : witness (i - 1) = 2 * witness i := by
        unfold witness
        have h_i1 : i - 1 ≤ 1994 := by omega
        have h_i2 : i ≤ 1994 := by omega
        simp [h_i1, h_i2]
        rw [show ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 by omega]
        rw [show (997 : ℤ) - ((i : ℤ) - 1) = 1 + (997 - (i : ℤ)) by ring, zpow_add₀ (by norm_num)]
        norm_num
      have hi' : 0 < witness i := witness_pos i
      rw [hprev] at hpos ⊢
      field_simp
    · -- inversion step at `i = 1995`
      have hi5 : i = 1995 := by omega
      subst hi5
      have hprev : witness 1994 = 1 / witness 1995 := by
        unfold witness
        norm_num
      have h5 : 0 < witness 1995 := witness_pos 1995
      norm_num at hprev ⊢
      rw [hprev]
      field_simp
      ring

/-- Any admissible sequence satisfies `x 0 ≤ 2 ^ 997`. -/
lemma upper_bound {x : ℕ → ℝ} (hx : Constraint x) : x 0 ≤ (2 : ℝ) ^ (997 : ℕ) := by
  obtain ⟨hpos, hcyc, hrec⟩ := hx
  have hstep : ∀ i < 1995, x (i + 1) = x i / 2 ∨ x (i + 1) = 1 / x i := by
    intro i hi
    have h := hrec (i + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at h
    exact step_dichotomy (hpos i (by omega)) (hpos (i + 1) (by omega)) h
  set y : ℕ → ℝ := fun i => Real.logb 2 (x i) with hy
  have hystep : ∀ i < 1995, y (i + 1) = y i - 1 ∨ y (i + 1) = -y i := by
    intro i hi
    have hxi : 0 < x i := hpos i (by omega)
    rcases hstep i hi with h | h
    · left
      show Real.logb 2 (x (i + 1)) = Real.logb 2 (x i) - 1
      rw [h, Real.logb_div hxi.ne' (by norm_num)]
      simp
    · right
      show Real.logb 2 (x (i + 1)) = -Real.logb 2 (x i)
      rw [h, one_div, Real.logb_inv]
  obtain ⟨c, hc, hyN⟩ := sign_track y 1995 hystep
  have hy0 : y 1995 = y 0 := by
    show Real.logb 2 (x 1995) = Real.logb 2 (x 0)
    rw [hcyc]
  rw [abs_le] at hc
  push_cast at hc
  have hy0le : y 0 ≤ 997 := by
    rcases Int.even_or_odd (c + ((1995 : ℕ) : ℤ)) with hev | hodd
    · -- the sign is `+1`, forcing `c = 0` and hence `1995` even: impossible
      rw [hev.neg_one_zpow, hy0] at hyN
      have hc0 : (c : ℝ) = 0 := by linarith
      have hc0' : c = 0 := by exact_mod_cast hc0
      rw [hc0'] at hev
      norm_num at hev
    · -- the sign is `-1`, so `2 * y 0 = c` with `c` even and `c ≤ 1994`
      rw [hodd.neg_one_zpow, hy0] at hyN
      have h2 : 2 * y 0 = (c : ℝ) := by linarith
      have hceven : Even c := by
        obtain ⟨k, hk⟩ := hodd
        push_cast at hk
        exact ⟨k - 997, by omega⟩
      have hcle : c ≤ 1994 := by
        obtain ⟨k, hk⟩ := hceven
        omega
      have hcr : (c : ℝ) ≤ 1994 := by exact_mod_cast hcle
      linarith
  have hx0 : 0 < x 0 := hpos 0 (by omega)
  have hrew : x 0 = (2 : ℝ) ^ (y 0) := (Real.rpow_logb (by norm_num) (by norm_num) hx0).symm
  rw [hrew, show ((2 : ℝ) ^ (997 : ℕ)) = (2 : ℝ) ^ ((997 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hy0le)

/-- **IMO 1995, Problem 4.** The maximum value that `x 0` can have is `2 ^ 997`. -/
theorem imo1995_p4 :
    IsGreatest {a : ℝ | ∃ x : ℕ → ℝ, Constraint x ∧ x 0 = a} ((2 : ℝ) ^ (997 : ℕ)) := by
  refine ⟨⟨witness, witness_constraint, witness_zero⟩, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  exact upper_bound hx

end IMO1995P4
