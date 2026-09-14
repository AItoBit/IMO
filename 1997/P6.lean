import Mathlib

/-!
# IMO 1997 Problem 6 : bounds for the binary partition function

`f n` is the number of ways of writing `n` as a sum of powers of `2`, where the
order of the summands is irrelevant (so `f 4 = 4`, coming from
`4, 2+2, 2+1+1, 1+1+1+1`).  In this file `f` is *defined* by its standard
recurrence

* `f 0 = 1`,
* `f (2m+1) = f (2m)`,
* `f (2m+2) = f (2m+1) + f (m+1)`,

and we prove the bounds of IMO 1997 Problem 6,
`2 ^ (n ^ 2 / 4) < f (2 ^ n) < 2 ^ (n ^ 2 / 2)`.

That `f` really counts binary partitions is proved in `RequestProject.Counting`.
-/

namespace BinaryPartition

/-- The binary partition function, defined by its recurrence:
`f 0 = 1`, `f (2m+1) = f (2m)` and `f (2m+2) = f (2m+1) + f (m+1)`. -/
def f : ℕ → ℕ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 1 then f n else f n + f ((n + 1) / 2)
decreasing_by all_goals omega

@[simp] theorem f_zero : f 0 = 1 := by rw [f]

/-- If `n` is odd then the sum representing `n` must contain a `1`, giving a bijection
between the representations of `2m+1` and those of `2m`. -/
theorem f_odd (m : ℕ) : f (2 * m + 1) = f (2 * m) := by
  rw [show 2 * m + 1 = 2 * m + 1 from rfl, f, if_pos (by omega)]

/-- For even numbers, the representations containing a `1` biject with those of `2m+1`
and those not containing a `1` biject (by halving) with those of `m+1`. -/
theorem f_even (m : ℕ) : f (2 * m + 2) = f (2 * m + 1) + f (m + 1) := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from rfl, f, if_neg (by omega)]
  congr 2
  omega

theorem f_pos (n : ℕ) : 0 < f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, f_odd]; simp
    | (k + 2) =>
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · subst hj
        rw [show j + j + 2 = 2 * j + 2 from by ring, f_even]
        exact Nat.lt_of_lt_of_le (ih (2 * j + 1) (by omega)) (Nat.le_add_right _ _)
      · subst hj
        rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 from by ring, f_odd]
        exact ih (2 * (j + 1)) (by omega)

theorem f_le_succ (n : ℕ) : f n ≤ f (n + 1) := by
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    rw [show j + j + 1 = 2 * j + 1 from by ring, f_odd, show j + j = 2 * j from by ring]
  · subst hj
    rw [show 2 * j + 1 + 1 = 2 * j + 2 from by ring, f_even]
    exact Nat.le_add_right _ _

theorem f_mono : Monotone f := monotone_nat_of_le_succ f_le_succ

/-- Iterating `f (2m+2) = f (2m) + f (m+1)` : `f (2m) = 1 + f 1 + f 2 + ⋯ + f m`. -/
theorem f_two_mul (m : ℕ) : f (2 * m) = 1 + ∑ i ∈ Finset.range m, f (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring, f_even, f_odd, ih,
      Finset.sum_range_succ]
    ring

/-- The basic exchange step: `f a + f b ≥ f (a+1) + f (b-1)` when `a + b` is odd. -/
theorem f_pair_step (a d : ℕ) : f (a + 1) + f (a + 2 * d) ≤ f a + f (a + 2 * d + 1) := by
  rcases Nat.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `a` even : both sides are equal
    subst hm
    rw [show m + m + 1 = 2 * m + 1 from by ring, f_odd, show m + m = 2 * m from by ring,
      show 2 * m + 2 * d + 1 = 2 * (m + d) + 1 from by ring, f_odd,
      show 2 * (m + d) = 2 * m + 2 * d from by ring]
  · -- `a` odd
    subst hm
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring, f_even,
      show 2 * m + 1 + 2 * d + 1 = 2 * (m + d) + 2 from by ring, f_even,
      show 2 * (m + d) + 1 = 2 * m + 1 + 2 * d from by ring]
    have : f (m + 1) ≤ f (m + d + 1) := f_mono (by omega)
    omega

/-- The chain `f 1 + f (2r) ≥ f 2 + f (2r-1) ≥ ⋯ ≥ f r + f (r+1)`, in the form
`f (k+i) + f (k+i+1) ≤ f k + f (k+2i+1)`. -/
theorem f_pair (k i : ℕ) : f (k + i) + f (k + i + 1) ≤ f k + f (k + 2 * i + 1) := by
  induction i generalizing k with
  | zero => simp
  | succ i ih =>
    have h1 : f (k + 1) + f (k + 2 * (i + 1)) ≤ f k + f (k + 2 * (i + 1) + 1) :=
      f_pair_step k (i + 1)
    have h2 : f (k + 1 + i) + f (k + 1 + i + 1) ≤ f (k + 1) + f (k + 1 + 2 * i + 1) := ih (k + 1)
    have e1 : k + 1 + i = k + (i + 1) := by ring
    have e2 : k + 1 + 2 * i + 1 = k + 2 * (i + 1) := by ring
    rw [e1, e2] at h2
    omega

/-- Key lemma: `f 1 + f 2 + ⋯ + f (2r) ≥ 2r * f r`. -/
theorem sum_two_mul_ge (r : ℕ) : 2 * r * f r ≤ ∑ i ∈ Finset.range (2 * r), f (i + 1) := by
  have hsplit : ∑ i ∈ Finset.range (2 * r), f (i + 1)
      = ∑ i ∈ Finset.range r, f (i + 1) + ∑ i ∈ Finset.range r, f (r + i + 1) := by
    rw [show 2 * r = r + r from by ring, Finset.sum_range_add]
  have hrefl : ∑ i ∈ Finset.range r, f (r + i + 1)
      = ∑ i ∈ Finset.range r, f (2 * r - i) := by
    rw [← Finset.sum_range_reflect (fun i => f (r + i + 1)) r]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    congr 1
    omega
  have hterm : ∀ i ∈ Finset.range r, 2 * f r ≤ f (i + 1) + f (2 * r - i) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    obtain ⟨j, hj⟩ : ∃ j, r = i + 1 + j := ⟨r - i - 1, by omega⟩
    have h := f_pair (i + 1) j
    have e1 : i + 1 + j = r := hj.symm
    have e2 : i + 1 + 2 * j + 1 = 2 * r - i := by omega
    rw [e1, e2] at h
    have hr : f r ≤ f (r + 1) := f_le_succ r
    omega
  calc 2 * r * f r = ∑ _i ∈ Finset.range r, 2 * f r := by
        rw [Finset.sum_const, Finset.card_range]; ring
    _ ≤ ∑ i ∈ Finset.range r, (f (i + 1) + f (2 * r - i)) := Finset.sum_le_sum hterm
    _ = ∑ i ∈ Finset.range r, f (i + 1) + ∑ i ∈ Finset.range r, f (2 * r - i) :=
        Finset.sum_add_distrib
    _ = ∑ i ∈ Finset.range (2 * r), f (i + 1) := by rw [hsplit, hrefl]

theorem sum_le (m : ℕ) : ∑ i ∈ Finset.range m, f (i + 1) ≤ m * f m := by
  calc ∑ i ∈ Finset.range m, f (i + 1) ≤ ∑ _i ∈ Finset.range m, f m :=
        Finset.sum_le_sum fun i hi => f_mono (by simp only [Finset.mem_range] at hi; omega)
    _ = m * f m := by rw [Finset.sum_const, Finset.card_range]; ring

/-- Upper estimate for the doubling step. -/
theorem step_upper (n : ℕ) : f (2 ^ (n + 1)) ≤ 1 + 2 ^ n * f (2 ^ n) := by
  have h : f (2 * 2 ^ n) = 1 + ∑ i ∈ Finset.range (2 ^ n), f (i + 1) := f_two_mul _
  have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [h2, h]
  exact Nat.add_le_add_left (sum_le _) 1

/-- Lower estimate for the double-doubling step. -/
theorem step_lower (n : ℕ) : 2 ^ (n + 1) * f (2 ^ n) < f (2 ^ (n + 2)) := by
  have h : f (2 * 2 ^ (n + 1)) = 1 + ∑ i ∈ Finset.range (2 ^ (n + 1)), f (i + 1) := f_two_mul _
  have h2 : (2 : ℕ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
  have h3 : 2 * 2 ^ n * f (2 ^ n) ≤ ∑ i ∈ Finset.range (2 * 2 ^ n), f (i + 1) :=
    sum_two_mul_ge (2 ^ n)
  rw [h2, h]
  have h4 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [h4]
  omega

/-! ### Small values -/

theorem f_one : f 1 = 1 := by have h := f_odd 0; norm_num at h; exact h

theorem f_two : f 2 = 2 := by
  have h := f_even 0; have h1 := f_one; norm_num at h; omega

theorem f_three : f 3 = 2 := by
  have h := f_odd 1; have h2 := f_two; norm_num at h; omega

theorem f_four : f 4 = 4 := by
  have h := f_even 1; have h2 := f_two; have h3 := f_three; norm_num at h; omega

theorem f_five : f 5 = 4 := by
  have h := f_odd 2; have h4 := f_four; norm_num at h; omega

theorem f_six : f 6 = 6 := by
  have h := f_even 2; have h3 := f_three; have h5 := f_five; norm_num at h; omega

theorem f_seven : f 7 = 6 := by
  have h := f_odd 3; have h6 := f_six; norm_num at h; omega

theorem f_eight : f 8 = 10 := by
  have h := f_even 3; have h4 := f_four; have h7 := f_seven; norm_num at h; omega

/-! ### The two bounds -/


/-- Arithmetic core of the induction step for the upper bound. -/
private theorem arith_upper {A B F G : ℕ} (hA : 8 ≤ A) (hF1 : 1 ≤ F) (hFB : F + 1 ≤ B)
    (hIH : F ^ 2 < B) (hG : G ≤ 1 + A * F) : G ^ 2 < 2 * A ^ 2 * B := by
  nlinarith

/-- Upper bound (in a form avoiding real exponents): `f (2^n)^2 < 2^(n^2)` for `n ≥ 3`. -/
theorem upper_sq (n : ℕ) (hn : 3 ≤ n) : f (2 ^ n) ^ 2 < 2 ^ (n ^ 2) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · -- `n + 1 = 3`
      have hn2 : n = 2 := by omega
      subst hn2
      norm_num [f_eight]
    · have IH := ih hn3
      have hG : f (2 ^ (n + 1)) ≤ 1 + 2 ^ n * f (2 ^ n) := step_upper n
      have hA8 : 8 ≤ 2 ^ n := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      have hF1 : 1 ≤ f (2 ^ n) := f_pos _
      have hFB : f (2 ^ n) + 1 ≤ 2 ^ (n ^ 2) := by nlinarith
      have hgoal : (2 : ℕ) ^ ((n + 1) ^ 2) = 2 * (2 ^ n) ^ 2 * 2 ^ (n ^ 2) := by
        rw [show (n + 1) ^ 2 = n * 2 + n ^ 2 + 1 from by ring, pow_add, pow_add, pow_mul]
        ring
      rw [hgoal]
      exact arith_upper hA8 hF1 hFB IH hG

/-- Lower bound (in a form avoiding real exponents): `2^(n^2) < f (2^n)^4` for `n ≥ 1`. -/
theorem lower_pow4 (n : ℕ) (hn : 1 ≤ n) : 2 ^ (n ^ 2) < f (2 ^ n) ^ 4 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 1 => norm_num [f_two]
    | 2 => norm_num [f_four]
    | (m + 3) =>
      have IH : 2 ^ ((m + 1) ^ 2) < f (2 ^ (m + 1)) ^ 4 := ih (m + 1) (by omega) (by omega)
      have hstep : 2 ^ (m + 2) * f (2 ^ (m + 1)) < f (2 ^ (m + 3)) := step_lower (m + 1)
      calc (2 : ℕ) ^ ((m + 3) ^ 2) = (2 ^ (m + 2)) ^ 4 * 2 ^ ((m + 1) ^ 2) := by
            rw [← pow_mul, ← pow_add]
            congr 1
            ring
        _ < (2 ^ (m + 2)) ^ 4 * f (2 ^ (m + 1)) ^ 4 :=
            Nat.mul_lt_mul_of_pos_left IH (by positivity)
        _ = (2 ^ (m + 2) * f (2 ^ (m + 1))) ^ 4 := by rw [mul_pow]
        _ ≤ f (2 ^ (m + 3)) ^ 4 := Nat.pow_le_pow_left (le_of_lt hstep) 4

/-- **IMO 1997, Problem 6.** For `n ≥ 3`,
`2 ^ (n ^ 2 / 4) < f (2 ^ n) < 2 ^ (n ^ 2 / 2)`. -/
theorem imo1997_p6 (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) ^ 2 / 4) < (f (2 ^ n) : ℝ) ∧
      (f (2 ^ n) : ℝ) < (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) := by
  constructor
  · have h := lower_pow4 n (by omega)
    have h' : ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 4)) ^ (4 : ℕ) < (f (2 ^ n) : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 4)) 4, ← Real.rpow_mul (by norm_num),
        show (n : ℝ) ^ 2 / 4 * ((4 : ℕ) : ℝ) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      exact_mod_cast h
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h'
  · have h := upper_sq n hn
    have h' : (f (2 ^ n) : ℝ) ^ (2 : ℕ) < ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 2)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) ^ 2 / 2)) 2, ← Real.rpow_mul (by norm_num),
        show (n : ℝ) ^ 2 / 2 * ((2 : ℕ) : ℝ) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      exact_mod_cast h
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h'

end BinaryPartition
