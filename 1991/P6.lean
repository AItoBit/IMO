import Mathlib

open scoped Real

namespace IMO1991P6

/-- IMO 1991, Problem 6. -/
theorem imo_1991_p6 (a : ℝ) (ha : 1 < a) :
    ∃ x : ℕ → ℝ, (∃ C, ∀ i, |x i| ≤ C) ∧
      ∀ i j, i ≠ j → 1 ≤ |x i - x j| * |(i : ℤ) - j| ^ a := by
  let r : ℝ := Real.sqrt 2
  let C : ℝ := 2 * r + 1
  let x : ℕ → ℝ := fun n ↦ C * Int.fract ((n : ℝ) * r)

  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hr2 : r ^ 2 = 2 := by
    dsimp [r]
    norm_num
  have hCpos : 0 < C := by
    dsimp [C]
    positivity

  refine ⟨x, ⟨C, ?_⟩, ?_⟩
  · intro i
    have hf0 : 0 ≤ Int.fract ((i : ℝ) * r) := Int.fract_nonneg _
    have hf1 : Int.fract ((i : ℝ) * r) < 1 := Int.fract_lt_one _
    have hx0 : 0 ≤ x i := mul_nonneg hCpos.le hf0
    rw [abs_of_nonneg hx0]
    dsimp [x]
    nlinarith [mul_lt_mul_of_pos_left hf1 hCpos]
  · have hsep : ∀ i j : ℕ, j < i →
        1 ≤ |x i - x j| * ((i - j : ℕ) : ℝ) := by
      intro i j hji
      let n : ℕ := i - j
      let m : ℤ := ⌊(i : ℝ) * r⌋ - ⌊(j : ℝ) * r⌋
      let d : ℝ := (n : ℝ) * r - (m : ℝ)

      have hn : 0 < n := Nat.sub_pos_of_lt hji
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hirr : Irrational ((n : ℝ) * r) := by
        rw [irrational_natCast_mul_iff]
        exact ⟨Nat.ne_of_gt hn, by simpa [r] using irrational_sqrt_two⟩
      have hd : d ≠ 0 := by
        dsimp [d]
        exact sub_ne_zero.mpr (hirr.ne_int m)
      have hplus : (n : ℝ) * r + (m : ℝ) ≠ 0 := by
        have hne : (n : ℝ) * r ≠ ((-m : ℤ) : ℝ) := hirr.ne_int (-m)
        intro hzero
        apply hne
        push_cast
        linarith

      have hz : 2 * (n : ℤ) ^ 2 - m ^ 2 ≠ 0 := by
        intro hz0
        have hz0r :
            (2 : ℝ) * (n : ℝ) ^ 2 - (m : ℝ) ^ 2 = 0 := by
          exact_mod_cast hz0
        have hprod : d * ((n : ℝ) * r + (m : ℝ)) = 0 := by
          dsimp [d]
          nlinarith
        exact (mul_ne_zero hd hplus) hprod

      have hzabs :
          (1 : ℝ) ≤ |((2 * (n : ℤ) ^ 2 - m ^ 2 : ℤ) : ℝ)| := by
        have hz' := Int.one_le_abs hz
        exact_mod_cast hz'
      have hfactor :
          ((2 * (n : ℤ) ^ 2 - m ^ 2 : ℤ) : ℝ) =
            d * ((n : ℝ) * r + (m : ℝ)) := by
        push_cast
        dsimp [d]
        nlinarith
      rw [hfactor, abs_mul] at hzabs

      have hfloor : ⌊(j : ℝ) * r⌋ ≤ ⌊(i : ℝ) * r⌋ := by
        apply Int.floor_mono
        have hijR : (j : ℝ) ≤ i := by exact_mod_cast hji.le
        exact mul_le_mul_of_nonneg_right hijR hr0
      
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by
        dsimp [m]
        push_cast
        exact_mod_cast sub_nonneg.mpr hfloor
      have hm_upper : (m : ℝ) ≤ (n : ℝ) * r + 1 := by
        have hfi := Int.floor_le ((i : ℝ) * r)
        have hfj := Int.lt_floor_add_one ((j : ℝ) * r)
        dsimp [m, n]
        rw [Nat.cast_sub hji.le]
        push_cast
        linarith
      have hdenom :
          |(n : ℝ) * r + (m : ℝ)| ≤ (n : ℝ) * C := by
        rw [abs_of_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg n) hr0) hm0)]
        dsimp [C]
        nlinarith
      have hd_bound : (1 : ℝ) ≤ C * |d| * (n : ℝ) := by
        calc
          (1 : ℝ) ≤ |d| * |(n : ℝ) * r + (m : ℝ)| := hzabs
          _ ≤ |d| * ((n : ℝ) * C) :=
            mul_le_mul_of_nonneg_left hdenom (abs_nonneg d)
          _ = C * |d| * (n : ℝ) := by ring

      have hxdiff : x i - x j = C * d := by
        have hm_cast :
            (m : ℝ) = (⌊(i : ℝ) * r⌋ : ℝ) - (⌊(j : ℝ) * r⌋ : ℝ) := by
          dsimp [m]
          norm_cast
        calc
          x i - x j =
              C * ((i : ℝ) * r - (⌊(i : ℝ) * r⌋ : ℝ)) -
                C * ((j : ℝ) * r - (⌊(j : ℝ) * r⌋ : ℝ)) := rfl
          _ = C * (((i : ℝ) - (j : ℝ)) * r -
                ((⌊(i : ℝ) * r⌋ : ℝ) - (⌊(j : ℝ) * r⌋ : ℝ))) := by ring
          _ = C * ((n : ℝ) * r - (m : ℝ)) := by
            rw [hm_cast, Nat.cast_sub hji.le]
          _ = C * d := rfl
      rw [hxdiff, abs_mul, abs_of_pos hCpos]
      exact hd_bound

    intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hlin := hsep j i hij'
      have hpow : ((j - i : ℕ) : ℝ) ≤ ((j - i : ℕ) : ℝ) ^ a :=
        Real.self_le_rpow_of_one_le (by exact_mod_cast Nat.sub_pos_of_lt hij') ha.le
      have hmul := mul_le_mul_of_nonneg_left hpow (abs_nonneg (x j - x i))
      
      -- Isolate subtraction before applying absolute value theorems
      have hbaseZ : |(i : ℤ) - j| = ((j - i : ℕ) : ℤ) := by
        have h_sub : (i : ℤ) - j = -((j - i : ℕ) : ℤ) := by omega
        rw [h_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
      
      have hbase : ((|(i : ℤ) - j| : ℤ) : ℝ) = ((j - i : ℕ) : ℝ) := by
        exact_mod_cast hbaseZ
      rw [abs_sub_comm] at hlin
      calc
        (1 : ℝ) ≤ |x i - x j| * ((j - i : ℕ) : ℝ) := hlin
        _ ≤ |x i - x j| * ((j - i : ℕ) : ℝ) ^ a := by
          simpa [abs_sub_comm] using hmul
        _ = |x i - x j| * |(i : ℤ) - j| ^ a := by rw [hbase]
        
    · have hlin := hsep i j hji'
      have hpow : ((i - j : ℕ) : ℝ) ≤ ((i - j : ℕ) : ℝ) ^ a :=
        Real.self_le_rpow_of_one_le (by exact_mod_cast Nat.sub_pos_of_lt hji') ha.le
      have hmul := mul_le_mul_of_nonneg_left hpow (abs_nonneg (x i - x j))
      
      -- Isolate subtraction before applying absolute value theorems
      have hbaseZ : |(i : ℤ) - j| = ((i - j : ℕ) : ℤ) := by
        have h_sub : (i : ℤ) - j = ((i - j : ℕ) : ℤ) := by omega
        rw [h_sub, abs_of_nonneg (Nat.cast_nonneg _)]
        
      have hbase : ((|(i : ℤ) - j| : ℤ) : ℝ) = ((i - j : ℕ) : ℝ) := by
        exact_mod_cast hbaseZ
      calc
        (1 : ℝ) ≤ |x i - x j| * ((i - j : ℕ) : ℝ) := hlin
        _ ≤ |x i - x j| * ((i - j : ℕ) : ℝ) ^ a := hmul
        _ = |x i - x j| * |(i : ℤ) - j| ^ a := by rw [hbase]

end IMO1991P6
