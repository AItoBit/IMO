import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

private lemma classify_four (m n j p : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hj : 0 < j) (hp : 0 < p)
    (h₁ : n + p = m * j) (h₂ : n * p = m + j) :
    (m, n) = (1, 2) ∨ (m, n) = (2, 1) ∨
    (m, n) = (1, 3) ∨ (m, n) = (3, 1) ∨
    (m, n) = (2, 2) ∨ (m, n) = (2, 5) ∨
    (m, n) = (5, 2) ∨ (m, n) = (3, 5) ∨
    (m, n) = (5, 3) := by
  by_cases hm1 : m = 1
  · subst m
    have hn2 : 2 ≤ n := by
      by_contra h
      have : n = 1 := by omega
      subst n
      norm_num at h₁ h₂
      omega
    have hp2 : 2 ≤ p := by
      by_contra h
      have : p = 1 := by omega
      subst p
      norm_num at h₁ h₂
      omega
    have hnp : n * p = n + p + 1 := by omega
    have hnpZ : (n : ℤ) * p = n + p + 1 := by exact_mod_cast hnp
    have hnonneg : 0 ≤ ((n : ℤ) - 2) * ((p : ℤ) - 2) :=
      mul_nonneg (by omega) (by omega)
    have hn3 : n ≤ 3 := by nlinarith
    have hp3 : p ≤ 3 := by nlinarith
    interval_cases n <;> interval_cases p <;> norm_num at h₁ h₂ ⊢
  · by_cases hj1 : j = 1
    · subst j
      have hn2 : 2 ≤ n := by
        by_contra h
        have : n = 1 := by omega
        subst n
        norm_num at h₁ h₂
        omega
      have hp2 : 2 ≤ p := by
        by_contra h
        have : p = 1 := by omega
        subst p
        norm_num at h₁ h₂
        omega
      have hnp : n * p = n + p + 1 := by omega
      have hnpZ : (n : ℤ) * p = n + p + 1 := by exact_mod_cast hnp
      have hnonneg : 0 ≤ ((n : ℤ) - 2) * ((p : ℤ) - 2) :=
        mul_nonneg (by omega) (by omega)
      have hn3 : n ≤ 3 := by nlinarith
      have hp3 : p ≤ 3 := by nlinarith
      interval_cases n <;> interval_cases p <;> norm_num at h₁ h₂ ⊢ <;> omega
    · by_cases hn1 : n = 1
      · subst n
        have hm2 : 2 ≤ m := by omega
        have hj2 : 2 ≤ j := by omega
        have hmj : m * j = m + j + 1 := by omega
        have hmjZ : (m : ℤ) * j = m + j + 1 := by exact_mod_cast hmj
        have hnonneg : 0 ≤ ((m : ℤ) - 2) * ((j : ℤ) - 2) :=
          mul_nonneg (by omega) (by omega)
        have hm3 : m ≤ 3 := by nlinarith
        have hj3 : j ≤ 3 := by nlinarith
        interval_cases m <;> interval_cases j <;> norm_num at h₁ h₂ ⊢
      · by_cases hp1 : p = 1
        · subst p
          have hm2 : 2 ≤ m := by omega
          have hj2 : 2 ≤ j := by omega
          have hmj : m * j = m + j + 1 := by omega
          have hmjZ : (m : ℤ) * j = m + j + 1 := by exact_mod_cast hmj
          have hnonneg : 0 ≤ ((m : ℤ) - 2) * ((j : ℤ) - 2) :=
            mul_nonneg (by omega) (by omega)
          have hm3 : m ≤ 3 := by nlinarith
          have hj3 : j ≤ 3 := by nlinarith
          interval_cases m <;> interval_cases j <;> norm_num at h₁ h₂ ⊢ <;> omega
        · have hm2 : 2 ≤ m := by omega
          have hn2 : 2 ≤ n := by omega
          have hj2 : 2 ≤ j := by omega
          have hp2 : 2 ≤ p := by omega
          have hsumprod :
              ((m : ℤ) - 1) * ((j : ℤ) - 1) +
                ((n : ℤ) - 1) * ((p : ℤ) - 1) = 2 := by
            nlinarith
          have hA : (m : ℤ) - 1 ≤ ((m : ℤ) - 1) * ((j : ℤ) - 1) := by
            have hnonneg : 0 ≤ ((m : ℤ) - 1) * ((j : ℤ) - 2) :=
              mul_nonneg (by omega) (by omega)
            nlinarith
          have hB : 1 ≤ ((n : ℤ) - 1) * ((p : ℤ) - 1) := by
            have hnonneg : 0 ≤ ((n : ℤ) - 2) * ((p : ℤ) - 1) :=
              mul_nonneg (by omega) (by omega)
            nlinarith
          have hm_le : m ≤ 2 := by nlinarith
          have : m = 2 := by omega
          subst m
          have : j = 2 := by nlinarith
          subst j
          have : n = 2 := by nlinarith
          subst n
          have : p = 2 := by nlinarith
          subst p
          simp

/-- IMO 1994, Problem 4. -/
theorem imo_1994_p4 (m n : ℕ) :
    (0 < m ∧ 0 < n ∧ (m * n - 1) ∣ (n ^ 3 + 1)) ↔
      (m, n) = (1, 2) ∨ (m, n) = (2, 1) ∨
      (m, n) = (1, 3) ∨ (m, n) = (3, 1) ∨
      (m, n) = (2, 2) ∨ (m, n) = (2, 5) ∨
      (m, n) = (5, 2) ∨ (m, n) = (3, 5) ∨
      (m, n) = (5, 3) := by
  constructor
  · rintro ⟨hm, hn, hdiv⟩
    rcases hdiv with ⟨k, hk⟩
    have hmn : 1 ≤ m * n := by nlinarith [Nat.mul_pos hm hn]
    have hkpos : 0 < k := by
      by_contra hk0
      have : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      simp at hk
    have heq : n ^ 3 + 1 + k = m * n * k := by
      calc
        n ^ 3 + 1 + k = (m * n - 1) * k + k := by rw [hk]
        _ = ((m * n - 1) + 1) * k := by ring
        _ = m * n * k := by rw [Nat.sub_add_cancel hmn]
    have hmod : (k + 1) % n = 0 := by
      have h := congrArg (fun x : ℕ => x % n) heq
      simpa [Nat.add_mod, Nat.mul_mod, Nat.pow_succ, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using h
    have hndvd : n ∣ k + 1 := Nat.dvd_of_mod_eq_zero hmod
    rcases hndvd with ⟨j, hj_eq⟩
    have hjpos : 0 < j := by
      have : 0 < n * j := by rw [← hj_eq]; omega
      exact Nat.pos_of_mul_pos_left this
    have hbig : n * (n ^ 2 + j + m) = n * (m * n * j) := by
      calc
        n * (n ^ 2 + j + m) = n ^ 3 + n * j + m * n := by ring
        _ = (n ^ 3 + 1 + k) + m * n := by rw [← hj_eq]; ring
        _ = m * n * k + m * n := by rw [heq]
        _ = m * n * (k + 1) := by ring
        _ = n * (m * n * j) := by rw [hj_eq]; ring
    have hquad : n ^ 2 + j + m = m * n * j :=
      Nat.mul_left_cancel hn hbig
    have hmul_le : n * n ≤ n * (m * j) := by
      calc
        n * n ≤ n ^ 2 + j + m := by
          simp [pow_two]
          omega
        _ = m * n * j := hquad
        _ = n * (m * j) := by ring
    have hn_le : n ≤ m * j := Nat.le_of_mul_le_mul_left hmul_le hn
    let p := m * j - n
    have hfirst : n + p = m * j := by
      exact Nat.add_sub_of_le hn_le
    have hsecond : n * p = m + j := by
      calc
        n * p = n * (m * j) - n * n := by
          simp [p, Nat.mul_sub_left_distrib]
        _ = (n ^ 2 + j + m) - n ^ 2 := by
          congr 1
          · calc
              n * (m * j) = m * n * j := by ring
              _ = n ^ 2 + j + m := hquad.symm
          · simp [pow_two]
        _ = m + j := by omega
    have hppos : 0 < p := by
      apply Nat.pos_of_mul_pos_left (a := n)
      rw [hsecond]
      omega
    exact classify_four m n j p hm hn hjpos hppos hfirst hsecond
  · rintro (h | h | h | h | h | h | h | h | h)
    all_goals
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      norm_num
