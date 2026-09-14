import Mathlib

noncomputable section

open scoped BigOperators

namespace IMO1998P2

def passes {b : ℕ} (v : Fin b → Bool) : ℕ :=
  (Finset.univ.filter (fun j => v j = true)).card

def failures {b : ℕ} (v : Fin b → Bool) : ℕ :=
  (Finset.univ.filter (fun j => v j = false)).card

def agreementCount {a b : ℕ}
    (vote : Fin a → Fin b → Bool) (j l : Fin b) : ℕ :=
  (Finset.univ.filter (fun i => vote i j = vote i l)).card

def agreement {a b : ℕ}
    (vote : Fin a → Fin b → Bool)
    (i : Fin a) (j l : Fin b) : ℝ :=
  if vote i j = vote i l then 1 else 0

lemma row_count {a b : ℕ}
    (vote : Fin a → Fin b → Bool) (i : Fin a) :
    (∑ j : Fin b, ∑ l : Fin b, agreement vote i j l) =
      (passes (vote i) : ℝ) ^ 2 +
      (failures (vote i) : ℝ) ^ 2 := by
  have h (j l : Fin b) :
      agreement vote i j l =
        (if vote i j = true then (1 : ℝ) else 0) *
          (if vote i l = true then 1 else 0) +
        (if vote i j = false then (1 : ℝ) else 0) *
          (if vote i l = false then 1 else 0) := by
    cases hj : vote i j <;> cases hl : vote i l <;>
      simp [agreement, hj, hl]
  simp_rw [
    h,
    Finset.sum_add_distrib,
    ← Finset.mul_sum,
    ← Finset.sum_mul
  ]
  simp [passes, failures, pow_two]

lemma split_count {b : ℕ} (v : Fin b → Bool) :
    passes v + failures v = b := by
  calc
    passes v + failures v =
        ∑ j : Fin b,
          ((if v j = true then 1 else 0) +
            (if v j = false then 1 else 0) : ℕ) := by
      simp [passes, failures, Finset.sum_add_distrib]
    _ = ∑ _j : Fin b, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      cases v j <;> simp
    _ = b := by simp

lemma odd_square_bound {p q b : ℕ}
    (hs : p + q = b) (hb : Odd b) :
    (b : ℝ) ^ 2 + 1 ≤
      2 * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
  obtain ⟨m, hm⟩ := hb
  have hne : p ≠ q := by omega
  have hsR : (p : ℝ) + q = b := by
    exact_mod_cast hs
  have hs2 :
      ((p : ℝ) + q) ^ 2 = (b : ℝ) ^ 2 :=
    congrArg (fun z : ℝ => z ^ 2) hsR
  rcases lt_or_gt_of_ne hne with h | h
  · have hgap : (p : ℝ) + 1 ≤ q := by
      exact_mod_cast h
    nlinarith [sq_nonneg ((q : ℝ) - p - 1)]
  · have hgap : (q : ℝ) + 1 ≤ p := by
      exact_mod_cast h
    nlinarith [sq_nonneg ((p : ℝ) - q - 1)]

theorem imo1998_p2
    (a b : ℕ) (k : ℝ)
    (ha : 0 < a)
    (hb : 3 ≤ b)
    (hodd : Odd b)
    (vote : Fin a → Fin b → Bool)
    (hpair : ∀ j l : Fin b, j ≠ l →
      (agreementCount vote j l : ℝ) ≤ k) :
    ((b : ℝ) - 1) / (2 * b) ≤ k / a := by
  have hlower (i : Fin a) :
      (b : ℝ) ^ 2 + 1 ≤
        2 * (∑ j : Fin b, ∑ l : Fin b,
          agreement vote i j l) := by
    rw [row_count]
    exact odd_square_bound (split_count (vote i)) hodd

  have hlower_sum :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin a)))
      (fun i _ => hlower i)

  have hlower_total :
      (a : ℝ) * ((b : ℝ) ^ 2 + 1) ≤
        2 * (∑ i : Fin a, ∑ j : Fin b, ∑ l : Fin b,
          agreement vote i j l) := by
    simpa [← Finset.mul_sum, mul_add] using hlower_sum

  have hupper (j l : Fin b) :
      (∑ i : Fin a, agreement vote i j l) ≤
        (if l = j then (a : ℝ) - k else 0) + k := by
    by_cases h : l = j
    · subst l
      simp [agreement]
    · simpa [agreement, agreementCount, h] using
        hpair j l (Ne.symm h)

  have hupper_sum :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin b)))
      (fun j _ =>
        Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin b)))
          (fun l _ => hupper j l))

  have hupper_total :
      (∑ j : Fin b, ∑ l : Fin b, ∑ i : Fin a,
        agreement vote i j l) ≤
        (b : ℝ) * ((a : ℝ) - k + b * k) := by
    simpa [Finset.sum_add_distrib, mul_add] using hupper_sum

  have hswap :
      (∑ i : Fin a, ∑ j : Fin b, ∑ l : Fin b,
        agreement vote i j l) =
        ∑ j : Fin b, ∑ l : Fin b, ∑ i : Fin a,
          agreement vote i j l := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]

  rw [hswap] at hlower_total

  have hbR : (3 : ℝ) ≤ b := by
    exact_mod_cast hb
  have haR : (0 : ℝ) < a := by
    exact_mod_cast ha
  have hb1 : 0 < (b : ℝ) - 1 := by
    linarith

  have hprod :
      ((b : ℝ) - 1) * ((a : ℝ) * ((b : ℝ) - 1)) ≤
        ((b : ℝ) - 1) * (2 * (b : ℝ) * k) := by
    nlinarith [hlower_total, hupper_total]

  have hcore :
      (a : ℝ) * ((b : ℝ) - 1) ≤ 2 * (b : ℝ) * k := by
    by_contra h
    have hp :=
      mul_pos hb1 (sub_pos.mpr (lt_of_not_ge h))
    nlinarith [hprod]

  apply
    (div_le_div_iff₀
      (by linarith : (0 : ℝ) < 2 * b) haR).2
  nlinarith [hcore]

end IMO1998P2
