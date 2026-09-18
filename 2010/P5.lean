import Mathlib

open Pi Equiv Function

namespace IMO2010P5

/-- A configuration is reachable from `(1,1,1,1,1,1)` by legal moves. -/
inductive Reachable : (Fin 6 → ℕ) → Prop
  | base : Reachable 1

  /-- Type 1:
  remove one coin from `Bᵢ` and put two in `Bᵢ₊₁`. -/
  | move1 {B i}
      (rB : Reachable B)
      (hi : i < 5)
      (pB : 0 < B i) :
      Reachable
        (B - Pi.single i 1 +
          Pi.single (i + 1) 2)

  /-- Type 2:
  remove one coin from `Bᵢ`, then swap `Bᵢ₊₁` and `Bᵢ₊₂`. -/
  | move2 {B i}
      (rB : Reachable B)
      (hi : i < 4)
      (pB : 0 < B i) :
      Reachable
        (B ∘ Equiv.swap (i + 1) (i + 2) -
          Pi.single i 1)

lemma single_succ {k : ℕ} {i : Fin 6} :
    (Pi.single (i + 1) k : Fin 6 → ℕ) i = 0 := by
  simp

lemma single_succ' {k : ℕ} {i : Fin 6} :
    (Pi.single i k : Fin 6 → ℕ) (i + 1) = 0 := by
  simp

lemma single_add_two {k : ℕ} {i : Fin 6} :
    (Pi.single (i + 2) k : Fin 6 → ℕ) i = 0 := by
  simp

namespace Reachable

/--
Repeated Type 1 moves empty `Bᵢ` and add twice its content
to `Bᵢ₊₁`.
-/
lemma push
    {B : Fin 6 → ℕ}
    {i : Fin 6}
    (rB : Reachable B)
    (hi : i < 5) :
    Reachable
      (B - Pi.single i (B i) +
        Pi.single (i + 1) (2 * B i)) := by

  obtain hc | hc := (B i).eq_zero_or_pos

  · rwa [
      hc,
      mul_zero,
      Pi.single_zero,
      Pi.single_zero,
      add_zero,
      tsub_zero
    ]

  · convert! (rB.move1 hi hc).push hi using 1

    ext k
    simp only [Pi.add_apply, Pi.sub_apply]

    rcases eq_or_ne k i with rfl | hk

    · simp_rw [
        Pi.single_eq_same,
        tsub_self,
        single_succ
      ]

    · simp_rw [
        Pi.single_eq_of_ne hk,
        tsub_zero
      ]

      rcases eq_or_ne k (i + 1) with rfl | hk'

      · simp_rw [
          Pi.single_eq_same,
          single_succ
        ]
        grind

      · simp_rw [
          Pi.single_eq_of_ne hk',
          add_zero
        ]

termination_by B i

/--
The small explicit preparation:
`(1,1,1,1,1,1) → (0,0,5,11,0,0)`.
-/
lemma five_eleven :
    Reachable
      (Pi.single 2 5 +
       Pi.single 3 11) := by

  have R :
      Reachable
        (Pi.single 1 3 +
         Pi.single 2 1 +
         Pi.single 3 1 +
         Pi.single 4 1 +
         Pi.single 5 1) := by
    convert! Reachable.base.push
      (show (0 : Fin 6) < 5 by decide) using 1
    decide

  replace R :
      Reachable
        (Pi.single 2 7 +
         Pi.single 3 1 +
         Pi.single 4 1 +
         Pi.single 5 1) := by
    convert! R.push
      (show (1 : Fin 6) < 5 by decide) using 1
    decide

  replace R :
      Reachable
        (Pi.single 2 7 +
         Pi.single 4 3 +
         Pi.single 5 1) := by
    convert! R.push
      (show (3 : Fin 6) < 5 by decide) using 1
    decide

  replace R :
      Reachable
        (Pi.single 2 7 +
         Pi.single 5 7) := by
    convert! R.push
      (show (4 : Fin 6) < 5 by decide) using 1
    decide

  replace R :
      Reachable
        (Pi.single 2 6 +
         Pi.single 3 2 +
         Pi.single 5 7) := by
    convert! R.move1
      (show (2 : Fin 6) < 5 by decide)
      (by decide) using 1
    decide

  replace R :
      Reachable
        (Pi.single 2 6 +
         Pi.single 3 1 +
         Pi.single 4 2 +
         Pi.single 5 7) := by
    convert! R.move1
      (show (3 : Fin 6) < 5 by decide)
      (by decide) using 1
    decide

  replace R :
      Reachable
        (Pi.single 2 6 +
         Pi.single 3 1 +
         Pi.single 5 11) := by
    convert! R.push
      (show (4 : Fin 6) < 5 by decide) using 1
    decide

  replace R :
      Reachable
        (Pi.single 2 6 +
         Pi.single 4 11) := by
    convert! R.move2
      (show (3 : Fin 6) < 4 by decide)
      (by decide) using 1
    decide

  convert! R.move2
    (show (2 : Fin 6) < 4 by decide)
    (by decide) using 1
  decide

/--
One `push` followed by Type 2 decrements `Bᵢ`
and doubles `Bᵢ₊₁`, provided `Bᵢ₊₂ = 0`.
-/
lemma double
    {B : Fin 6 → ℕ}
    {i : Fin 6}
    (rB : Reachable B)
    (hi : i < 4)
    (pB : 0 < B i)
    (zB : B (i + 2) = 0) :
    Reachable
      (B +
        Pi.single (i + 1) (B (i + 1)) -
        Pi.single i 1) := by

  convert!
    (rB.push (show i + 1 < 5 by grind)).move2
      hi
      (by
        rw [
          Pi.add_apply,
          Pi.sub_apply,
          single_succ
        ]
        grind)

  ext k
  simp only [
    Function.comp_apply,
    Pi.add_apply,
    Pi.sub_apply
  ]

  have hs (j : Fin 6) :
      j + 1 + 1 = j + 2 := by
    grind

  rcases eq_or_ne k i with rfl | hk

  · rw [
      Equiv.swap_apply_of_ne_of_ne
        (by simp)
        (by simp),
      single_succ,
      hs,
      single_add_two,
      Nat.sub_zero
    ]

  · rcases eq_or_ne k (i + 1) with rfl | hk'

    · grind [
        Equiv.swap_apply_left,
        Pi.single_eq_same
      ]

    · rw [Pi.single_eq_of_ne hk']

      rcases eq_or_ne k (i + 2) with rfl | hk''

      · grind [
          Equiv.swap_apply_right,
          Pi.single_eq_same,
          single_succ
        ]

      · rw [
          Equiv.swap_apply_of_ne_of_ne hk' hk'',
          Pi.single_eq_of_ne hk',
          hs,
          Pi.single_eq_of_ne hk'',
          tsub_zero
        ]

/--
Repeat `double` until `Bᵢ` is empty.
-/
lemma doubles
    {B : Fin 6 → ℕ}
    {i : Fin 6}
    (rB : Reachable B)
    (hi : i < 4)
    (zB : B (i + 2) = 0) :
    Reachable
      (Function.update
        (B - Pi.single i (B i))
        (i + 1)
        (B (i + 1) * 2 ^ B i)) := by

  obtain hc | hc := (B i).eq_zero_or_pos

  · rwa [
      hc,
      Pi.single_zero,
      tsub_zero,
      pow_zero,
      mul_one,
      Function.update_eq_self
    ]

  · convert!
      (rB.double hi hc zB).doubles
        hi
        (by
          rw [
            Pi.sub_apply,
            Pi.add_apply,
            Pi.single_eq_of_ne (by simp),
            zB,
            zero_add,
            zero_tsub
          ]) using 1

    ext k

    simp_rw [
      Pi.sub_apply,
      Pi.add_apply,
      Pi.single_eq_same,
      single_succ,
      single_succ',
      add_zero,
      tsub_zero,
      ← two_mul,
      ← mul_rotate,
      ← pow_succ,
      Nat.sub_add_cancel hc
    ]

    rcases eq_or_ne k (i + 1) with rfl | hk'

    · simp only [
        mul_comm,
        Function.update_self
      ]

    · simp_rw [
        Function.update_of_ne hk',
        Pi.sub_apply,
        Pi.add_apply,
        Pi.single_eq_of_ne hk',
        add_zero
      ]

      rcases eq_or_ne k i with rfl | hk

      · simp_rw [
          Pi.single_eq_same,
          tsub_self
        ]

      · simp_rw [
          Pi.single_eq_of_ne hk,
          tsub_zero
        ]

termination_by B i

/--
The compound exponential move

`(n,0,0) → (0,2^n,0)`.
-/
lemma exp
    {B : Fin 6 → ℕ}
    {i : Fin 6}
    (rB : Reachable B)
    (hi : i < 4)
    (pB : 0 < B i)
    (zB : B (i + 1) = 0)
    (zB' : B (i + 2) = 0) :
    Reachable
      (B -
        Pi.single i (B i) +
        Pi.single (i + 1) (2 ^ B i)) := by

  convert!
    (rB.move1
      (show i < 5 by grind)
      pB).doubles
      hi
      (by
        rw [
          Pi.add_apply,
          Pi.sub_apply,
          zB',
          Pi.single_eq_of_ne (by simp),
          tsub_zero,
          Pi.single_eq_of_ne (by simp),
          zero_add
        ]) using 1

  simp_rw [
    Pi.add_apply,
    Pi.sub_apply,
    Pi.single_eq_same,
    single_succ,
    single_succ',
    zB,
    zero_tsub,
    zero_add,
    add_zero,
    ← pow_succ',
    Nat.sub_add_cancel pB
  ]

  ext k
  simp only [
    Pi.add_apply,
    Pi.sub_apply
  ]

  rcases eq_or_ne k (i + 1) with rfl | hk'

  · grind [
      Function.update_self,
      Pi.single_eq_same
    ]

  · simp only [
      Function.update_of_ne hk',
      Pi.sub_apply,
      Pi.add_apply,
      Pi.single_eq_of_ne hk',
      add_zero
    ]

    rcases eq_or_ne k i with rfl | hk

    · simp_rw [
        Pi.single_eq_same,
        tsub_self
      ]

    · simp_rw [
        Pi.single_eq_of_ne hk,
        tsub_zero
      ]

/--
One stage in the power tower construction.
-/
lemma exp_mid
    {k n : ℕ}
    (h :
      Reachable
        (Pi.single 2 (k + 1) +
         Pi.single 3 n))
    (hn : 0 < n) :
    Reachable
      (Pi.single 2 k +
       Pi.single 3 (2 ^ n)) := by

  have md :=
    h.exp
      (show (3 : Fin 6) < 4 by decide)
      (by simp [hn])
      (by simp [Pi.add_apply, Pi.single_eq_of_ne])
      (by simp [Pi.add_apply, Pi.single_eq_of_ne])

  convert!
    md.move2
      (show (2 : Fin 6) < 4 by decide)
      (by
        simp only [
          Pi.add_apply,
          Pi.sub_apply,
          Pi.single_eq_same
        ]

        iterate 3
          rw [Pi.single_eq_of_ne (by decide)]

        simp) using 1

  ext i
  simp only [
    Pi.add_apply,
    Pi.sub_apply,
    Function.comp_apply,
    Fin.reduceAdd
  ]

  rcases eq_or_ne i 2 with rfl | i2

  · simp only [
      Fin.isValue,
      Pi.single_eq_same,
      ne_eq,
      Fin.reduceEq,
      not_false_eq_true,
      Pi.single_eq_of_ne,
      add_zero,
      zero_add,
      add_tsub_cancel_right
    ]

    rw [
      Equiv.swap_apply_of_ne_of_ne
        (by decide)
        (by decide),
      Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide)
    ]

    simp

  · simp only [
      Fin.isValue,
      Pi.single_eq_same,
      ne_eq,
      Fin.reduceEq,
      not_false_eq_true,
      Pi.single_eq_of_ne,
      zero_add,
      add_tsub_cancel_right,
      i2,
      tsub_zero
    ]

    rcases eq_or_ne i 3 with rfl | i3

    · rw [
        Equiv.swap_apply_left,
        Pi.single_eq_same,
        Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide),
        zero_add
      ]

    · rw [Pi.single_eq_of_ne i3]

      rcases eq_or_ne i 4 with rfl | i4

      · rw [
          Equiv.swap_apply_right,
          Pi.single_eq_of_ne (by decide),
          Pi.single_eq_of_ne (by decide),
          zero_add
        ]

      · rw [
          Equiv.swap_apply_of_ne_of_ne i3 i4,
          Pi.single_eq_of_ne i2,
          Pi.single_eq_of_ne i4,
          zero_add
        ]

/--
When all coins are in box 4, Type 2 can discard
as many coins as desired.
-/
lemma reduce
    {m n : ℕ}
    (h : Reachable (Pi.single 3 n))
    (hmn : m ≤ n) :
    Reachable (Pi.single 3 m) := by

  induction n, hmn using Nat.le_induction with

  | base =>
      exact h

  | succ k _ ih =>
      apply ih

      convert!
        h.move2
          (show (3 : Fin 6) < 4 by decide)
          k.succ_pos

      ext i

      simp only [
        Pi.sub_apply,
        Function.comp_apply
      ]

      rcases eq_or_ne i 3 with rfl | i3

      · rw [
          Equiv.swap_apply_of_ne_of_ne
            (by decide)
            (by decide)
        ]

        simp_rw [
          Pi.single_eq_same,
          add_tsub_cancel_right
        ]

      · simp_rw [
          Pi.single_eq_of_ne i3,
          tsub_zero
        ]

        rw [Pi.single_eq_of_ne]

        rw [Equiv.swap_apply_def]
        split_ifs <;> grind

/--
The explicit inequality needed to show that the power tower
is larger than the target.
-/
lemma tower_inequality
    {m n : ℕ}
    (hm : m = 2010)
    (hn : n = 11) :
    2010 ^ 2010 ^ m
      ≤ 2 ^ 2 ^ 2 ^ 2 ^ 2 ^ n := by

  calc
    2010 ^ 2010 ^ m
        ≤ 2 ^ (11 * 2010 ^ m) := by
            rw [pow_mul]
            gcongr <;> lia

    _ ≤ 2 ^ 2 ^ 2 ^ 2 ^ 2 ^ n := by

      apply Nat.pow_le_pow_right Nat.zero_lt_two

      calc
        11 * 2010 ^ m
            ≤ 2 ^ (4 + 11 * m) := by
                rw [pow_add, pow_mul]
                gcongr <;> lia

        _ ≤ 2 ^ 2 ^ 2 ^ 2 ^ n := by

          apply Nat.pow_le_pow_right Nat.zero_lt_two

          calc
            4 + 11 * m
                ≤ 2 ^ 2 ^ 2 ^ 2 := by
                    rw [hm]
                    lia

            _ ≤ 2 ^ 2 ^ 2 ^ n := by
                iterate 3
                  apply Nat.pow_le_pow_right
                    Nat.zero_lt_two
                lia

/--
Reach the state with exactly one quarter of the final
target in box 4.
-/
lemma quarter_target
    {m : ℕ}
    (hm : m = 2010) :
    Reachable
      (Pi.single
        3
        (2010 ^ 2010 ^ m / 4)) := by

  have R :=
    five_eleven.exp_mid (by lia)

  set n : ℕ := 11

  iterate 4
    replace R :=
      R.exp_mid (Nat.two_pow_pos _)

  rw [Pi.single_zero, zero_add] at R

  exact
    R.reduce
      ((Nat.div_le_self ..).trans
        (tower_inequality hm rfl))

end Reachable

/--
**IMO 2010 Problem 5.**

Yes: the target state is reachable.
-/
theorem imo2010_p5 :
    Reachable
      (Pi.single
        (5 : Fin 6)
        (2010 ^ 2010 ^ 2010)) := by

  open Reachable

-- Avoid deep kernel recursion in the giant exponent.
  set m : ℕ := 2010

  have hm :
      m = 2010 := by
    rfl

  convert!
    ((quarter_target hm).push
      (show (3 : Fin 6) < 5 by decide)).push
      (show (4 : Fin 6) < 5 by decide)

  simp only [
    Pi.single_eq_same,
    tsub_self,
    Fin.reduceAdd,
    zero_add,
    Pi.single_inj
  ]

  rw [
    ← mul_assoc,
    show 2 * 2 = 4 by rfl,
    mul_comm,
    Nat.div_mul_cancel
  ]

  trans 2010 ^ 2

  · lia

  · apply pow_dvd_pow

    trans 2010 ^ 1

    · lia

    · gcongr <;> lia

end IMO2010P5
