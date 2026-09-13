import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open scoped Nat

/-- IMO 1994, Problem 1. -/
theorem imo_1994_p1 (m n : ℕ) (a : ℕ → ℕ) (h₀ : 0 < m ∧ 0 < n)
    (h₁ : Set.MapsTo a (Set.Icc 1 m) (Set.Icc 1 n))
    (h₂ : Set.InjOn a (Set.Icc 1 m))
    (h₃ :
      ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m,
        i ≤ j ∧ a i + a j ≤ n → ∃ k ∈ Finset.Icc 1 m, a i + a j = a k) :
    (n + 1 : ℚ) / 2 ≤ (∑ i ∈ Finset.Icc 1 m, a i : ℚ) / m := by
  classical
  let I : Finset ℕ := Finset.Icc 1 m
  let A : Finset ℕ := I.image a
  have hIcard : I.card = m := by
    simp [I, Nat.card_Icc]
  have hAcard : A.card = m := by
    calc
      A.card = I.card := by
        apply Finset.card_image_iff.mpr
        simpa [I] using h₂
      _ = m := hIcard
  have hA_closed {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hxy : x + y ≤ n) :
      x + y ∈ A := by
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    have hi' : i ∈ Finset.Icc 1 m := by simpa [I] using hi
    have hj' : j ∈ Finset.Icc 1 m := by simpa [I] using hj
    rcases le_total i j with hij | hji
    · rcases h₃ i hi' j hj' ⟨hij, hxy⟩ with ⟨k, hk, hk_eq⟩
      apply Finset.mem_image.mpr
      exact ⟨k, by simpa [I] using hk, hk_eq.symm⟩
    · rcases h₃ j hj' i hi' ⟨hji, by simpa [Nat.add_comm] using hxy⟩ with
        ⟨k, hk, hk_eq⟩
      apply Finset.mem_image.mpr
      exact ⟨k, by simpa [I] using hk, by simpa [Nat.add_comm] using hk_eq.symm⟩
  let e : Fin m ≃o {x // x ∈ A} := A.orderIsoOfFin hAcard
  let b : Fin m → ℕ := fun i => (e i : ℕ)
  have hb_mem (i : Fin m) : b i ∈ A := (e i).property
  have hb_bounds (i : Fin m) : b i ∈ Set.Icc 1 n := by
    rcases Finset.mem_image.mp (hb_mem i) with ⟨j, hj, hj_eq⟩
    rw [← hj_eq]
    apply h₁
    simpa [I] using hj
  have hpair (i : Fin m) : n + 1 ≤ b i + b (Fin.rev i) := by
    by_contra hbad
    have hsum : b i + b (Fin.rev i) ≤ n :=
      Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hbad)
    let emb : Fin (i.val + 1) → Fin m := fun t =>
      ⟨t.val, by omega⟩
    have hemb_le (t : Fin (i.val + 1)) : emb t ≤ i := by
      apply Fin.mk_le_mk.mpr
      omega
    have htranslated (t : Fin (i.val + 1)) :
        b (emb t) + b (Fin.rev i) ∈ A := by
      apply hA_closed (hb_mem _) (hb_mem _)
      have hmono : b (emb t) ≤ b i := by
        exact e.monotone (hemb_le t)
      omega
    let out : Fin (i.val + 1) → Fin m := fun t =>
      e.symm ⟨b (emb t) + b (Fin.rev i), htranslated t⟩
    have hout_gt (t : Fin (i.val + 1)) : Fin.rev i < out t := by
      rw [← e.lt_iff_lt]
      change (e (Fin.rev i)).val < (e (out t)).val
      have heout : e (out t) =
          ⟨b (emb t) + b (Fin.rev i), htranslated t⟩ := by
        simp [out]
      rw [heout]
      exact Nat.lt_add_of_pos_left (hb_bounds (emb t)).1
    let g : Fin (i.val + 1) → {k : Fin m // k ∈ Finset.Ioi (Fin.rev i)} :=
      fun t => ⟨out t, by simpa using hout_gt t⟩
    have hg : Function.Injective g := by
      intro t u htu
      have hout : out t = out u := congrArg Subtype.val htu
      have hsums : b (emb t) + b (Fin.rev i) = b (emb u) + b (Fin.rev i) := by
        simpa [out, b] using congrArg (fun z : Fin m => ((e z : {x // x ∈ A}) : ℕ)) hout
      have hb_eq : b (emb t) = b (emb u) := Nat.add_right_cancel hsums
      have hemb : emb t = emb u := by
        apply e.injective
        exact Subtype.ext hb_eq
      apply Fin.ext
      simpa [emb] using congrArg Fin.val hemb
    have hcard := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin, Fintype.card_coe, Fin.card_Ioi] at hcard
    rw [Fin.val_rev] at hcard
    omega
  let revEquiv : Fin m ≃ Fin m :=
    { toFun := Fin.rev
      invFun := Fin.rev
      left_inv := Fin.rev_involutive
      right_inv := Fin.rev_involutive }
  have hrev_sum : (∑ i : Fin m, b (Fin.rev i)) = ∑ i : Fin m, b i := by
    change (∑ i : Fin m, b (revEquiv i)) = ∑ i : Fin m, b i
    exact Equiv.sum_comp revEquiv b
  have hsum_nat : m * (n + 1) ≤ 2 * ∑ i : Fin m, b i := by
    calc
      m * (n + 1) = ∑ _i : Fin m, (n + 1) := by simp
      _ ≤ ∑ i : Fin m, (b i + b (Fin.rev i)) :=
        Finset.sum_le_sum fun i _ => hpair i
      _ = 2 * ∑ i : Fin m, b i := by
        rw [Finset.sum_add_distrib, hrev_sum]
        omega
  have hb_sum : (∑ i : Fin m, b i) = ∑ j ∈ I, a j := by
    calc
      (∑ i : Fin m, b i) = ∑ x : {x // x ∈ A}, (x : ℕ) := by
        simpa [b] using
          (Equiv.sum_comp e.toEquiv (fun x : {x // x ∈ A} => (x : ℕ)))
      _ = ∑ x ∈ A, x := by
        symm
        exact Finset.sum_subtype A (fun _ => Iff.rfl) id
      _ = ∑ j ∈ I, a j := by
        simpa [A] using
          (Finset.sum_image
            (fun x hx y hy hxy => h₂ (by simpa [I] using hx) (by simpa [I] using hy) hxy) :
            ∑ x ∈ I.image a, x = ∑ j ∈ I, a j)
  rw [hb_sum] at hsum_nat
  have hmQ : (0 : ℚ) < m := by exact_mod_cast h₀.1
  apply (div_le_div_iff₀ (by norm_num : (0 : ℚ) < 2) hmQ).2
  have hsumQ :
      (m : ℚ) * (n + 1) ≤ 2 * (∑ j ∈ I, a j : ℚ) := by
    calc
      (m : ℚ) * (n + 1) = ((m * (n + 1) : ℕ) : ℚ) := by norm_num
      _ ≤ ((2 * ∑ j ∈ I, a j : ℕ) : ℚ) := by
        exact_mod_cast hsum_nat
      _ = 2 * (∑ j ∈ I, a j : ℚ) := by
        norm_num
        exact map_sum (Nat.castRingHom ℚ) a I
  simpa [I, mul_comm] using hsumQ
