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
# IMO 2006, Problem 5

Let `P(x)` be a polynomial of degree `n > 1` with integer coefficients and let `k` be a positive
integer. Consider the polynomial `Q(x) = P(P(...P(P(x))...))`, where `P` occurs `k` times.
Prove that there are at most `n` integers `t` such that `Q(t) = t`.

The formalization below states the problem for `P : ℤ[X]` with `1 < P.natDegree`, with `Q` given by
`Imo2006P5.iterComp P k = P.comp^[k] X`.  The final results are
`Imo2006P5.imo2006_p5` (any finite set of solutions has at most `n` elements),
`Imo2006P5.imo2006_p5_setOf_finite` and `Imo2006P5.imo2006_p5_ncard` (the set of solutions is
finite and has at most `n` elements).

The proof follows the solution on the AoPS wiki (the same route as the corresponding entry in
Mathlib's archive of IMO problems): the key step is that `P^[k] t = t` forces
`P (P t) = t`, which reduces the problem to `k = 2`; that case is handled by exhibiting a nonzero
polynomial of degree `n` vanishing at every solution.
-/

namespace Imo2006P5

open Function Polynomial

/-- The `k`-fold composite `Q(x) = P(P(...P(x)...))` of a polynomial `P` with itself. -/
noncomputable def iterComp (P : ℤ[X]) (k : ℕ) : ℤ[X] := P.comp^[k] X

@[simp] lemma iterComp_zero (P : ℤ[X]) : iterComp P 0 = X := rfl

lemma eval_iterComp (P : ℤ[X]) (k : ℕ) (t : ℤ) :
    (iterComp P k).eval t = (fun x => P.eval x)^[k] t := by
  simp [iterComp, Polynomial.iterate_comp_eval]

/-- If every entry of a cyclic list of integers divides the next one, then all the entries have
the same absolute value. -/
lemma natAbs_eq_of_chain_dvd {l : Cycle ℤ} {x y : ℤ} (hl : l.Chain (· ∣ ·)) (hx : x ∈ l)
    (hy : y ∈ l) : x.natAbs = y.natAbs := by
  rw [Cycle.chain_iff_pairwise] at hl
  exact Int.natAbs_eq_of_dvd_dvd (hl x hx y hy) (hl y hy x hx)

/-- If `a ≠ b`, `|c - a| = |d - b|` and `|c - b| = |d - a|`, then `a + b = c + d`. -/
lemma add_eq_add_of_natAbs_eq_of_natAbs_eq {a b c d : ℤ} (hne : a ≠ b)
    (h₁ : (c - a).natAbs = (d - b).natAbs) (h₂ : (c - b).natAbs = (d - a).natAbs) :
    a + b = c + d := by
  rcases Int.natAbs_eq_natAbs_iff.1 h₁ with h₁ | h₁
  · rcases Int.natAbs_eq_natAbs_iff.1 h₂ with h₂ | h₂
    · exact absurd (by linarith : a = b) hne
    · linarith
  · linarith

/-- The key lemma: if `t` is a periodic point of `x ↦ P(x)`, then `P(P(t)) = t`. -/
lemma eval_eval_eq_of_isPeriodicPt {P : ℤ[X]} {t : ℤ}
    (ht : t ∈ periodicPts fun x => P.eval x) : P.eval (P.eval t) = t := by
  have key : IsPeriodicPt (fun x => P.eval x) 2 t := by
    -- the cycle `[P t - t, P (P t) - P t, ...]`
    set f : ℤ → ℤ := fun x => P.eval x with hf
    let C : Cycle ℤ := (periodicOrbit f t).map fun x => f x - x
    have HC : ∀ {n : ℕ}, f^[n + 1] t - f^[n] t ∈ C := by
      intro n
      rw [Cycle.mem_map, Function.iterate_succ_apply']
      exact ⟨_, iterate_mem_periodicOrbit ht n, rfl⟩
    -- all entries of `C` divide one another
    have Hdvd : C.Chain (· ∣ ·) := by
      rw [Cycle.chain_map, periodicOrbit_chain' _ ht]
      intro n
      convert sub_dvd_eval_sub (f^[n + 1] t) (f^[n] t) P using 2 <;>
        rw [Function.iterate_succ_apply']
    -- hence all entries of `C` have the same absolute value
    have Habs : ∀ m n : ℕ, (f^[m + 1] t - f^[m] t).natAbs = (f^[n + 1] t - f^[n] t).natAbs :=
      fun _ _ => natAbs_eq_of_chain_dvd Hdvd HC HC
    by_cases HC' : C.Chain (· = ·)
    · -- all entries of `C` are equal
      have Heq : ∀ m n : ℕ, f^[m + 1] t - f^[m] t = f^[n + 1] t - f^[n] t :=
        fun _ _ => Cycle.chain_iff_pairwise.1 HC' _ HC _ HC
      -- consequently `P^[n+1] t - t` has the same sign as `P t - t`
      have IH : ∀ n : ℕ, (f^[n + 1] t - t).sign = (f t - t).sign := by
        intro n
        induction n with
        | zero => rfl
        | succ n IH =>
          refine Eq.trans ?_ (Int.sign_add_eq_of_sign_eq IH)
          have H : f^[n + 1 + 1] t - f^[n + 1] t = f t - t := by simpa using Heq (n + 1) 0
          rw [← H, sub_add_sub_cancel']
      rcases ht with ⟨_ | m, hm, hm'⟩
      · exact absurd hm (lt_irrefl 0)
      · have H := IH m
        rw [hm'.isFixedPt.eq, sub_self, Int.sign_zero, eq_comm, Int.sign_eq_zero_iff_zero,
          sub_eq_zero] at H
        simp [IsPeriodicPt, IsFixedPt, H]
    · -- two consecutive entries of `C` differ, hence they are opposite
      rw [Cycle.chain_map, periodicOrbit_chain' _ ht] at HC'
      push_neg at HC'
      obtain ⟨n, hn⟩ := HC'
      rcases Int.natAbs_eq_natAbs_iff.1 (Habs n (n + 1)) with hn' | hn'
      · refine absurd ?_ hn
        simpa only [Function.iterate_succ_apply'] using hn'
      · rw [neg_sub, sub_right_inj] at hn'
        simp only [Function.iterate_succ_apply'] at hn'
        exact isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate ht hn'.symm
  simpa [IsPeriodicPt, IsFixedPt, Function.iterate_succ_apply'] using key

lemma iterComp_sub_X_ne_zero {P : ℤ[X]} (hP : 1 < P.natDegree) {k : ℕ} (hk : 0 < k) :
    iterComp P k - X ≠ 0 := by
  rw [sub_ne_zero, iterComp]
  apply_fun natDegree
  simpa using (one_lt_pow₀ hP hk.ne').ne'

/-- The case `k = 2`: the polynomial `P(P(x)) - x` has at most `natDegree P` integer roots. -/
theorem card_roots_comp_le {P : ℤ[X]} (hP : 1 < P.natDegree) :
    (P.comp P - X).roots.toFinset.card ≤ P.natDegree := by
  have hPX : (P - X).natDegree = P.natDegree := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    simpa using hP
  have hPX' : P - X ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hPX
    omega
  by_cases H : (P.comp P - X).roots.toFinset ⊆ (P - X).roots.toFinset
  · exact (Finset.card_le_card H).trans
      ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans_eq hPX))
  · -- otherwise there are `a ≠ b` with `P a = b` and `P b = a`
    obtain ⟨a, ha, hab⟩ := Finset.not_subset.1 H
    replace ha := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ha)
    rw [IsRoot.def, eval_sub, eval_comp, eval_X, sub_eq_zero] at ha
    rw [Multiset.mem_toFinset, mem_roots hPX', IsRoot.def, eval_sub, eval_X, sub_eq_zero] at hab
    set b := P.eval a with hb
    have hPab : (P + (X : ℤ[X]) - a - b).natDegree = P.natDegree := by
      rw [sub_sub, ← Int.cast_add]
      have h₁ : (P + X).natDegree = P.natDegree := by
        rw [natDegree_add_eq_left_of_natDegree_lt]
        simpa using hP
      rw [natDegree_sub_eq_left_of_natDegree_lt, h₁]
      rw [h₁, natDegree_intCast]
      omega
    have hPab' : P + (X : ℤ[X]) - a - b ≠ 0 := by
      intro h
      rw [h, natDegree_zero] at hPab
      omega
    -- every root of `P(P(x)) - x` is a root of `P(x) + x - a - b`
    suffices H' : (P.comp P - X).roots.toFinset ⊆ (P + (X : ℤ[X]) - a - b).roots.toFinset from
      (Finset.card_le_card H').trans
        ((Multiset.toFinset_card_le _).trans <| (card_roots' _).trans_eq hPab)
    intro t ht
    replace ht := isRoot_of_mem_roots (Multiset.mem_toFinset.1 ht)
    rw [IsRoot.def, eval_sub, eval_comp, eval_X, sub_eq_zero] at ht
    simp only [mem_roots hPab', sub_eq_iff_eq_add, Multiset.mem_toFinset, IsRoot.def,
      eval_sub, eval_add, eval_X, eval_intCast, Int.cast_id, zero_add]
    apply (add_eq_add_of_natAbs_eq_of_natAbs_eq hab ?_ ?_).symm <;>
        apply Int.natAbs_eq_of_dvd_dvd <;> set u := P.eval t with hu
    · rw [← ha, ← ht]; apply sub_dvd_eval_sub
    · apply sub_dvd_eval_sub
    · rw [← ht]; apply sub_dvd_eval_sub
    · rw [← ha]; apply sub_dvd_eval_sub

/-- The set of integer solutions of `Q(t) = t` is contained in the (finite) set of roots of
`P(P(x)) - x`. -/
lemma subset_roots_comp {P : ℤ[X]} (hP : 1 < P.natDegree) {k : ℕ} (hk : 0 < k) :
    {t : ℤ | (iterComp P k).eval t = t} ⊆ ↑(P.comp P - X).roots.toFinset := by
  have hP' : P.comp P - X ≠ 0 := by
    have := iterComp_sub_X_ne_zero hP (k := 2) two_pos
    simpa [iterComp, Function.iterate_succ_apply'] using this
  intro t ht
  simp only [Set.mem_setOf_eq, eval_iterComp] at ht
  simp only [Multiset.mem_toFinset, Finset.mem_coe, mem_roots hP',
    IsRoot.def, eval_sub, eval_comp, eval_X, sub_eq_zero]
  exact eval_eval_eq_of_isPeriodicPt ⟨k, hk, ht⟩

/-- **IMO 2006, Problem 5.** If `P` is an integer polynomial of degree `n > 1` and `k > 0`, then
any finite set of integers `t` with `Q(t) = t`, where `Q = P ∘ P ∘ ⋯ ∘ P` (`k` times), has at most
`n` elements. -/
theorem imo2006_p5 {P : ℤ[X]} (hP : 1 < P.natDegree) {k : ℕ} (hk : 0 < k) {S : Finset ℤ}
    (hS : ∀ t ∈ S, (iterComp P k).eval t = t) : S.card ≤ P.natDegree := by
  refine le_trans (Finset.card_le_card ?_) (card_roots_comp_le hP)
  intro t ht
  have := subset_roots_comp hP hk (show t ∈ {t : ℤ | (iterComp P k).eval t = t} from hS t ht)
  simpa using this

/-- **IMO 2006, Problem 5**, set version: there are only finitely many integers `t` with
`Q(t) = t`. -/
theorem imo2006_p5_setOf_finite {P : ℤ[X]} (hP : 1 < P.natDegree) {k : ℕ} (hk : 0 < k) :
    {t : ℤ | (iterComp P k).eval t = t}.Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (subset_roots_comp hP hk)

/-- **IMO 2006, Problem 5**, set version: there are at most `n` integers `t` with `Q(t) = t`. -/
theorem imo2006_p5_ncard {P : ℤ[X]} (hP : 1 < P.natDegree) {k : ℕ} (hk : 0 < k) :
    {t : ℤ | (iterComp P k).eval t = t}.ncard ≤ P.natDegree := by
  have hfin := imo2006_p5_setOf_finite hP hk
  rw [← hfin.coe_toFinset, Set.ncard_coe_finset]
  exact imo2006_p5 hP hk fun t ht => hfin.mem_toFinset.1 ht

end Imo2006P5
