import Mathlib

/-!
# IMO 2000, Problem 4

Cards `1..100` go into three boxes, each nonempty. The audience picks two boxes, one card from
each, and announces the sum; the magician must always be able to name the unused box. Count the
distributions for which this works.

Answer: `12`.

## Formalization

Card `n+1` is index `n : Fin 100`, so a distribution is `f : Fin 100 → Fin 3`. Every box nonempty
is `Function.Surjective f`. The trick works exactly when the sum determines the unordered pair of
boxes used, which is `Good` below. The count is `Nat.card {f // Good f} = 12`.

## The two families

* `fM i = i % 3` — cards congruent mod `3` together.
* `fT` — `{1}`, `{2,…,99}`, `{100}`.

Each admits `3! = 6` labellings of the boxes, and the two families are disjoint, giving `12`.

## Classification

Write `b₀ = f 0`, let `p` be least with `f p ≠ b₀` and `b₁ = f p`, let `q` be least with
`f q ∉ {b₀, b₁}` and `b₂ = f q`. So `p < q` and every index below `q` lands in `{b₀, b₁}`.

* **If `a, b < q` lie in different boxes then `a + b < q`.** Otherwise `t = a+b-q` satisfies
  `t < q`, and the pairs `(a,b)`, `(q,t)` have equal sums with `f q ∉ {b₀,b₁} ∋ f a, f b`,
  so matching them forces `f a` or `f b` to equal `b₂`.
* **Hence `f 0 = b₀` and `f i = b₁` for `1 ≤ i < q`.** Applying the above to `q-1` and `p`
  rules out `f (q-1) = b₀`; applying it to `i` and `q-1` rules out `f i = b₀` for `i ≥ 1`.
* **If `q = 2`:** `f 0, f 1, f 2` are distinct, and `(i+3) + i = (i+1) + (i+2)` propagates
  `f (i+3) = f i` by induction, giving `fM`.
* **If `q ≥ 3`:** index `q+1` cannot exist. Each of the three possible boxes for it collides:
  `f (q+1) = b₀` clashes via `(q+1)+1 = 2+q`; `f (q+1) ∈ {b₁, b₂}` clashes via
  `(q+1)+0 = 1+q`. So `q = 99`, giving `fT`.
-/

namespace Imo2000P4

/-- The trick always works: the sum determines the unordered pair of boxes drawn from. -/
def Good (f : Fin 100 → Fin 3) : Prop :=
  Function.Surjective f ∧
  ∀ a b c d : Fin 100, f a ≠ f b → f c ≠ f d → (a : ℕ) + (b : ℕ) = (c : ℕ) + (d : ℕ) →
    (f a = f c ∧ f b = f d) ∨ (f a = f d ∧ f b = f c)

/-- Cards congruent mod `3` share a box. -/
def fM : Fin 100 → Fin 3 := fun i => ⟨(i : ℕ) % 3, by omega⟩

/-- The distribution `{1}`, `{2,…,99}`, `{100}`. -/
def fT : Fin 100 → Fin 3 :=
  fun i => ⟨if (i : ℕ) = 0 then 0 else if (i : ℕ) = 99 then 2 else 1, by split_ifs <;> omega⟩

/-! ### The two families work -/

theorem Good_fM : Good fM := by
  constructor
  · intro b
    fin_cases b
    · exact ⟨⟨0, by norm_num⟩, by decide⟩
    · exact ⟨⟨1, by norm_num⟩, by decide⟩
    · exact ⟨⟨2, by norm_num⟩, by decide⟩
  · intro a b c d hab hcd hsum
    simp only [fM, ne_eq, Fin.mk.injEq] at hab hcd ⊢
    omega

theorem Good_fT : Good fT := by
  constructor
  · intro b
    fin_cases b
    · exact ⟨⟨0, by norm_num⟩, by decide⟩
    · exact ⟨⟨1, by norm_num⟩, by decide⟩
    · exact ⟨⟨99, by norm_num⟩, by decide⟩
  · intro a b c d hab hcd hsum
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    have hd := d.isLt
    simp only [fT, ne_eq, Fin.mk.injEq] at hab hcd ⊢
    split_ifs at hab hcd ⊢ <;> omega

/-- Relabelling the boxes preserves the property. -/
theorem Good_comp (σ : Equiv.Perm (Fin 3)) {f : Fin 100 → Fin 3} (hf : Good f) :
    Good (fun i => σ (f i)) := by
  obtain ⟨hs, hc⟩ := hf
  constructor
  · intro b
    obtain ⟨i, hi⟩ := hs (σ.symm b)
    exact ⟨i, by simp [hi]⟩
  · intro a b c d hab hcd hsum
    have hab' : f a ≠ f b := fun h => hab (congrArg σ h)
    have hcd' : f c ≠ f d := fun h => hcd (congrArg σ h)
    rcases hc a b c d hab' hcd' hsum with ⟨u, v⟩ | ⟨u, v⟩
    · exact Or.inl ⟨congrArg σ u, congrArg σ v⟩
    · exact Or.inr ⟨congrArg σ u, congrArg σ v⟩

/-! ### Classification -/

theorem fin3_cases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide

/-- Injectivity of a map out of `Fin 3` from the three pairwise inequalities. -/
theorem inj3 {h : Fin 3 → Fin 3} (d01 : h 0 ≠ h 1) (d02 : h 0 ≠ h 2) (d12 : h 1 ≠ h 2) :
    Function.Injective h := by
  intro j k hjk
  rcases fin3_cases j with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd hjk d01
      | exact absurd hjk.symm d01
      | exact absurd hjk d02
      | exact absurd hjk.symm d02
      | exact absurd hjk d12
      | exact absurd hjk.symm d12

theorem classify (f : Fin 100 → Fin 3) (hf : Good f) :
    (∃ σ : Equiv.Perm (Fin 3), f = fun i => σ (fM i)) ∨
      (∃ σ : Equiv.Perm (Fin 3), f = fun i => σ (fT i)) := by
  classical
  obtain ⟨hsurj, hcond⟩ := hf
  -- transport everything to a total function on `ℕ`
  set g : ℕ → Fin 3 := fun n => f ⟨n % 100, Nat.mod_lt _ (by norm_num)⟩ with hgdef
  have hg : ∀ (n : ℕ) (h : n < 100), g n = f ⟨n, h⟩ := by
    intro n h
    simp [hgdef, Nat.mod_eq_of_lt h]
  have hgf : ∀ i : Fin 100, g (i : ℕ) = f i := by
    intro i
    simp [hgdef, Nat.mod_eq_of_lt i.isLt]
  have hcond' : ∀ a b c d : ℕ, a < 100 → b < 100 → c < 100 → d < 100 →
      g a ≠ g b → g c ≠ g d → a + b = c + d →
      (g a = g c ∧ g b = g d) ∨ (g a = g d ∧ g b = g c) := by
    intro a b c d ha hb hc hd hab hcd hsum
    rw [hg a ha, hg b hb] at hab
    rw [hg c hc, hg d hd] at hcd
    have h1 := hcond ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hab hcd (by simpa using hsum)
    rw [← hg a ha, ← hg b hb, ← hg c hc, ← hg d hd] at h1
    exact h1
  -- three distinct values exist
  have hthree : ∀ x : Fin 3, ∃ y, y ≠ x := by decide
  have hpair : ∀ x y : Fin 3, x ≠ y → ∃ z, z ≠ x ∧ z ≠ y := by decide
  have hall3 : ∀ x y z w : Fin 3, x ≠ y → x ≠ z → y ≠ z → w = x ∨ w = y ∨ w = z := by decide
  -- the first index outside box `g 0`
  obtain ⟨p, hp100, hpne, hpmin⟩ : ∃ p, p < 100 ∧ g p ≠ g 0 ∧ ∀ m, m < p → g m = g 0 := by
    have H : ∃ n, n < 100 ∧ g n ≠ g 0 := by
      obtain ⟨y, hy⟩ := hthree (g 0)
      obtain ⟨i, hi⟩ := hsurj y
      exact ⟨(i : ℕ), i.isLt, by rw [hgf i, hi]; exact hy⟩
    obtain ⟨hA, hB⟩ := Nat.find_spec H
    refine ⟨Nat.find H, hA, hB, ?_⟩
    intro m hm
    by_contra hcon
    exact Nat.find_min H hm ⟨by omega, hcon⟩
  -- the first index outside both of the first two boxes
  obtain ⟨q, hq100, hqb0, hqb1, hqmin⟩ :
      ∃ q, q < 100 ∧ g q ≠ g 0 ∧ g q ≠ g p ∧ ∀ m, m < q → g m = g 0 ∨ g m = g p := by
    have H : ∃ n, n < 100 ∧ g n ≠ g 0 ∧ g n ≠ g p := by
      obtain ⟨z, hz0, hzp⟩ := hpair (g 0) (g p) (Ne.symm hpne)
      obtain ⟨i, hi⟩ := hsurj z
      exact ⟨(i : ℕ), i.isLt, by rw [hgf i, hi]; exact hz0, by rw [hgf i, hi]; exact hzp⟩
    obtain ⟨hA, hB, hC⟩ := Nat.find_spec H
    refine ⟨Nat.find H, hA, hB, hC, ?_⟩
    intro m hm
    by_contra hcon
    push Not at hcon
    exact Nat.find_min H hm ⟨by omega, hcon.1, hcon.2⟩
  have hp0 : p ≠ 0 := fun h => hpne (by rw [h])
  have hpq : p < q := by
    rcases Nat.lt_or_ge q p with h | h
    · exact absurd (hpmin q h) hqb0
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · exact absurd (by rw [h']) hqb1
      · exact h'
  have hq2 : 2 ≤ q := by omega
  -- Step 1: below `q`, cross-box sums stay below `q`
  have step1 : ∀ a b, a < q → b < q → g a ≠ g b → a + b < q := by
    intro a b ha hb hab
    by_contra hcon
    push Not at hcon
    have ht : a + b - q < q := by omega
    have hsum : a + b = q + (a + b - q) := by omega
    have hqt : g q ≠ g (a + b - q) := by
      rcases hqmin _ ht with h | h <;> rw [h]
      · exact hqb0
      · exact hqb1
    have h1 := hcond' a b q (a + b - q) (by omega) (by omega) hq100 (by omega) hab hqt hsum
    have h2 : g a = g q ∨ g b = g q := by tauto
    rcases h2 with h | h
    · rcases hqmin a ha with h3 | h3 <;> rw [h3] at h
      · exact hqb0 h.symm
      · exact hqb1 h.symm
    · rcases hqmin b hb with h3 | h3 <;> rw [h3] at h
      · exact hqb0 h.symm
      · exact hqb1 h.symm
  -- Step 2: box structure below `q`
  have hqm1 : g (q - 1) = g p := by
    rcases hqmin (q - 1) (by omega) with h | h
    · exfalso
      have hne : g (q - 1) ≠ g p := by rw [h]; exact Ne.symm hpne
      have := step1 (q - 1) p (by omega) hpq hne
      omega
    · exact h
  have hmid : ∀ i, 1 ≤ i → i < q → g i = g p := by
    intro i hi1 hiq
    rcases hqmin i hiq with h | h
    · exfalso
      have hne : g i ≠ g (q - 1) := by rw [h, hqm1]; exact Ne.symm hpne
      have := step1 i (q - 1) hiq (by omega) hne
      omega
    · exact h
  rcases Nat.lt_or_ge q 3 with hq | hq
  · -- `q = 2`: the mod-3 family
    left
    have hqe : q = 2 := by omega
    have d01 : g 0 ≠ g 1 := by
      rw [hmid 1 (by omega) (by omega)]
      exact Ne.symm hpne
    have d02 : g 0 ≠ g 2 := by rw [← hqe]; exact Ne.symm hqb0
    have d12 : g 1 ≠ g 2 := by
      rw [hmid 1 (by omega) (by omega), ← hqe]
      exact Ne.symm hqb1
    -- three consecutive indices always land in three different boxes
    have htriple : ∀ i, i + 2 < 100 → g i ≠ g (i + 1) ∧ g (i + 1) ≠ g (i + 2) ∧ g i ≠ g (i + 2) := by
      intro i
      induction i with
      | zero => intro _; exact ⟨d01, d12, d02⟩
      | succ n ih =>
          intro hn
          obtain ⟨e1, e2, e3⟩ := ih (by omega)
          have key : g (n + 3) = g n := by
            by_contra hc
            have h1 := hcond' (n + 3) n (n + 1) (n + 2) (by omega) (by omega) (by omega)
              (by omega) hc e2 (by omega)
            rcases h1 with ⟨_, v⟩ | ⟨_, v⟩
            · exact e3 v
            · exact e1 v
          refine ⟨by simpa using e2, ?_, ?_⟩
          · simp only [show n + 1 + 1 = n + 2 from rfl, show n + 1 + 2 = n + 3 from rfl, key]
            exact Ne.symm e3
          · simp only [show n + 1 + 2 = n + 3 from rfl, key]
            exact Ne.symm e1
    have hstep3 : ∀ i, i + 3 < 100 → g (i + 3) = g i := by
      intro i hi
      obtain ⟨e1, e2, e3⟩ := htriple i (by omega)
      by_contra hc
      have h1 := hcond' (i + 3) i (i + 1) (i + 2) (by omega) (by omega) (by omega) (by omega)
        hc e2 (by omega)
      rcases h1 with ⟨_, v⟩ | ⟨_, v⟩
      · exact e3 v
      · exact e1 v
    have hmod : ∀ i, i < 100 → g i = g (i % 3) := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        rcases Nat.lt_or_ge i 3 with h3 | h3
        · congr 1; omega
        · have h1 : i - 3 + 3 = i := by omega
          have h2 := hstep3 (i - 3) (by omega)
          rw [h1] at h2
          rw [h2, ih (i - 3) (by omega) (by omega)]
          congr 1
          omega
    -- assemble the permutation
    refine ⟨Equiv.ofBijective (fun j : Fin 3 => g (j : ℕ))
      (Finite.injective_iff_bijective.1 (inj3 d01 d02 d12)), ?_⟩
    funext i
    have hi := i.isLt
    rw [← hgf i, hmod (i : ℕ) hi]
    rfl
  · -- `q ≥ 3`: the `{1}, {2..99}, {100}` family
    right
    have hq99 : q = 99 := by
      by_contra hcon
      have hq1 : q + 1 < 100 := by omega
      have h1 : g 1 = g p := hmid 1 (by omega) (by omega)
      have h2 : g 2 = g p := hmid 2 (by omega) (by omega)
      rcases hall3 (g 0) (g p) (g q) (g (q + 1)) (Ne.symm hpne) (Ne.symm hqb0) (Ne.symm hqb1)
        with hc | hc | hc
      · -- `g (q+1) = g 0` : use `(q+1) + 1 = 2 + q`
        have hne1 : g (q + 1) ≠ g 1 := by rw [hc, h1]; exact Ne.symm hpne
        have hne2 : g 2 ≠ g q := by rw [h2]; exact Ne.symm hqb1
        have h3 := hcond' (q + 1) 1 2 q hq1 (by omega) (by omega) hq100 hne1 hne2 (by omega)
        rcases h3 with ⟨u, v⟩ | ⟨u, v⟩
        · rw [hc, h2] at u; exact hpne u.symm
        · rw [hc] at u; exact hqb0 u.symm
      · -- `g (q+1) = g p` : use `(q+1) + 0 = 1 + q`
        have hne1 : g (q + 1) ≠ g 0 := by rw [hc]; exact hpne
        have hne2 : g 1 ≠ g q := by rw [h1]; exact Ne.symm hqb1
        have h3 := hcond' (q + 1) 0 1 q hq1 (by omega) (by omega) hq100 hne1 hne2 (by omega)
        rcases h3 with ⟨u, v⟩ | ⟨u, v⟩
        · exact hqb0 v.symm
        · rw [hc] at u; exact hqb1 u.symm
      · -- `g (q+1) = g q` : use `(q+1) + 0 = 1 + q`
        have hne1 : g (q + 1) ≠ g 0 := by rw [hc]; exact hqb0
        have hne2 : g 1 ≠ g q := by rw [h1]; exact Ne.symm hqb1
        have h3 := hcond' (q + 1) 0 1 q hq1 (by omega) (by omega) hq100 hne1 hne2 (by omega)
        rcases h3 with ⟨u, v⟩ | ⟨u, v⟩
        · rw [hc, h1] at u; exact hqb1 u
        · rw [h1] at v; exact hpne v.symm
    have h1 : g 1 = g p := hmid 1 (by omega) (by omega)
    have e01 : g 0 ≠ g 1 := by rw [h1]; exact Ne.symm hpne
    have e099 : g 0 ≠ g 99 := by rw [← hq99]; exact Ne.symm hqb0
    have e199 : g 1 ≠ g 99 := by rw [h1, ← hq99]; exact Ne.symm hqb1
    refine ⟨Equiv.ofBijective
      (fun j : Fin 3 => if (j : ℕ) = 0 then g 0 else if (j : ℕ) = 1 then g 1 else g 99)
      (Finite.injective_iff_bijective.1 (inj3 e01 e099 e199)), ?_⟩
    funext i
    have hi := i.isLt
    rw [← hgf i]
    show g (i : ℕ) =
      (if ((fT i : ℕ)) = 0 then g 0 else if ((fT i : ℕ)) = 1 then g 1 else g 99)
    have hval : (fT i : ℕ) = if (i : ℕ) = 0 then 0 else if (i : ℕ) = 99 then 2 else 1 := rfl
    rw [hval]
    by_cases h0 : (i : ℕ) = 0
    · rw [h0]
      norm_num
    · by_cases h99 : (i : ℕ) = 99
      · rw [h99]
        norm_num
      · rw [if_neg h0, if_neg h99]
        norm_num
        rw [hmid (i : ℕ) (by omega) (by omega), h1]

/-! ### The count -/

/-- The two patterns, selected by a `Bool`. -/
def pat : Bool → (Fin 100 → Fin 3)
  | false => fM
  | true => fT

/-- The `12` distributions, indexed by a relabelling of the boxes and a choice of family. -/
def Phi (p : Equiv.Perm (Fin 3) × Bool) : {f : Fin 100 → Fin 3 // Good f} :=
  ⟨fun i => p.1 (pat p.2 i), by
    rcases p with ⟨σ, t⟩
    cases t
    · exact Good_comp σ Good_fM
    · exact Good_comp σ Good_fT⟩

theorem Phi_injective : Function.Injective Phi := by
  rintro ⟨σ, t⟩ ⟨τ, s⟩ h
  have hfun : ∀ i, σ (pat t i) = τ (pat s i) :=
    fun i => congrFun (congrArg Subtype.val h) i
  have hM1 : fM ⟨1, by norm_num⟩ = 1 := by decide
  have hM2 : fM ⟨2, by norm_num⟩ = 2 := by decide
  have hT1 : fT ⟨1, by norm_num⟩ = 1 := by decide
  have hT2 : fT ⟨2, by norm_num⟩ = 1 := by decide
  have hne12 : (1 : Fin 3) ≠ 2 := by decide
  have hkey : t = s := by
    cases t <;> cases s
    · rfl
    · exfalso
      have e1 := hfun ⟨1, by norm_num⟩
      have e2 := hfun ⟨2, by norm_num⟩
      simp only [pat] at e1 e2
      rw [hM1, hT1] at e1
      rw [hM2, hT2] at e2
      exact hne12 (σ.injective (e1.trans e2.symm))
    · exfalso
      have e1 := hfun ⟨1, by norm_num⟩
      have e2 := hfun ⟨2, by norm_num⟩
      simp only [pat] at e1 e2
      rw [hT1, hM1] at e1
      rw [hT2, hM2] at e2
      exact hne12 (τ.injective (e1.symm.trans e2))
    · rfl
  subst hkey
  have hsurj : Function.Surjective (pat t) := by
    cases t
    · exact Good_fM.1
    · exact Good_fT.1
  have hστ : σ = τ := by
    apply Equiv.ext
    intro v
    obtain ⟨i, hi⟩ := hsurj v
    rw [← hi]
    exact hfun i
  simp [hστ]

theorem Phi_surjective : Function.Surjective Phi := by
  rintro ⟨f, hf⟩
  rcases classify f hf with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · exact ⟨⟨σ, false⟩, by simp [Phi, pat, hσ]⟩
  · exact ⟨⟨σ, true⟩, by simp [Phi, pat, hσ]⟩

/-- **IMO 2000 P4.** There are exactly `12` distributions for which the trick always works. -/
theorem imo2000_p4 : Nat.card {f : Fin 100 → Fin 3 // Good f} = 12 := by
  rw [← Nat.card_eq_of_bijective Phi ⟨Phi_injective, Phi_surjective⟩]
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_perm]
  decide

end Imo2000P4
