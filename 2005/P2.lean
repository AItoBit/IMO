import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace IMO2005P2

open Function

/-!  A kernel-checked formalization of IMO 2005, Problem 2.

The sequence is indexed from `1`, as in the statement; index `0` is ignored.
`Int.emod (a i) n` is the remainder of `a i` modulo `n`.
-/

private lemma small_modEq_eq {N : ℕ} {x y : ℤ}
    (hxy : x ≡ y [ZMOD N]) (hsmall : |y - x| < (N : ℤ)) : x = y := by
  have hdvd : (N : ℤ) ∣ y - x := Int.modEq_iff_dvd.mp hxy
  have hsmall' : (y - x).natAbs < N := by
    have : ((y - x).natAbs : ℤ) < (N : ℤ) := by
      simpa only [Int.natCast_natAbs] using hsmall
    exact_mod_cast this
  have hz : y - x = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hsmall')
  omega

theorem imo2005_p2 (a : ℕ → ℤ)
    (hpos : ∀ i, ∃ j, i < j ∧ 0 < a j)
    (hneg : ∀ i, ∃ j, i < j ∧ a j < 0)
    (hrem : ∀ n : ℕ, 0 < n →
      ((Finset.Icc 1 n).image fun i => Int.emod (a i) n).card = n) :
    ∀ z : ℤ, ∃! i, 0 < i ∧ a i = z := by
  -- Distinctness of the first `n` remainders, in a convenient form.
  have hmod : ∀ (n : ℕ), 0 < n → ∀ i j : ℕ,
      1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
      a i ≡ a j [ZMOD n] → i = j := by
    intro n hn i j hi₁ hin hj₁ hjn hij
    have hcard : (Finset.Icc 1 n).card = n := by simp [Nat.card_Icc]
    have hc : ((Finset.Icc 1 n).image fun r => Int.emod (a r) n).card =
        (Finset.Icc 1 n).card := by rw [hrem n hn, hcard]
    have hinj := Finset.card_image_iff.mp hc
    apply hinj
    · exact Finset.mem_Icc.mpr ⟨hi₁, hin⟩
    · exact Finset.mem_Icc.mpr ⟨hj₁, hjn⟩
    · exact hij.eq

  -- Hence the positive-indexed part of the sequence is globally injective.
  have hinj : ∀ ⦃i j : ℕ⦄, 0 < i → 0 < j → a i = a j → i = j := by
    intro i j hi hj hij
    let n := max i j
    apply hmod n (by simp [n, hi]) i j hi (le_max_left _ _) hj (le_max_right _ _)
    simp [hij]

  -- Translate the sequence so that its first term is zero.
  let b : ℕ → ℤ := fun i => a i - a 1
  have hb₁ : b 1 = 0 := by simp [b]
  have hbmod : ∀ (n : ℕ), 0 < n → ∀ i j : ℕ,
      1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
      b i ≡ b j [ZMOD n] → i = j := by
    intro n hn i j hi₁ hin hj₁ hjn hij
    apply hmod n hn i j hi₁ hin hj₁ hjn
    rw [Int.modEq_iff_dvd] at hij ⊢
    simpa [b] using hij

  -- An injective list of `n` residues modulo `n` contains every residue.
  have hsurj : ∀ (n : ℕ), 0 < n → ∀ z : ℤ,
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ b i ≡ z [ZMOD n] := by
    intro n hn z
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let f : Fin n → ZMod n := fun i => (b (i.1 + 1) : ZMod n)
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      have := hbmod n hn (i.1 + 1) (j.1 + 1) (by omega) (by omega)
          (by omega) (by omega)
          ((ZMod.intCast_eq_intCast_iff _ _ n).mp hij)
      omega
    have hcard : Fintype.card (Fin n) = Fintype.card (ZMod n) := by
      simp [ZMod.card]
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩
    obtain ⟨i, hi⟩ := hbij.2 (z : ZMod n)
    refine ⟨i.1 + 1, by omega, by omega, ?_⟩
    exact (ZMod.intCast_eq_intCast_iff _ _ n).mp hi

  -- The standard bound: after translation, `|b i| < i`.
  have hbound : ∀ i : ℕ, 0 < i → (b i).natAbs < i := by
    intro i hi
    by_contra hnot
    have hle : i ≤ (b i).natAbs := by omega
    have hbne : b i ≠ 0 := by
      intro hz
      have hai : a i = a 1 := by dsimp [b] at hz; omega
      have : i = 1 := hinj hi (by omega) hai
      subst i
      exact hnot (by simp [hb₁])
    have hN : 0 < (b i).natAbs := Int.natAbs_pos.mpr hbne
    have hcong : b 1 ≡ b i [ZMOD (b i).natAbs] := by
      rw [Int.modEq_iff_dvd]
      simp only [hb₁, sub_zero]
      exact Int.natCast_dvd.mpr dvd_rfl
    have hi₁ : 1 = i := hbmod (b i).natAbs hN 1 i (by omega) (by omega)
        hi hle hcong
    apply hbne
    rw [← hi₁, hb₁]

  -- Every prefix of `b` is an interval of consecutive integers.
  have hinterval : ∀ k : ℕ, ∃ l : ℤ,
      l ≤ 0 ∧ 0 ≤ l + k ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ k + 1 → l ≤ b i ∧ b i ≤ l + k) ∧
      (∀ z : ℤ, l ≤ z → z ≤ l + k →
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ k + 1 ∧ b i = z) := by
    intro k
    induction k with
    | zero =>
        refine ⟨0, by omega, by omega, ?_, ?_⟩
        · intro i hi hik
          have : i = 1 := by omega
          subst i
          simp [hb₁]
        · intro z hz₁ hz₂
          refine ⟨1, by omega, by omega, ?_⟩
          have : z = 0 := by omega
          simpa [this] using hb₁
    | succ k ih =>
        obtain ⟨l, hl₀, h₀u, hold, hfill⟩ := ih
        let N : ℕ := k + 2
        let x : ℤ := b N
        let low : ℤ := l - 1
        obtain ⟨i, hi₁, hiN, hic⟩ := hsurj N (by simp [N]) low
        have hi : i = N := by
          by_cases heq : i = N
          · exact heq
          exfalso
          have hi_lt : i < N := lt_of_le_of_ne hiN heq
          have hik : i ≤ k + 1 := by simp [N] at hi_lt ⊢; omega
          obtain ⟨hlib, hbiu⟩ := hold i hi₁ hik
          have hdvd : (N : ℤ) ∣ low - b i := Int.modEq_iff_dvd.mp hic
          have hne : low - b i ≠ 0 := by simp [low]; omega
          have habs := Int.natAbs_le_of_dvd_ne_zero hdvd hne
          have habs' : |(N : ℤ)| ≤ |low - b i| := by
            have : (((N : ℤ).natAbs : ℕ) : ℤ) ≤
                (((low - b i).natAbs : ℕ) : ℤ) := by exact_mod_cast habs
            simpa only [Int.natCast_natAbs] using this
          have hnonpos : low - b i ≤ 0 := by simp [low]; omega
          rw [abs_of_nonneg (Int.ofNat_zero_le N), abs_of_nonpos hnonpos] at habs'
          simp [N, low] at habs'
          omega
        subst i
        have hxc : x ≡ low [ZMOD N] := by simpa [x] using hic
        have hxabs : x.natAbs < N := by
          simpa [x] using hbound N (by simp [N])
        have hxabs' : |x| < (N : ℤ) := by
          have : (x.natAbs : ℤ) < (N : ℤ) := by exact_mod_cast hxabs
          simpa only [Int.natCast_natAbs] using this
        have hxlo : -(N : ℤ) < x := by
          by_cases hx : 0 ≤ x
          · omega
          · rw [abs_of_nonpos (le_of_not_ge hx)] at hxabs'
            omega
        have hxhi : x < N := by
          by_cases hx : 0 ≤ x
          · rw [abs_of_nonneg hx] at hxabs'
            omega
          · omega
        have hlowlo : -(N : ℤ) < low := by simp [low, N] at *; omega
        have hlowhi : low < (N : ℤ) := by simp [low, N] at *; omega
        have hlowx : low ≤ x := by
          by_cases hle : low ≤ x
          · exact hle
          exfalso
          have hxl : x < low := lt_of_not_ge hle
          have hs : |low - x| < (N : ℤ) := by
            rw [abs_of_nonneg (by omega : 0 ≤ low - x)]
            simp [low, N] at *
            omega
          have heq := small_modEq_eq hxc hs
          omega
        have hdiff₀ : 0 ≤ x - low := by omega
        have hdiff₂ : x - low < 2 * (N : ℤ) := by simp [low, N] at *; omega
        have hxcases : x = low ∨ x = l + k + 1 := by
          by_cases hsmall : x - low < (N : ℤ)
          · left
            apply small_modEq_eq hxc
            rw [abs_of_nonpos (by omega : low - x ≤ 0)]
            omega
          · right
            have hc₂ : x ≡ low + N [ZMOD N] := by
              rw [Int.modEq_iff_dvd] at hxc ⊢
              have hself : (N : ℤ) ∣ (N : ℤ) := dvd_rfl
              convert Int.dvd_add hxc hself using 1
              all_goals ring
            have hsmall₂ : |(low + N) - x| < (N : ℤ) := by
              rw [abs_of_nonpos]
              · omega
              · omega
            have := small_modEq_eq hc₂ hsmall₂
            simp [low, N] at this ⊢
            omega
        rcases hxcases with hxlow | hxhigh
        · refine ⟨l - 1, by omega, by omega, ?_, ?_⟩
          · intro j hj₁ hjN
            by_cases hjold : j ≤ k + 1
            · obtain ⟨hjl, hju⟩ := hold j hj₁ hjold
              constructor <;> omega
            · have : j = N := by simp [N] at *; omega
              subst j
              constructor
              · simp [x, hxlow, low, N]
              · simp [x, hxlow, low, N]
                omega
          · intro z hzl hzu
            by_cases hz : z = l - 1
            · refine ⟨N, by simp [N], by simp [N], ?_⟩
              simpa [x, hxlow, low] using hz.symm
            · obtain ⟨j, hj₁, hjN, hjz⟩ := hfill z (by omega) (by omega)
              exact ⟨j, hj₁, by omega, hjz⟩
        · refine ⟨l, hl₀, by omega, ?_, ?_⟩
          · intro j hj₁ hjN
            by_cases hjold : j ≤ k + 1
            · obtain ⟨hjl, hju⟩ := hold j hj₁ hjold
              constructor <;> omega
            · have : j = N := by simp [N] at *; omega
              subst j
              constructor <;> simp [x, hxhigh, N] <;> omega
          · intro z hzl hzu
            by_cases hz : z = l + k + 1
            · refine ⟨N, by simp [N], by simp [N], ?_⟩
              simpa [x, hxhigh] using hz.symm
            · obtain ⟨j, hj₁, hjN, hjz⟩ := hfill z hzl (by omega)
              exact ⟨j, hj₁, by omega, hjz⟩

  -- Positive terms are unbounded above (injectivity rules out a finite range).
  let PNat := {i : ℕ // 0 < i}
  let ap : PNat → ℤ := fun i => a i.1
  have hapinj : Function.Injective ap := by
    intro i j hij
    apply Subtype.ext
    exact hinj i.2 j.2 hij
  have hposInf : ({i : PNat | 0 < ap i} : Set PNat).Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro i
    obtain ⟨j, hij, hj⟩ := hpos i.1
    exact ⟨⟨j, lt_trans i.2 hij⟩, hj, hij⟩
  have habove : ∀ t : ℤ, ∃ i : ℕ, 0 < i ∧ t < a i := by
    intro t
    by_cases hex : ∃ i : ℕ, 0 < i ∧ t < a i
    · exact hex
    push_neg at hex
    exfalso
    have hfin : (ap ⁻¹' Set.Icc (1 : ℤ) t).Finite :=
      (Set.finite_Icc (1 : ℤ) t).preimage (hapinj.injOn)
    apply hposInf
    apply hfin.subset
    intro i hi
    change 0 < a i.1 at hi
    change (1 : ℤ) ≤ a i.1 ∧ a i.1 ≤ t
    exact ⟨by omega, hex i.1 i.2⟩

  -- Likewise, negative terms are unbounded below.
  have hnegInf : ({i : PNat | ap i < 0} : Set PNat).Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro i
    obtain ⟨j, hij, hj⟩ := hneg i.1
    exact ⟨⟨j, lt_trans i.2 hij⟩, hj, hij⟩
  have hbelow : ∀ t : ℤ, ∃ i : ℕ, 0 < i ∧ a i < t := by
    intro t
    by_cases hex : ∃ i : ℕ, 0 < i ∧ a i < t
    · exact hex
    push_neg at hex
    exfalso
    have hfin : (ap ⁻¹' Set.Icc t (-1 : ℤ)).Finite :=
      (Set.finite_Icc t (-1 : ℤ)).preimage (hapinj.injOn)
    apply hnegInf
    apply hfin.subset
    intro i hi
    change a i.1 < 0 at hi
    change t ≤ a i.1 ∧ a i.1 ≤ (-1 : ℤ)
    exact ⟨hex i.1 i.2, by omega⟩

  intro z
  obtain ⟨p, hp₀, hp⟩ := hbelow z
  obtain ⟨q, hq₀, hq⟩ := habove z
  let K := max p q
  have hK : 0 < K := lt_of_lt_of_le hp₀ (le_max_left _ _)
  obtain ⟨l, hl₀, h₀u, hinside, hfill⟩ := hinterval K
  have hpK : p ≤ K + 1 := by dsimp [K]; omega
  have hqK : q ≤ K + 1 := by dsimp [K]; omega
  obtain ⟨hlp, _⟩ := hinside p hp₀ hpK
  obtain ⟨_, hqu⟩ := hinside q hq₀ hqK
  let zb : ℤ := z - a 1
  have hzl : l ≤ zb := by simp [b, zb] at hlp hp; omega
  have hzu : zb ≤ l + K := by simp [b, zb] at hqu hq; omega
  obtain ⟨i, hi₀, hiK, hbi⟩ := hfill zb hzl hzu
  have hai : a i = z := by simp [b, zb] at hbi; omega
  refine ⟨i, ⟨hi₀, hai⟩, ?_⟩
  · intro j hj
    exact hinj hj.1 hi₀ (hj.2.trans hai.symm)

end IMO2005P2
