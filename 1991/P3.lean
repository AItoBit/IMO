import Mathlib

namespace IMO1991P3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def domain : Finset ℕ := Finset.Icc 1 280

def PairwiseCoprime (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

def HasFive (S : Finset ℕ) : Prop :=
  ∃ T : Finset ℕ, T ⊆ S ∧ T.card = 5 ∧ PairwiseCoprime T

/-- Every subset of exactly `k` elements has the required five numbers. -/
def ForcesFive (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ domain → S.card = k → HasFive S

/-- Nine explicit lists of pairwise coprime numbers to allow computational reduction. -/
def blockLists (i : Fin 9) : List ℕ :=
  match i.val with
  | 0 => [1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277]
  | 1 => [121, 49, 25, 9, 4]
  | 2 => [143, 119, 95, 27, 8]
  | 3 => [169, 77, 85, 57, 16]
  | 4 => [187, 91, 115, 81, 32]
  | 5 => [209, 161, 65, 51, 58]
  | 6 => [221, 133, 55, 69, 62]
  | 7 => [247, 203, 125, 33, 34]
  | _ => [253, 217, 145, 39, 38]

/-- Convert the explicit lists to Finsets for subset logic. -/
def blocks (i : Fin 9) : Finset ℕ := (blockLists i).toFinset

def covered : Finset ℕ := Finset.univ.biUnion blocks

def remainder : Finset ℕ := domain \ covered

/-- Computable boolean checker for pairwise coprimality using lists. -/
def checkPairwiseCoprimeList (L : List ℕ) : Bool :=
  L.all fun a => L.all fun b => (a == b) || (Nat.gcd a b == 1)

theorem checkPairwiseCoprimeList_iff (L : List ℕ) :
    checkPairwiseCoprimeList L = true ↔ ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Nat.Coprime a b := by
  simp only [checkPairwiseCoprimeList, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h a ha b hb hab
    rcases h a ha b hb with h' | h'
    · exact False.elim (hab h')
    · exact h'
  · intro h a ha b hb
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr (h a ha b hb hab)

/-- These numerical certificates use kernel reduction natively and computably. -/
theorem blocks_pairwise (i : Fin 9) : PairwiseCoprime (blocks i) := by
  have h : PairwiseCoprime (blocks i) ↔ checkPairwiseCoprimeList (blockLists i) = true := by
    rw [checkPairwiseCoprimeList_iff]
    unfold PairwiseCoprime blocks
    simp only [List.mem_toFinset]
  rw [h]
  fin_cases i <;> decide

theorem remainder_card : remainder.card = 180 := by
  decide

private theorem card_union_family_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset ℕ) :
    (s.biUnion f).card ≤ ∑ i ∈ s, (f i).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_left ih _)

private theorem intersection_card_le_four
    (S : Finset ℕ) (hno : ¬ HasFive S) (i : Fin 9) :
    (S ∩ blocks i).card ≤ 4 := by
  by_contra h
  have hfive : 5 ≤ (S ∩ blocks i).card := by omega
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hfive
  apply hno
  refine ⟨T, ?_, hcard, ?_⟩
  · intro x hx
    exact (Finset.mem_inter.mp (hT hx)).1
  · intro a ha b hb hab
    exact blocks_pairwise i a
      (Finset.mem_inter.mp (hT ha)).2 b
      (Finset.mem_inter.mp (hT hb)).2 hab

/-- The upper bound for every subset with no five pairwise coprime elements. -/
theorem card_le_216_of_no_five
    (S : Finset ℕ) (hS : S ⊆ domain)
    (hno : ¬ HasFive S) :
    S.card ≤ 216 := by
  have hcover :
      S ⊆ remainder ∪
        Finset.univ.biUnion (fun i : Fin 9 => S ∩ blocks i) := by
    intro x hx
    by_cases hc : x ∈ covered
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hc
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_inter.mpr ⟨hx, hxi⟩⟩
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_sdiff.mpr ⟨hS hx, hc⟩

  have hsum :
      (∑ i : Fin 9, (S ∩ blocks i).card) ≤ 36 := by
    calc
      (∑ i : Fin 9, (S ∩ blocks i).card) ≤
          ∑ _i : Fin 9, (4 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact intersection_card_le_four S hno i
      _ = 36 := by simp

  have hfamily :
      (Finset.univ.biUnion
        (fun i : Fin 9 => S ∩ blocks i)).card ≤ 36 :=
    le_trans (card_union_family_le Finset.univ
      (fun i : Fin 9 => S ∩ blocks i)) hsum

  have hcard := Finset.card_le_card hcover
  have hunion := Finset.card_union_le remainder
    (Finset.univ.biUnion (fun i : Fin 9 => S ∩ blocks i))
  rw [remainder_card] at hunion
  omega

theorem every_217_subset : ForcesFive 217 := by
  intro S hS hcard
  by_contra hno
  have h := card_le_216_of_no_five S hS hno
  omega

/-- The extremal set: all multiples of 2, 3, 5, or 7 in the interval. -/
def bad : Finset ℕ :=
  domain.filter (fun n => n % 2 = 0 ∨ n % 3 = 0 ∨ n % 5 = 0 ∨ n % 7 = 0)

theorem bad_card : bad.card = 216 := by
  decide

theorem bad_subset : bad ⊆ domain := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

def color (n : ℕ) : Fin 4 :=
  if n % 2 = 0 then 0 else if n % 3 = 0 then 1 else if n % 5 = 0 then 2 else 3

def factor (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | _ => 7

private theorem factor_ge_two (i : Fin 4) : 2 ≤ factor i := by
  fin_cases i <;> decide

private theorem factor_dvd (n : ℕ) (hn : n ∈ bad) :
    factor (color n) ∣ n := by
  have h : n % 2 = 0 ∨ n % 3 = 0 ∨ n % 5 = 0 ∨ n % 7 = 0 :=
    (Finset.mem_filter.mp hn).2
  by_cases h2 : n % 2 = 0
  · have : 2 ∣ n := Nat.dvd_of_mod_eq_zero h2
    simpa [color, factor, h2]
  · by_cases h3 : n % 3 = 0
    · have : 3 ∣ n := Nat.dvd_of_mod_eq_zero h3
      simpa [color, factor, h2, h3]
    · by_cases h5 : n % 5 = 0
      · have : 5 ∣ n := Nat.dvd_of_mod_eq_zero h5
        simpa [color, factor, h2, h3, h5]
      · have h7 : n % 7 = 0 := by tauto
        have : 7 ∣ n := Nat.dvd_of_mod_eq_zero h7
        simpa [color, factor, h2, h3, h5]

/-- Pairwise coprime subsets of the extremal set have at most four elements. -/
theorem bad_pairwise_card_le_four
    (T : Finset ℕ) (hT : T ⊆ bad) (hcop : PairwiseCoprime T) :
    T.card ≤ 4 := by
  let f : {x // x ∈ T} → Fin 4 := fun x => color x.val
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have heq : color a.val = color b.val := hab
    have ha : factor (color a.val) ∣ a.val :=
      factor_dvd a.val (hT a.property)
    have hb : factor (color a.val) ∣ b.val := by
      rw [heq]
      exact factor_dvd b.val (hT b.property)
    have hg : factor (color a.val) ∣ Nat.gcd a.val b.val :=
      Nat.dvd_gcd ha hb
    have hc : Nat.gcd a.val b.val = 1 :=
      hcop a.val a.property b.val b.property hne
    rw [hc] at hg
    have hle : factor (color a.val) ≤ 1 :=
      Nat.le_of_dvd (by decide) hg
    have hge := factor_ge_two (color a.val)
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

theorem bad_has_no_five : ¬ HasFive bad := by
  rintro ⟨T, hT, hcard, hcop⟩
  have h := bad_pairwise_card_le_four T hT hcop
  omega

/-- The least requested cardinality is exactly 217. -/
theorem imo1991_problem3 :
    IsLeast {k : ℕ | ForcesFive k} 217 := by
  constructor
  · exact every_217_subset
  · intro k hk
    change ForcesFive k at hk
    by_contra hnot
    have hkle : k ≤ bad.card := by
      rw [bad_card]
      omega
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hkle
    have hSU : S ⊆ domain := fun x hx => bad_subset (hS hx)
    obtain ⟨T, hTS, hTcard, hcop⟩ := hk S hSU hcard
    exact bad_has_no_five
      ⟨T, (fun x hx => hS (hTS hx)), hTcard, hcop⟩

end IMO1991P3
