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

namespace IMO1978Q6

/-- A colouring `c` of the numbers `1, …, 1978` by six countries is `SumFreeColoring`
if no member's number is the sum of the numbers of two members of his own country. -/
def SumFreeColoring (c : ℕ → Fin 6) : Prop :=
  ∀ x y : ℕ, 0 < x → 0 < y → x + y ≤ 1978 → c x = c (x + y) → c y = c (x + y) → False

/-- The invariant carried through the pigeonhole induction: `T` is a set of numbers in
`[1, 1978]`, none of whose elements, and none of whose positive pairwise differences,
receives a colour from the set `F` of already-discarded colours. -/
def Inv (c : ℕ → Fin 6) (T : Finset ℕ) (F : Finset (Fin 6)) : Prop :=
  (∀ t ∈ T, 0 < t ∧ t ≤ 1978) ∧ (∀ t ∈ T, c t ∉ F) ∧
    (∀ t ∈ T, ∀ t' ∈ T, t < t' → c (t' - t) ∉ F)

lemma step (c : ℕ → Fin 6) (hc : SumFreeColoring c) (T : Finset ℕ) (F : Finset (Fin 6))
    (q : ℕ) (hinv : Inv c T F) (hcard : q * (6 - F.card) < T.card) :
    ∃ (T' : Finset ℕ) (F' : Finset (Fin 6)), Inv c T' F' ∧ F'.card = F.card + 1 ∧ q ≤ T'.card := by
  obtain ⟨hpos, hcol, hdiff⟩ := hinv
  -- pigeonhole: some colour outside `F` occurs at least `q + 1` times in `T`
  have hsum : T.card = ∑ a ∈ Fᶜ, (T.filter (fun t => c t = a)).card :=
    Finset.card_eq_sum_card_fiberwise (fun t ht => Finset.mem_compl.mpr (hcol t ht))
  have hFc : (Fᶜ : Finset (Fin 6)).card = 6 - F.card := by
    rw [Finset.card_compl]; simp
  obtain ⟨a, ha, hA⟩ : ∃ a ∈ (Fᶜ : Finset (Fin 6)), q + 1 ≤ (T.filter (fun t => c t = a)).card := by
    by_contra hcon
    push_neg at hcon
    have hle : ∑ a ∈ (Fᶜ : Finset (Fin 6)), (T.filter (fun t => c t = a)).card
        ≤ ∑ _a ∈ (Fᶜ : Finset (Fin 6)), q :=
      Finset.sum_le_sum (fun a ha => Nat.lt_succ_iff.mp (hcon a ha))
    rw [Finset.sum_const, smul_eq_mul, hFc, mul_comm] at hle
    omega
  set A : Finset ℕ := T.filter (fun t => c t = a)
  have hAsub : A ⊆ T := Finset.filter_subset _ _
  have hAcol : ∀ t ∈ A, c t = a := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  set M : ℕ := A.max' hAne
  have hMA : M ∈ A := A.max'_mem hAne
  have hMT : M ∈ T := hAsub hMA
  have hMle : ∀ t ∈ A, t ≤ M := fun t ht => A.le_max' t ht
  refine ⟨(A.erase M).image (fun t => M - t), insert a F, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- positivity / boundedness
    intro u hu
    simp only [Finset.mem_image, Finset.mem_erase] at hu
    obtain ⟨t, ⟨htM, htA⟩, rfl⟩ := hu
    have h1 : t < M := lt_of_le_of_ne (hMle t htA) htM
    have h2 : M ≤ 1978 := (hpos M hMT).2
    omega
  · -- colours of elements
    intro u hu
    simp only [Finset.mem_image, Finset.mem_erase] at hu
    obtain ⟨t, ⟨htM, htA⟩, rfl⟩ := hu
    have htT : t ∈ T := hAsub htA
    have h1 : t < M := lt_of_le_of_ne (hMle t htA) htM
    have hnF : c (M - t) ∉ F := hdiff t htT M hMT h1
    simp only [Finset.mem_insert]
    rintro (heq | hmem)
    · -- `c (M - t) = a` would give a monochromatic solution `t + (M - t) = M`
      refine hc t (M - t) (hpos t htT).1 (by omega) (by
        have := (hpos M hMT).2; omega) ?_ ?_
      · rw [show t + (M - t) = M by omega, hAcol t htA, hAcol M hMA]
      · rw [show t + (M - t) = M by omega, heq, hAcol M hMA]
    · exact hnF hmem
  · -- colours of differences
    intro u hu u' hu' hlt
    simp only [Finset.mem_image, Finset.mem_erase] at hu hu'
    obtain ⟨t, ⟨htM, htA⟩, rfl⟩ := hu
    obtain ⟨s, ⟨hsM, hsA⟩, rfl⟩ := hu'
    have htT : t ∈ T := hAsub htA
    have hsT : s ∈ T := hAsub hsA
    have h1 : t < M := lt_of_le_of_ne (hMle t htA) htM
    have h2 : s < M := lt_of_le_of_ne (hMle s hsA) hsM
    have h3 : s < t := by omega
    have hsub : M - s - (M - t) = t - s := by omega
    rw [hsub]
    have hnF : c (t - s) ∉ F := hdiff s hsT t htT h3
    simp only [Finset.mem_insert]
    rintro (heq | hmem)
    · refine hc s (t - s) (hpos s hsT).1 (by omega) (by
        have := (hpos t htT).2; omega) ?_ ?_
      · rw [show s + (t - s) = t by omega, hAcol s hsA, hAcol t htA]
      · rw [show s + (t - s) = t by omega, heq, hAcol t htA]
    · exact hnF hmem
  · -- the set of discarded colours grows by one
    have : a ∉ F := Finset.mem_compl.mp ha
    rw [Finset.card_insert_of_notMem this]
  · -- cardinality bound
    have hinj : Set.InjOn (fun t => M - t) (A.erase M) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_erase] at hx hy
      have h1 : x ≤ M := hMle x hx.2
      have h2 : y ≤ M := hMle y hy.2
      simp only at hxy
      omega
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hMA]
    omega

/-- **IMO 1978, Problem 6.**  An international society has members from six different
countries, the members being numbered `1, 2, …, 1978`.  Then some member's number is the
sum of the numbers of two (not necessarily distinct) members from his own country. -/
theorem imo1978_p6 (c : ℕ → Fin 6) :
    ∃ x y z : ℕ, x ∈ Finset.Icc 1 1978 ∧ y ∈ Finset.Icc 1 1978 ∧ z ∈ Finset.Icc 1 1978 ∧
      x + y = z ∧ c x = c z ∧ c y = c z := by
  by_contra hcon
  push_neg at hcon
  have hc : SumFreeColoring c := by
    intro x y hx hy hxy h1 h2
    have hx' : x ∈ Finset.Icc 1 1978 := Finset.mem_Icc.mpr ⟨hx, by omega⟩
    have hy' : y ∈ Finset.Icc 1 1978 := Finset.mem_Icc.mpr ⟨hy, by omega⟩
    have hz' : x + y ∈ Finset.Icc 1 1978 := Finset.mem_Icc.mpr ⟨by omega, hxy⟩
    exact absurd h2 (hcon x y (x + y) hx' hy' hz' rfl h1)
  have h0 : Inv c (Finset.Icc 1 1978) ∅ := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_Icc] at ht
      omega
    · intro t _; simp
    · intro t _ t' _ _; simp
  have hcard0 : (Finset.Icc 1 1978).card = 1978 := by simp
  obtain ⟨T1, F1, i1, f1, s1⟩ := step c hc _ ∅ 329 h0 (by simp [hcard0])
  obtain ⟨T2, F2, i2, f2, s2⟩ := step c hc T1 F1 65 i1 (by omega)
  obtain ⟨T3, F3, i3, f3, s3⟩ := step c hc T2 F2 16 i2 (by omega)
  obtain ⟨T4, F4, i4, f4, s4⟩ := step c hc T3 F3 5 i3 (by omega)
  obtain ⟨T5, F5, i5, f5, s5⟩ := step c hc T4 F4 2 i4 (by omega)
  obtain ⟨T6, F6, i6, f6, s6⟩ := step c hc T5 F5 1 i5 (by omega)
  -- now `F6` contains all six colours, yet `T6` is nonempty
  have hF6 : F6 = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [f6, f5, f4, f3, f2, f1]
  obtain ⟨t, ht⟩ : T6.Nonempty := Finset.card_pos.mp (by omega)
  exact i6.2.1 t ht (by simp [hF6])

end IMO1978Q6
