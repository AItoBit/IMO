import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max

private lemma infinite_sdiff_finite {α : Type*} {s t : Set α}
    (hs : s.Infinite) (ht : t.Finite) : (s \ t).Infinite := by
  intro hst
  apply hs
  apply (hst.union ht).subset
  intro x hx
  by_cases hxt : x ∈ t
  · exact Or.inr hxt
  · exact Or.inl ⟨hx, hxt⟩

private lemma two_primes_differ_at_high_bit (S : Set ℕ) (hS : S.Infinite)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
      ∃ k, 2 ≤ k ∧ p.testBit k ≠ q.testBit k := by
  classical
  let U : Set ℕ := S \ {2}
  have hU : U.Infinite := infinite_sdiff_finite hS (Set.finite_singleton 2)
  let U₀ : Set ℕ := {x ∈ U | x.testBit 1 = false}
  let U₁ : Set ℕ := {x ∈ U | x.testBit 1 = true}
  have hUnion : U₀ ∪ U₁ = U := by
    ext x
    change ((x ∈ U ∧ x.testBit 1 = false) ∨
      (x ∈ U ∧ x.testBit 1 = true)) ↔ x ∈ U
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      cases hbit : x.testBit 1
      · exact Or.inl ⟨hx, rfl⟩
      · exact Or.inr ⟨hx, rfl⟩
  have hInf : U₀.Infinite ∨ U₁.Infinite := by
    rw [← Set.infinite_union, hUnion]
    exact hU
  have auxiliary (T : Set ℕ) (hT : T.Infinite) (hTU : T ⊆ U)
      (c : Bool) (hc : ∀ x ∈ T, x.testBit 1 = c) :
      ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
        ∃ k, 2 ≤ k ∧ p.testBit k ≠ q.testBit k := by
    obtain ⟨p, hpT⟩ := hT.nonempty
    have hT' : (T \ {p}).Infinite :=
      infinite_sdiff_finite hT (Set.finite_singleton p)
    obtain ⟨q, hqT, hqp⟩ := hT'.nonempty
    have hpU := hTU hpT
    have hqU := hTU hqT
    have hpS : p ∈ S := hpU.1
    have hqS : q ∈ S := hqU.1
    have hp2 : p ≠ 2 := by simpa [U] using hpU.2
    have hq2 : q ≠ 2 := by simpa [U] using hqU.2
    have hpq : p ≠ q := Ne.symm (by simpa using hqp)
    refine ⟨p, hpS, q, hqS, hpq, ?_⟩
    by_cases hex : ∃ k, 2 ≤ k ∧ p.testBit k ≠ q.testBit k
    · exact hex
    exfalso
    have hbits' : ∀ k, 2 ≤ k → p.testBit k = q.testBit k := by
      intro k hk
      by_contra hne
      exact hex ⟨k, hk, hne⟩
    have hpodd : Odd p := (hprime p hpS).odd_of_ne_two hp2
    have hqodd : Odd q := (hprime q hqS).odd_of_ne_two hq2
    have hbit0 : p.testBit 0 = q.testBit 0 := by
      have hpmod : p % 2 = 1 := by
        rcases hpodd with ⟨r, hr⟩
        omega
      have hqmod : q % 2 = 1 := by
        rcases hqodd with ⟨r, hr⟩
        omega
      have hpbit : p.testBit 0 = true :=
        Nat.mod_two_eq_one_iff_testBit_zero.mp hpmod
      have hqbit : q.testBit 0 = true :=
        Nat.mod_two_eq_one_iff_testBit_zero.mp hqmod
      exact hpbit.trans hqbit.symm
    have hbit1 : p.testBit 1 = q.testBit 1 :=
      (hc p hpT).trans (hc q hqT).symm
    have : p = q := Nat.eq_of_testBit_eq fun i => by
      by_cases hi0 : i = 0
      · simpa [hi0] using hbit0
      by_cases hi1 : i = 1
      · simpa [hi1] using hbit1
      exact hbits' i (by omega)
    exact hpq this
  rcases hInf with h₀ | h₁
  · exact auxiliary U₀ h₀ (fun _ hx => hx.1) false (fun _ hx => hx.2)
  · exact auxiliary U₁ h₁ (fun _ hx => hx.1) true (fun _ hx => hx.2)

/-- IMO 1994, Problem 6. -/
theorem imo_1994_p6 (is_prod_of_k_distinct_elements : ℕ → ℕ → Set ℕ → Prop)
    (h₀ :
      is_prod_of_k_distinct_elements = fun n k S =>
        ∃ Sₙ : Finset ℕ, ↑Sₙ ⊆ S ∧ Finset.card Sₙ = k ∧ ∏ x ∈ Sₙ, x = n) :
    ∃ A : Set ℕ,
      (∀ a ∈ A, 0 < a) ∧
        ∀ S : Set ℕ,
          (S.Infinite ∧ ∀ s ∈ S, Nat.Prime s) →
            ∃ m ∈ A, ∃ n ∉ A, ∃ k ≥ 2, 0 < m ∧ 0 < n ∧
              is_prod_of_k_distinct_elements m k S ∧
                is_prod_of_k_distinct_elements n k S := by
  classical
  rw [h₀]
  let leastPrime : ℕ → ℕ := fun n =>
    if h : n.primeFactors.Nonempty then n.primeFactors.min' h else 0
  let A : Set ℕ :=
    {n | 0 < n ∧ (leastPrime n).testBit n.primeFactors.card = true}
  refine ⟨A, ?_, ?_⟩
  · intro a ha
    exact ha.1
  · intro S hS
    rcases hS with ⟨hSinf, hprime⟩
    obtain ⟨p, hpS, q, hqS, hpq, k, hk, hbit⟩ :=
      two_primes_differ_at_high_bit S hSinf hprime
    have construct (r s : ℕ) (hrS : r ∈ S) (hsS : s ∈ S)
        (hrbit : r.testBit k = true) (hsbit : s.testBit k = false) :
        ∃ m ∈ A, ∃ n ∉ A, ∃ k' ≥ 2, 0 < m ∧ 0 < n ∧
          (∃ Sₘ : Finset ℕ, ↑Sₘ ⊆ S ∧ Sₘ.card = k' ∧
            ∏ x ∈ Sₘ, x = m) ∧
          ∃ Sₙ : Finset ℕ, ↑Sₙ ⊆ S ∧ Sₙ.card = k' ∧
            ∏ x ∈ Sₙ, x = n := by
      let V : Set ℕ := S \ Set.Iic (max r s)
      have hVinf : V.Infinite :=
        infinite_sdiff_finite hSinf (Set.finite_Iic (max r s))
      obtain ⟨R, hRV, hRcard⟩ := hVinf.exists_subset_card_eq (k - 1)
      have hRS : (R : Set ℕ) ⊆ S := fun x hx => (hRV hx).1
      have hRlarge {x : ℕ} (hx : x ∈ R) : max r s < x := by
        simpa using (hRV hx).2
      have hrR : r ∉ R := by
        intro hr
        have := hRlarge hr
        omega
      have hsR : s ∉ R := by
        intro hs
        have := hRlarge hs
        omega
      let Fₘ : Finset ℕ := insert r R
      let Fₙ : Finset ℕ := insert s R
      have hFmcard : Fₘ.card = k := by
        simp [Fₘ, hrR, hRcard]
        omega
      have hFncard : Fₙ.card = k := by
        simp [Fₙ, hsR, hRcard]
        omega
      have hFmS : (Fₘ : Set ℕ) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxR
        · exact hrS
        · exact hRS hxR
      have hFnS : (Fₙ : Set ℕ) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxR
        · exact hsS
        · exact hRS hxR
      have hFmprime : ∀ x ∈ Fₘ, Nat.Prime x := fun x hx => hprime x (hFmS hx)
      have hFnprime : ∀ x ∈ Fₙ, Nat.Prime x := fun x hx => hprime x (hFnS hx)
      let m : ℕ := ∏ x ∈ Fₘ, x
      let n : ℕ := ∏ x ∈ Fₙ, x
      have hmpos : 0 < m := by
        dsimp [m]
        exact Finset.prod_pos fun x hx => (hFmprime x hx).pos
      have hnpos : 0 < n := by
        dsimp [n]
        exact Finset.prod_pos fun x hx => (hFnprime x hx).pos
      have hmFactors : m.primeFactors = Fₘ := by
        dsimp [m]
        exact Nat.primeFactors_prod hFmprime
      have hnFactors : n.primeFactors = Fₙ := by
        dsimp [n]
        exact Nat.primeFactors_prod hFnprime
      have hFmne : Fₘ.Nonempty := ⟨r, by simp [Fₘ]⟩
      have hFnne : Fₙ.Nonempty := ⟨s, by simp [Fₙ]⟩
      have hFmmin : Fₘ.min' hFmne = r := by
        apply le_antisymm
        · exact Finset.min'_le Fₘ r (by simp [Fₘ])
        · apply Finset.le_min' Fₘ hFmne r
          intro x hx
          rcases Finset.mem_insert.mp (by simpa [Fₘ] using hx) with rfl | hxR
          · exact le_rfl
          · exact le_trans (le_max_left r s) (le_of_lt (hRlarge hxR))
      have hFnmin : Fₙ.min' hFnne = s := by
        apply le_antisymm
        · exact Finset.min'_le Fₙ s (by simp [Fₙ])
        · apply Finset.le_min' Fₙ hFnne s
          intro x hx
          rcases Finset.mem_insert.mp (by simpa [Fₙ] using hx) with rfl | hxR
          · exact le_rfl
          · exact le_trans (le_max_right r s) (le_of_lt (hRlarge hxR))
      have hmA : m ∈ A := by
        change 0 < m ∧ (leastPrime m).testBit m.primeFactors.card = true
        refine ⟨hmpos, ?_⟩
        simp only [leastPrime, hmFactors]
        simp [hFmne, hFmmin, hFmcard, hrbit]
      have hnA : n ∉ A := by
        intro hnA'
        have hb : (leastPrime n).testBit n.primeFactors.card = true := hnA'.2
        simp only [leastPrime, hnFactors] at hb
        simp [hFnne, hFnmin, hFncard, hsbit] at hb
      refine ⟨m, hmA, n, hnA, k, hk, hmpos, hnpos, ?_, ?_⟩
      · exact ⟨Fₘ, hFmS, hFmcard, rfl⟩
      · exact ⟨Fₙ, hFnS, hFncard, rfl⟩
    cases hpbit : p.testBit k <;> cases hqbit : q.testBit k
    · exact False.elim (hbit (hpbit.trans hqbit.symm))
    · exact construct q p hqS hpS hqbit hpbit
    · exact construct p q hpS hqS hpbit hqbit
    · exact False.elim (hbit (hpbit.trans hqbit.symm))
