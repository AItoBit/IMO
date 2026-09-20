import Mathlib

namespace IMO2018P5

/-!
# IMO 2018 Problem 5 — stabilization core

The source's p-adic argument eventually proves that for all
sufficiently large `n`,

    a (n + 1) ∣ a n.

Because all `a n` are positive, this implies

    a (n + 1) ≤ a n.

Thus the tail is a nonincreasing sequence of positive
natural numbers and must eventually stabilize.

This file formalizes that final descent argument and the
finite synchronization step used in the p-adic proof.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Positivity plus divisibility gives an inequality
============================================================
-/

/--
If `x ∣ y` and `y > 0`, then `x ≤ y`.
-/
lemma le_of_dvd_pos
    {x y : ℕ}
    (hy : 0 < y)
    (hxy : x ∣ y) :
    x ≤ y := by

  exact
    Nat.le_of_dvd
      hy
      hxy

/--
If the next term divides the current positive term,
the sequence cannot increase.
-/
lemma next_le_of_dvd
    {a : ℕ → ℕ}
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    {n : ℕ}
    (hdiv :
      a (n + 1) ∣ a n) :
    a (n + 1) ≤ a n := by

  exact
    le_of_dvd_pos
      (hpos n)
      hdiv

/-!
============================================================
2. Strict descent if two divisible terms differ
============================================================
-/

/--
If `x ∣ y`, `y > 0`, and `x ≠ y`, then `x < y`.
-/
lemma lt_of_dvd_ne
    {x y : ℕ}
    (hy : 0 < y)
    (hdiv :
      x ∣ y)
    (hne :
      x ≠ y) :
    x < y := by

  have hle :
      x ≤ y :=
    Nat.le_of_dvd
      hy
      hdiv

  exact
    lt_of_le_of_ne
      hle
      hne

/-!
============================================================
3. The eventual tail is antitone
============================================================
-/

/--
If every successor after `N` divides its predecessor,
then the tail is nonincreasing.
-/
lemma tail_antitone
    {a : ℕ → ℕ}
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    {N : ℕ}
    (hdiv :
      ∀ n : ℕ,
        N ≤ n →
        a (n + 1) ∣ a n) :
    ∀ m n : ℕ,
      N ≤ m →
      m ≤ n →
      a n ≤ a m := by

  intro m n hm hmn

  induction n, hmn using Nat.le_induction with

  | base =>
      exact le_rfl

  | succ n hmn ih =>

      have hn :
          N ≤ n := by
        omega

      have hstep :
          a (n + 1) ≤ a n :=
        next_le_of_dvd
          hpos
          (hdiv n hn)

      exact
        le_trans
          hstep
          ih

/-!
============================================================
4. A minimum tail value exists
============================================================
-/

/--
There is at least one value appearing in the tail.
-/
lemma tail_values_nonempty
    (a : ℕ → ℕ)
    (N : ℕ) :
    Set.Nonempty
      {x : ℕ |
        ∃ n : ℕ,
          N ≤ n ∧
          a n = x} := by

  refine
    ⟨a N, ?_⟩

  exact
    ⟨N,
     le_rfl,
     rfl⟩

/--
The tail values have a minimum.
-/
lemma exists_min_tail_value
    (a : ℕ → ℕ)
    (N : ℕ) :
    ∃ m : ℕ,
      (∃ n : ℕ,
        N ≤ n ∧
        a n = m) ∧
      ∀ x : ℕ,
        (∃ n : ℕ,
          N ≤ n ∧
          a n = x) →
        m ≤ x := by

  let S : Set ℕ :=
    {x : ℕ |
      ∃ n : ℕ,
        N ≤ n ∧
        a n = x}

  have hS :
      S.Nonempty := by

    exact
      tail_values_nonempty
        a
        N

  let m : ℕ :=
    sInf S

  have hmS :
      m ∈ S := by

    exact
      Nat.sInf_mem
        hS

  refine
    ⟨m,
     ?_,
     ?_⟩

  · exact hmS

  · intro x hx

    exact
      Nat.sInf_le
        hx

/-!
============================================================
5. Eventual constancy of a divisibility chain
============================================================
-/

/--
A positive natural-number sequence with

    a(n+1) ∣ a(n)

eventually is eventually constant.
-/
theorem eventually_constant_of_eventually_dvd
    (a : ℕ → ℕ)
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    (N : ℕ)
    (hdiv :
      ∀ n : ℕ,
        N ≤ n →
        a (n + 1) ∣ a n) :
    ∃ M : ℕ,
      N ≤ M ∧
      ∀ n : ℕ,
        M ≤ n →
        a n = a M := by

  obtain
    ⟨m,
     ⟨M, hNM, hM⟩,
     hmin⟩ :=
    exists_min_tail_value
      a
      N

  refine
    ⟨M,
     hNM,
     ?_⟩

  intro n hMn

  have hnN :
      N ≤ n := by
    omega

  have hupper :
      a n ≤ a M :=
    tail_antitone
      hpos
      hdiv
      M
      n
      hNM
      hMn

  have hlower :
      m ≤ a n := by

    apply hmin

    exact
      ⟨n,
       hnN,
       rfl⟩

  rw [hM] at hupper

  have han :
      a n = m := by
    omega

  calc
    a n = m :=
      han

    _ = a M :=
      hM.symm

/-!
============================================================
6. Consecutive terms are eventually equal
============================================================
-/

/--
The formulation appearing in the IMO problem:

there exists `M` such that

    a m = a (m+1)

for all `m ≥ M`.
-/
theorem consecutive_equal_eventually
    (a : ℕ → ℕ)
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    (N : ℕ)
    (hdiv :
      ∀ n : ℕ,
        N ≤ n →
        a (n + 1) ∣ a n) :
    ∃ M : ℕ,
      ∀ m : ℕ,
        M ≤ m →
        a m = a (m + 1) := by

  obtain
    ⟨M, _hNM, hconst⟩ :=
    eventually_constant_of_eventually_dvd
      a
      hpos
      N
      hdiv

  refine
    ⟨M, ?_⟩

  intro m hm

  have hm1 :
      M ≤ m + 1 := by
    omega

  have h₁ :
      a m = a M :=
    hconst
      m
      hm

  have h₂ :
      a (m + 1) = a M :=
    hconst
      (m + 1)
      hm1

  exact
    h₁.trans
      h₂.symm

/-!
============================================================
7. Finite synchronization of eventual properties
============================================================
-/

/--
If finitely many properties each hold eventually,
there is one common index after which they all hold.
-/
lemma finite_eventually_all
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (P : ι → ℕ → Prop)
    (h :
      ∀ i ∈ s,
        ∃ N : ℕ,
          ∀ n : ℕ,
            N ≤ n →
            P i n) :
    ∃ M : ℕ,
      ∀ i ∈ s,
        ∀ n : ℕ,
          M ≤ n →
          P i n := by

  classical

  induction s using Finset.induction_on with

  | empty =>

      refine
        ⟨0, ?_⟩

      intro i hi

      simp at hi

  | @insert i s hi ih =>

      obtain
        ⟨Ni, hNi⟩ :=
        h i
          (Finset.mem_insert_self i s)

      have htail :
          ∀ j ∈ s,
            ∃ N : ℕ,
              ∀ n : ℕ,
                N ≤ n →
                P j n := by

        intro j hj

        exact
          h j
            (Finset.mem_insert_of_mem hj)

      obtain
        ⟨Ns, hNs⟩ :=
        ih
          htail

      refine
        ⟨max Ni Ns,
         ?_⟩

      intro j hj n hn

      have hjCases :
          j = i ∨ j ∈ s :=
        Finset.mem_insert.mp
          hj

      rcases hjCases with
        rfl | hjs

      · apply hNi

        exact
          le_trans
            (Nat.le_max_left Ni Ns)
            hn

      · apply
          hNs
            j
            hjs
            n

        exact
          le_trans
            (Nat.le_max_right Ni Ns)
            hn

/-!
============================================================
8. Synchronizing valuation stabilization
============================================================
-/

/--
Abstract version of the source's finite-prime step.

For each prime in a finite set, suppose the associated
valuation is eventually unchanged between consecutive terms.

Then all those valuations stabilize simultaneously after
one common index.
-/
lemma finite_valuation_stabilization
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (v : ι → ℕ → ℕ)
    (h :
      ∀ p ∈ s,
        ∃ N : ℕ,
          ∀ n : ℕ,
            N ≤ n →
            v p (n + 1) =
              v p n) :
    ∃ M : ℕ,
      ∀ p ∈ s,
        ∀ n : ℕ,
          M ≤ n →
          v p (n + 1) =
            v p n := by

  exact
    finite_eventually_all
      s
      (fun p n =>
        v p (n + 1) =
          v p n)
      h

/-!
============================================================
9. Strict decrease at every nonconstant step
============================================================
-/

/--
If consecutive terms differ, the divisibility chain
strictly decreases.
-/
lemma strict_drop_of_change
    (a : ℕ → ℕ)
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    {n : ℕ}
    (hdiv :
      a (n + 1) ∣ a n)
    (hne :
      a (n + 1) ≠ a n) :
    a (n + 1) < a n := by

  exact
    lt_of_dvd_ne
      (hpos n)
      hdiv
      hne

/-!
============================================================
10. Packaging the final stage of IMO 2018 Problem 5
============================================================
-/

/--
Once the p-adic portion of the source proof has established

    a(n+1) ∣ a(n)

for all sufficiently large `n`, the original conclusion
follows.
-/
theorem imo2018_p5_final_core
    (a : ℕ → ℕ)
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    (N : ℕ)
    (hdiv :
      ∀ n : ℕ,
        N ≤ n →
        a (n + 1) ∣ a n) :
    ∃ M : ℕ,
      ∀ m : ℕ,
        M ≤ m →
        a m = a (m + 1) := by

  exact
    consecutive_equal_eventually
      a
      hpos
      N
      hdiv

end IMO2018P5
