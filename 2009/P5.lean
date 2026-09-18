import Mathlib

/-!
# IMO 2009 Problem 5

Determine all functions `f` from the positive integers to the positive
integers such that, for every positive integers `a,b`, the numbers

    a, f b, f (b + f a - 1)

are the side lengths of a nondegenerate triangle.

The unique solution is

    f n = n.

Positive integers are represented by natural numbers together with
positivity hypotheses.
-/

namespace IMO2009P5

open Finset

/-- Three natural numbers satisfy the strict triangle inequalities. -/
def TriangleSides (a b c : ℕ) : Prop :=
  a < b + c ∧
  b < a + c ∧
  c < a + b

/-! ## Elementary triangle lemmas -/

/--
If `1, a, b` are the side lengths of a nondegenerate triangle,
then `a = b`.
-/
lemma triangle_one_left_eq
    {a b : ℕ}
    (h : TriangleSides 1 a b) :
    a = b := by
  rcases h with ⟨h₁, h₂, h₃⟩
  omega

/--
If `a, 1, b` are the side lengths of a nondegenerate triangle,
then `a = b`.
-/
lemma triangle_one_middle_eq
    {a b : ℕ}
    (h : TriangleSides a 1 b) :
    a = b := by
  rcases h with ⟨h₁, h₂, h₃⟩
  omega

/-! ## Periodicity implies boundedness -/

/--
A natural-valued sequence with a positive period is bounded.
-/
lemma bounded_of_periodic
    (F : ℕ → ℕ)
    (d : ℕ)
    (hd : 0 < d)
    (hper : ∀ n : ℕ, F (n + d) = F n) :
    ∃ M : ℕ, ∀ n : ℕ, F n ≤ M := by

  let M : ℕ :=
    ∑ i ∈ Finset.range d, F i

  refine ⟨M, ?_⟩

  intro n

  induction n using Nat.strong_induction_on with
  | h n ih =>

      by_cases hn : n < d

      · have hmem :
            n ∈ Finset.range d :=
          Finset.mem_range.mpr hn

        dsimp [M]

        exact
          Finset.single_le_sum
            (fun i hi => Nat.zero_le (F i))
            hmem

      · have hdn :
            d ≤ n := by
          omega

        have hlt :
            n - d < n := by
          omega

        have hIH :
            F (n - d) ≤ M :=
          ih (n - d) hlt

        have hnd :
            (n - d) + d = n := by
          omega

        have heq :
            F n = F (n - d) := by
          calc
            F n = F ((n - d) + d) := by
              rw [hnd]
            _ = F (n - d) :=
              hper (n - d)

        rw [heq]

        exact hIH

/-! ## Subadditive involutions -/

/--
Repeated subadditivity:

    g (m * y) ≤ m * g y.
-/
lemma subadd_mul_le
    (g : ℕ → ℕ)
    (hg0 : g 0 = 0)
    (hsub :
      ∀ x y : ℕ,
        g (x + y) ≤ g x + g y) :
    ∀ m y : ℕ,
      g (m * y) ≤ m * g y := by

  intro m y

  induction m with

  | zero =>
      simp [hg0]

  | succ m ih =>
      calc
        g (Nat.succ m * y)
            = g (m * y + y) := by
                rw [Nat.succ_mul]

        _ ≤ g (m * y) + g y :=
          hsub (m * y) y

        _ ≤ m * g y + g y :=
          Nat.add_le_add_right ih (g y)

        _ = Nat.succ m * g y := by
          rw [Nat.succ_mul]

/--
A self-inverse subadditive function `g : ℕ → ℕ` fixing `0`
must be the identity.
-/
lemma involutive_subadditive_eq_id
    (g : ℕ → ℕ)
    (hg0 : g 0 = 0)
    (hinv :
      ∀ n : ℕ,
        g (g n) = n)
    (hsub :
      ∀ x y : ℕ,
        g (x + y) ≤ g x + g y) :
    ∀ n : ℕ, g n = n := by

  intro n

  by_contra hne

  /-
  If `g n ≠ n`, involutivity gives some `x` with `x < g x`.
  -/
  obtain ⟨x, hx⟩ :
      ∃ x : ℕ, x < g x := by

    by_cases hng : n < g n

    · exact ⟨n, hng⟩

    · have hgn :
          g n < n := by
        omega

      refine ⟨g n, ?_⟩

      rw [hinv n]

      exact hgn

  let y : ℕ := g x

  have hxy :
      x < y := by
    exact hx

  have hypos :
      0 < y := by
    omega

  have hgy :
      g y = x := by
    dsimp [y]
    exact hinv x

  /-
  Bound the finitely many values `g r` with `r < y`.
  -/
  let C : ℕ :=
    ∑ r ∈ Finset.range y, g r

  have hC :
      ∀ r : ℕ,
        r < y →
        g r ≤ C := by

    intro r hr

    have hrmem :
        r ∈ Finset.range y :=
      Finset.mem_range.mpr hr

    dsimp [C]

    exact
      Finset.single_le_sum
        (fun i hi => Nat.zero_le (g i))
        hrmem

  /-
  Set a threshold N.
  -/
  let N : ℕ :=
    (C + 1) * y

  /-
  Beyond N, we prove g(q) < q.
  -/
  have heventual :
      ∀ q : ℕ,
        N < q →
        g q < q := by

    intro q hq

    let a : ℕ := q / y
    let r : ℕ := q % y

    have hr :
        r < y := by
      dsimp [r]
      exact Nat.mod_lt q hypos

    have hdecomp :
        a * y + r = q := by
      dsimp [a, r]
      simpa [Nat.mul_comm] using
        (Nat.div_add_mod q y)

    /-
    Show `C < a`.
    -/
    have ha :
        C < a := by

      by_contra hnot

      have hac :
          a ≤ C := by
        omega

      have hay :
          a * y ≤ C * y := by
        exact Nat.mul_le_mul_right y hac

      have hqle :
          q ≤ (C + 1) * y := by

        have hlt :
            q < (C + 1) * y := by

          rw [← hdecomp]

          calc
            a * y + r
                < a * y + y := by
                  exact
                    Nat.add_lt_add_left
                      hr
                      (a * y)

            _ ≤ C * y + y := by
                  exact
                    Nat.add_le_add_right
                      hay
                      y

            _ = (C + 1) * y := by
                  rw [Nat.add_mul]
                  simp

        exact Nat.le_of_lt hlt

      dsimp [N] at hq

      omega

    /-
    Subadditivity on the multiple a*y.
    -/
    have hmul :
        g (a * y) ≤ a * g y :=
      subadd_mul_le
        g hg0 hsub a y

    have hqbound :
        g q ≤ a * x + C := by

      rw [← hdecomp]

      calc
        g (a * y + r)
            ≤ g (a * y) + g r :=
          hsub (a * y) r

        _ ≤ a * g y + C :=
          Nat.add_le_add
            hmul
            (hC r hr)

        _ = a * x + C := by
          rw [hgy]

    /-
    Show the upper bound is strictly below q.
    -/
    have hstrict :
        a * x + C < q := by

      rw [← hdecomp]

      have hxy1 :
          x + 1 ≤ y := by
        omega

      have hmulxy :
          a * (x + 1) ≤ a * y :=
        Nat.mul_le_mul_left a hxy1

      have hCa :
          C + 1 ≤ a := by
        omega

      have hCx :
          a * x + C < a * (x + 1) := by

        have hC_lt_a :
            C < a := by
          omega

        calc
          a * x + C
              < a * x + a := by
                exact
                  Nat.add_lt_add_left
                    hC_lt_a
                    (a * x)

          _ = a * (x + 1) := by
                rw [Nat.mul_add]
                simp

      have hmain :
          a * x + C < a * y :=
        lt_of_lt_of_le
          hCx
          hmulxy

      exact
        lt_of_lt_of_le
          hmain
          (Nat.le_add_right (a * y) r)

    exact
      lt_of_le_of_lt
        hqbound
        hstrict

  /-
  Bound all values of g on [0,N].
  -/
  let D : ℕ :=
    ∑ p ∈ Finset.range (N + 1), g p

  have hD :
      ∀ p : ℕ,
        p ≤ N →
        g p ≤ D := by

    intro p hp

    have hpmem :
        p ∈ Finset.range (N + 1) := by
      apply Finset.mem_range.mpr
      omega

    dsimp [D]

    exact
      Finset.single_le_sum
        (fun i hi => Nat.zero_le (g i))
        hpmem

  /-
  Choose Q larger than both N and D.
  -/
  let Q : ℕ :=
    N + D + 1

  have hQN :
      N < Q := by
    dsimp [Q]
    omega

  have hQD :
      D < Q := by
    dsimp [Q]
    omega

  have hQsmall :
      g Q < Q :=
    heventual Q hQN

  let p : ℕ :=
    g Q

  have hpQ :
      p < Q := by
    exact hQsmall

  have hgp :
      g p = Q := by
    dsimp [p]
    exact hinv Q

  by_cases hpN :
      p ≤ N

  · have hpbound :
        g p ≤ D :=
      hD p hpN

    rw [hgp] at hpbound

    omega

  · have hNp :
        N < p := by
      omega

    have hpsmall :
        g p < p :=
      heventual p hNp

    rw [hgp] at hpsmall

    omega

/-! ## Main argument -/

/--
Forward implication of IMO 2009 Problem 5.
-/
theorem imo2009_p5_forward
    (f : ℕ → ℕ)
    (hfpos :
      ∀ n : ℕ,
        0 < n →
        0 < f n)
    (htri :
      ∀ a b : ℕ,
        0 < a →
        0 < b →
        TriangleSides
          a
          (f b)
          (f (b + f a - 1))) :
    ∀ n : ℕ,
      0 < n →
      f n = n := by

  /-
  Step 1: prove f(1) = 1.
  -/
  have hf1 :
      f 1 = 1 := by

    let u : ℕ :=
      f 1

    have hu :
        0 < u := by
      dsimp [u]
      exact hfpos 1 (by omega)

    by_contra hne

    have hu1 :
        1 < u := by
      omega

    let d : ℕ :=
      u - 1

    have hd :
        0 < d := by
      dsimp [d]
      omega

    let F : ℕ → ℕ :=
      fun n => f (n + 1)

    /-
    Taking a = 1 gives periodicity.
    -/
    have hper :
        ∀ n : ℕ,
          F (n + d) = F n := by

      intro n

      have ht :=
        htri
          1
          (n + 1)
          (by omega)
          (by omega)

      have heq :
          f (n + 1) =
            f ((n + 1) + f 1 - 1) := by
        exact triangle_one_left_eq ht

      have hu_eq :
          f 1 = u := by
        rfl

      have hidx :
          (n + 1) + f 1 - 1 =
            (n + d) + 1 := by
        rw [hu_eq]
        dsimp [d]
        omega

      change
        f ((n + d) + 1) =
          f (n + 1)

      rw [← hidx]

      exact heq.symm

    obtain ⟨M, hM⟩ :=
      bounded_of_periodic
        F d hd hper

    have hfbound :
        ∀ z : ℕ,
          0 < z →
          f z ≤ M := by

      intro z hz

      have hz1 :
          (z - 1) + 1 = z := by
        omega

      have hm :=
        hM (z - 1)

      change
        f ((z - 1) + 1) ≤ M
        at hm

      rw [hz1] at hm

      exact hm

    /-
    Take A = 2M+1 and contradict the triangle inequality.
    -/
    let A : ℕ :=
      2 * M + 1

    have hApos :
        0 < A := by
      dsimp [A]
      omega

    have hfApos :
        0 < f A :=
      hfpos A hApos

    have ht :=
      htri A 1 hApos (by omega)

    rcases ht with
      ⟨hfirst, _, _⟩

    have hidx :
        1 + f A - 1 = f A := by
      omega

    have hfirst' :
        A < f 1 + f (f A) := by
      simpa [hidx] using hfirst

    have hf1bound :
        f 1 ≤ M :=
      hfbound 1 (by omega)

    have hffAbound :
        f (f A) ≤ M :=
      hfbound (f A) hfApos

    have hsumBound :
        f 1 + f (f A) ≤ 2 * M := by
      omega

    have hAlarge :
        2 * M < A := by
      dsimp [A]
      omega

    omega

  /-
  Step 2:
      f(f x) = x.
  -/
  have hinv :
      ∀ x : ℕ,
        0 < x →
        f (f x) = x := by

    intro x hx

    have ht :=
      htri x 1 hx (by omega)

    have hidx :
        1 + f x - 1 = f x := by

      have hfxpos :
          0 < f x :=
        hfpos x hx

      omega

    rw [hf1, hidx] at ht

    exact
      (triangle_one_middle_eq ht).symm

  /-
  Define g(x) = f(x+1)-1.
  -/
  let g : ℕ → ℕ :=
    fun x => f (x + 1) - 1

  have hg_succ :
      ∀ x : ℕ,
        g x + 1 = f (x + 1) := by

    intro x

    have hp :
        0 < f (x + 1) :=
      hfpos (x + 1) (by omega)

    dsimp [g]

    omega

  have hg0 :
      g 0 = 0 := by
    dsimp [g]
    rw [hf1]

  /-
  g is an involution.
  -/
  have hginv :
      ∀ x : ℕ,
        g (g x) = x := by

    intro x

    have hff :
        f (f (x + 1)) = x + 1 :=
      hinv (x + 1) (by omega)

    have hs :
        g (g x) + 1 =
          f (g x + 1) :=
      hg_succ (g x)

    have hx :
        g x + 1 =
          f (x + 1) :=
      hg_succ x

    rw [hx, hff] at hs

    omega

  /-
  Prove subadditivity.
  -/
  have hgsub :
      ∀ x y : ℕ,
        g (x + y) ≤ g x + g y := by

    intro x y

    have hfx :
        0 < f (x + 1) :=
      hfpos (x + 1) (by omega)

    have ht :=
      htri
        (f (x + 1))
        (y + 1)
        hfx
        (by omega)

    have hff :
        f (f (x + 1)) = x + 1 :=
      hinv (x + 1) (by omega)

    have hidx :
        (y + 1) +
              f (f (x + 1)) -
              1
          =
        x + y + 1 := by
      rw [hff]
      omega

    rcases ht with
      ⟨_, _, hthird⟩

    rw [hidx] at hthird

    have hxg :
        g x + 1 =
          f (x + 1) :=
      hg_succ x

    have hyg :
        g y + 1 =
          f (y + 1) :=
      hg_succ y

    have hxyg :
        g (x + y) + 1 =
          f (x + y + 1) := by
      simpa [Nat.add_assoc] using
        hg_succ (x + y)

    omega

  /-
  Hence g is the identity.
  -/
  have hgid :
      ∀ x : ℕ,
        g x = x :=
    involutive_subadditive_eq_id
      g hg0 hginv hgsub

  /-
  Recover f(n)=n.
  -/
  intro n hn

  have hidx :
      (n - 1) + 1 = n := by
    omega

  have hg :
      g (n - 1) = n - 1 :=
    hgid (n - 1)

  have hs :
      g (n - 1) + 1 =
        f ((n - 1) + 1) :=
    hg_succ (n - 1)

  rw [hidx] at hs

  omega

/-! ## Complete characterization -/

/--
The condition from the olympiad problem.
-/
def Good (f : ℕ → ℕ) : Prop :=
  (∀ n : ℕ,
      0 < n →
      0 < f n) ∧
  (∀ a b : ℕ,
      0 < a →
      0 < b →
      TriangleSides
        a
        (f b)
        (f (b + f a - 1)))

/--
The identity function satisfies the problem condition.
-/
lemma identity_is_good :
    Good (fun n : ℕ => n) := by

  constructor

  · intro n hn
    exact hn

  · intro a b ha hb

    change
      TriangleSides
        a
        b
        (b + a - 1)

    unfold TriangleSides

    constructor

    · omega

    constructor

    · omega

    · omega

/--
**IMO 2009 Problem 5.**

The functions satisfying the condition are exactly the identity function
on the positive integers.
-/
theorem imo2009_p5
    (f : ℕ → ℕ) :
    Good f ↔
      ∀ n : ℕ,
        0 < n →
        f n = n := by

  constructor

  · intro hf

    exact
      imo2009_p5_forward
        f
        hf.1
        hf.2

  · intro hid

    constructor

    · intro n hn

      rw [hid n hn]

      exact hn

    · intro a b ha hb

      have hfa :
          f a = a :=
        hid a ha

      have hfb :
          f b = b :=
        hid b hb

      rw [hfa, hfb]

      have hargpos :
          0 < b + a - 1 := by
        omega

      have hfarg :
          f (b + a - 1) =
            b + a - 1 :=
        hid
          (b + a - 1)
          hargpos

      rw [hfarg]

      unfold TriangleSides

      constructor

      · omega

      constructor

      · omega

      · omega

end IMO2009P5
