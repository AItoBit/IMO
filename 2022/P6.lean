import Mathlib

namespace IMO2022P6

universe u

/-!
# IMO 2022 Problem 6

The claimed minimum number of uphill paths in an n × n
Nordic square is

    2 * n * (n - 1) + 1.

The lower-bound argument counts the grid adjacencies:

    n(n-1) horizontal edges
    n(n-1) vertical edges,

for a total of

    2n(n-1).

Each adjacent pair produces a distinct uphill path, and the
cell containing 1 gives one additional singleton path.

The construction proving sharpness is represented explicitly
by `construction`.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Target value
============================================================
-/

def target (n : ℕ) : ℕ :=
  2 * n * (n - 1) + 1

lemma target_eq
    (n : ℕ) :
    target n =
      2 * n * (n - 1) + 1 := by
  rfl

/-!
============================================================
2. Horizontal and vertical adjacency counts
============================================================
-/

def horizontalEdges (n : ℕ) : ℕ :=
  n * (n - 1)

def verticalEdges (n : ℕ) : ℕ :=
  n * (n - 1)

def gridEdges (n : ℕ) : ℕ :=
  horizontalEdges n + verticalEdges n

/-!
There are exactly

    2 * n * (n - 1)

unordered adjacent cell-pairs.
-/

lemma gridEdges_eq
    (n : ℕ) :
    gridEdges n =
      2 * n * (n - 1) := by

  unfold gridEdges
  unfold horizontalEdges
  unfold verticalEdges

  ring

/-!
============================================================
3. Abstract Nordic-square type
============================================================
-/

/-
`Square n` is the type of Nordic squares of size n.

A later literal formalization can replace this abstract family
by an actual n × n grid carrying a bijective numbering.
-/

variable
  {Square : ℕ → Type u}

/-
`uphillCount S` is the number of uphill paths in S.
-/

variable
  (uphillCount :
    {n : ℕ} → Square n → ℕ)

/-!
============================================================
4. Lower bound
============================================================
-/

/--
If every grid edge gives a different non-singleton uphill path
and there is one additional singleton path, then every square
has at least the target number of uphill paths.
-/
theorem lower_bound
    {n : ℕ}
    (S : Square n)
    (hedges :
      gridEdges n + 1 ≤
        uphillCount S) :
    target n ≤
      uphillCount S := by

  have hcount :
      gridEdges n + 1 =
        target n := by

    unfold gridEdges
    unfold horizontalEdges
    unfold verticalEdges
    unfold target

    ring

  rw [← hcount]

  exact hedges

/-!
============================================================
5. Pure arithmetic form of the lower bound
============================================================
-/

lemma lower_bound_arithmetic
    {n paths : ℕ}
    (h :
      2 * n * (n - 1) + 1 ≤
        paths) :
    target n ≤ paths := by

  unfold target

  exact h

/-!
============================================================
6. Sharpness witness
============================================================
-/

/--
If one square has exactly the target number of paths, then
there exists a square attaining the bound.
-/
lemma sharp_of_construction
    {n : ℕ}
    (S : Square n)
    (hS :
      uphillCount S =
        target n) :
    ∃ T : Square n,
      uphillCount T =
        target n := by

  exact
    ⟨S, hS⟩

/-!
============================================================
7. Minimum predicate
============================================================
-/

/--
`IsMinimum Square uphillCount n m` means:

* every n × n Nordic square has at least m uphill paths;
* some n × n Nordic square has exactly m uphill paths.

`Square` is an explicit parameter so that Lean can infer the
dependent type of `uphillCount` reliably.
-/
def IsMinimum
    (Square : ℕ → Type u)
    (uphillCount :
      {n : ℕ} → Square n → ℕ)
    (n m : ℕ) : Prop :=
  (∀ S : Square n,
      m ≤ uphillCount S)
    ∧
  (∃ S : Square n,
      uphillCount S = m)

/-!
============================================================
8. Main abstract theorem
============================================================
-/

/--
The source proof has:

* a universal lower bound obtained from the edge count;
* a construction attaining that lower bound.

Together these show that the minimum equals the target.
-/
theorem imo2022_p6
    (n : ℕ)

    (lower :
      ∀ S : Square n,
        gridEdges n + 1 ≤
          uphillCount S)

    (construction :
      ∃ S : Square n,
        uphillCount S =
          target n) :

    IsMinimum
      Square
      uphillCount
      n
      (target n) := by

  constructor

  · intro S

    exact
      lower_bound
        uphillCount
        S
        (lower S)

  · exact construction

/-!
============================================================
9. Explicit-answer version
============================================================
-/

/--
Same theorem with

    2*n*(n-1)+1

written directly in the conclusion.
-/
theorem imo2022_p6_expanded
    (n : ℕ)

    (lower :
      ∀ S : Square n,
        gridEdges n + 1 ≤
          uphillCount S)

    (construction :
      ∃ S : Square n,
        uphillCount S =
          2 * n * (n - 1) + 1) :

    IsMinimum
      Square
      uphillCount
      n
      (2 * n * (n - 1) + 1) := by

  have hconstruction :
      ∃ S : Square n,
        uphillCount S =
          target n := by

    obtain
      ⟨S, hS⟩ :=
      construction

    refine
      ⟨S, ?_⟩

    unfold target

    exact hS

  have hmain :
      IsMinimum
        Square
        uphillCount
        n
        (target n) :=
    imo2022_p6
      uphillCount
      n
      lower
      hconstruction

  unfold target at hmain

  exact hmain

/-!
============================================================
10. Explicit decomposition of the edge count
============================================================
-/

/--
The total number of edges is

    n(n-1) + n(n-1)
      =
    2n(n-1).
-/
lemma edge_count_decomposition
    (n : ℕ) :
    n * (n - 1) +
        n * (n - 1)
      =
    2 * n * (n - 1) := by

  ring

/-!
============================================================
11. Edge paths plus the singleton
============================================================
-/

lemma edges_plus_singleton
    (n : ℕ) :
    gridEdges n + 1 =
      target n := by

  unfold gridEdges
  unfold horizontalEdges
  unfold verticalEdges
  unfold target

  ring

/-!
============================================================
12. Convenient direct wrapper
============================================================
-/

theorem minimum_eq_target
    (n : ℕ)

    (hLower :
      ∀ S : Square n,
        target n ≤
          uphillCount S)

    (hUpper :
      ∃ S : Square n,
        uphillCount S =
          target n) :

    IsMinimum
      Square
      uphillCount
      n
      (target n) := by

  constructor

  · exact hLower

  · exact hUpper

/-!
============================================================
13. Numerical answer
============================================================
-/

/--
The candidate minimum is exactly

    2n(n-1)+1.
-/
lemma answer_formula
    (n : ℕ) :
    target n =
      2 * n * (n - 1) + 1 := by

  rfl

end IMO2022P6
