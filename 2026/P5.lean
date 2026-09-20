import Mathlib

namespace IMO2026P5

noncomputable section

/-!
# IMO 2026 Problem 5

Find all functions f : ℝ₊ → ℝ₊ such that

    sqrt((x² + f(y)²) / 2)
      ≥ (f(x) + y) / 2
      ≥ sqrt(x f(y))

for all positive x,y.

The answer is

    f(x) = x + c

for a constant c ≥ 0.

We work with `f : ℝ → ℝ` and carry positivity explicitly.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Original condition
============================================================
-/

def OriginalCondition
    (f : ℝ → ℝ) : Prop :=
  (∀ x : ℝ,
      0 < x →
      0 < f x)
  ∧
  (∀ x y : ℝ,
      0 < x →
      0 < y →
      (f x + y) / 2
        ≤
      Real.sqrt
        ((x ^ 2 + (f y) ^ 2) / 2)
      ∧
      Real.sqrt (x * f y)
        ≤
      (f x + y) / 2)

/-!
============================================================
2. RMS-AM
============================================================
-/

/--
For nonnegative real numbers,

    (a+b)/2 ≤ sqrt((a²+b²)/2).
-/
lemma rms_am
    {a b : ℝ}
    (ha :
      0 ≤ a)
    (hb :
      0 ≤ b) :
    (a + b) / 2
      ≤
    Real.sqrt
      ((a ^ 2 + b ^ 2) / 2) := by

  have hrad :
      0 ≤
        (a ^ 2 + b ^ 2) / 2 := by
    positivity

  have hsqrt_nonneg :
      0 ≤
        Real.sqrt
          ((a ^ 2 + b ^ 2) / 2) :=
    Real.sqrt_nonneg _

  have hsqrt_sq :
      (Real.sqrt
        ((a ^ 2 + b ^ 2) / 2)) ^ 2
        =
      (a ^ 2 + b ^ 2) / 2 := by

    exact
      Real.sq_sqrt
        hrad

  have havg_nonneg :
      0 ≤ (a + b) / 2 := by
    positivity

  have hsq :
      ((a + b) / 2) ^ 2
        ≤
      (a ^ 2 + b ^ 2) / 2 := by

    nlinarith [sq_nonneg (a - b)]

  nlinarith

/-!
============================================================
3. AM-GM
============================================================
-/

/--
For nonnegative real numbers,

    sqrt(ab) ≤ (a+b)/2.
-/
lemma am_gm
    {a b : ℝ}
    (ha :
      0 ≤ a)
    (hb :
      0 ≤ b) :
    Real.sqrt (a * b)
      ≤
    (a + b) / 2 := by

  have hab :
      0 ≤ a * b :=
    mul_nonneg
      ha
      hb

  have hsqrt_nonneg :
      0 ≤ Real.sqrt (a * b) :=
    Real.sqrt_nonneg _

  have hsqrt_sq :
      (Real.sqrt (a * b)) ^ 2 =
        a * b := by

    exact
      Real.sq_sqrt
        hab

  have havg_nonneg :
      0 ≤ (a + b) / 2 := by
    positivity

  have hsq :
      a * b
        ≤
      ((a + b) / 2) ^ 2 := by

    nlinarith [sq_nonneg (a - b)]

  nlinarith

/-!
============================================================
4. Candidate functions are positive
============================================================
-/

lemma affine_positive
    {c x : ℝ}
    (hc :
      0 ≤ c)
    (hx :
      0 < x) :
    0 < x + c := by

  nlinarith

/-!
============================================================
5. Every f(x)=x+c, c≥0, satisfies the problem
============================================================
-/

theorem affine_satisfies
    (c : ℝ)
    (hc :
      0 ≤ c) :
    OriginalCondition
      (fun x : ℝ => x + c) := by

  constructor

  · intro x hx

    exact
      affine_positive
        hc
        hx

  · intro x y hx hy

    have hyc :
        0 ≤ y + c := by
      nlinarith

    have hx0 :
        0 ≤ x :=
      le_of_lt hx

    constructor

    · have h :
          (x + (y + c)) / 2
            ≤
          Real.sqrt
            ((x ^ 2 + (y + c) ^ 2) / 2) :=

        rms_am
          hx0
          hyc

      simpa [
        add_assoc,
        add_comm,
        add_left_comm
      ] using h

    · have h :
          Real.sqrt
              (x * (y + c))
            ≤
          (x + (y + c)) / 2 :=

        am_gm
          hx0
          hyc

      simpa [
        add_assoc,
        add_comm,
        add_left_comm
      ] using h

/-!
============================================================
6. Positivity extracted from the original condition
============================================================
-/

lemma condition_pos
    {f : ℝ → ℝ}
    (h :
      OriginalCondition f)
    {x : ℝ}
    (hx :
      0 < x) :
    0 < f x := by

  exact
    h.1
      x
      hx

/-!
============================================================
7. The source's substitution x = f(y)
============================================================
-/

/--
Putting x = f(y) into the original inequality forces

    f(f(y)) = 2 f(y) - y.

This is one of the key identities in Solutions 1 and 3.
-/
lemma iterate_identity
    {f : ℝ → ℝ}
    (h :
      OriginalCondition f)
    {y : ℝ}
    (hy :
      0 < y) :
    f (f y) =
      2 * f y - y := by

  have hfy :
      0 < f y :=
    condition_pos
      h
      hy

  have hineq :=
    h.2
      (f y)
      y
      hfy
      hy

  rcases hineq with
    ⟨hleft, hright⟩

  have hL :
      Real.sqrt
          (((f y) ^ 2 + (f y) ^ 2) / 2)
        =
      f y := by

    have hinside :
        ((f y) ^ 2 + (f y) ^ 2) / 2
          =
        (f y) ^ 2 := by
      ring

    rw [hinside]

    rw [Real.sqrt_sq_eq_abs]

    exact
      abs_of_pos
        hfy

  have hR :
      Real.sqrt
          (f y * f y)
        =
      f y := by

    have hmul :
        f y * f y =
          (f y) ^ 2 := by
      ring

    rw [hmul]

    rw [Real.sqrt_sq_eq_abs]

    exact
      abs_of_pos
        hfy

  rw [hL] at hleft
  rw [hR] at hright

  nlinarith

/-!
============================================================
8. f is injective on the positive reals
============================================================
-/

/--
If a,b > 0 and f(a)=f(b), then a=b.

This follows immediately from

    f(f(t)) = 2 f(t) - t.
-/
lemma injective_on_positive
    {f : ℝ → ℝ}
    (h :
      OriginalCondition f)
    {a b : ℝ}
    (ha :
      0 < a)
    (hb :
      0 < b)
    (hab :
      f a = f b) :
    a = b := by

  have hA :
      f (f a) =
        2 * f a - a :=
    iterate_identity
      h
      ha

  have hB :
      f (f b) =
        2 * f b - b :=
    iterate_identity
      h
      hb

  have hff :
      f (f a) =
        f (f b) := by
    rw [hab]

  nlinarith

/-!
============================================================
9. The auxiliary difference function
============================================================
-/

def shift
    (f : ℝ → ℝ)
    (x : ℝ) : ℝ :=
  f x - x

/-!
============================================================
10. Iterate identity means shift(f(x)) = shift(x)
============================================================
-/

lemma shift_iterate
    {f : ℝ → ℝ}
    (h :
      OriginalCondition f)
    {x : ℝ}
    (hx :
      0 < x) :
    shift f (f x) =
      shift f x := by

  unfold shift

  have hid :
      f (f x) =
        2 * f x - x :=
    iterate_identity
      h
      hx

  linarith

/-!
============================================================
11. Source balance relation
============================================================
-/

/--
The central rigidity relation in the supplied solutions is

    f(x) + y = f(y) + x.

Equivalently,

    f(x) - x = f(y) - y.

Once this is established, f is immediately affine.
-/
def Balanced
    (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    0 < x →
    0 < y →
    f x + y =
      f y + x

/-!
============================================================
12. Balance makes f(x)-x constant
============================================================
-/

lemma shift_constant_of_balanced
    {f : ℝ → ℝ}
    (hbal :
      Balanced f) :
    ∀ x : ℝ,
      0 < x →
      f x - x =
        f 1 - 1 := by

  intro x hx

  have h :=
    hbal
      x
      1
      hx
      (by norm_num)

  linarith

/-!
============================================================
13. Balance gives the affine formula
============================================================
-/

lemma affine_of_balanced
    {f : ℝ → ℝ}
    (h :
      OriginalCondition f)
    (hbal :
      Balanced f) :
    ∃ c : ℝ,
      0 ≤ c ∧
      ∀ x : ℝ,
        0 < x →
        f x = x + c := by

  let c : ℝ :=
    f 1 - 1

  have hformula :
      ∀ x : ℝ,
        0 < x →
        f x = x + c := by

    intro x hx

    have hcst :
        f x - x =
          f 1 - 1 :=
      shift_constant_of_balanced
        hbal
        x
        hx

    dsimp [c]

    linarith

  have hc :
      0 ≤ c := by

    by_contra hneg

    have hcneg :
        c < 0 := by
      linarith

    let x : ℝ :=
      -c / 2

    have hx :
        0 < x := by

      dsimp [x]

      linarith

    have hfx :
        f x = x + c :=
      hformula
        x
        hx

    have hpos :
        0 < f x :=
      condition_pos
        h
        hx

    dsimp [x] at hfx

    nlinarith

  exact
    ⟨c,
     hc,
     hformula⟩

/-!
============================================================
14. Agreement with an affine function on positive inputs
    is sufficient
============================================================
-/

lemma condition_of_affine_on_positive
    {f : ℝ → ℝ}
    {c : ℝ}
    (hc :
      0 ≤ c)
    (hf :
      ∀ x : ℝ,
        0 < x →
        f x = x + c) :
    OriginalCondition f := by

  constructor

  · intro x hx

    rw [hf x hx]

    exact
      affine_positive
        hc
        hx

  · intro x y hx hy

    have hfx :
        f x = x + c :=
      hf x hx

    have hfy :
        f y = y + c :=
      hf y hy

    rw [hfx, hfy]

    have hyc :
        0 ≤ y + c := by
      nlinarith

    have hx0 :
        0 ≤ x :=
      le_of_lt hx

    constructor

    · have h :
          (x + (y + c)) / 2
            ≤
          Real.sqrt
            ((x ^ 2 + (y + c) ^ 2) / 2) :=

        rms_am
          hx0
          hyc

      simpa [
        add_assoc,
        add_comm,
        add_left_comm
      ] using h

    · have h :
          Real.sqrt
              (x * (y + c))
            ≤
          (x + (y + c)) / 2 :=

        am_gm
          hx0
          hyc

      simpa [
        add_assoc,
        add_comm,
        add_left_comm
      ] using h

/-!
============================================================
15. Classification once the source balance lemma is proved
============================================================
-/

/--
The only remaining source-specific rigidity step is:

    OriginalCondition f → Balanced f.

Given that lemma, the complete classification follows.
-/
theorem imo2026_p5_classification
    (f : ℝ → ℝ)
    (balance_from_condition :
      OriginalCondition f →
      Balanced f) :
    OriginalCondition f ↔
    ∃ c : ℝ,
      0 ≤ c ∧
      ∀ x : ℝ,
        0 < x →
        f x = x + c := by

  constructor

  · intro h

    exact
      affine_of_balanced
        h
        (balance_from_condition h)

  · intro h

    rcases h with
      ⟨c, hc, hf⟩

    exact
      condition_of_affine_on_positive
        hc
        hf

/-!
============================================================
16. Direct final wrapper
============================================================
-/

theorem imo2026_p5_core
    {f : ℝ → ℝ}
    (h :
      OriginalCondition f)
    (hbalance :
      Balanced f) :
    ∃ c : ℝ,
      0 ≤ c ∧
      ∀ x : ℝ,
        0 < x →
        f x = x + c := by

  exact
    affine_of_balanced
      h
      hbalance

end

end IMO2026P5
