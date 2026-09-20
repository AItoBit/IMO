import Mathlib

namespace IMO2017P2

open Function

/-
IMO 2017 Problem 2

Find all f : ℝ → ℝ such that

  f (f x * f y) + f (x + y) = f (x * y)

for all x, y ∈ ℝ.
-/

def Good (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    f (f x * f y) + f (x + y) = f (x * y)


/- ============================================================
   Candidate solutions
   ============================================================ -/

lemma good_zero :
    Good (0 : ℝ → ℝ) := by
  intro x y
  simp


lemma good_one_sub :
    Good (fun x : ℝ => 1 - x) := by
  intro x y
  dsimp
  ring


lemma good_sub_one :
    Good (fun x : ℝ => x - 1) := by
  intro x y
  dsimp
  ring


namespace Good

variable {f : ℝ → ℝ}


/- ============================================================
   Negating a solution
   ============================================================ -/

lemma neg
    (hf : Good f) :
    Good (-f) := by
  intro x y
  calc
    -f (-f x * -f y) + -f (x + y)
        =
        -(f (f x * f y) + f (x + y)) := by
          rw [neg_mul_neg, neg_add]
    _ = -f (x * y) := by
          exact congrArg Neg.neg (hf x y)


/- ============================================================
   Basic identities
   ============================================================ -/

lemma map_map_add_one_mul_add_one_of_mul_eq_one
    (hf : Good f)
    {x y : ℝ}
    (hxy : x * y = 1) :
    f (f (x + 1) * f (y + 1)) = 0 := by

  calc
    f (f (x + 1) * f (y + 1))
        =
        f ((x + 1) * (y + 1))
          - f ((x + 1) + (y + 1)) := by
            exact eq_sub_of_add_eq (hf (x + 1) (y + 1))

    _ =
        f ((1 + x) + (y + 1))
          - f ((x + 1) + (y + 1)) := by
            congr 2
            nlinarith [hxy]

    _ = 0 := by
          rw [add_comm 1 x, sub_self]


lemma map_map_mul_map_zero_add_map
    (hf : Good f)
    (x : ℝ) :
    f (f x * f 0) + f x = f 0 := by

  have h := hf x 0
  simpa using h


lemma map_map_zero_sq
    (hf : Good f) :
    f (f 0 ^ 2) = 0 := by

  have hmul :
      (-1 : ℝ) * (-1) = 1 := by
    norm_num

  have h :=
    map_map_add_one_mul_add_one_of_mul_eq_one
      hf
      hmul

  have h' :
      f (f 0 * f 0) = 0 := by
    simpa using h

  simpa [pow_two] using h'


/- ============================================================
   Zeros of nonzero solutions
   ============================================================ -/

lemma map_eq_zero_imp_eq_one
    (hf : Good f)
    (hf_ne_zero : f ≠ 0)
    {c : ℝ}
    (hc : f c = 0) :
    c = 1 := by

  by_contra hc1

  have hcsub :
      c - 1 ≠ 0 := by
    exact sub_ne_zero.mpr hc1

  have hinv :
      (c - 1) * (c - 1)⁻¹ = 1 := by
    exact mul_inv_cancel₀ hcsub

  have hz :=
    map_map_add_one_mul_add_one_of_mul_eq_one
      hf
      hinv

  have hf0 :
      f 0 = 0 := by

    have hz' :
        f
          (f ((c - 1) + 1) *
            f ((c - 1)⁻¹ + 1))
          = 0 :=
      hz

    rw [sub_add_cancel, hc, zero_mul] at hz'

    exact hz'

  apply hf_ne_zero

  funext x

  have hx :=
    map_map_mul_map_zero_add_map hf x

  rw [hf0, mul_zero, hf0] at hx

  simpa using hx


lemma map_zero_sq_eq_one
    (hf : Good f)
    (hf_ne_zero : f ≠ 0) :
    f 0 ^ 2 = 1 := by

  apply map_eq_zero_imp_eq_one hf hf_ne_zero

  exact map_map_zero_sq hf


lemma map_zero_eq_one_or_neg_one
    (hf : Good f)
    (hf_ne_zero : f ≠ 0) :
    f 0 = 1 ∨ f 0 = -1 := by

  exact
    sq_eq_one_iff.mp
      (map_zero_sq_eq_one hf hf_ne_zero)


lemma map_one_eq_zero
    (hf : Good f) :
    f 1 = 0 := by

  rcases eq_or_ne f 0 with hzero | hnonzero

  · have h :=
      congrFun hzero 1

    simpa using h

  · have hsquare :=
      map_zero_sq_eq_one hf hnonzero

    have hz :=
      map_map_zero_sq hf

    rw [hsquare] at hz

    exact hz


/- ============================================================
   Case f(0) = 1
   ============================================================ -/

lemma map_eq_zero_iff_eq_one
    (hf : Good f)
    (hf0 : f 0 = 1)
    {c : ℝ} :
    f c = 0 ↔ c = 1 := by

  constructor

  · intro hc

    apply map_eq_zero_imp_eq_one hf

    · intro hzero

      have h :=
        congrFun hzero 0

      rw [hf0] at h

      norm_num at h

    · exact hc

  · intro hc

    subst c

    exact map_one_eq_zero hf


lemma map_add_one
    (hf : Good f)
    (hf0 : f 0 = 1)
    (x : ℝ) :
    f (x + 1) + 1 = f x := by

  have h :=
    hf x 1

  rw [map_one_eq_zero hf] at h
  rw [mul_zero] at h
  rw [hf0] at h
  rw [mul_one] at h

  linarith


lemma map_sub_one
    (hf : Good f)
    (hf0 : f 0 = 1)
    (x : ℝ) :
    f (x - 1) = f x + 1 := by

  have h :=
    map_add_one hf hf0 (x - 1)

  rw [sub_add_cancel] at h

  exact h.symm


/- ============================================================
   Injectivity
   ============================================================ -/

lemma injective_of_map_zero_eq_one
    (hf : Good f)
    (hf0 : f 0 = 1) :
    Function.Injective f := by

  have hshift :
      ∀ x : ℝ,
        f (x - 1) = f x + 1 :=
    map_sub_one hf hf0

  have hzero :
      ∀ {x : ℝ},
        f x = 0 ↔ x = 1 := by
    intro x
    exact map_eq_zero_iff_eq_one hf hf0


  /-
  f(2 f(y)) + 1 + f(y) = f(-y)
  -/
  have hneg_formula :
      ∀ y : ℝ,
        f (2 * f y) + 1 + f y =
          f (-y) := by

    intro y

    have hfnegone :
        f (-1) = 2 := by

      have h :=
        hshift 0

      norm_num [hf0] at h ⊢

      exact h

    have h := hf (-1) y

    rw [hfnegone] at h

    have hsum :
        (-1 : ℝ) + y = y - 1 := by
      ring

    have hprod :
        (-1 : ℝ) * y = -y := by
      ring

    rw [hsum, hprod] at h
    rw [hshift y] at h

    linarith


  /-
  If f(-y)=f(y), then y=0.
  -/
  have hsymm :
      ∀ {y : ℝ},
        f (-y) = f y →
        y = 0 := by

    intro y hy

    have h1 :=
      hneg_formula y

    rw [hy] at h1

    have hf2 :
        f (2 * f y) = -1 := by
      linarith

    have hz :
        f (2 * f y - 1) = 0 := by

      rw [hshift]
      rw [hf2]

      norm_num

    have harg :
        2 * f y - 1 = 1 :=
      hzero.mp hz

    have hfy :
        f y = 1 := by
      linarith

    have hadd :=
      map_add_one hf hf0 y

    have hyzero :
        f (y + 1) = 0 := by
      linarith

    have hyarg :
        y + 1 = 1 :=
      hzero.mp hyzero

    linarith


  /-
  f(a)=f(b) -> f(-a)=f(-b)
  -/
  have hneg :
      ∀ {a b : ℝ},
        f a = f b →
        f (-a) = f (-b) := by

    intro a b hab

    have ha :=
      hneg_formula a

    have hb :=
      hneg_formula b

    rw [hab] at ha

    linarith


  intro a b hab

  have hnegab :
      f (-a) = f (-b) :=
    hneg hab


  /-
  Crucial fixed part.

  We have

      ha : A = f(a*b)
      hb : A = f(b*a)

  hence

      f(a*b) = A = f(b*a)

  i.e. ha.symm.trans hb.
  -/
  have habprod :
      f (a * b) = f (b * a) := by

    have ha :=
      hf a b

    have hb :=
      hf b a

    have hmul :
        f a * f b =
          f b * f a := by
      ring

    have hadd :
        a + b =
          b + a := by
      ring

    rw [hmul, hadd] at ha

    exact ha.symm.trans hb


  /-
  Consequently

    f(a*(-b)) = f(b*(-a)).
  -/
  have hnegprod :
      f (a * (-b)) =
        f (b * (-a)) := by

    have hn :
        f (-(a * b)) =
          f (-(b * a)) :=
      hneg habprod

    have ha :
        a * (-b) = -(a * b) := by
      ring

    have hb :
        b * (-a) = -(b * a) := by
      ring

    rw [ha, hb]

    exact hn


  /-
  Compare P(a,-b) and P(b,-a).
  -/
  have hpa :=
    hf a (-b)

  have hpb :=
    hf b (-a)

  have hfirst :
      f (f a * f (-b)) =
        f (f b * f (-a)) := by

    rw [hab, hnegab]


  have hsum :
      f (a + -b) =
        f (b + -a) := by

    calc
      f (a + -b)
          =
          f (a * (-b))
            - f (f a * f (-b)) := by
              linarith [hpa]

      _ =
          f (b * (-a))
            - f (f b * f (-a)) := by
              rw [hnegprod, hfirst]

      _ =
          f (b + -a) := by
              linarith [hpb]


  /-
  Thus

    f(-(a-b)) = f(a-b).
  -/
  have hsym :
      f (-(a - b)) =
        f (a - b) := by

    have hleft :
        -(a - b) =
          b + -a := by
      ring

    have hright :
        a - b =
          a + -b := by
      ring

    rw [hleft, hright]

    exact hsum.symm


  have hdiff :
      a - b = 0 :=
    hsymm hsym

  exact sub_eq_zero.mp hdiff


/- ============================================================
   Classification for f(0)=1
   ============================================================ -/

lemma eq_one_sub_of_map_zero_eq_one
    (hf : Good f)
    (hf0 : f 0 = 1) :
    f = fun x : ℝ => 1 - x := by

  have hinj :
      Function.Injective f :=
    injective_of_map_zero_eq_one hf hf0


  /-
  P(x,0):

    f(f(x)) + f(x) = 1.
  -/
  have hff :
      ∀ x : ℝ,
        f (f x) + f x = 1 := by

    intro x

    have h :=
      map_map_mul_map_zero_add_map hf x

    rw [hf0, mul_one] at h

    exact h


  /-
  f(f(f(x))) = f(x).
  -/
  have htriple :
      ∀ x : ℝ,
        f (f (f x)) = f x := by

    intro x

    have h1 :=
      hff x

    have h2 :=
      hff (f x)

    linarith


  /-
  Injectivity gives f(f(x)) = x.
  -/
  have hdouble :
      ∀ x : ℝ,
        f (f x) = x := by

    intro x

    apply hinj

    exact htriple x


  funext x

  have h1 :=
    hff x

  have h2 :=
    hdouble x

  linarith


end Good


/- ============================================================
   FINAL CLASSIFICATION
   ============================================================ -/

theorem imo2017_p2
    (f : ℝ → ℝ) :
    (∀ x y : ℝ,
        f (f x * f y) + f (x + y) =
          f (x * y))
      ↔
        f = (0 : ℝ → ℝ)
        ∨
        f = (fun x : ℝ => x - 1)
        ∨
        f = (fun x : ℝ => 1 - x) := by

  change
    Good f ↔
      f = (0 : ℝ → ℝ)
      ∨
      f = (fun x : ℝ => x - 1)
      ∨
      f = (fun x : ℝ => 1 - x)

  constructor


  /- Forward direction -/
  · intro hf

    rcases eq_or_ne f 0 with hzero | hnonzero

    /- f = 0 -/
    · exact Or.inl hzero


    /- f ≠ 0, hence f(0)=±1 -/
    · have hf0cases :
          f 0 = 1 ∨ f 0 = -1 :=
        Good.map_zero_eq_one_or_neg_one
          hf
          hnonzero

      rcases hf0cases with hf0 | hf0


      /- f(0)=1 -/
      · right
        right

        exact
          Good.eq_one_sub_of_map_zero_eq_one
            hf
            hf0


      /- f(0)=-1 -/
      · right
        left

        have hneg :
            Good (-f) :=
          Good.neg hf

        have hneg0 :
            (-f) 0 = 1 := by
          change -f 0 = 1
          linarith

        have hclass :
            (-f) =
              (fun x : ℝ => 1 - x) :=
          Good.eq_one_sub_of_map_zero_eq_one
            hneg
            hneg0

        funext x

        have hx :=
          congrFun hclass x

        change -f x = 1 - x at hx

        linarith


  /- Reverse direction -/
  · intro h

    rcases h with hzero | hsub | hone

    · rw [hzero]
      exact good_zero

    · rw [hsub]
      exact good_sub_one

    · rw [hone]
      exact good_one_sub


end IMO2017P2
