import Mathlib

/--
Formalization of the solution of IMO 1968 Problem 4.
If `a, b, c, d, e, f` are the edge lengths of a tetrahedron, they form 4 triangular faces.
Without loss of generality, we can assume `a` is the maximum edge length.
We prove that either the vertex with edges `a, c, e` or the vertex with edges `a, b, f`
satisfies the condition that its three meeting edges form a triangle.
-/
theorem imo1968_p4_wlog
  (a b c d e f : ℝ)
  (face1 : a + b > c ∧ b + c > a ∧ c + a > b)
  (face2 : a + e > f ∧ e + f > a ∧ f + a > e)
  (face3 : b + d > f ∧ d + f > b ∧ f + b > d)
  (_face4 : c + d > e ∧ d + e > c ∧ e + c > d)
  (hmax_b : a ≥ b)
  (_hmax_c : a ≥ c)
  (hmax_d : a ≥ d)
  (_hmax_e : a ≥ e)
  (_hmax_f : a ≥ f) :
  (b + c > d ∧ c + d > b ∧ d + b > c) ∨
  (a + c > e ∧ c + e > a ∧ e + a > c) ∨
  (a + b > f ∧ b + f > a ∧ f + a > b) ∨
  (d + e > f ∧ e + f > d ∧ f + d > e) := by
  
  -- As shown in "image_98e229.png", we condition on whether b + f > a
  by_cases h : b + f > a
  · -- If b + f > a, the vertex with edges a, b, f forms a triangle.
    -- a + b > f and f + a > b follow from a ≥ f, a ≥ b, and the strict positivity of edges.
    have h_abf : a + b > f ∧ b + f > a ∧ f + a > b := ⟨by linarith, h, by linarith⟩
    exact Or.inr (Or.inr (Or.inl h_abf))
    
  · -- Otherwise, b + f ≤ a. We show the vertex with edges a, c, e forms a triangle.
    -- c + e > a follows from combining e + f > a, b + c > a, and b + f ≤ a.
    -- a + c > e and e + a > c follow from a ≥ e, a ≥ c, and edge positivity.
    have h_le : b + f ≤ a := not_lt.mp h
    have h_ace : a + c > e ∧ c + e > a ∧ e + a > c := ⟨by linarith, by linarith, by linarith⟩
    exact Or.inr (Or.inl h_ace)
