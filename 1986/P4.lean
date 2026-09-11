import Mathlib

/-!
# IMO 1986, Problem 4 (Algebraic Core)



While the triangle `XYZ` moves from `OAB` to `OBC`, the vertices `Y` and `Z`
move along the segments `AB` and `BC`. The solution observes that `XYBZ` 
is a cyclic quadrilateral. 

We formalize the algebraic angle summation that proves this cyclicity:
The interior angle of a regular n-gon at vertex B is `angle_YBZ = (n-2) * π / n`.
The angle of the moving triangle `XYZ` at X corresponds to the central 
angle of the regular n-gon: `angle_YXZ = 2 * π / n`.
Their sum is exactly `π` (180 degrees), which is the necessary and sufficient 
condition for opposite angles in a cyclic quadrilateral.
-/

namespace IMO1986P4

theorem cyclic_quad_angle_sum (n : ℝ) (hn : n ≠ 0)
    (angle_YBZ angle_YXZ : ℝ)
    (h_YBZ : angle_YBZ = (n - 2) * Real.pi / n)
    (h_YXZ : angle_YXZ = 2 * Real.pi / n) :
    angle_YBZ + angle_YXZ = Real.pi := by
  
  -- Establish that n / n = 1 for the non-zero number of sides
  have h_div : n / n = 1 := div_self hn
  
  -- Verify the summation of the opposite angles algebraically
  calc angle_YBZ + angle_YXZ = (n - 2) * Real.pi / n + 2 * Real.pi / n := by rw [h_YBZ, h_YXZ]
    _ = Real.pi * (n / n) := by ring
    _ = Real.pi * 1 := by rw [h_div]
    _ = Real.pi := by ring

end IMO1986P4
