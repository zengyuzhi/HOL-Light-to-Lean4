import Mathlib
import Aesop

namespace Quartic

/-! ### QUARTIC_1 -/
theorem quartic_1 (y b a c d R s D x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3 : R = 0)
  (h4 : s^2 = y^2 - 4 * d)
  (h5 : D^2 = 3 * a^2 / 4 - 2 * b + 2 * s)
  (h6 : x = -a / 4 + R / 2 + D / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- Step 1: Simplify x using R = 0
  have h7 : x = -a / 4 + D / 2 := by rw [h6, h3]; ring_nf
  -- Step 2: Rearranging h4 gives d = (y^2 - s^2) / 4
  have hd : d = (y^2 - s^2) / 4 := by
    rw [h4]
    ring
  -- Step 3: Use h2 and h3 to express y
  have h13 : R^2 = 0 := by rw [h3]; ring_nf
  have h14 : a^2 / 4 - b + y = 0 := by rw [←h2, h13]
  have h15 : y = b - a^2 / 4 := by linarith
  -- Step 4: Use h1 with the substitutions to derive the identity (a^3 - 4ab + 8c)^2 = 0
  have hC : a ^ 3 - 4 * a * b + 8 * c = 0 := by
    have h1' : (a ^ 3 - 4 * a * b + 8 * c) ^ 2 = 0 := by
      rw [h15] at h1
      rw [hd] at h1
      field_simp at h1
      ring_nf at h1
      have h_poly : b * a * c * 65536 + b * a ^ 4 * 8192 + (-(b ^ 2 * a ^ 2 * 16384) - a ^ 3 * c * 16384) +
        (-(a ^ 6 * 1024) - c ^ 2 * 65536) = -1024 * (a ^3 - 4 * a * b + 8 * c) ^ 2 := by
          simp [add_mul, mul_add, mul_comm, mul_assoc, mul_left_comm, pow_two, pow_three]; ring_nf
      rw [h_poly] at h1 ; nlinarith
    have h2_local_scope : a ^ 3 - 4 * a * b + 8 * c = 0 := by
      have h3_local_scope : (a ^ 3 - 4 * a * b + 8 * c) ^ 2 = 0 := h1'
      have h4_local_scope : a ^ 3 - 4 * a * b + 8 * c = 0 := by nlinarith [h3_local_scope]
      exact h4_local_scope
    exact h2_local_scope
  -- Step 5: Simplify D² using h5 and the expression for b in terms of y
  have hD2_y_form : D^2 = a^2 / 4 - 2 * y + 2 * s := by
    have hb_val_for_D : b = y + a^2/4 := by linarith [h15]
    rw [h5, hb_val_for_D]
    ring
  -- Step 6: Prove that x satisfies a quadratic equation
  have h_quadratic_root : x^2 + a/2 * x + (y-s)/2 = 0 := by
    rw [h7]
    ring_nf
    rw [hD2_y_form]
    field_simp
    ring
  -- Step 7: Express b and c in terms of y using h15 and hC
  have hb_y_form : b = y + a^2/4 := by
    linarith [h15]
  have hc_y_form : c = a * y / 2 := by
    have temp_hC_rewritten := hC
    rw [hb_y_form] at temp_hC_rewritten
    ring_nf at temp_hC_rewritten
    have H_8c_eq_4ay : 8 * c = 4 * a * y := by linarith [temp_hC_rewritten]
    calc c = (8 * c) / 8 := by field_simp
         _ = (4 * a * y) / 8 := by rw [H_8c_eq_4ay]
         _ = a * y / 2 := by field_simp; ring
  -- Step 8: Factor the quartic as product of two quadratics
  have h_poly_factorization : x^4 + a*x^3 + b*x^2 + c*x + d =
      (x^2 + a/2*x + (y-s)/2) * (x^2 + a/2*x + (y+s)/2) := by
    rw [hb_y_form]
    rw [hc_y_form]
    rw [hd]
    ring
  -- Step 9: Since x is a root of the first quadratic, the whole quartic evaluates to 0
  rw [h_poly_factorization]
  rw [h_quadratic_root]
  simp


/-! ### QUARTIC_2 -/
theorem quartic_2 (y b a c d R s D x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3 : R = 0)
  (h4 : s^2 = y^2 - 4 * d)
  (h5 : D^2 = 3 * a^2 / 4 - 2 * b + 2 * s)
  (h6 : x = -a / 4 + R / 2 - D / 2) :  -- Note the -D/2
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- Step 1: Simplify x using R = 0
  have h7 : x = -a / 4 - D / 2 := by rw [h6, h3]; ring_nf
  -- Step 2: Rearranging h4 gives d = (y^2 - s^2) / 4
  have hd : d = (y^2 - s^2) / 4 := by rw [h4]; ring
  -- Step 3: Simplify y using h2 and h3
  have h13 : R^2 = 0 := by rw [h3]; ring_nf
  have h14 : a^2 / 4 - b + y = 0 := by rw [←h2, h13]
  have h15 : y = b - a^2 / 4 := by linarith
  -- Step 4: Use h1 and the substitutions for y and d to derive:
  have hC : a ^ 3 - 4 * a * b + 8 * c = 0 := by
    have h1' : (a ^ 3 - 4 * a * b + 8 * c) ^ 2 = 0 := by
      rw [h15, hd] at h1
      field_simp at h1
      ring_nf at h1
      have h_poly : b * a * c * 65536 + b * a ^ 4 * 8192 + (-(b ^ 2 * a ^ 2 * 16384) - a ^ 3 * c * 16384) +
        (-(a ^ 6 * 1024) - c ^ 2 * 65536) = -1024 * (a ^3 - 4 * a * b + 8 * c) ^ 2 := by
          simp [add_mul, mul_add, mul_comm, mul_assoc, mul_left_comm, pow_two, pow_three]; ring_nf
      rw [h_poly] at h1 ; nlinarith
    have h2_local_scope : a ^ 3 - 4 * a * b + 8 * c = 0 := by
      have h3_local_scope : (a ^ 3 - 4 * a * b + 8 * c) ^ 2 = 0 := h1'
      nlinarith [h3_local_scope]
    exact h2_local_scope
  -- Step 5: Simplify D² using h5 and y
  have hD2_y_form : D^2 = a^2 / 4 - 2 * y + 2 * s := by
    have hb_val_for_D : b = y + a^2 / 4 := by linarith [h15]
    rw [h5, hb_val_for_D]; ring
  -- Step 6: Show x satisfies the quadratic x^2 + a/2*x + (y-s)/2 = 0
  have h_quadratic_root : x^2 + a/2 * x + (y-s)/2 = 0 := by
    rw [h7]; ring_nf
    rw [hD2_y_form]; field_simp; ring
  -- Step 7: Express b and c using y and a
  have hb_y_form : b = y + a^2 / 4 := by linarith [h15]
  have hc_y_form : c = a * y / 2 := by
    rw [hb_y_form] at hC; ring_nf at hC
    have : 8 * c = 4 * a * y := by linarith [hC]
    calc c = (8 * c) / 8 := by field_simp
         _ = (4 * a * y) / 8 := by rw [this]
         _ = a * y / 2 := by field_simp; ring
  -- Step 8: Factor the quartic polynomial
  have h_poly_factorization : x^4 + a*x^3 + b*x^2 + c*x + d =
      (x^2 + a/2*x + (y-s)/2) * (x^2 + a/2*x + (y+s)/2) := by
    rw [hb_y_form, hc_y_form, hd]; ring
  -- Step 9: Conclude via root of first quadratic
  rw [h_poly_factorization, h_quadratic_root]; simp


/-! ### QUARTIC_3 -/
theorem quartic_3 (y b a c d R s E x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3 : R = 0)
  (h4 : s^2 = y^2 - 4 * d)
  (h5 : E^2 = 3 * a^2 / 4 - 2 * b - 2 * s)-- Note E and -2*s
  (h6 : x = -a / 4 - R / 2 + E / 2) :-- Note -R/2 and +E/2
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- Step 1: Simplify x using R = 0
  have h7 : x = -a / 4 + E / 2 := by rw [h6, h3]; ring_nf
  -- Step 2: Solve for d using h4: s^2 = y^2 - 4 * d  =>  d = (y^2 - s^2)/4
  have hd : d = (y^2 - s^2) / 4 := by
    rw [h4]
    ring
  -- Step 3: Use h2 and h3 to get a simpler expression for y
  have h13 : R^2 = 0 := by rw [h3]; ring_nf
  have h14 : a^2 / 4 - b + y = 0 := by rw [←h2, h13]
  have h15 : y = b - a^2 / 4 := by linarith

  -- Step 4: Use h1 and the substitutions for y and d to derive:
  have hC : a ^ 3 - 4 * a * b + 8 * c = 0 := by
    have h1' : (a ^ 3 - 4 * a * b + 8 * c) ^ 2 = 0 := by
      rw [h15] at h1
      rw [hd] at h1
      field_simp at h1
      ring_nf at h1
      have h_poly : b * a * c * 65536 + b * a ^ 4 * 8192 + (-(b ^ 2 * a ^ 2 * 16384) - a ^ 3 * c * 16384) +
        (-(a ^ 6 * 1024) - c ^ 2 * 65536) = -1024 * (a ^3 - 4 * a * b + 8 * c) ^ 2 := by
          simp [add_mul, mul_add, mul_comm, mul_assoc, mul_left_comm, pow_two, pow_three]; ring_nf
      rw [h_poly] at h1 ; nlinarith
    have h2_local_scope : a ^ 3 - 4 * a * b + 8 * c = 0 := by
      have h3_local_scope : (a ^ 3 - 4 * a * b + 8 * c) ^ 2 = 0 := h1'
      nlinarith [h3_local_scope]
    exact h2_local_scope
  -- Step 5: Substitute y from h15 into h5 to simplify E^2
  have hE2_y_form : E^2 = a^2 / 4 - 2 * y - 2 * s := by
    have hb_val_for_E : b = y + a^2/4 := by linarith [h15]
    rw [h5, hb_val_for_E] -- Substitute E^2 with its definition (h5) and b with its expression
    ring
  -- Step 6: Prove that x is a root of x^2 + (a/2)*x + (y+s)/2 = 0
  have h_quadratic_root : x^2 + a/2 * x + (y+s)/2 = 0 := by
    rw [h7] -- Substitute x = -a/4 + E/2
    ring_nf -- Normalizes the expression with x substituted
    rw [hE2_y_form] -- Substitute E^2 = a^2/4 - 2*y - 2*s (from Step 5)
    field_simp
    ring
  -- Step 7: Express b and c in terms of y and a, using h15 and hC
  have hb_y_form : b = y + a^2/4 := by
    linarith [h15]
  have hc_y_form : c = a * y / 2 := by
    have temp_hC_rewritten := hC
    rw [hb_y_form] at temp_hC_rewritten
    ring_nf at temp_hC_rewritten
    have H_8c_eq_4ay : 8 * c = 4 * a * y := by linarith [temp_hC_rewritten]
    calc c = (8 * c) / 8 := by field_simp;
         _ = (4 * a * y) / 8 := by rw [H_8c_eq_4ay]
         _ = a * y / 2 := by field_simp; ring
  -- Step 8: Show the quartic polynomial can be factorized using the above relations
  have h_poly_factorization : x^4 + a*x^3 + b*x^2 + c*x + d =
      (x^2 + a/2*x + (y-s)/2) * (x^2 + a/2*x + (y+s)/2) := by
    rw [hb_y_form, hc_y_form, hd]
    ring
  -- Step 9: Combine factorization and quadratic root to prove the main goal
  rw [h_poly_factorization]
  rw [h_quadratic_root] -- The second factor (x^2 + a/2*x + (y+s)/2) is 0
  simp -- Automatically simplifies (anything) * 0 to 0


/-! ### QUARTIC_4 -/
theorem quartic_4 (y b a c d R s E x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3 : R = 0)
  (h4 : s^2 = y^2 - 4 * d)
  (h5 : E^2 = 3 * a^2 / 4 - 2 * b - 2 * s)
  (h6 : x = -a / 4 - R / 2 - E / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
    -- Step 1: Simplify x using R = 0
  have h7 : x = -a / 4 - E / 2 := by rw [h6, h3]; ring_nf
  -- Step 2: Solve for d using h4: s^2 = y^2 - 4 * d  =>  d = (y^2 - s^2)/4
  have hd : d = (y^2 - s^2) / 4 := by
    rw [h4]
    ring
  -- Step 3: Use h2 and h3 to get a simpler expression for y
  have h13 : R^2 = 0 := by rw [h3]; ring_nf
  have h14 : a^2 / 4 - b + y = 0 := by rw [←h2, h13]
  have h15 : y = b - a^2 / 4 := by linarith

  -- Step 4: Use h1 and the substitutions for y and d to derive:
  have hC : a ^ 3 - 4 * a * b + 8 * c = 0 := by
    have h1' : (a ^ 3 - 4 * a * b + 8 * c) ^ 2 = 0 := by
      rw [h15] at h1
      rw [hd] at h1
      field_simp at h1
      ring_nf at h1
      have h_poly : b * a * c * 65536 + b * a ^ 4 * 8192 + (-(b ^ 2 * a ^ 2 * 16384) - a ^ 3 * c * 16384) +
        (-(a ^ 6 * 1024) - c ^ 2 * 65536) = -1024 * (a ^3 - 4 * a * b + 8 * c) ^ 2 := by
          simp [add_mul, mul_add, mul_comm, mul_assoc, mul_left_comm, pow_two, pow_three]; ring_nf
      rw [h_poly] at h1 ; nlinarith
    have h2_local_scope : a ^ 3 - 4 * a * b + 8 * c = 0 := by
      have h3_local_scope : (a ^ 3 - 4 * a * b + 8 * c) ^ 2 = 0 := h1'
      nlinarith [h3_local_scope]
    exact h2_local_scope
  -- Step 5: Substitute y from h15 into h5 to simplify E^2
  have hE2_y_form : E^2 = a^2 / 4 - 2 * y - 2 * s := by
    have hb_val_for_E : b = y + a^2/4 := by linarith [h15]
    rw [h5, hb_val_for_E] -- Substitute E^2 with its definition (h5) and b with its expression
    ring
  -- Step 6: Prove that x is a root of x^2 + (a/2)*x + (y+s)/2 = 0
  have h_quadratic_root : x^2 + a/2 * x + (y+s)/2 = 0 := by
    rw [h7] -- Substitute x = -a/4 - E/2
    ring_nf -- Normalizes the expression with x substituted
    rw [hE2_y_form] -- Substitute E^2 = a^2/4 - 2*y - 2*s (from Step 5)
    field_simp
    ring
  -- Step 7: Express b and c in terms of y and a, using h15 and hC
  have hb_y_form : b = y + a^2/4 := by
    linarith [h15]
  have hc_y_form : c = a * y / 2 := by
    have temp_hC_rewritten := hC
    rw [hb_y_form] at temp_hC_rewritten
    ring_nf at temp_hC_rewritten
    have H_8c_eq_4ay : 8 * c = 4 * a * y := by linarith [temp_hC_rewritten]
    calc c = (8 * c) / 8 := by field_simp;
          _ = (4 * a * y) / 8 := by rw [H_8c_eq_4ay]
          _ = a * y / 2 := by field_simp; ring
  -- Step 8: Show the quartic polynomial can be factorized using the above relations
  have h_poly_factorization : x^4 + a*x^3 + b*x^2 + c*x + d =
     (x^2 + a/2*x + (y-s)/2) * (x^2 + a/2*x + (y+s)/2) := by
    rw [hb_y_form]
    rw [hc_y_form]
    rw [hd]
    ring
  -- Step 9: Combine factorization and quadratic root to prove the main goal
  rw [h_poly_factorization]
  rw [h_quadratic_root] -- The second factor (x^2 + a/2*x + (y+s)/2) is 0
  simp -- Automatically simplifies (anything) * 0 to 0


/-! ### QUARTIC_1' -/
theorem quartic_1' (y b a c d R D x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3 : R ≠ 0)
  (h4 : D^2 = 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R))
  (h5 : x = -a / 4 + R / 2 + D / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by

  -- Define S, an auxiliary term used in Ferrari's method.
  let S := (a*y/2 - c) / (2*R)

  -- Show that D^2 equals the discriminant from the quadratic formula for the first factor.
  have h_D_calc_sq_equals_h4_D_sq : (a/2 - R)^2 - 2*y + 4*S = D^2 := by
    rw [h4]
    calc (a/2 - R)^2 - 2*y + 4*S
      = (a/2 - R)^2 - 2*y + 4*((a*y/2 - c) / (2*R)) := by simp only [S]
      _ = a^2/4 - a*R + R^2 - 2*y + (a*y - 2*c)/R := by { field_simp [h3]; ring }
      _ = a^2/4 - a*R + R^2 - 2*(R^2 - a^2/4 + b) + (a*(R^2 - a^2/4 + b) - 2*c)/R := by
        rw [show y = R^2 - a^2/4 + b by linarith [h2]]
      _ = 3*a^2/4 - R^2 - 2*b + (-a^3 + 4*a*b - 8*c)/(4*R) := by { field_simp [h3]; ring }
      _ = 3*a^2/4 - R^2 - 2*b + (4*a*b - 8*c - a^3)/(4*R) := by ring

  -- Prove that x is a root of the quadratic factor X^2 + (a/2 - R)X + (y/2 - S).
  have h_x_is_root_of_quadratic : x^2 + (a/2 - R)*x + (y/2 - S) = 0 := by
    rw [h5]
    ring_nf
    rw [←h_D_calc_sq_equals_h4_D_sq]
    simp only [S]
    ring

  -- Show that h1 implies the condition (a*y/2 - c)^2 - R^2*(y^2 - 4*d) = 0.
  have h_resolvent_identity : (a*y/2 - c)^2 - R^2*(y^2 - 4*d) = 0 := by
    have temp_id : (a*y/2 - c)^2 - (a^2/4 - b + y)*(y^2 - 4*d) =
                    -(y^3 - b*y^2 + (a*c - 4*d)*y - (a^2*d - 4*b*d + c^2)) := by ring
    rw [←h2] at temp_id
    have h_rhs_expr_equiv : y^3 - b*y^2 + (a*c - 4*d)*y - (a^2*d - 4*b*d + c^2) =
                            y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 := by ring
    rw [h_rhs_expr_equiv] at temp_id
    rw [h1] at temp_id
    simp only [neg_zero] at temp_id
    exact temp_id

  -- Show polynomial factorization.
  have h_rhs_eq_lhs : (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S)) =
                      x^4 + a*x^3 + b*x^2 + c*x + d := by
    calc (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S))
      = (x^2 + a/2*x + y/2)^2 - (R*x + S)^2 := by ring
      _ = x^4 + a*x^3 + (a^2/4 + y - R^2)*x^2 + (a*y/2 - 2*R*S)*x + (y^2/4 - S^2) := by ring
      _ = x^4 + a*x^3 + b*x^2 + (a*y/2 - 2*R*S)*x + (y^2/4 - S^2) := by
        rw [(show a^2/4 + y - R^2 = b by linarith [h2])]
      _ = x^4 + a*x^3 + b*x^2 + c*x + (y^2/4 - S^2) := by
        simp only [S]; field_simp [h3]; ring
      _ = x^4 + a*x^3 + b*x^2 + c*x + d := by
        simp only [S]
        have const_term_eq_d : y^2 / 4 - ((a * y / 2 - c) / (2 * R))^2 = d := by
          apply eq_of_sub_eq_zero
          field_simp [h3]
          conv =>
            lhs
            rw [show y ^ 2 * (2 * (2 * R)) ^ 2 - 4 * (a * y - 2 * c) ^ 2 - 4 * (2 * (2 * R)) ^ 2 * d =
                 -16 * ( (a*y/2 - c)^2 - R^2*(y^2 - 4*d) ) by ring]
          rw [h_resolvent_identity]
          simp
        rw [const_term_eq_d]

  have h_poly_factorization : x^4 + a*x^3 + b*x^2 + c*x + d =
    (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S)) := Eq.symm h_rhs_eq_lhs

  -- Conclude proof using factorization and the root property.
  rw [h_poly_factorization]
  rw [h_x_is_root_of_quadratic]
  simp


/-! ### QUARTIC_2' -/
theorem quartic_2' (y b a c d R D x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3 : R ≠ 0)
  (h4 : D^2 = 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R))
  (h5 : x = -a / 4 + R / 2 - D / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- Define S using Ferrari's method.
  let S := (a*y/2 - c) / (2*R)

  -- Verify that D^2 equals the discriminant from the quadratic factor.
  have h_D_calc_sq_equals_h4_D_sq : (a/2 - R)^2 - 2*y + 4*S = D^2 := by
    rw [h4]
    calc (a/2 - R)^2 - 2*y + 4*S
      = (a/2 - R)^2 - 2*y + 4*((a*y/2 - c) / (2*R)) := by simp only [S]
      _ = a^2/4 - a*R + R^2 - 2*y + (a*y - 2*c)/R := by { field_simp [h3]; ring }
      _ = a^2/4 - a*R + R^2 - 2*(R^2 - a^2/4 + b) + (a*(R^2 - a^2/4 + b) - 2*c)/R := by
        rw [show y = R^2 - a^2/4 + b by linarith [h2]]
      _ = 3*a^2/4 - R^2 - 2*b + (-a^3 + 4*a*b - 8*c)/(4*R) := by { field_simp [h3]; ring }
      _ = 3*a^2/4 - R^2 - 2*b + (4*a*b - 8*c - a^3)/(4*R) := by ring
  -- Show x is a root of the corresponding quadratic.
  have h_x_is_root_of_quadratic : x^2 + (a/2 - R)*x + (y/2 - S) = 0 := by
    rw [h5]
    ring_nf
    rw [←h_D_calc_sq_equals_h4_D_sq]
    simp only [S]
    ring
  -- Use the resolvent identity derived from h1.
  have h_resolvent_identity : (a*y/2 - c)^2 - R^2*(y^2 - 4*d) = 0 := by
    have temp_id : (a*y/2 - c)^2 - (a^2/4 - b + y)*(y^2 - 4*d) =
                    -(y^3 - b*y^2 + (a*c - 4*d)*y - (a^2*d - 4*b*d + c^2)) := by ring
    rw [←h2] at temp_id
    have h_rhs_expr_equiv : y^3 - b*y^2 + (a*c - 4*d)*y - (a^2*d - 4*b*d + c^2) =
                            y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 := by ring
    rw [h_rhs_expr_equiv] at temp_id
    rw [h1] at temp_id
    simp only [neg_zero] at temp_id
    exact temp_id
  -- Show that the factorized form equals the original quartic.
  have h_rhs_eq_lhs : (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S)) =
                      x^4 + a*x^3 + b*x^2 + c*x + d := by
    calc (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S))
      = (x^2 + a/2*x + y/2)^2 - (R*x + S)^2 := by ring
      _ = x^4 + a*x^3 + (a^2/4 + y - R^2)*x^2 + (a*y/2 - 2*R*S)*x + (y^2/4 - S^2) := by ring
      _ = x^4 + a*x^3 + b*x^2 + (a*y/2 - 2*R*S)*x + (y^2/4 - S^2) := by rw [(show a^2/4 + y - R^2 = b by linarith [h2])]
      _ = x^4 + a*x^3 + b*x^2 + c*x + (y^2/4 - S^2) := by simp only [S]; field_simp [h3]; ring
      _ = x^4 + a*x^3 + b*x^2 + c*x + d := by{
        simp only [S]
        have const_term_eq_d : y^2 / 4 - ((a * y / 2 - c) / (2 * R))^2 = d := by
          apply eq_of_sub_eq_zero
          field_simp [h3]
          conv =>
            lhs
            rw [show y ^ 2 * (2 * (2 * R)) ^ 2 - 4 * (a * y - 2 * c) ^ 2 - 4 * (2 * (2 * R)) ^ 2 * d =
                 -16 * ( (a*y/2 - c)^2 - R^2*(y^2 - 4*d) ) by ring]
          rw [h_resolvent_identity]
          simp
        rw [const_term_eq_d]}

  have h_poly_factorization : x^4 + a*x^3 + b*x^2 + c*x + d =
    (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S)) := Eq.symm h_rhs_eq_lhs
  -- Finish using factorization and root identity.
  rw [h_poly_factorization]
  rw [h_x_is_root_of_quadratic]
  simp


/-! ### QUARTIC_3' -/
theorem quartic_3' (y b a c d R E x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3 : R ≠ 0)
  (h4 : E^2 = 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R))
  (h5 : x = -a / 4 - R / 2 + E / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- Step 1: Define S, an auxiliary term from Ferrari's method.
  let S := (a*y/2 - c) / (2*R)
  -- Step 2: Show that E^2 from hypothesis h4 is consistent with the discriminant needed for x.
  have h_E_calc_sq_equals_h4_E_sq : (a/2 + R)^2 - 2*y - 4*S = E^2 := by
    rw [h4]
    calc (a/2 + R)^2 - 2*y - 4*S
        = (a/2 + R)^2 - 2*y - 4*((a*y/2 - c) / (2*R)) := by simp only [S] -- unfold S
        _ = a^2/4 + a*R + R^2 - 2*y - (a*y - 2*c)/R := by { field_simp [h3]; ring } -- Expand and simplify fraction
        _ = a^2/4 + a*R + R^2 - 2*(R^2 - a^2/4 + b) - (a*(R^2 - a^2/4 + b) - 2*c)/R := by
            rw [show y = R^2 - a^2/4 + b by linarith [h2]]
        _ = 3*a^2/4 - R^2 - 2*b + (a^3 - 4*a*b + 8*c)/(4*R) := by { field_simp [h3]; ring } -- Combine terms
        _ = 3*a^2/4 - R^2 - 2*b - (4*a*b - 8*c - a^3)/(4*R) := by ring -- Matches the RHS of h4

  -- Step 3: Prove that x (from h5) is a root of X^2 + (a/2 + R)X + (y/2 + S) = 0.
  have h_x_is_root_of_quadratic : x^2 + (a/2 + R)*x + (y/2 + S) = 0 := by
    rw [h5]
    ring_nf
    rw [←h_E_calc_sq_equals_h4_E_sq]
    simp only [S]
    ring
  -- Step 4: Show that h1 (resolvent cubic) implies the condition needed for the constant term in the factorization.
  have h_resolvent_identity : (a*y/2 - c)^2 - R^2*(y^2 - 4*d) = 0 := by
    have temp_id : (a*y/2 - c)^2 - (a^2/4 - b + y)*(y^2 - 4*d) =
                   -(y^3 - b*y^2 + (a*c - 4*d)*y - (a^2*d - 4*b*d + c^2)) := by ring
    rw [←h2] at temp_id
    have h_rhs_expr_equiv : y^3 - b*y^2 + (a*c - 4*d)*y - (a^2*d - 4*b*d + c^2) =
                            y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 := by ring
    rw [h_rhs_expr_equiv] at temp_id
    rw [h1] at temp_id
    simp only [neg_zero] at temp_id
    exact temp_id
  -- Step 5: Show the polynomial factorization.
  have h_rhs_eq_lhs : (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S)) =
                      x^4 + a*x^3 + b*x^2 + c*x + d := by
    calc (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S))
        = (x^2 + a/2*x + y/2)^2 - (R*x + S)^2 := by ring
        _ = x^4 + a*x^3 + (a^2/4 + y - R^2)*x^2 + (a*y/2 - 2*R*S)*x + (y^2/4 - S^2) := by ring
        _ = x^4 + a*x^3 + b*x^2 + (a*y/2 - 2*R*S)*x + (y^2/4 - S^2) := by
            rw [(show a^2/4 + y - R^2 = b by linarith [h2])]
        _ = x^4 + a*x^3 + b*x^2 + c*x + (y^2/4 - S^2) := by
            simp only [S]
            field_simp [h3]
            ring
        _ = x^4 + a*x^3 + b*x^2 + c*x + d := by
            simp only [S]
            have const_term_eq_d : y^2 / 4 - ((a * y / 2 - c) / (2 * R))^2 = d := by
              apply eq_of_sub_eq_zero
              field_simp [h3]
              conv =>
                lhs
                rw [show y ^ 2 * (2 * (2 * R)) ^ 2 - 4 * (a * y - 2 * c) ^ 2 - 4 * (2 * (2 * R)) ^ 2 * d =
                         -16 * ( (a*y/2 - c)^2 - R^2*(y^2 - 4*d) ) by ring]
              rw [h_resolvent_identity]
              simp
            rw [const_term_eq_d]
  have h_poly_factorization : x^4 + a*x^3 + b*x^2 + c*x + d =
      (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S)) := Eq.symm h_rhs_eq_lhs
  -- Step 6: Final proof using factorization and root.
  rw [h_poly_factorization]
  rw [h_x_is_root_of_quadratic]
  simp


/-! ### QUARTIC_4' -/
theorem quartic_4' (y b a c d R E x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3 : R ≠ 0)
  (h4 : E^2 = 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R))
  (h5 : x = -a / 4 - R / 2 - E / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- Step 1: Define S, an auxiliary term from Ferrari's method.

  let S := (a*y/2 - c) / (2*R)

  -- Step 2: Show that E^2 from hypothesis h4 is consistent with the discriminant needed for x.
  have h_E_calc_sq_equals_h4_E_sq : (a/2 + R)^2 - 2*y - 4*S = E^2 := by
    rw [h4] -- Substitute E^2 with its definition from h4
    -- Now show (a/2 + R)^2 - 2*y - 4*S equals the RHS of h4
    calc (a/2 + R)^2 - 2*y - 4*S
        = (a/2 + R)^2 - 2*y - 4*((a*y/2 - c) / (2*R)) := by simp only [S]
        _ = a^2/4 + a*R + R^2 - 2*y - (a*y - 2*c)/R := by { field_simp [h3]; ring }
        _ = a^2/4 + a*R + R^2 - 2*(R^2 - a^2/4 + b) - (a*(R^2 - a^2/4 + b) - 2*c)/R := by
            rw [show y = R^2 - a^2/4 + b by linarith [h2]]
        _ = 3*a^2/4 - R^2 - 2*b + (a^3 - 4*a*b + 8*c)/(4*R) := by { field_simp [h3]; ring }
        _ = 3*a^2/4 - R^2 - 2*b - (4*a*b - 8*c - a^3)/(4*R) := by ring

  -- Step 3: Prove that x (from h5) is a root of X^2 + (a/2 + R)X + (y/2 + S) = 0.
  have h_x_is_root_of_quadratic : x^2 + (a/2 + R)*x + (y/2 + S) = 0 := by
    rw [h5]
    ring_nf
    rw [←h_E_calc_sq_equals_h4_E_sq]
    simp only [S]
    ring

  -- Step 4: Show that h1 (resolvent cubic) implies the condition needed for the constant term in the
  have h_resolvent_identity : (a*y/2 - c)^2 - R^2*(y^2 - 4*d) = 0 := by
    have temp_id : (a*y/2 - c)^2 - (a^2/4 - b + y)*(y^2 - 4*d) =
                   -(y^3 - b*y^2 + (a*c - 4*d)*y - (a^2*d - 4*b*d + c^2)) := by ring
    rw [←h2] at temp_id
    have h_rhs_expr_equiv : y^3 - b*y^2 + (a*c - 4*d)*y - (a^2*d - 4*b*d + c^2) =
                            y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 := by
      ring
    rw [h_rhs_expr_equiv] at temp_id
    rw [h1] at temp_id
    simp only [neg_zero] at temp_id
    exact temp_id

  -- Step 5: Show the polynomial factorization.
  have h_rhs_eq_lhs : (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S)) =
                      x^4 + a*x^3 + b*x^2 + c*x + d := by
    calc (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S))
        = (x^2 + a/2*x + y/2)^2 - (R*x + S)^2 := by ring
        _ = x^4 + a*x^3 + (a^2/4 + y - R^2)*x^2 + (a*y/2 - 2*R*S)*x + (y^2/4 - S^2) := by ring
        _ = x^4 + a*x^3 + b*x^2 + (a*y/2 - 2*R*S)*x + (y^2/4 - S^2) := by
            rw [(show a^2/4 + y - R^2 = b by linarith [h2])]
        _ = x^4 + a*x^3 + b*x^2 + c*x + (y^2/4 - S^2) := by
            simp only [S]
            field_simp [h3]
            ring
        _ = x^4 + a*x^3 + b*x^2 + c*x + d := by
            simp only [S]
            have const_term_eq_d : y^2 / 4 - ((a * y / 2 - c) / (2 * R))^2 = d := by
              apply eq_of_sub_eq_zero
              field_simp [h3]
              conv =>
                lhs
                rw [show y ^ 2 * (2 * (2 * R)) ^ 2 - 4 * (a * y - 2 * c) ^ 2 - 4 * (2 * (2 * R)) ^ 2 * d =
                         -16 * ( (a*y/2 - c)^2 - R^2*(y^2 - 4*d) ) by ring]
              rw [h_resolvent_identity]
              simp
            rw [const_term_eq_d]
  have h_poly_factorization : x^4 + a*x^3 + b*x^2 + c*x + d =
      (x^2 + (a/2 - R)*x + (y/2 - S)) * (x^2 + (a/2 + R)*x + (y/2 + S)) := Eq.symm h_rhs_eq_lhs

  -- Step 6: Final proof using factorization and root.
  rw [h_poly_factorization]
  rw [h_x_is_root_of_quadratic]
  simp


/-! ### QUARTIC_1 (general verison with def. E) -/
theorem quartic_root_d_case (y b a c d R s D x : ℝ)
  (h1_cubic : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2_R_sq : R^2 = a^2 / 4 - b + y)
  (h3_s_sq : s^2 = y^2 - 4 * d)
  (h4_D_sq_cond : D^2 = if R = 0 then 3 * a^2 / 4 - 2 * b + 2 * s
                       else 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R))
  (h5_x_def : x = -a / 4 + R / 2 + D / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- Proof using the dependency theorems by cases on R = 0 or R ≠ 0.
  cases' eq_or_ne R 0 with hR_is_zero hR_is_not_zero
  -- Case 1: R = 0
  · -- If R = 0, the definition of D^2 simplifies to the 'then' branch of the if-statement.
    have h4_D_sq_simplified : D^2 = 3 * a^2 / 4 - 2 * b + 2 * s := by
      rw [h4_D_sq_cond, if_pos hR_is_zero]

    -- Apply theorem quartic_1, which handles the R=0 case for x defined with D.
    exact quartic_1 y b a c d R s D x h1_cubic h2_R_sq hR_is_zero h3_s_sq h4_D_sq_simplified h5_x_def

  -- Case 2: R ≠ 0
  · -- If R ≠ 0, the definition of D^2 simplifies to the 'else' branch of the if-statement.
    have h4_D_sq_simplified : D^2 = 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R) := by
      rw [h4_D_sq_cond, if_neg hR_is_not_zero] -- Apply the condition R≠0 to h4_D_sq_cond

    -- Apply theorem quartic_1', which handles the R≠0 case for x defined with D.
    exact quartic_1' y b a c d R D x h1_cubic h2_R_sq hR_is_not_zero h4_D_sq_simplified h5_x_def


/-! ### QUARTIC_1 (general version) -/
theorem quartic_1_general (y b a c d R s D E x : ℝ)
  (h1 : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2 : R^2 = a^2 / 4 - b + y)
  (h3_s_sq : s^2 = y^2 - 4 * d) -- Renamed h3 to h3_s_sq for clarity within this proof
  (h4_D_sq : D^2 = if R = 0 then 3 * a^2 / 4 - 2 * b + 2 * s
                   else 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R))
  (h5_E_sq : E^2 = if R = 0 then 3 * a^2 / 4 - 2 * b - 2 * s
                   else 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R))
  (h6_x_def : x = -a / 4 + R / 2 + D / 2 ∨ x = -a / 4 - R / 2 + E / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- Case split on whether R is zero or non-zero.
  cases' eq_or_ne R 0 with hR_is_zero hR_is_not_zero
  -- Case 1: R = 0
  · -- If R = 0, simplify the definitions of D^2 and E^2 using the 'then' branch of the if-statements.
    rw [if_pos hR_is_zero] at h4_D_sq
    rw [if_pos hR_is_zero] at h5_E_sq
    -- Case split on the definition of x.
    cases' h6_x_def with h6_x_is_D_case h6_x_is_E_case
    -- Subcase 1.1: x involves D
    · -- Apply theorem quartic_1, which handles the R=0 case for x involving D.
      -- The variable x is passed as an argument, and h6_x_is_D_case provides the proof for quartic_1's 6th hypothesis.
      exact quartic_1 y b a c d R s D x h1 h2 hR_is_zero h3_s_sq h4_D_sq h6_x_is_D_case
    -- Subcase 1.2: x involves E
    · -- Apply theorem quartic_3, which handles the R=0 case for x involving E.
      exact quartic_3 y b a c d R s E x h1 h2 hR_is_zero h3_s_sq h5_E_sq h6_x_is_E_case
  -- Case 2: R ≠ 0
  · -- If R ≠ 0, simplify the definitions of D^2 and E^2 using the 'else' branch of the if-statements.
    rw [if_neg hR_is_not_zero] at h4_D_sq
    rw [if_neg hR_is_not_zero] at h5_E_sq
    -- Case split on the definition of x.
    cases' h6_x_def with h6_x_is_D_case h6_x_is_E_case
    -- Subcase 2.1: x involves D
    · -- Apply theorem quartic_1', which handles the R≠0 case for x involving D.
      exact quartic_1' y b a c d R D x h1 h2 hR_is_not_zero h4_D_sq h6_x_is_D_case
    -- Subcase 2.2: x involves E
    · -- Apply theorem quartic_3', which handles the R≠0 case for x involving E.
      exact quartic_3' y b a c d R E x h1 h2 hR_is_not_zero h5_E_sq h6_x_is_E_case


-- (P_conditions AND P_x_forms) IMPLIES (Quartic_Equation = 0)
/-! ### QUARTIC_CASES (forward) -/
theorem quartic_cases_forward (y b a c d R s D E x : ℝ)
  (h1_cubic : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2_R_sq : R^2 = a^2 / 4 - b + y)
  (h3_s_sq : s^2 = y^2 - 4 * d)
  (h4_D_sq_cond : D^2 = if R = 0 then 3 * a^2 / 4 - 2 * b + 2 * s
                       else 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R))
  (h5_E_sq_cond : E^2 = if R = 0 then 3 * a^2 / 4 - 2 * b - 2 * s
                       else 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R))
  (h6_x_forms : x = -a / 4 + R / 2 + D / 2 ∨
                x = -a / 4 + R / 2 - D / 2 ∨
                x = -a / 4 - R / 2 + E / 2 ∨
                x = -a / 4 - R / 2 - E / 2) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 := by
  -- We handle each case of h6_x_forms (the four possible forms of x)
  rcases h6_x_forms with h_x_form1 | h_x_form2 | h_x_form3 | h_x_form4
  -- Case 1: x = -a / 4 + R / 2 + D / 2
    -- We need to consider subcases based on whether R = 0 or R ≠ 0 for D^2
  by_cases hR_zero : R = 0
  -- Subcase 1.1: R = 0
  -- Get the specific definition of D^2 for R = 0
  have h_D_sq_val : D^2 = 3 * a^2 / 4 - 2 * b + 2 * s := by
    rw [h4_D_sq_cond, if_pos hR_zero]
  -- Apply quartic_1 theorem for R=0 case
  exact quartic_1 y b a c d R s D x h1_cubic h2_R_sq hR_zero h3_s_sq h_D_sq_val h_x_form1
  -- Subcase 1.2: R ≠ 0
  -- Get the specific definition of D^2 for R ≠ 0
  have h_D_sq_val : D^2 = 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R) := by
    rw [h4_D_sq_cond, if_neg hR_zero]
  -- Apply quartic_1' theorem for R≠0 case
  exact quartic_1' y b a c d R D x h1_cubic h2_R_sq hR_zero h_D_sq_val h_x_form1

  -- Case 2: x = -a / 4 + R / 2 - D / 2
  by_cases hR_zero : R = 0
  -- Subcase 2.1: R = 0
  have h_D_sq_val : D^2 = 3 * a^2 / 4 - 2 * b + 2 * s := by
    rw [h4_D_sq_cond, if_pos hR_zero]
  exact quartic_2 y b a c d R s D x h1_cubic h2_R_sq hR_zero h3_s_sq h_D_sq_val h_x_form2
  -- Subcase 2.2: R ≠ 0
  have h_D_sq_val : D^2 = 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R) := by
    rw [h4_D_sq_cond, if_neg hR_zero]
  exact quartic_2' y b a c d R D x h1_cubic h2_R_sq hR_zero h_D_sq_val h_x_form2

  -- Case 3: x = -a / 4 - R / 2 + E / 2
  -- We need to consider subcases based on whether R = 0 or R ≠ 0 for E^2
  by_cases hR_zero : R = 0
  -- Subcase 3.1: R = 0
  -- Get the specific definition of E^2 for R = 0
  have h_E_sq_val : E^2 = 3 * a^2 / 4 - 2 * b - 2 * s := by
    rw [h5_E_sq_cond, if_pos hR_zero]
  -- Apply quartic_3 theorem for R=0 case
  exact quartic_3 y b a c d R s E x h1_cubic h2_R_sq hR_zero h3_s_sq h_E_sq_val h_x_form3
  -- Subcase 3.2: R ≠ 0
  -- Get the specific definition of E^2 for R ≠ 0
  have h_E_sq_val : E^2 = 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R) := by
    rw [h5_E_sq_cond, if_neg hR_zero]
  -- Apply quartic_3' theorem for R≠0 case
  exact quartic_3' y b a c d R E x h1_cubic h2_R_sq hR_zero h_E_sq_val h_x_form3

  -- Case 4: x = -a / 4 - R / 2 - E / 2
  by_cases hR_zero : R = 0
  -- Subcase 4.1: R = 0
  have h_E_sq_val : E^2 = 3 * a^2 / 4 - 2 * b - 2 * s := by
    rw [h5_E_sq_cond, if_pos hR_zero]
  exact quartic_4 y b a c d R s E x h1_cubic h2_R_sq hR_zero h3_s_sq h_E_sq_val h_x_form4
  -- Subcase 4.2: R ≠ 0
  have h_E_sq_val : E^2 = 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R) := by
    rw [h5_E_sq_cond, if_neg hR_zero]
  exact quartic_4' y b a c d R E x h1_cubic h2_R_sq hR_zero h_E_sq_val h_x_form4


/-! ### QUARTIC_CASES -/
-- Lemma 1: If R = 0, then a specific condition relating a, b, c holds,
-- which ensures the 'x' coefficient matches.
lemma R0_condition_for_coeff_c (y b a c d R : ℝ)
  (h1_cubic : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2_R_sq : R^2 = a^2 / 4 - b + y)
  (hR0 : R = 0) :
  a * (b - a^2 / 4) / 2 = c := by

  -- Step 1: Derive y in terms of a and b using h2_R_sq and hR0.
  have y_val : y = b - a^2 / 4 := by
    rw [hR0] at h2_R_sq
    simp only [zero_pow, sq] at h2_R_sq -- Simplifies R^2 to 0.
    -- h2_R_sq is now: 0 = a^2 / 4 - b + y
    linarith [h2_R_sq] -- Rearranges to y = b - a^2/4.

  -- Step 2: Show that the terms involving `d` in h1_cubic vanish because their coefficient is zero.
  have d_coefficient : -4*y - a^2 + 4*b = 0 := by
    rw [y_val]
    ring
  have h1_cubic_no_d : y^3 - b*y^2 + a*c*y - c^2 = 0 := by
    have h_rw_h1_cubic : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 =
                         y^3 - b*y^2 + a*c*y - c^2 + d*(-4*y - a^2 + 4*b) := by
      ring
    rw [h_rw_h1_cubic] at h1_cubic
    rw [d_coefficient, mul_zero, add_zero] at h1_cubic
    exact h1_cubic

  -- Step 3: Show that h1_cubic_no_d (which is y^3 - b*y^2 + a*c*y - c^2 = 0)
  -- This is done by showing h1_cubic_no_d's LHS is a multiple of (2*c - a*y)^2.
  have h_2c_minus_ay_sq_eq_0 : (2*c - a*y)^2 = 0 := by
    have b_val_in_terms_of_y : b = y + a^2/4 := by
      linarith [y_val]
    -- Show that LHS of h1_cubic_no_d is (-1/4) * (2*c - a*y)^2
    have h_lhs_identity : y^3 - b*y^2 + a*c*y - c^2 = (-1/4 : ℝ) * (2*c - a*y)^2 := by
      calc y^3 - b*y^2 + a*c*y - c^2
          _ = y^3 - (y + a^2/4)*y^2 + a*c*y - c^2    := by rw [b_val_in_terms_of_y]
          _ = -(a^2/4)*y^2 + a*c*y - c^2            := by ring
          _ = (-1/4 : ℝ) * (4*c^2 - 4*a*c*y + a^2*y^2) := by
              field_simp [show (4 : ℝ) ≠ 0 by norm_num] -- Factor out -1/4
              ring
          _ = (-1/4 : ℝ) * (2*c - a*y)^2             := by ring-- (X-Y)^2 = (Y-X)^2
    have  : (2*c - a*y)^2 = 0 := by
      by_contra h
      have h3 : (-1/4 : ℝ) * (2*c - a*y)^2 < 0 := by
        have h4 : (2*c - a*y)^2 > 0 := by
          by_contra h5
          have h6 : (2*c - a*y)^2 ≤ 0 := by linarith
          have h7 : (2*c - a*y)^2 ≥ 0 := by nlinarith
          have h8 : (2*c - a*y)^2 = 0 := by linarith
          contradiction
        nlinarith [h4]
      linarith [h1_cubic_no_d]
    exact this

    -- Concludes (2*c - a*y) = 0
  simp [show (-1/4 : ℝ) ≠ 0 by norm_num] at h_2c_minus_ay_sq_eq_0

  -- Step 5: Substitute y_val into 2*c - a*y = 0 and rearrange to match the goal.
  rw [y_val] at h_2c_minus_ay_sq_eq_0
  linarith [h_2c_minus_ay_sq_eq_0]


-- Lemma 2: If R ≠ 0, Ferrari's identity for the constant term 'd' holds.
lemma R_ne0_identity_for_coeff_d (y b a c d R : ℝ)
  (h1_cubic : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2_R_sq : R^2 = a^2 / 4 - b + y)
  (hR_ne0 : R ≠ 0) :
  (y^2 - ((a*y - 2*c)/(2*R))^2) / 4 = d := by

  -- Step 1: Rewrite b in terms of y, a, and R.
  have b_val : b = y + a^2/4 - R^2 := by
    linarith [h2_R_sq]

  -- Step 2: Manipulate the cubic equation h1_cubic.
  have h1_cubic_rearranged : y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 =
    y^3 - b*y^2 + a*c*y - c^2 - d*(4*y + a^2 - 4*b)  := by
    calc  y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2
        _ = y^3 - b*y^2 + a*c*y - 4*d*y - a^2*d + 4*b*d - c^2 := by ring
        _ = y^3 - b*y^2 + a*c*y - c^2 - (4*d*y + a^2*d - 4*b*d) := by ring
        _ = y^3 - b*y^2 + a*c*y - c^2 - d*(4*y + a^2 - 4*b)   := by ring

  rw [h1_cubic_rearranged] at h1_cubic

  -- Substitute b_val into the coefficient of d: (4*y + a^2 - 4*b)
  have d_coeff_val : 4*y + a^2 - 4*b = 4*R^2 := by
    rw [b_val]
    ring

  -- So, h1_cubic_rearranged becomes: y^3 - b*y^2 + a*c*y - c^2 - d*(4*R^2) = 0
  have four_R_sq_d_eq_expr : 4*R^2*d = y^3 - b*y^2 + a*c*y - c^2 := by
    rw [d_coeff_val] at h1_cubic_rearranged
    linarith [h1_cubic_rearranged]

  -- Step 3: Substitute b_val into the right-hand side of four_R_sq_d_eq_expr and expand.
  -- RHS = y^3 - (y + a^2/4 - R^2)*y^2 + a*c*y - c^2
  -- This simplifies to R^2*y^2 - (a^2/4)*y^2 + a*c*y - c^2 (let's call this Expr_X)
  have expr_X_def : R^2*y^2 - (a^2/4)*y^2 + a*c*y - c^2 =
                   y^3 - (y + a^2/4 - R^2)*y^2 + a*c*y - c^2 := by ring
  rw [← b_val ] at expr_X_def
  rw [← expr_X_def] at four_R_sq_d_eq_expr


  -- Step 4 & 5 (Combined): Recognize the algebraic structure and relate to the goal.
  have eq_multiplied : 16*R^2*d = 4*R^2*y^2 - ((a*y - 2*c)^2):= by
    calc 16*R^2*d
        _ = 4 * (4*R^2*d)                                 := by ring
        _ = 4 * (R^2*y^2 - (a^2/4)*y^2 + a*c*y - c^2)     := by rw [four_R_sq_d_eq_expr]
        _ = 4*R^2*y^2 - a^2*y^2 + 4*a*c*y - 4*c^2         := by ring
        _ = 4*R^2*y^2 - (a^2*y^2 - 4*a*c*y + 4*c^2)       := by ring
        _ = 4*R^2*y^2 - ((a*y - 2*c)^2)                   := by ring
  field_simp [hR_ne0, show (4:ℝ) ≠ 0 by norm_num]
  rw [show y^2 * (2*R)^2 = 4*R^2*y^2 by ring]
  rw [show d * ((2*R)^2 * 4) = 16*R^2*d by ring]
  exact Eq.symm eq_multiplied



-- Main Theorem
theorem quartic_cases (y b a c d R s D E x : ℝ)
  (h1_cubic : y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0)
  (h2_R_sq : R^2 = a^2 / 4 - b + y)
  (h3_s_sq : s^2 = y^2 - 4 * d)
  (h4_D_sq_cond : D^2 = if R = 0 then 3 * a^2 / 4 - 2 * b + 2 * s
                       else 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R))
  (h5_E_sq_cond : E^2 = if R = 0 then 3 * a^2 / 4 - 2 * b - 2 * s
                       else 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R)) :
  x^4 + a * x^3 + b * x^2 + c * x + d = 0 ↔
  (x = -a / 4 + R / 2 + D / 2 ∨ x = -a / 4 + R / 2 - D / 2 ∨
   x = -a / 4 - R / 2 + E / 2 ∨ x = -a / 4 - R / 2 - E / 2) := by
  apply Iff.intro
  -- Define the four root forms for convenience
  let t1 := -a / 4 + R / 2 + D / 2
  let t2 := -a / 4 + R / 2 - D / 2
  let t3 := -a / 4 - R / 2 + E / 2
  let t4 := -a / 4 - R / 2 - E / 2

  -- Define the constant terms of the expected quadratic factors
  let K_D_const := (a^2/16 - a*R/4 + R^2/4) - D^2/4
  let K_E_const := (a^2/16 + a*R/4 + R^2/4) - E^2/4

  -- Direction 1: (quartic_eq_zero) → (x = t1 ∨ x = t2 ∨ x = t3 ∨ x = t4)
  · intro h_quartic_eq_zero

-- Step 1: Prove the polynomial factorization identity:
    -- x^4 + ax^3 + bx^2 + cx + d = (x^2 + (a/2 - R)x + K_D_const) * (x^2 + (a/2 + R)x + K_E_const)
    have h_poly_factor_to_quadratics :
      x^4 + a*x^3 + b*x^2 + c*x + d =
      (x^2 + (a/2 - R)*x + K_D_const) * (x^2 + (a/2 + R)*x + K_E_const) := by
        -- Proof is by expanding the RHS and verifying coefficients match a, b, c, d.
        -- Use `suffices` to make the goal proving the difference is zero.
        suffices (x^2 + (a/2 - R)*x + K_D_const) * (x^2 + (a/2 + R)*x + K_E_const) -
                 (x^4 + a*x^3 + b*x^2 + c*x + d) = 0 by linarith
        -- Verify coefficients of the difference are zero.
        calc (x^2 + (a/2 - R)*x + K_D_const) * (x^2 + (a/2 + R)*x + K_E_const) - (x^4 + a*x^3 + b*x^2 + c*x + d)
            _ = x^4 + ((a/2+R)+(a/2-R))*x^3 + (K_D_const+K_E_const+(a/2-R)*(a/2+R))*x^2 + ((a/2-R)*K_E_const+(a/2+R)*K_D_const)*x + K_D_const*K_E_const
                - (x^4 + a*x^3 + b*x^2 + c*x + d) := by ring -- Expand the product
            _ = x^4 + a*x^3 + (K_D_const+K_E_const + a^2/4-R^2)*x^2 + ((a/2-R)*K_E_const+(a/2+R)*K_D_const)*x + K_D_const*K_E_const
                - (x^4 + a*x^3 + b*x^2 + c*x + d) := by {ring } -- Simplify x^3 and (a/2-R)(a/2+R) terms
        -- Now show each coefficient matches (b, c, d) resulting in zero.

        have coeff_x2_eq_b : K_D_const + K_E_const + a^2/4 - R^2 = b := by
          simp only [K_D_const, K_E_const] -- Substitute definitions
          -- K_D+K_E = a^2/8 + R^2/2 - (D^2+E^2)/4
          by_cases hR0_coeff_check : R = 0
          · have hD2_is : D^2 = 3*a^2/4 - 2*b + 2*s := by rw [h4_D_sq_cond, if_pos hR0_coeff_check]
            have hE2_is : E^2 = 3*a^2/4 - 2*b - 2*s := by rw [h5_E_sq_cond, if_pos hR0_coeff_check]
            simp only [hR0_coeff_check, hD2_is, hE2_is, add_halves, sub_zero, mul_zero, zero_div]
            field_simp; ring -- Simplifies to b = b
          · have hD2_is : D^2 = 3*a^2/4 - R^2 - 2*b + (4*a*b-8*c-a^3)/(4*R) := by rw [h4_D_sq_cond, if_neg hR0_coeff_check]
            have hE2_is : E^2 = 3*a^2/4 - R^2 - 2*b - (4*a*b-8*c-a^3)/(4*R) := by rw [h5_E_sq_cond, if_neg hR0_coeff_check]
            simp only [hD2_is, hE2_is, add_halves]
            field_simp [hR0_coeff_check]
            ring

        -- Coefficient of x: (a/2-R)*K_E_const + (a/2+R)*K_D_const = c
        have coeff_x1_eq_c : (a/2 - R)*K_E_const + (a/2 + R)*K_D_const = c := by
          by_cases hR0_coeff_check : R = 0
          -- Current goal: (a/2 - R)*K_E_const + (a/2 + R)*K_D_const = c
          rw [hR0_coeff_check] -- Substitutes R with 0
          -- Goal: (a/2 - 0)*K_E_const + (a/2 + 0)*K_D_const = c
          simp only [sub_zero, add_zero]
          -- Goal: a/2 * K_E_const + a/2 * K_D_const = c
          rw [← mul_add] -- Factors out a/2
          have h_c_val := R0_condition_for_coeff_c y b a c d R h1_cubic h2_R_sq hR0_coeff_check
          -- Need to show a/2 * (K_D_const+K_E_const) = a/2 * (b-a^2/4)
          have h_const_sum : K_D_const + K_E_const = b - a^2/4 := by
            have y_val : y = b - a^2/4 := by { rw [hR0_coeff_check] at h2_R_sq; simp at h2_R_sq; linarith [h2_R_sq] }
            have hD2_is : D^2 = 3*a^2/4 - 2*b + 2*s := by rw [h4_D_sq_cond, if_pos hR0_coeff_check]
            have hE2_is : E^2 = 3*a^2/4 - 2*b - 2*s := by rw [h5_E_sq_cond, if_pos hR0_coeff_check]
            simp only [hR0_coeff_check, hD2_is, hE2_is, K_D_const, K_E_const, add_halves, sub_zero, mul_zero, zero_div]
            ring
          -- Prove the main goal for this case: (a/2 - R)*K_E_const + (a/2 + R)*K_D_const = c
          rw [add_comm K_E_const K_D_const]
          rw [h_const_sum]
          ring_nf; ring_nf at h_c_val
          exact h_c_val
           -- Case R≠0: Term simplifies to c after complex algebra.
          have y_val : y = R^2 - a^2/4 + b := by linarith [h2_R_sq]
          have hD2_is : D^2 = 3*a^2/4 - R^2 - 2*b + (4*a*b-8*c-a^3)/(4*R) := by rw [h4_D_sq_cond, if_neg hR0_coeff_check]
          have hE2_is : E^2 = 3*a^2/4 - R^2 - 2*b - (4*a*b-8*c-a^3)/(4*R) := by rw [h5_E_sq_cond, if_neg hR0_coeff_check]
          simp only [K_D_const, K_E_const, hD2_is, hE2_is, y_val]
          field_simp [hR0_coeff_check]
          ring

        -- Constant coefficient: K_D_const * K_E_const = d
        have coeff_const_eq_d : K_D_const * K_E_const = d := by
          by_cases hR0_coeff_check : R = 0
          -- Case R=0: Goal is K_D_const * K_E_const = d
          -- We aim to show K_D_const * K_E_const = (y^2 - s^2) / 4, then use h3_s_sq.
          have product_is_y_s_form : K_D_const * K_E_const = (y^2 - s^2) / 4 := by
              -- Locally expand K_D_const, K_E_const and use D^2, E^2 for R=0
              have hD2_local : D^2 = 3*a^2/4 - 2*b + 2*s := by rw [h4_D_sq_cond, if_pos hR0_coeff_check]
              have hE2_local : E^2 = 3*a^2/4 - 2*b - 2*s := by rw [h5_E_sq_cond, if_pos hR0_coeff_check]
              have y_val_local : y = b - a^2/4 := by { rw [hR0_coeff_check] at h2_R_sq; simp at h2_R_sq; linarith [h2_R_sq] }
              -- Rewrite K_D_const and K_E_const in terms of y_val_local and s
              have K_D_expanded : K_D_const = (b - a ^ 2 / 4 - s) / 2 := by
                simp only [K_D_const, hR0_coeff_check, hD2_local, y_val_local]
                field_simp [show (16 : ℝ) ≠ 0 by norm_num, show (4 : ℝ) ≠ 0 by norm_num, show (2 : ℝ) ≠ 0 by norm_num]
                ring
              have K_E_expanded : K_E_const = (b - a ^ 2 / 4 + s) / 2 := by
                simp only [K_E_const, hR0_coeff_check, hE2_local, y_val_local]
                field_simp [show (16 : ℝ) ≠ 0 by norm_num, show (4 : ℝ) ≠ 0 by norm_num, show (2 : ℝ) ≠ 0 by norm_num]
                ring
              rw [K_D_expanded, K_E_expanded]
              rw [y_val_local]
              ring
          rw [product_is_y_s_form]
          rw [h3_s_sq]
          field_simp [show (4 : ℝ) ≠ 0 by norm_num] -- Goal: (4*d)/4 = d
          ring_nf
          -- Case R≠0: Product simplifies to (y^2 - s_eff^2)/4 where s_eff=(ay-2c)/(2R). Use Lemma 2.
          have h_d_val := R_ne0_identity_for_coeff_d y b a c d R h1_cubic h2_R_sq hR0_coeff_check
          rw [← h_d_val]
          have y_val_local : y = R^2 - a^2/4 + b := by linarith [h2_R_sq] -- Renamed to avoid conflict if y is used differently
          have hD2_is_local : D^2 = 3*a^2/4 - R^2 - 2*b + (4*a*b-8*c-a^3)/(4*R) := by rw [h4_D_sq_cond, if_neg hR0_coeff_check]
          have hE2_is_local : E^2 = 3*a^2/4 - R^2 - 2*b - (4*a*b-8*c-a^3)/(4*R) := by rw [h5_E_sq_cond, if_neg hR0_coeff_check]
          simp only [K_D_const, K_E_const, hD2_is_local, hE2_is_local, y_val_local]
          field_simp [hR0_coeff_check, -- R ≠ 0
            show (2:ℝ) ≠ 0 by norm_num, show (4:ℝ) ≠ 0 by norm_num,
            show (8:ℝ) ≠ 0 by norm_num, show (16:ℝ) ≠ 0 by norm_num,
            show (32:ℝ) ≠ 0 by norm_num, show (64:ℝ) ≠ 0 by norm_num,
            show (128:ℝ) ≠ 0 by norm_num, show (256:ℝ) ≠ 0 by norm_num]
          ring
        -- Now substitute the coefficient equalities back into the expanded expression
        rw [coeff_x2_eq_b, coeff_x1_eq_c, coeff_const_eq_d]
        ring

    -- Step 2: Factor the verified quadratic product into linear factors.
    have h_quadratics_to_linear_factors :
      (x^2 + (a/2 - R)*x + K_D_const) * (x^2 + (a/2 + R)*x + K_E_const) =
      (x - t1) * (x - t2) * (x - t3) * (x - t4) := by
        simp only [K_D_const, K_E_const, t1, t2, t3, t4] -- Expand definitions
        ring

    -- Step 3: Combine factorizations and deduce the root form for x.
    rw [h_poly_factor_to_quadratics, h_quadratics_to_linear_factors] at h_quartic_eq_zero
    simp [mul_eq_zero] at h_quartic_eq_zero
    -- h_quartic_eq_zero is now: ((x - t1 = 0 ∨ x - t2 = 0) ∨ x - t3 = 0) ∨ x - t4 = 0
    rw [sub_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero] at h_quartic_eq_zero -- Change x-ti=0 to x=ti
    simp [or_assoc] at h_quartic_eq_zero
    -- Sub t1,t2,t3,t4 back to their definitions
    aesop

  -- Direction 2: (x is one of the forms t1..t4) → (quartic = 0) ("If" direction)
  · intro h_x_forms
    -- This direction is proven by the helper theorem `quartic_cases_forward`.
    exact quartic_cases_forward y b a c d R s D E x h1_cubic h2_R_sq h3_s_sq h4_D_sq_cond h5_E_sq_cond h_x_forms


end Quartic
