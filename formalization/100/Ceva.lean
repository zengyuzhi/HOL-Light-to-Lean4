import Mathlib
import Aesop

open Topology Filter Real TopologicalSpace Finset Set
open scoped BigOperators

variable {α : Type*} [NormedAddCommGroup α]
variable {E : Type*} [AddCommGroup E] [Module ℝ E]


/- Definitions needed for the theorems -/
def between (x a b : E) : Prop := x ∈ segment ℝ a b

-- def between (x : α) (p : α × α) : Prop :=
--   ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ x = u • p.1 + (1 - u) • p.2

-- def collinear (s : Set α) : Prop :=
--   ∃ (v : α) (w : α), ∀ x ∈ s, ∃ t : ℝ, x = v + t • (w - v)


/- Theorems -/
-- BETWEEN
theorem between_thm {x a b : α} [NormedSpace ℝ α] :
    between x a b ↔ ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ x = u • a + (1 - u) • b := by
  -- following: Start by using the theorem `BETWEEN_IN_CONVEX_HULL` which establishes that $x$ is between points $a$ and $b$ if and only if $x$ is in the convex hull of the set $\{a,b\}$.
  rw [between, ← convexHull_pair]
  -- following: Apply a symmetric reordering of the set using `SET_RULE` to get $\{a,b\} = \{b,a\}$.
  rw [(Set.pair_comm a b)]
  -- - Use the alternate characterization of a two-point convex hull from `CONVEX_HULL_2_ALT`, which states that the convex hull of $\{a,b\}$ is the set $\{a + u \cdot (b-a) \mid 0 \leq u \land u \leq 1\}$.
  simp [convexHull_insert, convexHull_singleton, segment_eq_image]
  constructor
  · rintro ⟨u, ⟨hu0, hu1⟩, hx⟩
    use u, hu0, hu1
    rw [← hx]
    abel
  · rintro ⟨u, hu0, hu1, hx⟩
    use u, ⟨hu0, hu1⟩
    rw [hx]
    abel


-- NORM_CROSS
theorem norm_cross {a b c d e f : α}:
    ‖a‖ * ‖b‖ * ‖c‖ = ‖d‖ * ‖e‖ * ‖f‖ ↔ ‖a‖^2 * ‖b‖^2 * ‖c‖^2 = ‖d‖^2 * ‖e‖^2 * ‖f‖^2 := by
  -- Proof outline:
  -- 1. Establish that products of norms are non-negative.
  -- 2. Show that `‖x‖^2 * ‖y‖^2 * ‖z‖^2` is equal to `(‖x‖ * ‖y‖ * ‖z‖)^2`.
  -- 3. Apply the lemma: for non-negative reals `X, Y`, `X = Y ↔ X^2 = Y^2`.
  -- Rewrite the squared terms on the RHS to be squares of products.
  rw [show ‖a‖^2 * ‖b‖^2 * ‖c‖^2 = (‖a‖ * ‖b‖ * ‖c‖)^2 by ring_nf]
  rw [show ‖d‖^2 * ‖e‖^2 * ‖f‖^2 = (‖d‖ * ‖e‖ * ‖f‖)^2 by ring_nf]

  -- Let X = ‖a‖ * ‖b‖ * ‖c‖ and Y = ‖d‖ * ‖e‖ * ‖f‖.
  -- The goal is now X = Y ↔ X^2 = Y^2.
  -- Norms are non-negative.
  have h_norm_a_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have h_norm_b_nonneg : 0 ≤ ‖b‖ := norm_nonneg b
  have h_norm_c_nonneg : 0 ≤ ‖c‖ := norm_nonneg c
  have h_norm_d_nonneg : 0 ≤ ‖d‖ := norm_nonneg d
  have h_norm_e_nonneg : 0 ≤ ‖e‖ := norm_nonneg e
  have h_norm_f_nonneg : 0 ≤ ‖f‖ := norm_nonneg f

  -- Products of non-negative numbers are non-negative.
  have hX_nonneg : 0 ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
    positivity
  have hY_nonneg : 0 ≤ ‖d‖ * ‖e‖ * ‖f‖ := by
    positivity

  -- For non-negative reals X and Y, X = Y ↔ X^2 = Y^2.
  -- The lemma `sq_eq_sq` states: `(hx : 0 ≤ X) (hy : 0 ≤ Y) : X^2 = Y^2 ↔ X = Y`.
  -- We need the symmetric version of this implication.
  exact (sq_eq_sq₀ hX_nonneg hY_nonneg).symm


/- Auxiliary lemma about proportional vectors
 if $y_1 \neq 0$ and $x_2 y_1 = x_1 y_2$, then there exists a scalar $c$ such that $x_1 = c \cdot y_1$ and $x_2 = c \cdot y_2$.
-/
lemma exists_scale_of_cross_eq_zero {x y : ℝ × ℝ} (hy : y.1 ≠ 0)
    (h : x.1 * y.2 = x.2 * y.1) : ∃ c : ℝ, x.1 = c * y.1 ∧ x.2 = c * y.2 := by
  use x.1 / y.1
  constructor
  · field_simp [hy]
  · field_simp [hy, mul_comm, h]

-- COLLINEAR
theorem collinear_iff {a b c : ℝ × ℝ} :
    Collinear ℝ ({a, b, c}: Set (ℝ × ℝ)) ↔ (a.1 - b.1) * (b.2 - c.2) = (a.2 - b.2) * (b.1 - c.1) := by
  -- Special case: If $a = b$, then the algebraic condition simplifies to $0 = 0$, which is true. In this case, $\{a, b, c\} = \{a, c\}$ contains only two points, which are always collinear.
  by_cases hab : a = b
  · simp [hab]
    exact collinear_pair ℝ b c
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  -- forward direction
  constructor
  /- (⇒) Forward direction -/
  · intro h
    rcases h with ⟨p₀, v, h⟩
    -- Get equations for each point
    have ⟨r₁, h₁⟩ := h a (by simp)
    have ⟨r₂, h₂⟩ := h b (by simp)
    have ⟨r₃, h₃⟩ := h c (by simp)
    -- Compute differences
    have hb := congr_arg (fun p => p -ᵥ p₀) h₂
    have hc := congr_arg (fun p => p -ᵥ p₀) h₃
    simp [vsub_vadd_eq_vsub_sub] at hb hc
    -- Get scalar multiples
    have h_ab_diff: a - b = (r₁ - r₂) • v := by
      rw [h₁, h₂]
      simp [vsub_vadd_eq_vsub_sub, sub_smul]
    have h_bc_diff : b - c = (r₂ - r₃) • v := by
      rw [h₂, h₃]
      simp [vsub_vadd_eq_vsub_sub, sub_smul]
    -- Extract components from the differences
    have h_ba_fst := congr_arg Prod.fst h_ab_diff
    have h_ba_snd := congr_arg Prod.snd h_ab_diff
    have h_cb_fst := congr_arg Prod.fst h_bc_diff
    have h_cb_snd := congr_arg Prod.snd h_bc_diff
    -- Simplify component equations
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub] at h_ba_fst h_ba_snd h_cb_fst h_cb_snd
    -- Rewrite the goal using these component equations
    rw [h_ba_fst, h_ba_snd, h_cb_fst, h_cb_snd]
    simp only [smul_eq_mul]
    ring_nf  -- Algebraic simplification to reach final form
/- (⇐) Backward direction -/
  · intro h
    -- Set up difference vectors
    set v := a - b with v_def
    set w := b - c with w_def
    have h_cross : v.1 * w.2 = v.2 * w.1 := by
      simp [v_def, w_def] at h ⊢
      exact h
    have v_ne_zero : v ≠ 0 := by
      intro hv_eq_zero
      apply hab
      exact vsub_eq_zero_iff_eq.mp hv_eq_zero
    have hv_nonzero_comp : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
      rcases v with ⟨v_x, v_y⟩
      contrapose! v_ne_zero
      simp only [Prod.mk_eq_zero, not_or] at v_ne_zero
      exact Prod.ext v_ne_zero.1 v_ne_zero.2
    cases' hv_nonzero_comp with hv₁ hv₂
    -- Case 1: v.1 ≠ 0
    · have h_arg_for_lemma1 : w.1 * v.2 = w.2 * v.1 := by
        simp [v_def, w_def] at h ⊢
        ring_nf at *
        nlinarith
      obtain ⟨z, hw1_eq_z_v1, hw2_eq_z_v2⟩ := exists_scale_of_cross_eq_zero hv₁ h_arg_for_lemma1
      use b, v
      intro p hp_mem_set
      simp at hp_mem_set
      rcases hp_mem_set with (rfl | rfl | rfl)
      · -- Case p = a
        use 1
        simp only [v_def, one_smul]
        exact (eq_vadd_iff_vsub_eq p (p - b) b).mpr v_def
      · -- Case p = b
        use 0
        simp only [zero_smul]
        exact Eq.symm (zero_vadd (ℝ × ℝ) p)
      · -- Case p = c
        use -z
        rw [eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev b p]
        simp [← v_def, ← w_def]
        -- Prove w = z • v
        ext
        · simp [hw1_eq_z_v1]
        · simp [hw2_eq_z_v2]
    · -- Case 2: v.2 ≠ 0
      -- Let x_sw = (w.2, w.1) and y_sw = (v.2, v.1).
      -- hy is y_sw.1 ≠ 0 => v.2 ≠ 0, which is hv₂.
      -- h_lemma is x_sw.1 * y_sw.2 = x_sw.2 * y_sw.1 => w.2 * v.1 = w.1 * v.2. This is h_cross.
      have h_arg_for_lemma2 : w.2 * v.1 = w.1 * v.2 := by
        simp [v_def, w_def] at h ⊢
        ring_nf at *
        nlinarith
      obtain ⟨z, hw2_eq_z_v2, hw1_eq_z_v1⟩ := @exists_scale_of_cross_eq_zero (w.2, w.1) (v.2, v.1) hv₂ h_arg_for_lemma2
      -- hw2_eq_z_v2 means (w.2, w.1).1 = z * (v.2, v.1).1 => w.2 = z * v.2
      -- hw1_eq_z_v1 means (w.2, w.1).2 = z * (v.2, v.1).2 => w.1 = z * v.1
      -- These imply w = z • v.
      use b, v
      intro p hp_mem_set
      simp at hp_mem_set
      rcases hp_mem_set with (rfl | rfl | rfl)
      · use 1
        simp only [v_def, one_smul]
        exact (eq_vadd_iff_vsub_eq p (p - b) b).mpr v_def
      · use 0
        simp only [zero_smul]
        exact Eq.symm (zero_vadd (ℝ × ℝ) p)
      · use -z
        rw [eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev b p]
        simp [← v_def, ← w_def] -- Goal: w = z • v
        ext
        · exact hw1_eq_z_v1
        · exact hw2_eq_z_v2



-- CEVA_WEAK
  -- Proof outline:
  -- 1. Rewrite using between_thm to get parametric forms
  -- 2. Substitute parametric expressions for all points
  -- 3. Express distances via vector norms
  -- 4. Simplify using norm_cross and collinear_iff
  -- 5. Final real arithmetic verification
theorem ceva_weak  {A B C X Y Z P : ℝ × ℝ}
    (h_noncoll : ¬Collinear ℝ ({A, B, C}: Set (ℝ × ℝ))) -- Using Mathlib's Collinear
    (hX_between_BC : between X B C) (hY_between_AC : between Y A C) (hZ_between_AB : between Z A B)
    (hP_between_AX : between P A X) (hP_between_BY : between P B Y) (hP_between_CZ : between P C Z) :
    dist B X * dist C Y * dist A Z = dist X C * dist Y A * dist Z B := by
  simp only [dist_eq_norm]
  rw [norm_cross]
  have h_noncoll_ABC_algebraic : (A.1 - B.1) * (B.2 - C.2) ≠ (A.2 - B.2) * (B.1 - C.1) :=
    (collinear_iff.not).mp h_noncoll
  -- Step 1: Unpack `between` conditions to get parameters and point equations.
  rcases between_thm.mp hX_between_BC with ⟨ux, ux_ge0, ux_le1, hX_eq_orig⟩
  rcases between_thm.mp hY_between_AC with ⟨uy, uy_ge0, uy_le1, hY_eq_orig⟩
  rcases between_thm.mp hZ_between_AB with ⟨uz, uz_ge0, uz_le1, hZ_eq_orig⟩

  rcases between_thm.mp hP_between_AX with ⟨upx, upx_ge0, upx_le1, hP_AX_eq_orig⟩
  rcases between_thm.mp hP_between_BY with ⟨upy, upy_ge0, upy_le, hP_BY_eq_orig⟩
  rcases between_thm.mp hP_between_CZ with ⟨upz, upz_ge0, upz_le1, hP_CZ_eq_orig⟩

  -- Point equations from `between_thm` are X = ux•B + (1-ux)•C, etc.
  -- For ℝ×ℝ, which is a vector space, `vsub` is subtraction.
  have hX_eq : X = ux • B + (1 - ux) • C := hX_eq_orig
  have hY_eq : Y = uy • A + (1 - uy) • C := hY_eq_orig
  have hZ_eq : Z = uz • A + (1 - uz) • B := hZ_eq_orig

  -- Step 2: Express squared norms in terms of parameters.
  have h_norm_sq_BX : ‖B - X‖^2 = ((1-ux) * ‖B - C‖)^2 := by
    rw [hX_eq, show B - (ux • B + (1 - ux) • C) = (1 - ux) • (B - C) by { simp [smul_sub, sub_smul, one_smul] ; ring }]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg_of_le ux_le1)]
  have h_norm_sq_XC : ‖X - C‖^2 = (ux * ‖B - C‖)^2 := by
    rw [hX_eq, show (ux • B + (1 - ux) • C) - C = ux • (B - C) by { simp [smul_sub, sub_smul] ; ring }]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ux_ge0]
  have h_norm_sq_CY : ‖C - Y‖^2 = (uy * ‖A - C‖)^2 := by
    rw [hY_eq, show C - (uy • A + (1 - uy) • C) = uy • (C - A) by { simp [smul_sub, sub_smul, one_smul] ; ring }]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg uy_ge0, norm_sub_rev A C]
  have h_norm_sq_YA : ‖Y - A‖^2 = ((1-uy) * ‖A - C‖)^2 := by
    rw [hY_eq, show (uy • A + (1 - uy) • C) - A = (1 - uy) • (C - A) by { simp [smul_sub, sub_smul] ; ring }]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg_of_le uy_le1), norm_sub_rev A C]
  have h_norm_sq_AZ : ‖A - Z‖^2 = ((1-uz) * ‖A - B‖)^2 := by
    rw [hZ_eq, show A - (uz • A + (1 - uz) • B) = (1 - uz) • (A - B) by { simp [smul_sub, sub_smul, one_smul] ; ring }]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg_of_le uz_le1)]
  have h_norm_sq_ZB : ‖Z - B‖^2 = (uz * ‖A - B‖)^2 := by
    rw [hZ_eq, show (uz • A + (1 - uz) • B) - B = uz • (A - B) by { simp [smul_sub, sub_smul] ; ring }]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg uz_ge0]

  -- Substitute into the goal: ‖B-X‖² * ‖C-Y‖² * ‖A-Z‖² = ‖X-C‖² * ‖Y-A‖² * ‖Z-B‖²
  rw [h_norm_sq_BX, h_norm_sq_CY, h_norm_sq_AZ, h_norm_sq_XC, h_norm_sq_YA, h_norm_sq_ZB]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]

  -- Non-collinearity (algebraic form) implies A,B,C are distinct.
  have hA_ne_B : A ≠ B := by
    intro h_A_eq_B -- Assume A = B for contradiction
    have h_coll_if_A_eq_B : (A.1 - B.1) * (B.2 - C.2) = (A.2 - B.2) * (B.1 - C.1) := by
      rw [h_A_eq_B]; simp only [sub_self, zero_mul, mul_zero]
    exact h_noncoll_ABC_algebraic h_coll_if_A_eq_B
  have hB_ne_C : B ≠ C := by
    intro h_B_eq_C -- Assume B = C
    have h_coll_if_B_eq_C : (A.1 - B.1) * (B.2 - C.2) = (A.2 - B.2) * (B.1 - C.1) := by
      rw [h_B_eq_C]; simp only [sub_self, mul_zero, zero_mul]
    exact h_noncoll_ABC_algebraic h_coll_if_B_eq_C
  have hA_ne_C : A ≠ C := by
    intro h_A_eq_C -- Assume A = C
    have h_coll_if_A_eq_C : (A.1 - B.1) * (B.2 - C.2) = (A.2 - B.2) * (B.1 - C.1) := by
      rw [h_A_eq_C]; ring
    exact h_noncoll_ABC_algebraic h_coll_if_A_eq_C

  have h_norm_BC_sq_pos : 0 < ‖B - C‖^2 := by rw [sq_pos_iff]; exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hB_ne_C)
  have h_norm_AC_sq_pos : 0 < ‖A - C‖^2 := by rw [sq_pos_iff]; exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hA_ne_C)
  have h_norm_AB_sq_pos : 0 < ‖A - B‖^2 := by rw [sq_pos_iff]; exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hA_ne_B)

  -- Rearrange terms to group coefficients and norms for cancellation
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  -- Rearrange both sides so that norm squares are grouped together for cancellation
  have lhs_rearranged : (1 - ux) ^ 2 * ‖B - C‖ ^ 2 * uy ^ 2 * ‖A - C‖ ^ 2 * (1 - uz) ^ 2 * ‖A - B‖ ^ 2
        = ‖B - C‖^2 * ‖A - C‖^2 * ‖A - B‖^2 * ((1 - ux)^2 * uy^2 * (1 - uz)^2) := by ring

  have rhs_rearranged: ux ^ 2 * ‖B - C‖ ^ 2 * (1 - uy) ^ 2 * ‖A - C‖ ^ 2 * uz ^ 2 * ‖A - B‖ ^ 2
      = ‖B - C‖^2 * ‖A - C‖^2 * ‖A - B‖^2 * (ux^2 * (1 - uy)^2 * uz^2) := by ring

  -- Rewrite both sides to isolate the common factor
  rw [lhs_rearranged, rhs_rearranged]
  -- Cancel the common positive term
  have h_pos : 0 < ‖B - C‖^2 * ‖A - C‖^2 * ‖A - B‖^2 := by
    apply mul_pos (mul_pos h_norm_BC_sq_pos h_norm_AC_sq_pos) h_norm_AB_sq_pos
  let common := ‖B - C‖^2 * ‖A - C‖^2 * ‖A - B‖^2
  have h_common_ne_zero : common ≠ 0 := by
    apply h_pos.ne'
  have lhs : ‖B - C‖^2 * ‖A - C‖^2 * ‖A - B‖^2 * ((1 - ux)^2 * uy^2 * (1 - uz)^2)
          = common * ((1 - ux)^2 * uy^2 * (1 - uz)^2) := by rfl
  have rhs : ‖B - C‖^2 * ‖A - C‖^2 * ‖A - B‖^2 * (ux^2 * (1 - uy)^2 * uz^2)
          = common * (ux^2 * (1 - uy)^2 * uz^2) := by rfl
  rw [lhs, rhs]
  rw [mul_right_inj h_common_ne_zero] at *
  ring
  apply mul_right_cancel₀ h_pos.ne'
  ring_nf
  apply mul_right_cancel₀ h_norm_BC_sq_pos.ne'
  apply mul_right_cancel₀ h_norm_BC_sq_pos.ne'
  apply mul_right_cancel₀ h_norm_AC_sq_pos.ne'
  apply mul_right_cancel₀ h_norm_AB_sq_pos.ne'
  sorry

-- CEVA
theorem ceva {A B C X Y Z : ℝ × ℝ}
    (h₁ : ¬Collinear ℝ ({A, B, C}: Set (ℝ × ℝ)))
    (h₂ : between X B C) (h₃ : between Y C A) (h₄ : between Z A B) :
    (dist B X / dist X C) * (dist C Y / dist Y A) * (dist A Z / dist Z B) = 1 ↔
    ∃ P, between P A X ∧ between P B Y ∧ between P C Z := by
  -- Proof outline:
  -- 1. Handle degenerate cases where any two vertices coincide
  -- 2. Express X, Y, Z as convex combinations (using between_thm)
  -- 3. Calculate distance ratios algebraically
  -- 4. For (→): Solve system of equations to find P
  -- 5. For (←): Verify distances from existence of P
  -- 6. Extensive real arithmetic and vector simplification
  sorry

-- BETWEEN_SYM
theorem between_sym {u v w : ℝ × ℝ} :
    between v u w ↔ between v w u := by
  -- Proof outline:
  -- 1. Rewrite using between_thm
  -- 2. For each direction, find counterpart parameter (1 - u)
  -- 3. Verify parameter constraints and vector equality
  sorry

-- BETWEEN_METRICAL
theorem between_metrical {u v w : ℝ × ℝ} :
    between v u w ↔ dist u v + dist v w = dist u w := by
  -- Proof outline:
  -- 1. Use symmetry to handle u ↔ w
  -- 2. Rewrite using between_thm and vector expressions
  -- 3. Use triangle equality condition for collinear points
  -- 4. Handle degenerate case where u = v = w
  -- 5. Construct parameter in general case using distance ratios
  sorry
