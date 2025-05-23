import Mathlib
import Aesop

open Real Complex

noncomputable section

-- rotate2d
def rotate2d (θ : ℝ) (z : ℂ) : ℂ := Complex.exp (θ * I) * z

-- reflect2d
def reflect2d (t : ℝ) (z : ℂ) : ℂ :=
  rotate2d t z * (conjAe (rotate2d (-t) z))

-- REFLECT2D_COMPOSE
theorem reflect2d_compose (s t : ℝ) :
    reflect2d s ∘ reflect2d t = fun z ↦ rotate2d (2 * (s - t)) z := by sorry
    -- [Informal Proof]
  -- The proof demonstrates that composing two reflection operations with angles $s$ and $t$ is equivalent to a rotation by $2(s-t)$:
  -- 1. We begin by expanding the definition of `reflect2d`, where $\text{reflect2d}(t) = \text{rotate2d}(t) \circ \text{cnj} \circ \text{rotate2d}(-t)$
  -- 2. We rewrite the composition into its complex number representation:
  --    - $\text{rotate2d}(θ)$ corresponds to multiplication by $e^{iθ}$ in the complex plane
  --    - $\text{cnj}$ is the complex conjugate operation
  -- 3. We simplify using properties of complex conjugation:
  --    - $\overline{\overline{z}} = z$
  --    - $\overline{e^{it}} = e^{-it}$
  --    - $\overline{z_1 \cdot z_2} = \overline{z_1} \cdot \overline{z_2}$
  --    - $\overline{i} = -i$
  -- 4. Through algebraic manipulation of exponentials, we arrive at:
  --    $$\text{reflect2d}(s) \circ \text{reflect2d}(t) = \text{multiplication by } e^{i \cdot 2(s-t)}$$
  -- 5. Since multiplication by $e^{i \cdot 2(s-t)}$ is exactly the action of $\text{rotate2d}(2(s-t))$, the theorem is proven.

-- rotate_about
def rotate_about (a : ℂ) (t : ℝ) (x : ℂ) : ℂ := a + rotate2d t (x - a)

-- reflect_across
noncomputable def reflect_across (a b : ℂ) (x : ℂ) : ℂ := a + reflect2d (Complex.arg (b - a)) (x - a)

-- Theorem REFLECT_ACROSS_COMPOSE
theorem reflect_across_compose (a b c : ℂ) (h₁ : b ≠ a) (h₂ : c ≠ a) :
  reflect_across a b ∘ reflect_across a c = rotate_about a (2 * Complex.arg ((b - a) / (c - a))) := by
    funext x
    have h₃ : b - a ≠ 0 := by
      intro h
      apply h₁
      simp [sub_eq_zero] at h ⊢
      <;> simp_all
    have h₄ : c - a ≠ 0 := by
      intro h
      apply h₂
      simp [sub_eq_zero] at h ⊢
      <;> simp_all
    sorry

-- Theorem REFLECT_ACROSS_COMPOSE_ANGLE
theorem reflect_across_compose_angle (a b c : ℂ)
    (h₁ : b ≠ a) (h₂ : c ≠ a)
    (h₃ : 0 ≤ ((c - a) / (b - a)).im) :
    reflect_across a c ∘ reflect_across a b =
      rotate_about a (2 * Complex.arg ((c - a) / (b - a))):= by
    have h₄ : reflect_across a b ∘ reflect_across a c = rotate_about a (2 * Complex.arg ((b - a) / (c - a))) := by{sorry}
    have h₅ : reflect_across a c ∘ reflect_across a b = rotate_about a (2 * Complex.arg ((c - a) / (b - a))) := by
      have h₆ : Complex.arg ((b - a) / (c - a)) = -Complex.arg ((c - a) / (b - a)) := by
        have h₇ : (b - a) / (c - a) = ((c - a) / (b - a))⁻¹ := by
          field_simp [sub_ne_zero.mpr h₁, sub_ne_zero.mpr h₂]
          <;> ring_nf
          <;> field_simp [sub_ne_zero.mpr h₁, sub_ne_zero.mpr h₂]
          <;> ring_nf
        rw [h₇]
        rw [Complex.arg_inv]
        <;> sorry  -- Failed simp and linarith tactics
      have h₇ : reflect_across a c ∘ reflect_across a b = reflect_across a b ∘ reflect_across a c := by
        sorry  -- Failed ext and simp tactics
      rw [h₇]
      rw [h₄]
      rw [show (2 : ℝ) * Complex.arg ((b - a) / (c - a)) = (2 : ℝ) * (-Complex.arg ((c - a) / (b - a))) by rw [h₆]]
      <;> simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
      <;> ring_nf
      <;> norm_num
      <;> try linarith
      <;> try nlinarith
      sorry
    exact h₅


-- REFLECT_ACROSS_COMPOSE_INVOLUTION
theorem reflect_across_compose_involution (a b : ℂ) (h : a ≠ b) :
  reflect_across a b ∘ reflect_across a b = id := by
  -- Use the compositional property of reflections to express the composition
  have h₁ : reflect_across a b ∘ reflect_across a b = rotate_about a (2 * Complex.arg ((b - a) / (b - a))) := sorry

  rw [h₁]
  -- Simplify the angle of rotation
  have h₂ : (b - a : ℂ) / (b - a) = 1 := by
    sorry
  have h₃ : Complex.arg ((b - a : ℂ) / (b - a)) = 0 := by
    rw [h₂]
    simp [Complex.arg_one]
  have h₄ : rotate_about a (2 * Complex.arg ((b - a : ℂ) / (b - a))) = rotate_about a 0 := by
    rw [h₃]
    <;> simp [Complex.arg_one]
    <;> ring
  rw [h₄]
  -- Prove that a rotation by angle 0 is the identity
  have h₅ : (rotate_about a 0 : ℂ → ℂ) = id := sorry
  rw [h₅]
  <;> rfl

-- REFLECT_ACROSS_SYM
theorem reflect_across_sym (a b : ℂ) : reflect_across a b = reflect_across b a := by
  by_cases h : a = b
  · -- Case: a = b
    subst_vars
    simp [reflect_across]
  · -- Case: a ≠ b
    sorry  -- [Informal Proof] Algebraic manipulation with complex numbers fails due to complexity

-- ITER_ROTATE_ABOUT
theorem iter_rotate_about (n : ℕ) (a : ℂ) (t : ℝ) :
  (rotate_about a t)^[n] = rotate_about a (n * t) := by sorry

-- REAL_LE_IM_DIV_CYCLIC
theorem real_le_im_div_cyclic (a b c : ℂ) :
  (0 ≤ ((c - a) / (b - a)).im) ↔ (0 ≤ ((a - b) / (c - b)).im) := by
  constructor
  · -- Prove the forward direction: 0 ≤ Im((c - a)/(b - a)) → 0 ≤ Im((a - b)/(c - b))
    intro h
    -- Use the imaginary part of the division formula to rewrite the inequality
    have h₁ : 0 ≤ ((a - b) / (c - b)).im := by sorry
    exact h₁
  · -- Prove the reverse direction: 0 ≤ Im((a - b)/(c - b)) → 0 ≤ Im((c - a)/(b - a))
    intro h
    -- Use the imaginary part of the division formula to rewrite the inequality
    have h₁ : 0 ≤ ((c - a) / (b - a)).im := by sorry
    exact h₁

-- ROTATE_ABOUT_INVERT
theorem rotate_about_invert (a : ℂ) (t : ℝ) (w z : ℂ) :
  rotate_about a t w = z ↔ w = rotate_about a (-t) z := by
  apply Iff.intro
  · -- Prove the forward direction: rotate_about a t w = z → w = rotate_about a (-t) z
    intro h
    have h₁ : w = rotate_about a (-t) z := by
      have h₂ : rotate_about a t w = z := h
      calc
        w = rotate_about a (-t) (rotate_about a t w) := by
          -- Prove that rotate_about a (-t) (rotate_about a t w) = w
          sorry
        _ = rotate_about a (-t) z := by rw [h₂]
    exact h₁
  · -- Prove the backward direction: w = rotate_about a (-t) z → rotate_about a t w = z
    intro h
    have h₁ : rotate_about a t w = z := by
      have h₂ : w = rotate_about a (-t) z := h
      calc
        rotate_about a t w = rotate_about a t (rotate_about a (-t) z) := by rw [h₂]
        _ = z := by
          -- Prove that rotate_about a t (rotate_about a (-t) z) = z
          sorry
    exact h₁

-- ROTATE_EQ_REFLECT_LEMMA
theorem rotate_eq_reflect_lemma (a b z : ℂ) (t : ℝ)
  (h₁ : b ≠ a) (h₂ : 2 * Complex.arg ((b - a) / (z - a)) = t) :
  rotate_about a t z = reflect_across a b z := by
  have h₃ : rotate_about a t z = reflect_across a b z := by
    -- Expand definitions to show that rotating is equivalent to reflecting
    rw [rotate_about, reflect_across]
    -- Introduce a helper lemma to manage the algebraic manipulations
    have h₄ : Complex.exp (t * Complex.I) * (z - a) = Complex.exp (Complex.arg (b - a) * Complex.I) * (Complex.conjAe (Complex.exp (-Complex.arg (b - a) * Complex.I) * (z - a))) := by
      sorry
    -- Use the simplified equation to conclude the proof
    have h₈ : Complex.exp (t * Complex.I) * (z - a) = Complex.exp (Complex.arg (b - a) * Complex.I) * (Complex.conjAe (Complex.exp (-Complex.arg (b - a) * Complex.I) * (z - a))) := by
      exact h₄
    calc
      a + Complex.exp (t * Complex.I) * (z - a) = a + (Complex.exp (Complex.arg (b - a) * Complex.I) * (Complex.conjAe (Complex.exp (-Complex.arg (b - a) * Complex.I) * (z - a)))) := by rw [h₈]
      _ = a + Complex.exp (Complex.arg (b - a) * Complex.I) * (Complex.conjAe (Complex.exp (-Complex.arg (b - a) * Complex.I) * (z - a))) := by simp [add_assoc]
    sorry
  -- Conclude the proof
  exact h₃

-- ROTATE_EQ_REFLECT_PI_LEMMA
theorem rotate_eq_reflect_pi_lemma (a b z : ℂ) (t : ℝ)
  (h₁ : b ≠ a) (h₂ : 2 * Complex.arg ((b - a) / (z - a)) = 4 * Real.pi + t) :
  rotate_about a t z = reflect_across a b z := by
  have h₃ : t = 2 * Complex.arg ((b - a) / (z - a)) - 4 * Real.pi := by
    linarith
  rw [h₃]
  -- Expand the definition of `rotate_about` (for t = -4π )
  have h₄ : rotate_about a (2 * Complex.arg ((b - a) / (z - a)) - 4 * Real.pi) z = rotate_about a (2 * Complex.arg ((b - a) / (z - a))) z := sorry
  -- [Informal Proof] Show rotation by theta-4π is same as rotation by theta since 4π is two full rotations
  rw [h₄]
  -- Apply ROTATE_EQ_REFLECT_LEMMA
  have h₅ : rotate_about a (2 * Complex.arg ((b - a) / (z - a))) z = reflect_across a b z := sorry
  -- [Informal Proof] Apply the previously established lemma connecting rotation and reflection
  rw [h₅]

-- EQUILATERAL_TRIANGLE_ALGEBRAIC
theorem equilateral_triangle_algebraic (A B C j : ℂ)
  (h₁ : j^3 = 1) (h₂ : j ≠ 1)
  (h₃ : A + j * B + j^2 * C = 0) :
  dist A B = dist B C ∧ dist C A = dist B C := by sorry

-- AFFINE_GROUP_ITER_3
theorem affine_group_iter_3 (a b : ℂ) :
  (fun z ↦ a * z + b)^[3] = (fun z ↦ a^3 * z + b * (1 + a + a^2)) := by
  have h₀ : ∀ z : ℂ, (fun (z : ℂ) ↦ a * z + b)^[3] z = a ^ 3 * z + b * (1 + a + a ^ 2) := by
    sorry
  funext z
  apply h₀

-- AFFINE_GROUP_COMPOSE
theorem affine_group_compose (a₁ b₁ a₂ b₂ : ℂ) :
  (fun z ↦ a₁ * z + b₁) ∘ (fun z ↦ a₂ * z + b₂) =
  (fun z ↦ (a₁ * a₂) * z + (b₁ + a₁ * b₂)) := by
  ext z
  simp [Function.comp_apply]
  <;> ring
  <;> simp_all [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  <;> ring_nf
  <;> simp_all [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  <;> linarith

-- AFFINE_GROUP_I
theorem affine_group_I :
  id = (fun (z:ℂ) ↦ 1 * z + 0) := by sorry
  -- [Informal Proof]
  -- The identity function is equal to the affine transformation z ↦ 1*z + 0
  -- This can be proven by function extensionality and simple arithmetic
  -- simplification showing that 1*z + 0 = z for all complex z

-- AFFINE_GROUP_EQ
theorem affine_group_eq (a b a' b' : ℂ) :
  (fun z ↦ a * z + b) = (fun z ↦ a' * z + b') ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have h₁ : a = a' := by
      -- [Informal Proof] To prove a = a', we evaluate the functions at z = 1 and simplify
      sorry
    have h₂ : b = b' := by
      -- [Informal Proof] To prove b = b', we evaluate the functions at z = 0 and simplify
      sorry
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩
    -- [Informal Proof] Direct substitution when a = a' and b = b'
    rfl

-- AFFINE_GROUP_ROTATE_ABOUT
theorem affine_group_rotate_about (a : ℂ) (t : ℝ) :
  rotate_about a t = (fun z ↦ Complex.exp (t * I) * z + (1 - Complex.exp (t * I)) * a) := by
  funext z
  -- Expand the definition of `rotate_about`
  have h₁ : rotate_about a t z = a + rotate2d t (z - a) := by
    sorry
  rw [h₁]
  -- Use the fact that `rotate2d t` can be expressed in complex form as multiplication by `e^{it}`
  have h₂ : rotate2d t (z - a) = Complex.exp (t * I) * (z - a) := by
    sorry
  rw [h₂]
  -- Simplify the resulting expression using complex ring arithmetic
  sorry


-- ALGEBRAIC_LEMMA
theorem algebraic_lemma (a₁ a₂ a₃ b₁ b₂ b₃ A B C : ℂ)
  (h₁ : (fun z ↦ a₃ * z + b₃) ((fun z ↦ a₁ * z + b₁) B) = B)
  (h₂ : (fun z ↦ a₁ * z + b₁) ((fun z ↦ a₂ * z + b₂) C) = C)
  (h₃ : (fun z ↦ a₂ * z + b₂) ((fun z ↦ a₃ * z + b₃) A) = A)
  (h₄ : (fun z ↦ a₁ * z + b₁)^[3] ∘ (fun z ↦ a₂ * z + b₂)^[3] ∘ (fun z ↦ a₃ * z + b₃)^[3] = id)
  (h₅ : a₁ * a₂ * a₃ ≠ 1)
  (h₆ : a₁ * a₂ ≠ 1)
  (h₇ : a₂ * a₃ ≠ 1)
  (h₈ : a₃ * a₁ ≠ 1) :
  (a₁ * a₂ * a₃)^3 = 1 ∧ a₁ * a₂ * a₃ ≠ 1 ∧
  C + (a₁ * a₂ * a₃) * A + (a₁ * a₂ * a₃)^2 * B = 0 := by
  have h₉ : (a₁ * a₂ * a₃) ^ 3 = 1 := sorry -- [Informal Proof] This follows from the composition condition h₄ by complex algebra
  have h₁₀ : a₁ * a₂ * a₃ ≠ 1 := h₅
  have h₁₁ : C + (a₁ * a₂ * a₃) * A + (a₁ * a₂ * a₃) ^ 2 * B = 0 := by
    have h₁₁₁ : (a₁ * a₂ * a₃) * a₁ ^ 2 * a₂ * (a₁ - a₁ * a₂ * a₃) * (a₂ - a₁ * a₂ * a₃) * (a₃ - a₁ * a₂ * a₃) * (C + (a₁ * a₂ * a₃) * A + (a₁ * a₂ * a₃) ^ 2 * B) = 0 := sorry -- [Informal Proof] Derived from fixed point equations and field arithmetic
    have h₁₁₂ : (a₁ * a₂ * a₃) * a₁ ^ 2 * a₂ * (a₁ - a₁ * a₂ * a₃) * (a₂ - a₁ * a₂ * a₃) * (a₃ - a₁ * a₂ * a₃) ≠ 0 := sorry -- [Informal Proof] Non-zero by assumption h₅ and field properties
    sorry
  exact ⟨h₉, h₁₀, h₁₁⟩

noncomputable def angle (a b c : ℂ) : ℝ :=
  Complex.arg ((c - b) / (a - b))

-- MORLEY
theorem morley (A B C P Q R : ℂ)
  (h_noncol : ¬ Collinear ℂ ({A, B, C} : Set ℂ))
  (h_conv : {P, Q, R} ⊆ convexHull ℝ ({A, B, C} : Set ℂ))
  (h_angles₁ : angle A B R = angle A B C / 3)
  (h_angles₂ : angle B A R = angle B A C / 3)
  (h_angles₃ : angle B C P = angle B C A / 3)
  (h_angles₄ : angle C B P = angle C B A / 3)
  (h_angles₅ : angle C A Q = angle C A B / 3)
  (h_angles₆ : angle A C Q = angle A C B / 3) :
  dist R P = dist P Q ∧ dist Q R = dist P Q := by sorry
