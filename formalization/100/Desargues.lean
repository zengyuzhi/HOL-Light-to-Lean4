import Mathlib
import Aesop

open Real InnerProductSpace
open scoped RealInnerProductSpace
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
namespace Desargues
-- NORMAL_EXISTS
theorem normal_exists (u v : ℝ³) :
    ∃ (w : ℝ³), w ≠ 0 ∧ inner u w = (0 : ℝ) ∧ inner v w = (0 : ℝ) := by sorry

-- direction_tybij
def Direction := {x : ℝ³ // x ≠ 0}
def mk_dir (x : ℝ³) (h : x ≠ 0) : Direction := ⟨x, h⟩
def dest_dir (d : Direction) : ℝ³ := d.val
theorem direction_tybij :
    (∀ (x : Direction), mk_dir (dest_dir x) x.property = x) ∧
    (∀ x h, dest_dir (mk_dir x h) = x) := by sorry

-- perpdir
def perpdir (x y : Direction) : Prop := inner (dest_dir x) (dest_dir y) = (0 : ℝ)
infix:50 " _|_ " => perpdir

-- pardir
def pardir (x y : Direction) : Prop := crossProduct (dest_dir x) (dest_dir y) = 0
infix:50 " || " => pardir

-- DIRECTION_CLAUSES
theorem direction_clauses (P : ℝ³ → Prop) :
    (∀ x : Direction, P (dest_dir x)) ↔ (∀ x, x ≠ 0 → P x) ∧
    ((∃ x : Direction, P (dest_dir x)) ↔ (∃ x, x ≠ 0 ∧ P x)) := by sorry

-- PARDIR_REFL, PARDIR_SYM, PARDIR_TRANS
theorem pardir_refl (x : Direction) : x || x := by sorry
theorem pardir_sym (x y : Direction) : x || y ↔ y || x := by sorry
theorem pardir_trans (x y z : Direction) : (x || y) ∧ (y || z) → (x || z) := by sorry

-- PARDIR_EQUIV
theorem pardir_equiv (x y : Direction) :
    (∀ z, x || z ↔ y || z) ↔ x || y := by sorry

-- DIRECTION_AXIOM_1
theorem direction_axiom_1 (p p' : Direction) : ¬(p || p') →
    ∃ l, p _|_ l ∧ p' _|_ l ∧ ∀ l', p _|_ l' ∧ p' _|_ l' → l' || l := by sorry

-- DIRECTION_AXIOM_2
theorem direction_axiom_2 (l l' : Direction) : ∃ (p: Direction), p _|_ l ∧ p _|_ l' := by sorry

-- DIRECTION_AXIOM_3
theorem direction_axiom_3 : ∃ p p' p'' : Direction,
    ¬(p || p') ∧ ¬(p' || p'') ∧ ¬(p || p'') ∧
    ¬(∃ l, p _|_ l ∧ p' _|_ l ∧ p'' _|_ l) := by sorry

-- DIRECTION_AXIOM_4_WEAK
theorem direction_axiom_4_weak (l : Direction) : ∃ (p p' : Direction), ¬(p || p') ∧ (p _|_ l) ∧ (p' _|_ l) := by sorry

-- ORTHOGONAL_COMBINE
theorem orthogonal_combine (x a b : Direction) :
    a _|_ x ∧ b _|_ x ∧ ¬(a || b) →
    ∃ c, c _|_ x ∧ ¬(a || c) ∧ ¬(b || c) := by sorry

-- DIRECTION_AXIOM_4
theorem direction_axiom_4 (l : Direction) : ∃ p p' p'' : Direction,
    ¬(p || p') ∧ ¬(p' || p'') ∧ ¬(p || p'') ∧
    p _|_ l ∧ p' _|_ l ∧ p'' _|_ l := by sorry

-- Setoid instance for Direction
instance directionSetoid : Setoid Direction where
  r     := pardir
  iseqv := {
    refl  := pardir_refl
    symm  := fun {x y} hxy => (pardir_sym x y).mp hxy
    trans := fun {x y z} hxy hyz => pardir_trans x y z ⟨hxy, hyz⟩
  }

-- line_tybij
def Line := Quotient directionSetoid
def mk_line (d : Direction) : Line := Quotient.mk directionSetoid d
noncomputable def dest_line (l : Line) : {d : Direction // Quotient.mk directionSetoid d = l} := ⟨ @Quotient.out Direction directionSetoid l,
    @Quotient.out_eq Direction directionSetoid l ⟩
theorem line_tybij : (∀ x, mk_line (dest_line x).val = x) ∧
                    (∀ x, dest_line (mk_line x) = ⟨x, rfl⟩) := by sorry

-- PERPDIR_WELLDEF
theorem perpdir_welldef (x y x' y' : Direction) :
    (x || x') ∧ (y || y') → (x _|_ y ↔ x' _|_ y') := by sorry

-- perpl, perpl_th
def perpl (l l' : Line) : Prop :=
  Quotient.lift₂ (fun d d' : Direction => d _|_ d')
    (fun d1 d1_prime d2 d2_prime h_d1_equiv h_d2_equiv =>
      propext (perpdir_welldef d1 d1_prime d2 d2_prime ⟨h_d1_equiv, h_d2_equiv⟩))
    l l'
theorem perpl_th : perpl = fun l l' =>
  Quotient.lift₂ (fun d d' : Direction => d _|_ d')
    (fun a a_prime b b_prime h_a h_b =>
      propext (perpdir_welldef a a_prime b b_prime ⟨h_a, h_b⟩))
    l l' := rfl

-- line_lift_thm
theorem line_lift_thm (d₁ d₂ : Direction) :
  perpl (mk_line d₁) (mk_line d₂) ↔ (d₁ _|_ d₂) := by sorry
-- theorem line_lift_thm {P : Line → Prop}
--     (h : ∀ d : Direction, P (mk_line d))
--     (h_respects : ∀ d d' : Direction, d || d' → P (mk_line d) ↔ P (mk_line d')) :
--     ∀ l, P l := by sorry

-- LINE_AXIOM_1
theorem line_axiom_1 (p p' : Line) (h : p ≠ p') :
    ∃ (l : Line), perpl p l ∧ perpl p' l ∧ ∀ l', perpl p l' ∧ perpl p' l' → l' = l := by sorry

-- LINE_AXIOM_2
theorem line_axiom_2 (l l' : Line) : ∃ p, perpl p l ∧ perpl p l' := by sorry

-- LINE_AXIOM_3
theorem line_axiom_3 : ∃ p p' p'' : Line,
    p ≠ p' ∧ p' ≠ p'' ∧ p ≠ p'' ∧
    ¬(∃ l, perpl p l ∧ perpl p' l ∧ perpl p'' l) := by sorry

-- LINE_AXIOM_4
theorem line_axiom_4 (l : Line) : ∃ p p' p'' : Line,
    p ≠ p' ∧ p' ≠ p'' ∧ p ≠ p'' ∧
    perpl p l ∧ perpl p' l ∧ perpl p'' l := by sorry

-- point_tybij
-- def Point := Line
structure Point where
  to_line : Line
def mk_point (l : Line) : Point := Point.mk l
def dest_point (p : Point) : Line := p.to_line
theorem point_tybij : mk_point ∘ dest_point = id ∧ dest_point ∘ mk_point = id := by sorry

-- on
def on (p : Point) (l : Line) : Prop := perpl (dest_point p) l

-- POINT_CLAUSES
theorem point_clauses (P : Line → Prop) :
    (∀ p : Point, P (dest_point p)) ↔ (∀ l, P l) ∧
    ((∃ p : Point, P (dest_point p)) ↔ (∃ l, P l)) := by sorry

-- POINT_TAC
-- macro "point_tac" th:term : tactic => `(tactic| rewrite [on, point_clauses]; exact $th)

-- AXIOM_1
theorem axiom_1 (p p' : Point) : p ≠ p' →
    ∃ l, on p l ∧ on p l ∧ ∀ l', on p l' ∧ on p' l' → l' = l := by sorry

-- AXIOM_2
theorem axiom_2 (l l' : Line) : ∃ p, on p l ∧ on p l' := by sorry

-- AXIOM_3
theorem axiom_3 : ∃ p p' p'' : Point,
    p ≠ p' ∧ p' ≠ p'' ∧ p ≠ p'' ∧
    ¬(∃ l, on p l ∧ on p' l ∧ on p'' l) := by sorry

-- AXIOM_4
theorem axiom_4 (l : Line) : ∃ p p' p'' : Point,
    p ≠ p' ∧ p' ≠ p'' ∧ p ≠ p'' ∧
    on p l ∧ on p' l ∧ on p'' l := by sorry

-- projl
def projl (x : ℝ³) : Line := mk_line (mk_dir x (by sorry))

-- projp
def projp (x : ℝ³) : Point := mk_point (projl x)

-- PROJL_TOTAL
theorem projl_total (l : Line) : ∃ x, x ≠ 0 ∧ l = projl x := by sorry

-- homol
noncomputable def homol (l : Line) : ℝ³ := (projl_total l).choose

-- PROJP_TOTAL
theorem projp_total (p : Point) : ∃ (x : ℝ³), x ≠ 0 ∧ p = projp x := by sorry

-- homop_def
noncomputable def homop_def (p : Point) : ℝ³ := homol (dest_point p)

-- homop
theorem homop (p : Point) :
    homop_def p ≠ 0 ∧ p = projp (homop_def p) := by sorry

-- parallel
def parallel (x y : ℝ³) : Prop := crossProduct x y = 0

-- ON_HOMOL
theorem on_homol (p : Point) (l : Line) : on p l ↔ inner (homop_def p) (homol l) = (0: ℝ) := by sorry

-- EQ_HOMOL
theorem eq_homol (l l' : Line) : l = l' ↔ parallel (homol l) (homol l') := by sorry

-- EQ_HOMOP
theorem eq_homop (p p' : Point) : p = p' ↔ parallel (homop_def p) (homop_def p') := by sorry

-- PARALLEL_PROJL_HOMOL
theorem parallel_projl_homol (x : ℝ³) : parallel x (homol (projl x)) := by sorry

-- PARALLEL_PROJP_HOMOP
theorem parallel_projp_homop (x : ℝ³) : parallel x (homop_def (projp x)) := by sorry

-- PARALLEL_PROJP_HOMOP_EXPLICIT
theorem parallel_projp_homop_explicit (x : ℝ³) :
    x ≠ 0 → ∃ (a:ℝ), a ≠ 0 ∧ homop_def (projp x) = a • x := by sorry

-- bracket
noncomputable def bracket (p₁ p₂ p₃ : Point) : ℝ :=
    Matrix.det ![homop_def p₁, homop_def p₂, homop_def p₃]

-- COLLINEAR
def collinear (s : Set Point) : Prop := ∃ l : Line, ∀ p ∈ s, on p l

-- COLLINEAR_SINGLETON
theorem collinear_singleton (a : Point) : collinear {a} := by sorry

-- COLLINEAR_PAIR
theorem collinear_pair (a b : Point) : collinear {a, b} := by sorry

-- COLLINEAR_TRIPLE
theorem collinear_triple (a b c : Point) :
    collinear {a, b, c} ↔ ∃ l, on p l ∧ on p l ∧ on p l := by sorry

-- COLLINEAR_BRACKET
theorem collinear_bracket (p₁ p₂ p₃ : Point) :
    collinear {p₁, p₂, p₃} ↔ bracket p₁ p₂ p₃ = 0 := by sorry

-- BRACKET_SWAP, BRACKET_SHUFFLE
theorem bracket_swap (x y z : Point) :
    bracket x y z = -bracket x z y := by sorry

theorem bracket_shuffle (x y z : Point) :
    bracket x y z = bracket y z x ∧
    bracket x y z = bracket z x y := by sorry

-- BRACKET_SWAP_CONV
-- Skipped as it's a conversion tactic

-- DESARGUES_DIRECT
theorem desargues_direct
    (A' B S A P C R Q C' B' : Point)
    (h1 : ¬collinear {A', B, S})
    (h2 : ¬collinear {A, P, C})
    (h3 : ¬collinear {A, P, R})
    (h4 : ¬collinear {A, C, B})
    (h5 : ¬collinear {A, B, R})
    (h6 : ¬collinear {C', P, A'})
    (h7 : ¬collinear {C', P, B})
    (h8 : ¬collinear {C', P, B'})
    (h9 : ¬collinear {C', A', S})
    (h10 : ¬collinear {C', A', B'})
    (h11 : ¬collinear {P, C, A'})
    (h12 : ¬collinear {P, C, B})
    (h13 : ¬collinear {P, A', R})
    (h14 : ¬collinear {P, B, Q})
    (h15 : ¬collinear {P, Q, B'})
    (h16 : ¬collinear {C, B, S})
    (h17 : ¬collinear {A', Q, B'})
    (h18 : collinear {P, A', A})
    (h19 : collinear {P, B, B'})
    (h20 : collinear {P, C', C})
    (h21 : collinear {B, C, Q})
    (h22 : collinear {B', C', Q})
    (h23 : collinear {A, R, C})
    (h24 : collinear {A', C', R})
    (h25 : collinear {B, S, A})
    (h26 : collinear {A', S, B'}) :
    collinear {Q, S, R} := by sorry
