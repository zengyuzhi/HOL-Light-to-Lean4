# morley.ml

## Overview

Number of statements: 22

`morley.ml` formalizes Alain Connes's proof of Morley's theorem. It relies on the `iter.ml` and `geom.ml` files from the HOL Light library. The file aims to provide a formal verification of this geometric theorem within the HOL Light system.


## reflect2d

### Name of formal statement
reflect2d

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let reflect2d = new_definition
 `reflect2d t = rotate2d t o cnj o rotate2d(--t)`;;
```

### Informal statement
The function `reflect2d` of *t* is defined as the composition of `rotate2d` applied to the negation of *t*, followed by `cnj`, followed by `rotate2d` applied to *t*.

### Informal sketch
- The definition of `reflect2d` specifies how to reflect a point in the complex plane about the line that passes through the origin and makes the angle *t* with the real axis.
- The `rotate2d` function rotates a point by an angle.
- The `cnj` function takes the complex conjugate of a point.
- The composition `o` means function composition. `f o g` is the function that first applies `g` and then applies `f`.
- `reflect2d t` is the reflection about the line through the origin with angle *t*. It's achieved by:
    - Rotating by -*t* so the reflection line is the real axis (`rotate2d(--t)`).
    - Taking the complex conjugate (`cnj`).
    - Rotating back by *t* (`rotate2d(t)`).

### Mathematical insight
The reflection about a line through the origin can be expressed as a rotation to the real axis, conjugation, and rotation back. This definition leverages existing functions for rotation and conjugation to provide a concise definition of reflection, corresponding to a coordinate change into a frame where the mirroring line corresponds to the real axis where the reflection operation `cnj` is easily expressible.

### Dependencies
- `rotate2d`
- `cnj`


---

## REFLECT2D_COMPOSE

### Name of formal statement
REFLECT2D_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REFLECT2D_COMPOSE = prove
 (`!s t. reflect2d s o reflect2d t = rotate2d (&2 * (s - t))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; reflect2d] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ROTATE2D_COMPLEX; CNJ_CEXP; CNJ_MUL; CNJ_CNJ] THEN
  REWRITE_TAC[CNJ_II; CNJ_CX; CNJ_NEG; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CEXP_ADD] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; CX_MUL] THEN
  AP_TERM_TAC THEN SIMPLE_COMPLEX_ARITH_TAC);;
```

### Informal statement
For all real numbers `s` and `t`, the composition of `reflect2d s` and `reflect2d t` is equal to `rotate2d (&2 * (s - t))`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the left-hand side `reflect2d s o reflect2d t` using the definitions of `FUN_EQ_THM`, `o_THM`, and `reflect2d`.
- Apply generalization repeatedly to remove quantifiers.
- Rewrite using `ROTATE2D_COMPLEX`, `CNJ_CEXP`, `CNJ_MUL`, and `CNJ_CNJ` to express the rotations and reflections in terms of complex exponentials and conjugation.
- Rewrite using `CNJ_II`, `CNJ_CX`, `CNJ_NEG`, and `COMPLEX_MUL_ASSOC` to simplify the complex expressions.
- Apply the theorems resulting from the applications of `AP_THM_TAC` and `AP_TERM_TAC`.
- Rewrite using `GSYM CEXP_ADD`.
- Rewrite using `CX_NEG`, `COMPLEX_MUL_LNEG`, `COMPLEX_MUL_RNEG`, and `CX_MUL`.
- Apply the theorem resulting from the application of `AP_TERM_TAC`.
- Use `SIMPLE_COMPLEX_ARITH_TAC` to complete the arithmetic simplification.

### Mathematical insight
This theorem shows how two reflections in 2D space combine to form a rotation. Specifically, reflecting about line `s` (through origin) and then line `t` (through origin) equals to rotating by twice the angle between `s` and `t.`

### Dependencies
- `FUN_EQ_THM`
- `o_THM`
- `reflect2d`
- `ROTATE2D_COMPLEX`
- `CNJ_CEXP`
- `CNJ_MUL`
- `CNJ_CNJ`
- `CNJ_II`
- `CNJ_CX`
- `CNJ_NEG`
- `COMPLEX_MUL_ASSOC`
- `GSYM CEXP_ADD`
- `CX_NEG`
- `COMPLEX_MUL_LNEG`
- `COMPLEX_MUL_RNEG`
- `CX_MUL`


---

## rotate_about

### Name of formal statement
rotate_about

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rotate_about = new_definition
 `rotate_about a t x = a + rotate2d t (x - a)`;;
```

### Informal statement
The function `rotate_about` is defined such that for any point `a` (of type `:real^2`), any angle `t` (of type `:real`), and any point `x` (of type `:real^2`), `rotate_about a t x` is equal to `a` plus the result of rotating the vector `x - a` by the angle `t` using the `rotate2d` function.

### Informal sketch
The definition introduces `rotate_about` explicitly in terms of vector subtraction, rotation by `rotate2d`, and vector addition. No proof is required since it is a definition.
The definition expresses the rotation of a point `x` around a center `a` through an angle `t` by first translating `x` so that `a` is at the origin (`x - a`), then rotating by angle `t` using `rotate2d`, and finally translating back by adding `a`.

### Mathematical insight
This definition provides a convenient way to express rotation around an arbitrary point in the 2D plane. It decomposes the rotation into translation to the origin, rotation around the origin, and translation back. This approach allows the use of the simpler `rotate2d` that only deals with rotations about the origin. This is a standard technique in linear algebra.

### Dependencies
- Definition: `rotate2d`


---

## reflect_across

### Name of formal statement
reflect_across

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let reflect_across = new_definition
 `reflect_across (a,b) x = a + reflect2d (Arg(b - a)) (x - a)`;;
```

### Informal statement
The reflection of a point `x` across the line defined by points `a` and `b` is defined as `a` plus the reflection of `x - a` by twice the argument of `b - a`. Here, `reflect2d` signifies the reflection of a 2D vector, and `Arg` denotes the principal argument of a complex number.

### Informal sketch
The definition `reflect_across (a,b) x` represents a geometric transformation: reflection of the point `x` across the line passing through `a` and `b`.
-   The vector from `a` to `x` is computed as `x - a`.
-   The angle of the line defined by `a` and `b` relative to the x-axis is given by `Arg (b - a)`.
-   The rotation of `x-a` by twice the angle is done with `reflect2d (Arg(b - a)) (x - a)`.
-   Finally, we translate back by adding `a`.

### Mathematical insight
This definition leverages complex number representation for planar geometry. The argument of a complex number (here, `b - a`) represents the angle of the vector from the origin to that number. Multiplying by `2` accounts for the fact that a reflection involves twice the angle from the line of reflection to the point being reflected. The overall reflection is then achieved via translation by `-a`, a rotation using `reflect2d` and finally translation back by `a`. The use of complex numbers as vectors greatly simplifies the representation and the associated calculations.

### Dependencies
Complex analysis and vector functions in 2D space. Specifically `Arg` (argument) and `reflect2d` are needed


---

## REFLECT_ACROSS_COMPOSE

### Name of formal statement
REFLECT_ACROSS_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_COMPOSE = prove
 (`!a b c.
        ~(b = a) /\ ~(c = a)
        ==> reflect_across(a,b) o reflect_across(a,c) =
            rotate_about a (&2 * Arg((b - a) / (c - a)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[reflect_across; FUN_EQ_THM; o_THM; rotate_about] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM] REFLECT2D_COMPOSE] THEN
  X_GEN_TAC `x:complex` THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_2; ROTATE2D_ADD] THEN
  ASM_SIMP_TAC[ROTATE2D_SUB_ARG; COMPLEX_SUB_0]);;
```

### Informal statement
For all complex numbers `a`, `b`, and `c`, if `b` is not equal to `a` and `c` is not equal to `a`, then the composition of the reflection across the line through `a` and `b` followed by the reflection across the line through `a` and `c` is equal to the rotation about `a` by an angle of `2 * Arg((b - a) / (c - a))`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and implications.
- Rewrite using the definitions of `reflect_across`, function composition (`o`), `FUN_EQ_THM`, and `rotate_about`.
- Rewrite using vector arithmetic simplification `(a + x) - a = x`.
- Apply `REFLECT2D_COMPOSE` after applying equation rewriting using `FUN_EQ_THM` and the composition operator `o_THM`.
- Generalize an arbitrary complex number `x`.
- Apply the argument of the function equality.
- Rewrite using `REAL_MUL_2` and `ROTATE2D_ADD`.
- Simplify using assumptions and the definitions of `ROTATE2D_SUB_ARG` and `COMPLEX_SUB_0`.

### Mathematical insight
This theorem describes the geometric principle that the composition of two reflections across lines intersecting at a point is equivalent to a rotation about that point by twice the angle between the lines.
The angle between the lines through `a` and `b` and through `a` and `c` is given by `Arg((b - a) / (c - a))`.

### Dependencies
- `reflect_across`
- `FUN_EQ_THM`
- `o_THM`
- `rotate_about`
- `VECTOR_ARITH`
- `REFLECT2D_COMPOSE`
- `REAL_MUL_2`
- `ROTATE2D_ADD`
- `ROTATE2D_SUB_ARG`
- `COMPLEX_SUB_0`


---

## REFLECT_ACROSS_COMPOSE_ANGLE

### Name of formal statement
REFLECT_ACROSS_COMPOSE_ANGLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_COMPOSE_ANGLE = prove
 (`!a b c.
        ~(b = a) /\ ~(c = a) /\ &0 <= Im((c - a) / (b - a))
        ==> reflect_across(a,c) o reflect_across(a,b) =
            rotate_about a (&2 * angle(c,a,b))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ANGLE_SYM] THEN
  ASM_SIMP_TAC[REFLECT_ACROSS_COMPOSE] THEN
  ASM_SIMP_TAC[angle; VECTOR_ANGLE_ARG; COMPLEX_SUB_0;
               REAL_SUB_ARG; ARG_LE_PI]);;
```
### Informal statement
For all complex numbers `a`, `b`, and `c`, if `b` is not equal to `a`, and `c` is not equal to `a`, and the imaginary part of `(c - a) / (b - a)` is greater than or equal to 0, then the composition of the reflection across the line through `a` and `c` with the reflection across the line through `a` and `b` is equal to the rotation about `a` by an angle of `2 * angle(c,a,b)`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the assumptions and goal.
- Rewrite using the symmetry of the `angle` function (`ANGLE_SYM`).
- Simplify using the theorem for the composition of reflections (`REFLECT_ACROSS_COMPOSE`).
- Simplify using the definition of `angle` and properties of complex numbers, including the argument of a complex number (`angle`; `VECTOR_ANGLE_ARG`; `COMPLEX_SUB_0`; `REAL_SUB_ARG`; `ARG_LE_PI`).

### Mathematical insight
This theorem states that the composition of two reflections about intersecting lines is a rotation. Specifically, it shows that reflecting across the line from `a` to `b`, and then reflecting across the line from `a` to `c` is equivalent to rotating about the point `a` by twice the angle between the lines `ab` and `ac`. The premise `&0 <= Im((c - a) / (b - a))` is equivalent to the angle from `a` to `b` to `c` being non-negative, which is a necessary condition for `angle` to be well-defined.

### Dependencies
- `ANGLE_SYM`
- `REFLECT_ACROSS_COMPOSE`
- `angle`
- `VECTOR_ANGLE_ARG`
- `COMPLEX_SUB_0`
- `REAL_SUB_ARG`
- `ARG_LE_PI`


---

## REFLECT_ACROSS_COMPOSE_INVOLUTION

### Name of formal statement
REFLECT_ACROSS_COMPOSE_INVOLUTION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_COMPOSE_INVOLUTION = prove
 (`!a b. ~(a = b) ==> reflect_across(a,b) o reflect_across(a,b) = I`,
  SIMP_TAC[REFLECT_ACROSS_COMPOSE; COMPLEX_DIV_REFL; COMPLEX_SUB_0] THEN
  REWRITE_TAC[ARG_NUM; REAL_MUL_RZERO; rotate_about; FUN_EQ_THM] THEN
  REWRITE_TAC[ROTATE2D_ZERO; I_THM] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;
```
### Informal statement
For all complex numbers `a` and `b`, if `a` is not equal to `b`, then the composition of the reflection across the line defined by `a` and `b` with itself is equal to the identity function `I`.

### Informal sketch
The proof demonstrates that reflecting a complex number across a line, and then reflecting the result across the same line again, results in the original complex number. This means the transformation is an involution.

*   The proof starts by simplifying the expression `reflect_across(a, b) o reflect_across(a, b)` using the definition of `REFLECT_ACROSS_COMPOSE`, `COMPLEX_DIV_REFL` and `COMPLEX_SUB_0`.
*   The argument of the resulting function, application to `ARG_NUM`, and the definition of `REAL_MUL_RZERO` and `rotate_about` are rewritten, as well as the function equality `FUN_EQ_THM`.
*   The simplifications continue by using the definition of `ROTATE2D_ZERO` and `I_THM`.
*   Finally, the remaining terms are stripped and simplified using vector arithmetic.

### Mathematical insight
The theorem `REFLECT_ACROSS_COMPOSE_INVOLUTION` states that a reflection is an involution, i.e., applying it twice yields the identity. This is a fundamental property of reflections in geometry. The condition `~(a = b)` ensures that the line of reflection is well-defined.

### Dependencies
*   Definitions: `REFLECT_ACROSS_COMPOSE`
*   Theorems: `COMPLEX_DIV_REFL`, `COMPLEX_SUB_0`, `ARG_NUM`, `REAL_MUL_RZERO`, `rotate_about`, `FUN_EQ_THM`, `ROTATE2D_ZERO`, `I_THM`


---

## REFLECT_ACROSS_SYM

### Name of formal statement
REFLECT_ACROSS_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_SYM = prove
 (`!a b. reflect_across(a,b) = reflect_across(b,a)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a:complex = b` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; reflect_across; reflect2d; o_THM] THEN
  REWRITE_TAC[ROTATE2D_COMPLEX; CNJ_CEXP; CNJ_MUL; CNJ_CX; CNJ_II] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_RING `--ii * --z = ii * z`] THEN
  SUBGOAL_THEN `cexp(ii * Cx(Arg(b - a))) = (b - a) / Cx(norm(b - a)) /\
                cexp(ii * Cx(Arg(a - b))) = (a - b) / Cx(norm(a - b))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(COMPLEX_FIELD
     `~(a = Cx(&0)) /\ a * b = c ==> b = c / a`) THEN
    ASM_REWRITE_TAC[GSYM ARG; CX_INJ; NORM_EQ_0; VECTOR_SUB_EQ];
    REWRITE_TAC[COMPLEX_RING `a * a * cnj b = a pow 2 * cnj b`] THEN
    SUBST1_TAC(ISPECL [`a:complex`; `b:complex`] NORM_SUB) THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[complex_div] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `b - a = ((b - a) * n) pow 2 * (cnj za - cnj zb)
      ==> a + ((b - a) * n) pow 2 * cnj za =
          b + ((a - b) * n) pow 2 * cnj zb`) THEN
    REWRITE_TAC[CNJ_SUB; COMPLEX_RING `(z - a) - (z - b):complex = b - a`] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `(b' - a') * (b - a) = n pow 2 /\ ~(n = Cx(&0))
      ==> b - a = ((b - a) * inv n) pow 2 * (b' - a')`) THEN
    REWRITE_TAC[GSYM CNJ_SUB; COMPLEX_MUL_CNJ; CX_INJ] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_ZERO; COMPLEX_SUB_0]]);;
```

### Informal statement
For all complex numbers `a` and `b`, `reflect_across(a, b)` is equal to `reflect_across(b, a)`.

### Informal sketch
The proof demonstrates the symmetry of the `reflect_across` function with respect to its two point arguments.

- The proof starts by generalizing over arbitrary complex numbers `a` and `b`.
- Case split on whether or not `a` equals `b`.
  - If `a` equals `b`, the goal is proven by simplification (since `reflect_across(a,a)` = `reflect_across(a,a)`).
- Otherwise, the definition of `reflect_across` is expanded using `FUN_EQ_THM`, `reflect_across`, `reflect2d`, and `o_THM`.
- Several rewrite steps are applied to simplify the expression using `ROTATE2D_COMPLEX`, `CNJ_CEXP`, `CNJ_MUL`, `CNJ_CX`, `CNJ_II`, `CX_NEG`, and the ring property `--ii * --z = ii * z`.
- A key subgoal introduces the identities relating complex exponentials to normalized differences:
  `cexp(ii * Cx(Arg(b - a))) = (b - a) / Cx(norm(b - a))` and `cexp(ii * Cx(Arg(a - b))) = (a - b) / Cx(norm(a - b))`.
- Use `COMPLEX_FIELD` to introduce `~(a = Cx(&0)) /\ a * b = c ==> b = c / a` and then rewrite with `GSYM ARG`, `CX_INJ`, `NORM_EQ_0`, `VECTOR_SUB_EQ`.
- Further simplification using properties of complex numbers is performed.
- Use `NORM_SUB` with specialization introducing arbitrary complex number `z`. Rewrite with `complex_div`.
- Key step using `COMPLEX_RING`.
- Rewrite using properties of conjugation and apply another `COMPLEX_FIELD` theorem.
- Final simplifications using properties of complex conjugates and subtraction.

### Mathematical insight
The theorem `REFLECT_ACROSS_SYM` states that reflecting a point across the line defined by two other points is symmetric with respect to the defining points. Swapping these two points still defines the same line, and the reflection is thus the same. The proof involves expanding the definition of `reflect_across` in terms of complex exponentials and arguments and then using properties of complex arithmetic to show that the expression is symmetric.

### Dependencies
#### Theorems
- `FUN_EQ_THM`
- `ROTATE2D_COMPLEX`
- `CNJ_CEXP`
- `CNJ_MUL`
- `CNJ_CX`
- `CNJ_II`
- `CX_NEG`
- `COMPLEX_FIELD`
- `COMPLEX_RING`
- `COMPLEX_NORM_ZERO`

#### Definitions
- `reflect_across`
- `reflect2d`
- `o_THM`
- `ARG`
- `CX_INJ`
- `NORM_EQ_0`
- `VECTOR_SUB_EQ`
- `NORM_SUB`
- `complex_div`
- `CNJ_SUB`
- `COMPLEX_MUL_CNJ`
- `COMPLEX_SUB_0`


---

## ITER_ROTATE_ABOUT

### Name of formal statement
ITER_ROTATE_ABOUT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ITER_ROTATE_ABOUT = prove
 (`!n a t. ITER n (rotate_about a t) = rotate_about a (&n * t)`,
  REWRITE_TAC[FUN_EQ_THM; rotate_about] THEN
  REWRITE_TAC[VECTOR_ARITH `a + b:real^N = a + c <=> b = c`] THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER_ALT; REAL_MUL_LZERO; ROTATE2D_ZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x - a:real^N = x`; GSYM REAL_OF_NUM_SUC] THEN
  ASM_REWRITE_TAC[REAL_ADD_RDISTRIB; ROTATE2D_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[rotate_about; REAL_MUL_LID] THEN VECTOR_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, real numbers `t`, and vectors `a` in `real^N`, applying the `rotate_about a t` transformation `n` times is equivalent to applying the `rotate_about a (&n * t)` transformation once.

### Informal sketch
The proof proceeds by induction on `n`.
- The base case `n = 0` follows from the definition of `ITER 0 f = ID` and `ROTATE2D_ZERO` which states that `rotate_about a 0 = ID`.
- For the inductive step, assume that `ITER n (rotate_about a t) = rotate_about a (&n * t)`. Then, we must show that `ITER (SUC n) (rotate_about a t) = rotate_about a (&(SUC n) * t)`.
- Using the definition of `ITER`, we have `ITER (SUC n) (rotate_about a t) = rotate_about a t o ITER n (rotate_about a t)`.
- By the inductive hypothesis, this becomes `rotate_about a t o rotate_about a (&n * t)`.
- Applying `ROTATE2D_ADD` and some arithmetic simplification leads to `rotate_about a (&(SUC n) * t)`.

The proof uses rewriting with various lemmas and arithmetic simplification.

### Mathematical insight
This theorem demonstrates how repeated rotations about a point can be simplified into a single rotation by scaling the angle. This is a fundamental property of rotations and is essential for various geometric and algebraic manipulations. It connects the iterative application of a transformation with a direct computation of the equivalent transformation.

### Dependencies
- `FUN_EQ_THM`
- `rotate_about`
- `VECTOR_ARITH`
- `ITER_ALT`
- `REAL_MUL_LZERO`
- `ROTATE2D_ZERO`
- `REAL_OF_NUM_SUC`
- `REAL_ADD_RDISTRIB`
- `ROTATE2D_ADD`
- `REAL_MUL_LID`


---

## REAL_LE_IM_DIV_CYCLIC

### Name of formal statement
REAL_LE_IM_DIV_CYCLIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_LE_IM_DIV_CYCLIC = prove
 (`!a b c. &0 <= Im ((c - a) / (b - a)) <=> &0 <= Im((a - b) / (c - b))`,
  REWRITE_TAC[IM_COMPLEX_DIV_GE_0] THEN
  REWRITE_TAC[complex_mul; IM; IM_SUB; RE_SUB; IM_CNJ; CNJ_SUB; RE_CNJ] THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For all real numbers `a`, `b`, and `c`, `0 <= Im ((c - a) / (b - a))` if and only if `0 <= Im ((a - b) / (c - b))`.

### Informal sketch
The proof establishes the equivalence between the non-negativity of the imaginary part of `(c - a) / (b - a)` and the non-negativity of the imaginary part of `(a - b) / (c - b)`.
- The proof begins by rewriting using `IM_COMPLEX_DIV_GE_0`, which expresses conditions for non-negativity of the imaginary part of a complex division.
- The proof then uses algebraic rewriting rules involving `complex_mul`, `IM`, `IM_SUB`, `RE_SUB`, `IM_CNJ`, `CNJ_SUB`, and `RE_CNJ` to expand the complex numbers, their imaginary parts, their conjugates, and related operations.
- Finally, `REAL_ARITH_TAC` is applied, which closes the goal using real arithmetic reasoning.

### Mathematical insight
The theorem expresses a cyclic relationship between three real numbers `a`, `b`, and `c`, relating the imaginary parts of complex fractions formed from them. The condition `&0 <= Im ((c - a) / (b - a))` can be interpreted geometrically, related to the angles and orientations of the points `a`, `b`, and `c` in the complex plane. Establishing the equivalence captures a rotational symmetry.

### Dependencies
- Theorems: `IM_COMPLEX_DIV_GE_0`
- Definitions:`complex_mul`, `IM`, `IM_SUB`, `RE_SUB`, `IM_CNJ`, `CNJ_SUB`, `RE_CNJ`


---

## ROTATE_ABOUT_INVERT

### Name of formal statement
ROTATE_ABOUT_INVERT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ROTATE_ABOUT_INVERT = prove
 (`rotate_about a t w = z <=> w = rotate_about a (--t) z`,
  MATCH_MP_TAC(MESON[]
   `(!x. f(g x) = x) /\ (!y. g(f y) = y)
    ==> (f x = y <=> x = g y)`) THEN
  REWRITE_TAC[rotate_about; VECTOR_ADD_SUB; GSYM ROTATE2D_ADD] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_RINV] THEN
  REWRITE_TAC[ROTATE2D_ZERO] THEN VECTOR_ARITH_TAC);;
```

### Informal statement
For all vectors `a`, and real numbers `t`, and vectors `w` and `z`, `rotate_about a t w` equals `z` if and only if `w` equals `rotate_about a (--t) z`.

### Informal sketch
*   The proof uses a general result about the invertibility of functions: if `f(g x) = x` and `g(f y) = y`, then `f x = y` if and only if `x = g y`. The tactic `MATCH_MP_TAC` applies this result.
*   Then, rewrite using the definition of `rotate_about`, `VECTOR_ADD_SUB`, and the fact that `ROTATE2D_ADD` is symmetric to obtain an equivalent goal.
*   Rewrite using the additive inverse laws `REAL_ADD_LINV` and `REAL_ADD_RINV`, to simplify the expression.
*   Rewrite using `ROTATE2D_ZERO` which states that rotation by 0 is the identity.
*   Finally, the vector arithmetic tactic `VECTOR_ARITH_TAC` completes the proof.

### Mathematical insight
The theorem states that the inverse transformation of a rotation about a point by an angle `t` is a rotation about the same point by the angle `-t`. This result provides a way to undo the transformation done by `rotate_about`, which is a fundamental operation in geometry.

### Dependencies
*   Definitions: `rotate_about`, `VECTOR_ADD_SUB`, `ROTATE2D_ADD`
*   Theorems: `REAL_ADD_LINV`, `REAL_ADD_RINV`, `ROTATE2D_ZERO`
*   Tactics: `MESON`


---

## ROTATE_EQ_REFLECT_LEMMA

### Name of formal statement
ROTATE_EQ_REFLECT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ROTATE_EQ_REFLECT_LEMMA = prove
 (`!a b z t.
        ~(b = a) /\ &2 * Arg((b - a) / (z - a)) = t
        ==> rotate_about a t z = reflect_across (a,b) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rotate_about; reflect_across] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ROTATE2D_COMPLEX; reflect2d; o_THM] THEN
  REWRITE_TAC[CNJ_MUL; COMPLEX_MUL_ASSOC; CNJ_CEXP; CNJ_II] THEN
  REWRITE_TAC[CNJ_CX; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG;
              GSYM CEXP_ADD; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_RING `ii * a + ii * a = ii * Cx(&2) * a`] THEN
  ASM_CASES_TAC `z:complex = a` THEN
  ASM_REWRITE_TAC[CNJ_CX; COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (COMPLEX_RING
   `~(z = a)
    ==> c * (z - a) pow 2 = b * cnj (z - a) * (z - a)
        ==> c * (z - a) = b * cnj(z - a)`)) THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [ARG] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `(e1:complex) * e2 pow 2 = e3 ==> e1 * (n * e2) pow 2 = e3 * n pow 2`) THEN
  REWRITE_TAC[GSYM CEXP_ADD; GSYM CEXP_N; CEXP_EQ] THEN
  REWRITE_TAC[COMPLEX_RING
   `ii * t + Cx(&2) * ii * z = ii * u + v * ii <=>
    t + Cx(&2) * z - u = v`] THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB; GSYM CX_ADD; CX_INJ] THEN
  EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `&2 * a = &2 * b <=> a = b`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + (b - c):real = a - (c - b)`] THEN
  ASM_SIMP_TAC[REAL_SUB_ARG; COMPLEX_SUB_0] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `&0`; EXISTS_TAC `&2`] THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;
```
### Informal statement
For all complex numbers `a`, `b`, `z`, and real number `t`, if `b` is not equal to `a` and `2` times the argument of `(b - a) / (z - a)` is equal to `t`, then rotating `z` about `a` by angle `t` is equal to reflecting `z` across the line passing through `a` and `b`.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting the definitions of `rotate_about` and `reflect_across`.
- Apply `AP_TERM_TAC`.
- Rewrite using the definitions of `ROTATE2D_COMPLEX` and `reflect2d`, and the theorem `o_THM`.
- Rewrite using complex number arithmetic rules, including rules for conjugation (`CNJ_MUL`, `COMPLEX_MUL_ASSOC`, `CNJ_CEXP`, `CNJ_II`, `CNJ_CX`, `COMPLEX_MUL_LNEG`, `COMPLEX_MUL_RNEG`, `COMPLEX_NEG_NEG`, `GSYM CEXP_ADD`, `CX_NEG`).
- Rewrite using the complex ring property `ii * a + ii * a = ii * Cx(&2) * a`.
- Perform cases on `z = a`.
  - In the case `z = a`, rewrite using conjugation rules, `COMPLEX_MUL_RZERO`, and `COMPLEX_SUB_REFL`.
  - In the case `~(z = a)`, use an assumption that is derived from `~(z=a)` and `c * (z - a) pow 2 = b * cnj (z - a) * (z - a)` implies `c * (z - a) = b * cnj(z - a)`.
  - Rewrite using `COMPLEX_MUL_CNJ`.
- Apply `ARG` to `LAND_CONV o RAND_CONV o LAND_CONV)`.
- Apply a theorem to rewrite an expression of the form `(e1:complex) * e2 pow 2 = e3 ==> e1 * (n * e2) pow 2 = e3 * n pow 2`.
- Rewrite using `GSYM CEXP_ADD`, `GSYM CEXP_N`, and `CEXP_EQ`.
- Rewrite using the complex ring property `ii * t + Cx(&2) * ii * z = ii * u + v * ii <=> t + Cx(&2) * z - u = v`.
- Rewrite using `GSYM CX_MUL`, `GSYM CX_SUB`, `GSYM CX_ADD`, and `CX_INJ`.
- Expand `t`.
- Rewrite using `GSYM REAL_SUB_LDISTRIB` and `GSYM REAL_ADD_LDISTRIB`.
- Rewrite using real arithmetic `&2 * a = &2 * b <=> a = b`.
- Rewrite using real arithmetic `a + (b - c):real = a - (c - b)`.
- Simplify using `REAL_SUB_ARG` and `COMPLEX_SUB_0`.
- Split on conditions.
- Perform existential instantiation with `&0` and `&2`.
- Simplify using `INTEGER_CLOSED`.
- Apply real arithmetic.

### Mathematical insight
This theorem connects two fundamental geometric transformations in the complex plane: rotation and reflection. It states that under a specific condition relating the angle of rotation (`t`) to the argument of a complex number ratio, a rotation about a point `a` is equivalent to a reflection across the line defined by points `a` and `b`. This reveals a deeper connection between these seemingly distinct operations.

### Dependencies
- Definitions: `rotate_about`, `reflect_across`, `ROTATE2D_COMPLEX`, `reflect2d`
- Theorems: `o_THM`
- Complex Field: `CNJ_MUL`, `COMPLEX_MUL_ASSOC`, `CNJ_CEXP`, `CNJ_II`, `CNJ_CX`, `COMPLEX_MUL_LNEG`, `COMPLEX_MUL_RNEG`, `COMPLEX_NEG_NEG`, `GSYM CEXP_ADD`, `CX_NEG`
- Ring properties:`COMPLEX_RING`
- Real arithmetic: `REAL_SUB_ARG`, `REAL_SUB_LDISTRIB`, `REAL_ADD_LDISTRIB`, `INTEGER_CLOSED`
- Argument/Exponentiation: `ARG`, `CEXP_EQ`, `CEXP_N`, `CX_INJ`,
### Porting notes (optional)
- The extensive use of rewriting with complex number arithmetic suggests that a target proof assistant should have good automation for complex field manipulation.
- The dependencies listed are mostly standard, but a porter needs to verify the exact definitions used in HOL Light and ensure that their target system has compatible definitions. Lean's `Complex` library and its `ring_nf` tactic might be useful.


---

## ROTATE_EQ_REFLECT_PI_LEMMA

### Name of formal statement
ROTATE_EQ_REFLECT_PI_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ROTATE_EQ_REFLECT_PI_LEMMA = prove
 (`!a b z t.
        ~(b = a) /\ &2 * Arg((b - a) / (z - a)) = &4 * pi + t
        ==> rotate_about a t z = reflect_across (a,b) z`,
  REWRITE_TAC[REAL_ARITH `a = &4 * pi + t <=> t = a + --(&4 * pi)`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rotate_about a (&2 * Arg((b - a) / (z - a))) z` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC ROTATE_EQ_REFLECT_LEMMA THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[rotate_about; ROTATE2D_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  REWRITE_TAC[EULER; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; COS_NEG; SIN_NEG] THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; REAL_EXP_NEG; REAL_EXP_0; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_NEG_0; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_MUL_LID]);;
```

### Informal statement
For all complex numbers `a`, `b`, `z`, and real numbers `t`, if `b` is not equal to `a` and `2` times the argument of `(b - a) / (z - a)` equals `4 * pi + t`, then rotating `z` about `a` by angle `t` is equal to reflecting `z` across the line through `a` and `b`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the condition `&2 * Arg((b - a) / (z - a)) = &4 * pi + t` to `t = &2 * Arg((b - a) / (z - a)) - &4 * pi` using `REAL_ARITH`.
- Assume the hypothesis `~(b = a) /\ &2 * Arg((b - a) / (z - a)) = &4 * pi + t` and rewrite using the assumption
- Apply the transitivity of equality (`EQ_TRANS`).
- Prove `rotate_about a (&2 * Arg((b - a) / (z - a))) z = reflect_across (a,b) z`.
 - Split goal into `rotate_about a t z = rotate_about a (&2 * Arg((b - a) / (z - a))) z` and `rotate_about a (&2 * Arg((b - a) / (z - a))) z = reflect_across (a,b) z`
 - The second part uses the `ROTATE_EQ_REFLECT_LEMMA` and assumption rewriting.
- The first goal is proven using rewrite rules about `rotate_about`, `ROTATE2D_ADD`, `ROTATE2D_COMPLEX`, Euler's formula (`EULER`), and trigonometric identities (`RE_MUL_II`, `IM_MUL_II`, `RE_CX`, `IM_CX`, `COS_NEG`, `SIN_NEG`, `SIN_NPI`, `COS_NPI`), simplifying complex number operations and identities until both sides become syntactically equal.

### Mathematical insight
This theorem establishes a connection between rotations and reflections in the complex plane. Specifically, it states that a rotation by a certain angle is equivalent to a reflection across a line, given the condition relating the angle to the argument of a complex number ratio. The condition connects the angle of rotation `t` with the argument of the complex number `(b-a)/(z-a)`, which represents the angle between the vectors from `a` to `z` and from `a` to `b`. When `2 * Arg((b-a)/(z-a)) = 4*pi + t`, rotating `z` about `a` by the angle `t` is equivalent to reflecting `z` across the line defined by `a` and `b`.

### Dependencies
- `rotate_about`
- `reflect_across`
- `ROTATE_EQ_REFLECT_LEMMA`
- `REAL_ARITH`
- `ROTATE2D_ADD`
- `ROTATE2D_COMPLEX`
- `EULER`
- `RE_MUL_II`
- `IM_MUL_II`
- `RE_CX`
- `IM_CX`
- `COS_NEG`
- `SIN_NEG`
- `SIN_NPI`
- `COS_NPI`
- `REAL_EXP_NEG`
- `REAL_EXP_0`
- `CX_NEG`
- `COMPLEX_NEG_0`
- `COMPLEX_MUL_RZERO`
- `COMPLEX_ADD_RID`
- `COMPLEX_MUL_LID`

### Porting notes (optional)
- The proof relies on numerous rewrites involving complex number identities and trigonometric functions. Ensure that the target proof assistant has equivalent libraries or definitions available.
- The tactic `REAL_ARITH` is used for real arithmetic simplification; an equivalent tactic or manual rewriting may be required in other systems.
- The handling of complex numbers and their arguments may vary between systems, so pay close attention to the definitions and available simplification rules.


---

## EQUILATERAL_TRIANGLE_ALGEBRAIC

### Name of formal statement
EQUILATERAL_TRIANGLE_ALGEBRAIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EQUILATERAL_TRIANGLE_ALGEBRAIC = prove
 (`!A B C j.
        j pow 3 = Cx(&1) /\ ~(j = Cx(&1)) /\
        A + j * B + j pow 2 * C = Cx(&0)
        ==> dist(A,B) = dist(B,C) /\ dist(C,A) = dist(B,C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[dist] THEN
  SUBGOAL_THEN `C - A:complex = j * (B - C) /\ A - B = j pow 2 * (B - C)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(j pow 3) = &1` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
    REWRITE_TAC[COMPLEX_NORM_POW; REAL_POW_EQ_1; ARITH; REAL_ABS_NORM] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For all complex numbers `A`, `B`, `C`, and `j`, if `j` cubed equals the complex number 1, `j` is not equal to the complex number 1, and `A` plus `j` times `B` plus `j` squared times `C` equals the complex number 0, then the distance between `A` and `B` is equal to the distance between `B` and `C`, and the distance between `C` and `A` is equal to the distance between `B` and `C`.

### Informal sketch
The theorem provides algebraic conditions for three complex numbers `A`, `B`, and `C` to form the vertices of an equilateral triangle. The proof proceeds as follows:
- Assume the hypothesis: `j^3 = 1`, `j != 1`, and `A + j*B + j^2*C = 0`.
- Rewrite the goal using the definition of `dist`.
- Reduce the goal to showing that `C - A = j * (B - C)` and `A - B = j^2 * (B - C)`.
- Use the assumption `A + j*B + j^2*C = 0` and complex number algebra to prove the above two equations.
- Prove that `norm(j^3) = 1`.  This is done by using the assumption `j^3 = 1` and rewriting with the definitions of `COMPLEX_NORM_CX` and `REAL_ABS_NUM`.  Then, rewrite with `COMPLEX_NORM_POW`, `REAL_POW_EQ_1`, `ARITH`, `REAL_ABS_NORM`.  Finally, discharge by assuming the first conjunct.
- Rewrite with `COMPLEX_NORM_MUL` and `COMPLEX_NORM_POW`.
- Use real arithmetic to complete the proof.

### Mathematical insight
The theorem gives an algebraic characterization of when three complex numbers form an equilateral triangle.  The condition `j^3 = 1` and `j != 1` ensures that `j` is a primitive cube root of unity.  The condition `A + j*B + j^2*C = 0` expresses a symmetry between `A`, `B`, and `C` with respect to rotation by `j`.  The theorem shows that this algebraic condition is equivalent to the geometric condition that the triangle with vertices `A`, `B`, and `C` is equilateral. This is a standard result in complex number geometry.

### Dependencies
- `dist`
- `COMPLEX_NORM_CX`
- `REAL_ABS_NUM`
- `COMPLEX_NORM_POW`
- `REAL_POW_EQ_1`
- `ARITH`
- `REAL_ABS_NORM`
- `COMPLEX_NORM_MUL`

### Porting notes (optional)
- The tactics used in the proof rely heavily on rewriting with definitions and algebraic simplification. A similar approach can be adopted in other proof assistants, although the specific tactics will differ.
- The proof uses `COMPLEX_RING`, which encapsulates complex number arithmetic. This result might be proven directly, or a complex number library would need to be used.


---

## AFFINE_GROUP_ITER_3

### Name of formal statement
AFFINE_GROUP_ITER_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AFFINE_GROUP_ITER_3 = prove
 (`ITER 3 (\z. a * z + b) = (\z. a pow 3 * z + b * (Cx(&1) + a + a pow 2))`,
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `3`] THEN
  REWRITE_TAC[ITER; FUN_EQ_THM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement
For any complex numbers `a` and `b`, the 3-fold iteration of the affine transformation that maps `z` to `a * z + b` is equal to the affine transformation that maps `z` to `a^3 * z + b * (1 + a + a^2)`.

### Informal sketch
The proof proceeds by:
- Expanding the iteration `ITER 3 (\z. a * z + b)` using the definition of `ITER` and the theorem `FUN_EQ_THM` which states that two functions are equal if they have the same behaviour for all inputs.
- Numerically reducing the exponent `3` using `num_CONV `3``.
- Applying `NUM_REDUCE_CONV` to simplify the arithmetic expression arising from the iterated composition.
- Applying `COMPLEX_RING` to perform ring simplification of complex numbers, eventually leading to the desired result.

### Mathematical insight
This theorem shows the result of iterating an affine transformation three times. This is a specific instance that generalizes to `n` iterations, which have a closed-form expression, where the linear part is `a^n` and the constant part is `b * (1 + a + ... + a^(n-1))`. This expansion is useful in characterizing the long-term behavior of repeated affine transformations.

### Dependencies
- `ITER`
- `FUN_EQ_THM`
- `num_CONV`
- `NUM_REDUCE_CONV`
- `COMPLEX_RING`


---

## AFFINE_GROUP_COMPOSE

### Name of formal statement
AFFINE_GROUP_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AFFINE_GROUP_COMPOSE = prove
 (`(\z. a1 * z + b1) o (\z. a2 * z + b2) =
   (\z. (a1 * a2) * z + (b1 + a1 * b2))`,
  REWRITE_TAC[o_THM; FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;
```
### Informal statement
The composition of two affine transformations, each mapping a complex number `z` to `a * z + b` for some complex numbers `a` and `b`, is itself an affine transformation. Specifically, for complex numbers `a1`, `b1`, `a2`, and `b2`, the composition of the transformation `z` ↦ `a1 * z + b1` and the transformation `z` ↦ `a2 * z + b2` is equal to the transformation `z` ↦ `(a1 * a2) * z + (b1 + a1 * b2)`.

### Informal sketch
The theorem is proved as follows:
- First, rewrite the composition `o` using its definition `o_THM` (which states that `(f o g) x = f (g x)`) and the fact that functions are equal if they are equal at every point, which is done using `FUN_EQ_THM`.
- Then, simplify the resulting expression using the complex field axioms via the `COMPLEX_RING` conversion, which performs ring simplification for complex numbers.

### Mathematical insight
This theorem demonstrates that the set of affine transformations on the complex plane forms a group under composition. This is a fundamental property used in various areas of mathematics, including geometry and complex analysis. Affine transformations preserve collinearity and ratios of distances, making them important for studying geometric structures.

### Dependencies
- Theorems: `FUN_EQ_THM`, `o_THM`
- Conversions: `COMPLEX_RING`


---

## AFFINE_GROUP_I

### Name of formal statement
AFFINE_GROUP_I

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AFFINE_GROUP_I = prove
 (`I = (\z. Cx(&1) * z + Cx(&0))`,
  REWRITE_TAC[I_THM; FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;
```
### Informal statement
The function `I` is equal to the affine transformation that multiplies its argument `z` by the complex number 1 and adds the complex number 0, i.e.,  `(\z. Cx(&1) * z + Cx(&0))`.

### Informal sketch
The proof proceeds by:
- Rewriting using `I_THM` and `FUN_EQ_THM`. `I_THM` likely provides a definition or established property of the identity function `I`. `FUN_EQ_THM` is a theorem stating that two functions are equal if they agree on all inputs.
- Applying the conversion tactic `CONV_TAC` with `COMPLEX_RING`. This suggests that the goal is simplified using ring properties of complex numbers. Simplifying `Cx(&1) * z + Cx(&0)` to `z` using complex ring properties establishes the equality.

### Mathematical insight
This theorem shows that the identity function `I` can be represented as an affine transformation with a scaling factor of 1 and a translation of 0. This provides a straightforward connection between the identity function and the more general concept of affine transformations.

### Dependencies
- Theorems: `I_THM`, `FUN_EQ_THM`
- Conversions: `COMPLEX_RING`


---

## AFFINE_GROUP_EQ

### Name of formal statement
AFFINE_GROUP_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AFFINE_GROUP_EQ = prove
 (`!a b a' b. (\z. a * z + b) = (\z. a' * z + b') <=> a = a' /\ b = b'`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&1)`) THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement
For all complex numbers `a`, `b`, `a'`, and `b'`, the affine transformation function mapping `z` to `a * z + b` is equal to the affine transformation function mapping `z` to `a' * z + b'` if and only if `a` is equal to `a'` and `b` is equal to `b'`.

### Informal sketch
The proof proceeds as follows:
- Start with universally quantifying over `a`, `b`, `a'`, and `b'`.
- Apply extensionality, reducing the goal to showing that `(\z. a * z + b) = (\z. a' * z + b')` implies `a = a' /\ b = b'` AND ` a = a' /\ b = b'` implies `(\z. a * z + b) = (\z. a' * z + b')`.
- Simplify using `FUN_EQ_THM`.
- Discharge the assumption.
- Instantiate the universally quantified `z` with `0` in the implication `(\z. a * z + b) = (\z. a' * z + b')` by specializing the assumption with `Cx(&0)`. Then use Modus Ponens.
- Instantiate the universally quantified `z` with `1` in the implication `(\z. a * z + b) = (\z. a' * z + b')` by specializing the assumption with `Cx(&1)`. Then use Modus Ponens.
- Use the complex ring properties to complete the proof.

### Mathematical insight
This theorem formalizes the intuitive notion that an affine transformation over the complex numbers is uniquely determined by its coefficients `a` and `b`. It establishes that two affine transformations are equal if and only if their corresponding coefficients are equal. This is a fundamental property used when reasoning about affine transformations.

### Dependencies
- `FUN_EQ_THM`
- `COMPLEX_RING`

### Porting notes (optional)
- The proof relies on the properties of the complex numbers, specifically being able to evaluate the complex numbers `0` and `1`.
- The auto tactics can be replaced with manual proof steps.


---

## AFFINE_GROUP_ROTATE_ABOUT

### Name of formal statement
AFFINE_GROUP_ROTATE_ABOUT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AFFINE_GROUP_ROTATE_ABOUT = prove
 (`!a t. rotate_about a t =
         (\z. cexp(ii * Cx(t)) * z + (Cx(&1) - cexp(ii * Cx(t))) * a)`,
  REWRITE_TAC[rotate_about; FUN_EQ_THM; ROTATE2D_COMPLEX] THEN
  CONV_TAC COMPLEX_RING);;
```
### Informal statement
For all complex numbers `a` and real numbers `t`, the rotation about `a` by angle `t`, denoted `rotate_about a t`, is equal to the function that maps any complex number `z` to the complex number `cexp(ii * Cx(t)) * z + (Cx(&1) - cexp(ii * Cx(t))) * a`.

### Informal sketch
The proof proceeds as follows:
- Starting with the definition of `rotate_about a t`, we rewrite it using `rotate_about`, `FUN_EQ_THM` and `ROTATE2D_COMPLEX`. `ROTATE2D_COMPLEX` presumably relates the matrix-based 2D rotation to the complex exponential representation. `FUN_EQ_THM` is used to rewrite under a lambda abstraction.
- We then apply the `COMPLEX_RING` conversion tactic. This tactic performs algebraic simplification within the complex field. This likely simplifies the expression involving complex exponentials and complex numbers to the desired final form.

### Mathematical insight
This theorem provides an explicit formula, in terms of complex arithmetic, for the rotation of a complex number `z` about a point `a` by an angle `t`, where `t` is a real number.  This characterization of planar rotations in terms of complex numbers is a fundamental result. The formula essentially represents the rotation as a complex multiplication (`cexp(ii * Cx(t)) * z`) followed by a translation (`(Cx(&1) - cexp(ii * Cx(t))) * a`), which is characteristic of affine transformations.

### Dependencies
- Definitions: `rotate_about`
- Theorems: `FUN_EQ_THM`, `ROTATE2D_COMPLEX`
- Conversions: `COMPLEX_RING`


---

## ALGEBRAIC_LEMMA

### Name of formal statement
ALGEBRAIC_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ALGEBRAIC_LEMMA = prove
 (`!a1 a2 a3 b1 b2 b3 A B C.
        (\z. a3 * z + b3) ((\z. a1 * z + b1) B) = B /\
        (\z. a1 * z + b1) ((\z. a2 * z + b2) C) = C /\
        (\z. a2 * z + b2) ((\z. a3 * z + b3) A) = A /\
        ITER 3 (\z. a1 * z + b1) o ITER 3 (\z. a2 * z + b2) o
        ITER 3 (\z. a3 * z + b3) = I /\
        ~(a1 * a2 * a3 = Cx(&1)) /\
        ~(a1 * a2 = Cx(&1)) /\
        ~(a2 * a3 = Cx(&1)) /\
        ~(a3 * a1 = Cx(&1))
        ==> (a1 * a2 * a3) pow 3 = Cx (&1) /\
            ~(a1 * a2 * a3 = Cx (&1)) /\
            C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B = Cx(&0)`,
  REWRITE_TAC[AFFINE_GROUP_ITER_3; AFFINE_GROUP_COMPOSE; AFFINE_GROUP_I;
              AFFINE_GROUP_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `(a1 * a2 * a3) * a1 pow 2 * a2 *
    (a1 - a1 * a2 * a3) * (a2 - a1 * a2 * a3) * (a3 - a1 * a2 * a3) *
    (C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B) = Cx(&0)`
  MP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (COMPLEX_FIELD
     `a3 * (a1 * B + b1) + b3 = B
      ==> ~(a1 * a3 = Cx(&1))
          ==> B = (a3 * b1 + b3) / (Cx(&1) - a1 * a3)`))) THEN
    REPEAT(ANTS_TAC THENL
     [ASM_MESON_TAC[COMPLEX_MUL_SYM]; DISCH_THEN SUBST1_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (COMPLEX_RING
     `s = Cx(&0) ==> s + t = Cx(&0) ==> t = Cx(&0)`));
    REWRITE_TAC[COMPLEX_ENTIRE]] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD);;
```

### Informal statement
For all complex numbers `a1`, `a2`, `a3`, `b1`, `b2`, `b3`, `A`, `B`, and `C`, if the affine transformations `\z. a3 * z + b3` applied to `(\z. a1 * z + b1) B` equals `B`, `\z. a1 * z + b1` applied to `(\z. a2 * z + b2) C` equals `C`, `\z. a2 * z + b2` applied to `(\z. a3 * z + b3) A` equals `A`, the composition of iterating the affine transformation `\z. a1 * z + b1` three times, followed by iterating the affine transformation `\z. a2 * z + b2` three times, followed by iterating the affine transformation `\z. a3 * z + b3` three times, equals the identity transformation `I`,  `a1 * a2 * a3` is not equal to 1, `a1 * a2` is not equal to 1, `a2 * a3` is not equal to 1, and `a3 * a1` is not equal to 1, then `(a1 * a2 * a3)` to the power of 3 equals 1, `a1 * a2 * a3` is not equal to 1, and `C + (a1 * a2 * a3) * A + (a1 * a2 * a3)` squared times `B` equals 0.

### Informal sketch
The proof proceeds as follows:
- Apply rewriting using theorems related to affine groups, such as `AFFINE_GROUP_ITER_3`, which likely simplifies the iteration of affine transformations, and `AFFINE_GROUP_COMPOSE` and `AFFINE_GROUP_I` which handles compose and identity, and `AFFINE_GROUP_EQ`.
- Perform repeated generalization and stripping of the goal, followed by assumption rewriting.
- Split the goal into two subgoals using `CONJ_TAC`.
- Solve the first subgoal using rewriting with the complex ring axioms.
- For the remaining subgoal, introduce a sub-goal to prove: `(a1 * a2 * a3) * a1 pow 2 * a2 * (a1 - a1 * a2 * a3) * (a2 - a1 * a2 * a3) * (a3 - a1 * a2 * a3) * (C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B) = Cx(&0)`.
- Use the assumptions about the affine transformations to derive expressions for A, B, and C in terms of `a1`, `a2`, `a3`, `b1`, `b2`, and `b3`. This involves theorems related to complex fields.
- Simplify the expression in the subgoal using the derived expressions for A, B, and C. This involves several applications of `ANTS_TAC`, `ASM_MESON_TAC`, `DISCH_THEN SUBST1_TAC`, and `MATCH_MP_TAC` which deal with substitution and simplification of equations.
- Use `COMPLEX_ENTIRE` and `COMPLEX_FIELD` to solve the subgoal.

### Mathematical insight
This theorem relates the properties of compositions and iterations of particular affine transformations in the complex plane to algebraic constraints on the coefficients of those transformations. The affine transformations are of the form `f(z) = a*z + b`, where `a` and `b` are complex numbers. The theorem essentially states that if three such transformations, when iterated three times and composed, yield the identity, and if certain pairwise products of the scaling factors are not equal to 1, then the cube of the product of all three scaling factors must be 1, and also that a certain linear combination of the fixed points of the individual iterated transformations is 0..

### Dependencies
- `AFFINE_GROUP_ITER_3`
- `AFFINE_GROUP_COMPOSE`
- `AFFINE_GROUP_I`
- `AFFINE_GROUP_EQ`
- `COMPLEX_RING`
- `COMPLEX_FIELD`
- `COMPLEX_MUL_SYM`
- `COMPLEX_ENTIRE`


---

## CYCLIC_PERM_SUBGOAL_THEN

### Name of formal statement
CYCLIC_PERM_SUBGOAL_THEN

### Type of the formal statement
Tactic

### Formal Content
```ocaml
let CYCLIC_PERM_SUBGOAL_THEN =
  let lemma = MESON[]
   `(!A B C P Q R a b c g1 g2 g3.
       Ant A B C P Q R a b c g1 g2 g3 ==> Cns A B C P Q R a b c g1 g2 g3)
    ==> (!A B C P Q R a b c g1 g2 g3.
           Ant A B C P Q R a b c g1 g2 g3
           ==> Ant B C A Q R P b c a g2 g3 g1)
        ==> (!A B C P Q R a b c g1 g2 g3.
                   Ant A B C P Q R a b c g1 g2 g3
                   ==> Cns A B C P Q R a b c g1 g2 g3 /\
                       Cns B C A Q R P b c a g2 g3 g1 /\
                       Cns C A B R P Q c a b g3 g1 g2)`
  and vars =
   [`A:complex`; `B:complex`; `C:complex`;
    `P:complex`; `Q:complex`; `R:complex`;
    `a:real`; `b:real`; `c:real`;
    `g1:complex->complex`; `g2:complex->complex`; `g3:complex->complex`] in
  fun t ttac (asl,w) ->
      let asm = list_mk_conj (map (concl o snd) (rev asl)) in
      let gnw = list_mk_forall(vars,mk_imp(asm,t)) in
      let th1 = MATCH_MP lemma (ASSUME gnw) in
      let tm1 = fst(dest_imp(concl th1)) in
      let th2 = REWRITE_CONV[INSERT_AC; CONJ_ACI; ANGLE_SYM; EQ_SYM_EQ] tm1 in
      let th3 = DISCH_ALL(MP th1 (EQT_ELIM th2)) in
      (MP_TAC th3 THEN ANTS_TAC THENL
        [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC;
         DISCH_THEN(MP_TAC o SPEC_ALL) THEN ANTS_TAC THENL
          [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
           DISCH_THEN(CONJUNCTS_THEN2 ttac MP_TAC) THEN
           DISCH_THEN(CONJUNCTS_THEN ttac)]]) (asl,w);;
```

### Informal statement
The tactic `CYCLIC_PERM_SUBGOAL_THEN` takes a tactic `t` and a tactic `ttac` as arguments, along with the usual assumption list `asl` and goal `w`. It attempts to prove a goal by exploiting cyclic symmetry among three sets of variables. The tactic operates as follows:

It uses a lemma that states: If for all complex numbers `A`, `B`, `C`, `P`, `Q`, `R`, real numbers `a`, `b`, `c`, and functions `g1`, `g2`, `g3` from complex numbers to complex numbers, the assumption `Ant A B C P Q R a b c g1 g2 g3` implies the conclusion `Cns A B C P Q R a b c g1 g2 g3`, and if the assumption `Ant A B C P Q R a b c g1 g2 g3` implies the permuted assumption `Ant B C A Q R P b c a g2 g3 g1`, then it follows that if `Ant A B C P Q R a b c g1 g2 g3` holds, then the conjunction `Cns A B C P Q R a b c g1 g2 g3 /\ Cns B C A Q R P b c a g2 g3 g1 /\ Cns C A B R P Q c a b g3 g1 g2` holds as well.

### Informal sketch
The tactic `CYCLIC_PERM_SUBGOAL_THEN` aims to prove theorems that exhibit cyclic symmetry. It is structured as follows:

- It constructs a lemma expressing that if a property holds for `A`, `B`, `C`, `P`, `Q`, `R`, `a`, `b`, `c`, `g1`, `g2`, `g3` under an assumption `Ant A B C P Q R a b c g1 g2 g3`, and the permuted assumption `Ant B C A Q R P b c a g2 g3 g1` follows from the unpermuted one, then to prove the conclusion for the unpermuted variables, it’s sufficient to show that the conclusion and the conclusions formed by cyclic permutations also hold.

- The tactic retrieves the assumptions list `asl` from the current proof state and forms a combined assumption `asm`.

- The tactic applies the lemma using `MATCH_MP` with the goal, which is universally quantified over the types of the involved variables

- The resulting goal has the form where the assumptions need to be discharged.

- The tactic splits the goals. One goal simply requires showing that `Ant A B C P Q R a b c g1 g2 g3` implies `Ant B C A Q R P b c a g2 g3 g1`. This is solved with `REPEAT GEN_TAC` which discharges the quantifiers, effectively generalizing over all the variables and functions, and `STRIP_TAC` to move the assumptions into the assumption list.

- The remaining goal requires showing `Cns A B C P Q R a b c g1 g2 g3`, `Cns B C A Q R P b c a g2 g3 g1`, and `Cns C A B R P Q c a b g3 g1 g2` under the assumption `Ant A B C P Q R a b c g1 g2 g3`.

- The tactic splits the conjunctive goal into three subgoals, applying tactic `ttac` to the first subgoal, `MP_TAC` to the second, and `ttac` to the third.

### Mathematical insight
This tactic leverages cyclic permutation symmetry to reduce the proof burden. If a problem is cyclically symmetric in three sets of variables, it suffices to prove the implication for the original variables, prove that the first cyclic permutation of the premise implies the permuted premise, and then prove the three conclusions where the conclusions are also cyclically permuted. This can be beneficial if, for example, the proof for the original variables is easier than directly proving the result for all permutations.

### Dependencies
**Theorems:**
- `MESON` (uses the MESON prover to establish the cyclic symmetry lemma)

**Tactics:**
- `MP_TAC` (Modus Ponens tactic)
- `ANTS_TAC` (splits conjunctive or implicative goals)
- `POP_ASSUM_LIST`
- `ALL_TAC`
- `REPEAT GEN_TAC` (repeatedly applies the GEN_TAC tactic, discharging quantifiers)
- `STRIP_TAC` (moves assumptions from the goal to the assumption list)
- `DISCH_THEN`
- `SPEC_ALL`
- `CONJUNCTS_THEN2`
- `CONJUNCTS_THEN`
- `REPEAT CONJ_TAC` (repeatedly applies the CONJ_TAC tactic, splitting conjunctions)
- `FIRST_ASSUM ACCEPT_TAC`
- `REWRITE_CONV`
- `INSERT_AC`
- `CONJ_ACI`
- `ANGLE_SYM`
- `EQ_SYM_EQ`
- `ASSUME`
- `MATCH_MP`
- `EQT_ELIM`
- `DISCH_ALL`

**Definitions:**
- `list_mk_conj`
- `concl`
- `list_mk_forall`
- `mk_imp`
- `fst`
- `dest_imp`

### Porting notes (optional)
- The tactic relies on rewriting using `REWRITE_CONV` with associativity and commutativity rules for conjunction (`CONJ_ACI`), symmetry rules for equality (`EQ_SYM_EQ`), and `ANGLE_SYM`. Ensuring similar rewrite rules are available in the target proof assistant is important.
- Mimicking the effect of `MESON` in another system might require either porting the MESON prover or using an alternative automated proof search strategy within the target system.
- The overall structure of the tactic, involving premise manipulation and goal splitting, should be straightforwardly representable in most interactive proof assistants.


---

## MORLEY

### Name of formal statement
MORLEY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MORLEY = prove
 (`!A B C:real^2 P Q R.
     ~collinear{A,B,C} /\ {P,Q,R} SUBSET convex hull {A,B,C} /\
     angle(A,B,R) = angle(A,B,C) / &3 /\
     angle(B,A,R) = angle(B,A,C) / &3 /\
     angle(B,C,P) = angle(B,C,A) / &3 /\
     angle(C,B,P) = angle(C,B,A) / &3 /\
     angle(C,A,Q) = angle(C,A,B) / &3 /\
     angle(A,C,Q) = angle(A,C,B) / &3
     ==> dist(R,P) = dist(P,Q) /\ dist(Q,R) = dist(P,Q)`,
  MATCH_MP_TAC(MESON[]
    `(!A B C. &0 <= Im((C - A) / (B - A)) \/
              &0 <= Im((B - A) / (C - A))) /\
     (!A B C. Property A B C ==> Property A C B) /\
     (!A B C. &0 <= Im((C - A) / (B - A)) ==> Property A B C)
     ==> !A B C. Property A B C`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IM_COMPLEX_INV_LE_0] THEN
    REWRITE_TAC[COMPLEX_INV_DIV] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`P:real^2`; `Q:real^2`; `R:real^2`] THEN
    REWRITE_TAC[ANGLE_SYM; DIST_SYM; INSERT_AC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`P:real^2`; `R:real^2`; `Q:real^2`]) THEN
    REWRITE_TAC[ANGLE_SYM; DIST_SYM; INSERT_AC] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC])
   [`A:real^2 = B`; `A:real^2 = C`; `B:real^2 = C`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
       let th' = GEN_REWRITE_RULE I [REAL_LE_IM_DIV_CYCLIC] th in
       let th'' = GEN_REWRITE_RULE I [REAL_LE_IM_DIV_CYCLIC] th' in
       ASSUME_TAC th' THEN ASSUME_TAC th'') THEN
  ABBREV_TAC `a = angle(C:real^2,A,B) / &3` THEN
  ABBREV_TAC `b = angle(A:real^2,B,C) / &3` THEN
  ABBREV_TAC `c = angle(B:real^2,C,A) / &3` THEN
  ABBREV_TAC `g1 = rotate_about A (&2 * a)` THEN
  ABBREV_TAC `g2 = rotate_about B (&2 * b)` THEN
  ABBREV_TAC `g3 = rotate_about C (&2 * c)` THEN
  CYCLIC_PERM_SUBGOAL_THEN
    `ITER 3 g1 o ITER 3 g2 o ITER 3 g3 = (I:real^2->real^2)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g1"; "g2"; "g3"] THEN
    REWRITE_TAC[ITER_ROTATE_ABOUT] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"; "c"] THEN
    REWRITE_TAC[REAL_ARITH `&3 * &2 * a / &3 = &2 * a`] THEN
    ASM_SIMP_TAC[GSYM REFLECT_ACROSS_COMPOSE_ANGLE] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; REFLECT_ACROSS_SYM] THEN
    ASM_SIMP_TAC[REWRITE_RULE[FUN_EQ_THM; I_THM; o_THM]
                 REFLECT_ACROSS_COMPOSE_INVOLUTION];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN `&0 <= Im((P - B) / (C - B))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INSERT_SUBSET]) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ARITH `(u % A + v % B + w % C) - B:real^N =
                 u % (A - B) + w % (C - B) + ((u + v + w) - &1) % B`] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; IM_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[IM_MUL_CX; COMPLEX_DIV_REFL; COMPLEX_SUB_0; IM_CX] THEN
    SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN `&0 <= Im((B - C) / (P - C))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IM_COMPLEX_INV_LE_0; COMPLEX_INV_DIV] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INSERT_SUBSET]) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ARITH `(u % A + v % B + w % C) - C:real^N =
                   v % (B - C) + u % (A - C) + ((u + v + w) - &1) % C`] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; IM_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[IM_MUL_CX; COMPLEX_DIV_REFL; COMPLEX_SUB_0; IM_CX] THEN
    SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= u * --a ==> u * a <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
    ASM_REWRITE_TAC[GSYM IM_COMPLEX_INV_GE_0; COMPLEX_INV_DIV];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `~(P:real^2 = B) /\ ~(P = C)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x y z. ~(angle(x:real^2,y,z) / &3 = pi / &2)`
     (fun th -> ASM_MESON_TAC[th; ANGLE_REFL]) THEN
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= pi /\ &0 < pi ==> ~(a / &3 = pi / &2)`) THEN
    REWRITE_TAC[ANGLE_RANGE; PI_POS];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `(g3:complex->complex)(g1(Q)) = Q`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g1"; "g3"] THEN
    ONCE_REWRITE_TAC[ROTATE_ABOUT_INVERT] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `reflect_across(A,C) Q` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ROTATE_EQ_REFLECT_LEMMA THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [SYM(ASSUME `angle(C:real^2,A,Q) = a`)] THEN
      REWRITE_TAC[angle] THEN ONCE_REWRITE_TAC[VECTOR_ANGLE_SYM] THEN
      ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[REFLECT_ACROSS_SYM] THEN
    MATCH_MP_TAC ROTATE_EQ_REFLECT_PI_LEMMA THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
    REWRITE_TAC[REAL_ARITH `&2 * a = &4 * pi + &2 * --c <=>
                            a = &2 * pi - c`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [SYM(ASSUME `angle(B:real^2,C,A) / &3 = c`)] THEN
    ONCE_REWRITE_TAC[ANGLE_SYM] THEN FIRST_ASSUM(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[angle] THEN
    ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM COMPLEX_INV_DIV] THEN
    MATCH_MP_TAC ARG_INV THEN REWRITE_TAC[GSYM ARG_EQ_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `angle(A:real^2,C,Q) = &0` MP_TAC THENL
     [REWRITE_TAC[angle] THEN ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0];
      ASM_REWRITE_TAC[REAL_ARITH `a / &3 = &0 <=> a = &0`]] THEN
    ASM_MESON_TAC[COLLINEAR_ANGLE; ANGLE_SYM; INSERT_AC];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE LAND_CONV [AFFINE_GROUP_ROTATE_ABOUT])) THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `~(cexp(ii * Cx(&2 * a)) * cexp(ii * Cx(&2 * b)) = Cx(&1)) /\
    ~(cexp(ii * Cx(&2 * a)) * cexp(ii * Cx(&2 * b)) *
      cexp(ii * Cx(&2 * c)) = Cx(&1))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CEXP_ADD; GSYM COMPLEX_ADD_LDISTRIB; GSYM CX_ADD] THEN
    MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c /\ &0 < pi /\
      &3 * a + &3 * b + &3 * c = pi /\ ~(&3 * c = pi)
      ==> (&0 < &2 * a + &2 * b /\ &2 * a + &2 * b < &2 * pi) /\
          (&0 < &2 * a + &2 * b + &2 * c /\
           &2 * a + &2 * b + &2 * c < &2 * pi)`) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"; "c"] THEN
      REWRITE_TAC[REAL_ARITH `&3 * x / &3 = x`; PI_POS] THEN
      SIMP_TAC[ANGLE_RANGE; REAL_LE_DIV; REAL_POS] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[TRIANGLE_ANGLE_SUM; ADD_AC; ANGLE_SYM];
        ASM_MESON_TAC[COLLINEAR_ANGLE; ANGLE_SYM; INSERT_AC]];
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
      REWRITE_TAC[CEXP_II_NE_1; GSYM CX_ADD]];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a1 = cexp(ii * Cx(&2 * a))`;
    `a2 = cexp(ii * Cx(&2 * b))`;
    `a3 = cexp(ii * Cx(&2 * c))`;
    `b1 = (Cx (&1) - a1) * A`;
    `b2 = (Cx (&1) - a2) * B`;
    `b3 = (Cx (&1) - a3) * C`] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC EQUILATERAL_TRIANGLE_ALGEBRAIC THEN
  EXISTS_TAC `a1 * a2 * a3:complex` THEN
  MATCH_MP_TAC ALGEBRAIC_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`b1:complex`; `b2:complex`; `b3:complex`] THEN
  PURE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[]);;
```

### Informal statement
For any points `A`, `B`, and `C` in the real plane, and any points `P`, `Q`, and `R` also in the real plane, if:
1. `A`, `B`, and `C` are not collinear, and
2. the set `{P, Q, R}` is a subset of the convex hull of `{A, B, C}`, and
3. the angle from `A` to `B` to `R` is one-third of the angle from `A` to `B` to `C`, and
4. the angle from `B` to `A` to `R` is one-third of the angle from `B` to `A` to `C`, and
5. the angle from `B` to `C` to `P` is one-third of the angle from `B` to `C` to `A`, and
6. the angle from `C` to `B` to `P` is one-third of the angle from `C` to `B` to `A`, and
7. the angle from `C` to `A` to `Q` is one-third of the angle from `C` to `A` to `B`, and
8. the angle from `A` to `C` to `Q` is one-third of the angle from `A` to `C` to `B`,
then the distance from `R` to `P` is equal to the distance from `P` to `Q`, and the distance from `Q` to `R` is equal to the distance from `P` to `Q`.

### Informal sketch
The proof proceeds as follows:
- First, the theorem is specialized to complex numbers.
- Assumptions that points are *not* collinear are handled by cases, reducing to cases where the imaginary part of certain complex divisions is positive.
- Cases where any two of `A`, `B`, `C` coincide are eliminated.
- The proof then introduces abbreviations for one-third of the angles at each vertex (`a`, `b`, `c`) and rotations by twice these angles about each vertex (`g1`, `g2`, `g3`).
- A cyclic permutation subgoal shows that the composition `g1 o g2 o g3` repeated three times is the identity transformation.
- The proof establishes that the imaginary parts of some complex quantities involving `P`, `B`, and `C` are non-negative.
- A cyclic permutation subgoal proves that `P` is distinct from `B` and `C`.
- Another cyclic permutation subgoal shows `g3(g1(Q)) = Q`.
- Finally, the proof leverages an algebraic lemma (`EQUILATERAL_TRIANGLE_ALGEBRAIC` and `ALGEBRAIC_LEMMA`) about complex numbers, rotations, and equilateral triangles to establish the result.

### Mathematical insight
Morley's Trisector Theorem is a classical result in Euclidean geometry. It states that the points of intersection of the adjacent angle trisectors of any triangle form an equilateral triangle (the Morley triangle).

### Dependencies
- `COLLINEAR_2`
- `ANGLE_SYM`
- `DIST_SYM`
- `INSERT_AC`
- `REAL_LE_IM_DIV_CYCLIC`
- `ANGLE_RANGE`
- `PI_POS`
- `ITER_ROTATE_ABOUT`
- `REFLECT_ACROSS_COMPOSE_ANGLE`
- `FUN_EQ_THM`
- `o_THM`
- `I_THM`
- `REFLECT_ACROSS_SYM`
- `REFLECT_ACROSS_COMPOSE_INVOLUTION`
- `INSERT_SUBSET`
- `EMPTY_SUBSET`
- `CONVEX_HULL_3`
- `IN_ELIM_THM`
- `VECTOR_ARITH`
- `REAL_SUB_REFL`
- `VECTOR_MUL_LZERO`
- `VECTOR_ADD_RID`
- `complex_div`
- `COMPLEX_ADD_RDISTRIB`
- `IM_ADD`
- `COMPLEX_CMUL`
- `COMPLEX_MUL_ASSOC`
- `IM_MUL_CX`
- `COMPLEX_DIV_REFL`
- `COMPLEX_SUB_0`
- `IM_CX`
- `REAL_MUL_RZERO`
- `REAL_ADD_RID`
- `complex`
- `COMPLEX_INV_DIV`
- `ROTATE_ABOUT_INVERT`
- `ROTATE_EQ_REFLECT_LEMMA`
- `VECTOR_ANGLE_SYM`
- `VECTOR_ANGLE_ARG`
- `COMPLEX_SUB_0`
- `REFLECT_ACROSS_SYM`
- `ROTATE_EQ_REFLECT_PI_LEMMA`
- `EQ_TRANS`
- `REAL_MUL_RNEG`
- `ARG_INV`
- `ARG_EQ_0`
- `COLLINEAR_ANGLE`
- `AFFINE_GROUP_ROTATE_ABOUT`
- `CEXP_ADD`
- `COMPLEX_ADD_LDISTRIB`
- `CX_ADD`
- `CEXP_II_NE_1`
- `TRIANGLE_ANGLE_SUM`
- `ADD_AC`
- `EQUILATERAL_TRIANGLE_ALGEBRAIC`
- `ALGEBRAIC_LEMMA`


---

