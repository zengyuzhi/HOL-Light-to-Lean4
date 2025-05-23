# morley.ml

## Overview

Number of statements: 22

The `morley.ml` file formalizes Alain Connes's proof of Morley's theorem. It builds upon concepts from geometry, as indicated by its import of `Multivariate/geom.ml`, and utilizes iterative techniques from `Library/iter.ml`. The file's primary purpose is to provide a formal proof of Morley's theorem, contributing to the library's collection of formalized mathematical results. Its content is centered around the definitions, constructions, and theorems necessary to establish this proof.

## reflect2d

### Name of formal statement
reflect2d

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let reflect2d = new_definition
 `reflect2d t = rotate2d t o cnj o rotate2d(--t)`
```

### Informal statement
The function `reflect2d` is defined as the composition of three operations: a rotation by `t` radians, followed by complex conjugation `cnj`, and then another rotation by `-t` radians.

### Informal sketch
* The definition involves a sequence of geometric transformations in 2D space, specifically rotations and reflection.
* The `rotate2d` function applies a rotation by a given angle `t`.
* Complex conjugation `cnj` is used to reflect a point across the real axis.
* The composition `rotate2d t o cnj o rotate2d(--t)` effectively reflects a point across the line defined by `e^{i t}`.
* This construction relies on the properties of rotations and reflections in the complex plane.

### Mathematical insight
The `reflect2d` function represents a reflection about a line in the complex plane, which is parameterized by the angle `t`. This construction is crucial in geometric and algebraic applications, particularly in the context of Alain Connes's work on Morley's theorem, as indicated by the comment.

### Dependencies
* `rotate2d`
* `cnj`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles function composition and geometric transformations. Specifically, ensure that the rotation and complex conjugation operations are defined and composed correctly, and that the parameter `t` is properly handled as an angle in radians. Additionally, consider the representation of complex numbers and geometric transformations in the target system, as these may differ from HOL Light's implementation.

---

## REFLECT2D_COMPOSE

### Name of formal statement
REFLECT2D_COMPOSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REFLECT2D_COMPOSE = prove
 (`!s t. reflect2d s o reflect2d t = rotate2d (&2 * (s - t))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; reflect2d] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ROTATE2D_COMPLEX; CNJ_CEXP; CNJ_MUL; CNJ_CNJ] THEN
  REWRITE_TAC[CNJ_II; CNJ_CX; CNJ_NEG; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CEXP_ADD] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; CX_MUL] THEN
  AP_TERM_TAC THEN SIMPLE_COMPLEX_ARITH_TAC)
```

### Informal statement
For all `s` and `t`, the composition of `reflect2d s` and `reflect2d t` is equal to `rotate2d` of `2` times the difference between `s` and `t`.

### Informal sketch
* The proof begins by applying `REWRITE_TAC` with `FUN_EQ_THM`, `o_THM`, and `reflect2d` to establish the composition of `reflect2d s` and `reflect2d t`.
* It then applies `REPEAT GEN_TAC` to generalize the variables, followed by `REWRITE_TAC` with various theorems (`ROTATE2D_COMPLEX`, `CNJ_CEXP`, `CNJ_MUL`, `CNJ_CNJ`) to simplify the expression.
* The proof continues with `REWRITE_TAC` using `CNJ_II`, `CNJ_CX`, `CNJ_NEG`, and `COMPLEX_MUL_ASSOC` to further simplify the complex number operations.
* `AP_THM_TAC` and `AP_TERM_TAC` are applied to handle the function application and term manipulation.
* The proof then uses `REWRITE_TAC` with `GSYM CEXP_ADD` and other theorems (`CX_NEG`, `COMPLEX_MUL_LNEG`, `COMPLEX_MUL_RNEG`, `CX_MUL`) to simplify the expression.
* Finally, `AP_TERM_TAC` and `SIMPLE_COMPLEX_ARITH_TAC` are used to complete the proof.

### Mathematical insight
This theorem provides a relationship between the composition of two reflections and a rotation in 2D space. The key idea is that the composition of two reflections over lines `s` and `t` is equivalent to a rotation by an angle that is twice the difference between the angles of the two lines.

### Dependencies
* Theorems:
	+ `FUN_EQ_THM`
	+ `o_THM`
	+ `ROTATE2D_COMPLEX`
	+ `CNJ_CEXP`
	+ `CNJ_MUL`
	+ `CNJ_CNJ`
	+ `CNJ_II`
	+ `CNJ_CX`
	+ `CNJ_NEG`
	+ `COMPLEX_MUL_ASSOC`
	+ `CX_NEG`
	+ `COMPLEX_MUL_LNEG`
	+ `COMPLEX_MUL_RNEG`
	+ `CX_MUL`
* Definitions:
	+ `reflect2d`
	+ `rotate2d`

---

## rotate_about

### Name of formal statement
rotate_about

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rotate_about = new_definition
 `rotate_about a t x = a + rotate2d t (x - a)`
```

### Informal statement
The function `rotate_about` takes three arguments, `a`, `t`, and `x`, and returns the result of adding `a` to the rotation of `x - a` by the angle `t` in a two-dimensional space, as defined by the `rotate2d` function.

### Informal sketch
* The definition of `rotate_about` involves a translation of the point `x` by subtracting `a`, which can be thought of as moving the origin to `a`.
* The translated point is then rotated by the angle `t` using the `rotate2d` function.
* The result of the rotation is then translated back by adding `a`, effectively rotating the original point `x` about the point `a` by the angle `t`.
* The `rotate2d` function is presumed to perform a standard 2D rotation, which can be defined using trigonometric functions.

### Mathematical insight
The `rotate_about` function represents a geometric transformation that rotates a point `x` around a fixed point `a` by a given angle `t`. This is a fundamental operation in geometry and computer graphics, and is often used to describe motions and transformations of objects in 2D space. The definition of `rotate_about` in terms of `rotate2d` provides a concise way to express this transformation using existing geometric primitives.

### Dependencies
* `rotate2d`
 
### Porting notes
When porting this definition to another proof assistant, note that the `rotate2d` function may need to be defined or imported separately, as it is not a standard function in all systems. Additionally, the use of vector or point types may vary between systems, and the `+` and `-` operators may need to be interpreted accordingly.

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
The function `reflect_across` takes two points `a` and `b` and a point `x`, and returns the reflection of `x` across the line defined by `a` and `b`. This is calculated as `a` plus the result of reflecting the vector `x - a` across the line defined by the argument of `b - a`, using the `reflect2d` function.

### Informal sketch
* Define the line of reflection using points `a` and `b`.
* Calculate the vector from `a` to `x`.
* Reflect this vector across the line defined by the argument of `b - a` using `reflect2d`.
* Translate the result back to the original coordinate system by adding `a`.

### Mathematical insight
This definition provides a way to reflect a point across a line defined by two points in a 2D space. The `reflect2d` function is used to perform the actual reflection, and the argument of `b - a` determines the direction of the line. This construction is important in geometry and can be used in various applications such as computer graphics and geometric transformations.

### Dependencies
* `reflect2d`
* `Arg`

### Porting notes
When porting this definition to another proof assistant, note that the `reflect2d` function and the `Arg` function may need to be defined or imported separately. Additionally, the handling of complex numbers and 2D vectors may differ between systems, so care should be taken to ensure that the ported definition behaves correctly in the target system.

---

## REFLECT_ACROSS_COMPOSE

### Name of formal statement
REFLECT_ACROSS_COMPOSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_COMPOSE = prove
 (`!a b c.
        ~(b = a) /\ ~(c = a)
        ==> reflect_across(a,b) o reflect_across(a,c) =
            rotate_about a (&2 * Arg((b - a) / (c - a)))`,
  REPEAT STRIP_TAC THEN
  REPEAT REWRITE_TAC[reflect_across; FUN_EQ_THM; o_THM; rotate_about] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM] REFLECT2D_COMPOSE] THEN
  X_GEN_TAC `x:complex` THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_2; ROTATE2D_ADD] THEN
  ASM_SIMP_TAC[ROTATE2D_SUB_ARG; COMPLEX_SUB_0])
```

### Informal statement
For all points `a`, `b`, and `c` such that `b` is not equal to `a` and `c` is not equal to `a`, the composition of `reflect_across(a, b)` and `reflect_across(a, c)` is equal to `rotate_about a` by an angle of `2 * Arg((b - a) / (c - a))`.

### Informal sketch
* Start with the assumption that `b` and `c` are distinct from `a`.
* Express the composition `reflect_across(a, b) o reflect_across(a, c)` using the definition of function composition.
* Apply the `reflect_across` definition and `FUN_EQ_THM` to simplify the composition.
* Utilize `VECTOR_ARITH` to simplify vector operations, specifically `(a + x) - a = x`.
* Apply `REFLECT2D_COMPOSE` after rewriting with `FUN_EQ_THM` and `o_THM` to relate the composition to rotation.
* Generalize the result for any `x:complex` using `X_GEN_TAC`.
* Apply `AP_TERM_TAC` to simplify the expression under the rotation.
* Simplify further using `REAL_MUL_2` and `ROTATE2D_ADD`.
* Final simplification involves `ASM_SIMP_TAC` with `ROTATE2D_SUB_ARG` and `COMPLEX_SUB_0`.

### Mathematical insight
This theorem provides a relationship between reflecting a point across two different lines (defined by points `a` and `b` and by points `a` and `c`) and rotating about point `a`. The rotation angle is determined by the argument of the complex number representing the ratio of the vectors `b - a` and `c - a`. This relationship is crucial in geometric transformations and understanding how reflections compose in terms of rotations.

### Dependencies
#### Theorems
* `REFLECT2D_COMPOSE`
#### Definitions
* `reflect_across`
* `rotate_about`
* `FUN_EQ_THM`
* `o_THM`
* `VECTOR_ARITH`
* `REAL_MUL_2`
* `ROTATE2D_ADD`
* `ROTATE2D_SUB_ARG`
* `COMPLEX_SUB_0`

---

## REFLECT_ACROSS_COMPOSE_ANGLE

### Name of formal statement
REFLECT_ACROSS_COMPOSE_ANGLE

### Type of the formal statement
Theorem

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
               REAL_SUB_ARG; ARG_LE_PI])
```

### Informal statement
For all points `a`, `b`, and `c`, if `b` is not equal to `a`, `c` is not equal to `a`, and the imaginary part of `(c - a) / (b - a)` is non-negative, then the composition of reflecting across `a` and `c` and reflecting across `a` and `b` is equal to rotating about `a` by twice the angle between `c`, `a`, and `b`.

### Informal sketch
* The proof starts by assuming the conditions `~(b = a)`, `~(c = a)`, and `&0 <= Im((c - a) / (b - a))`.
* It then applies `STRIP_TAC` to strip the quantifiers and `ONCE_REWRITE_TAC` with `ANGLE_SYM` to rewrite the angle expression.
* The `ASM_SIMP_TAC` tactic is used with `REFLECT_ACROSS_COMPOSE`, `angle`, `VECTOR_ANGLE_ARG`, `COMPLEX_SUB_0`, `REAL_SUB_ARG`, and `ARG_LE_PI` to simplify the expression and establish the equality between the composition of reflections and the rotation.
* Key steps involve recognizing the geometric interpretation of reflecting across points and rotating about a point, and using properties of complex numbers to simplify expressions.

### Mathematical insight
This theorem provides a geometric relationship between reflections and rotations in the complex plane. It shows that under certain conditions, composing two reflections across different points is equivalent to rotating about a point by an angle that is twice the angle between the points of reflection. This is a fundamental property in geometry and has applications in various fields, including computer graphics and geometric transformations.

### Dependencies
* `reflect_across`
* `rotate_about`
* `angle`
* `VECTOR_ANGLE_ARG`
* `COMPLEX_SUB_0`
* `REAL_SUB_ARG`
* `ARG_LE_PI`
* `REFLECT_ACROSS_COMPOSE`
* `ANGLE_SYM`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of complex numbers, geometric transformations, and trigonometric functions. The `REFLECT_ACROSS_COMPOSE_ANGLE` theorem relies on properties of complex arithmetic and geometric interpretations, which may be represented differently in other systems. Additionally, the use of `STRIP_TAC`, `ONCE_REWRITE_TAC`, and `ASM_SIMP_TAC` tactics may need to be adapted to the target system's proof scripting language.

---

## REFLECT_ACROSS_COMPOSE_INVOLUTION

### Name of formal statement
REFLECT_ACROSS_COMPOSE_INVOLUTION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_COMPOSE_INVOLUTION = prove
 (`!a b. ~(a = b) ==> reflect_across(a,b) o reflect_across(a,b) = I`,
  SIMP_TAC[REFLECT_ACROSS_COMPOSE; COMPLEX_DIV_REFL; COMPLEX_SUB_0] THEN
  REWRITE_TAC[ARG_NUM; REAL_MUL_RZERO; rotate_about; FUN_EQ_THM] THEN
  REWRITE_TAC[ROTATE2D_ZERO; I_THM] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC)
```

### Informal statement
For all points `a` and `b`, if `a` is not equal to `b`, then the composition of `reflect_across(a, b)` with itself is equal to the identity function `I`.

### Informal sketch
* The proof starts by assuming `a` and `b` are distinct points.
* It then applies various simplification and rewriting steps using `SIMP_TAC`, `REWRITE_TAC`, and `VECTOR_ARITH_TAC` to manipulate the expression `reflect_across(a, b) o reflect_across(a, b)`.
* Key steps involve using the `REFLECT_ACROSS_COMPOSE` and `FUN_EQ_THM` theorems to simplify the composition, as well as applying properties of complex numbers and vector arithmetic.
* The proof ultimately shows that the composition of `reflect_across(a, b)` with itself simplifies to the identity function `I`.

### Mathematical insight
This theorem provides insight into the properties of reflections across lines defined by two points `a` and `b`. Specifically, it shows that reflecting a point twice across the same line returns the point to its original position, which is a fundamental property of geometric transformations.

### Dependencies
#### Theorems
* `REFLECT_ACROSS_COMPOSE`
* `COMPLEX_DIV_REFL`
* `COMPLEX_SUB_0`
* `ARG_NUM`
* `REAL_MUL_RZERO`
* `rotate_about`
* `FUN_EQ_THM`
* `ROTATE2D_ZERO`
* `I_THM`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of function composition, equality, and geometric transformations. The `reflect_across` function and its properties may need to be defined or imported from a relevant library. Additionally, the use of `SIMP_TAC` and `REWRITE_TAC` tactics may be replaced with equivalent simplification and rewriting mechanisms in the target system.

---

## REFLECT_ACROSS_SYM

### Name of formal statement
REFLECT_ACROSS_SYM

### Type of the formal statement
Theorem

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
    ASM_REWRITE_TAC[COMPLEX_NORM_ZERO; COMPLEX_SUB_0]])
```

### Informal statement
For all complex numbers `a` and `b`, the reflection of `a` across `b` is equal to the reflection of `b` across `a`. This statement is expressed using the `reflect_across` function, which is proven to be symmetric.

### Informal sketch
* The proof starts by considering the case where `a` equals `b`, and then proceeds with the case where `a` is not equal to `b`.
* It applies various rewrite rules, including `FUN_EQ_THM`, `reflect_across`, `reflect2d`, and `o_THM`, to simplify the expression.
* The proof then uses `SUBGOAL_THEN` to establish two equations involving `cexp` and `Cx`, and then uses `CONJUNCTS_THEN` and `SUBST1_TAC` to substitute these equations into the main proof.
* The proof also employs `MATCH_MP_TAC` with `COMPLEX_FIELD` and `COMPLEX_RING` to derive further equalities.
* Key steps involve using properties of complex numbers, such as `CNJ_CEXP`, `CNJ_MUL`, `CNJ_CX`, and `CNJ_II`, as well as `ROTATE2D_COMPLEX` and `CX_NEG`.
* The proof concludes by applying `ASM_REWRITE_TAC` with various theorems, including `COMPLEX_NORM_ZERO` and `COMPLEX_SUB_0`.

### Mathematical insight
This theorem provides a fundamental property of the `reflect_across` function, which is crucial in geometric and algebraic manipulations involving complex numbers. The symmetry property established by this theorem has significant implications in various mathematical contexts, including geometry, algebra, and analysis.

### Dependencies
* Theorems:
	+ `COMPLEX_FIELD`
	+ `COMPLEX_RING`
	+ `FUN_EQ_THM`
	+ `reflect_across`
	+ `reflect2d`
	+ `o_THM`
	+ `ROTATE2D_COMPLEX`
	+ `CNJ_CEXP`
	+ `CNJ_MUL`
	+ `CNJ_CX`
	+ `CNJ_II`
	+ `CX_NEG`
	+ `COMPLEX_NORM_ZERO`
	+ `COMPLEX_SUB_0`
* Definitions:
	+ `reflect_across`
	+ `reflect2d`
	+ `cexp`
	+ `Cx`
	+ `Arg`
	+ `norm`
	+ `complex_div`

---

## ITER_ROTATE_ABOUT

### Name of formal statement
ITER_ROTATE_ABOUT

### Type of the formal statement
Theorem

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
  REWRITE_TAC[rotate_about; REAL_MUL_LID] THEN VECTOR_ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, points `a`, and vectors `t`, the `n`-fold iteration of rotating about `a` by `t` is equal to rotating about `a` by `n` times `t`.

### Informal sketch
* The proof starts by applying `REWRITE_TAC` with `FUN_EQ_THM` and `rotate_about` to establish the equality of the iterated rotation and the single rotation by `n * t`.
* It then applies `REWRITE_TAC` with a vector arithmetic rule to simplify the expression.
* The proof proceeds by induction using `INDUCT_TAC`, followed by rewriting with `ITER_ALT`, `REAL_MUL_LZERO`, and `ROTATE2D_ZERO` to handle the base case and the inductive step.
* Further rewriting is done using `VECTOR_ARITH` and `GSYM REAL_OF_NUM_SUC` to simplify the expression.
* The proof then applies `ASM_REWRITE_TAC` with `REAL_ADD_RDISTRIB` and `ROTATE2D_ADD` to rearrange terms.
* Finally, it uses `REPEAT GEN_TAC`, `AP_TERM_TAC`, and `VECTOR_ARITH_TAC` to complete the proof.

### Mathematical insight
This theorem provides a key property of iterated rotations, showing that repeating a rotation `n` times is equivalent to a single rotation by `n` times the original angle. This is a fundamental result in geometry and has applications in various fields, including computer graphics and robotics.

### Dependencies
* Theorems:
	+ `FUN_EQ_THM`
	+ `VECTOR_ARITH`
	+ `ITER_ALT`
	+ `REAL_MUL_LZERO`
	+ `ROTATE2D_ZERO`
	+ `REAL_ADD_RDISTRIB`
	+ `ROTATE2D_ADD`
* Definitions:
	+ `rotate_about`
	+ `ITER`
* Inductive rules:
	+ `INDUCT_TAC` 

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of vector arithmetic and the `ITER` function, as these may be represented differently. Additionally, the use of `REWRITE_TAC` and `ASM_REWRITE_TAC` may need to be adapted to the target system's rewriting mechanisms.

---

## REAL_LE_IM_DIV_CYCLIC

### Name of formal statement
REAL_LE_IM_DIV_CYCLIC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REAL_LE_IM_DIV_CYCLIC = prove
 (`!a b c. &0 <= Im ((c - a) / (b - a)) <=> &0 <= Im((a - b) / (c - b))`,
  REWRITE_TAC[IM_COMPLEX_DIV_GE_0] THEN
  REWRITE_TAC[complex_mul; IM; IM_SUB; RE_SUB; IM_CNJ; CNJ_SUB; RE_CNJ] THEN
  REAL_ARITH_TAC)
```

### Informal statement
For all complex numbers $a$, $b$, and $c$, the following equivalence holds: the imaginary part of $\frac{c - a}{b - a}$ is non-negative if and only if the imaginary part of $\frac{a - b}{c - b}$ is non-negative.

### Informal sketch
* The proof starts with the given statement and applies `REWRITE_TAC` with `IM_COMPLEX_DIV_GE_0` to transform the expression involving imaginary parts.
* It then applies `REWRITE_TAC` again with several definitions and properties related to complex numbers, including `complex_mul`, `IM`, `IM_SUB`, `RE_SUB`, `IM_CNJ`, `CNJ_SUB`, and `RE_CNJ`, to further simplify the expressions.
* Finally, it uses `REAL_ARITH_TAC` to complete the proof, which likely involves basic properties of real arithmetic.

### Mathematical insight
This theorem provides an equivalence between two conditions involving the imaginary parts of fractions of complex numbers. The key idea is to show that the sign of the imaginary part of a fraction is preserved under a specific transformation of the numerator and denominator. This is likely useful in various contexts involving complex analysis or geometry.

### Dependencies
* Theorems and definitions:
	+ `IM_COMPLEX_DIV_GE_0`
	+ `complex_mul`
	+ `IM`
	+ `IM_SUB`
	+ `RE_SUB`
	+ `IM_CNJ`
	+ `CNJ_SUB`
	+ `RE_CNJ`
* Tactics:
	+ `REWRITE_TAC`
	+ `REAL_ARITH_TAC`

### Porting notes
When translating this theorem into another proof assistant, pay attention to the handling of complex numbers and their properties. The `REWRITE_TAC` steps may need to be replaced with equivalent rewriting mechanisms, and the `REAL_ARITH_TAC` step may require a different tactic or set of tactics to complete the proof. Additionally, the definitions and properties of complex numbers, such as `IM` and `RE`, may need to be defined or imported from a relevant library.

---

## ROTATE_ABOUT_INVERT

### Name of formal statement
ROTATE_ABOUT_INVERT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ROTATE_ABOUT_INVERT = prove
 (`rotate_about a t w = z <=> w = rotate_about a (--t) z`,
  MATCH_MP_TAC(MESON[]
   `(!x. f(g x) = x) /\ (!y. g(f y) = y)
    ==> (f x = y <=> x = g y)`) THEN
  REWRITE_TAC[rotate_about; VECTOR_ADD_SUB; GSYM ROTATE2D_ADD] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_RINV] THEN
  REWRITE_TAC[ROTATE2D_ZERO] THEN VECTOR_ARITH_TAC)
```

### Informal statement
The theorem `ROTATE_ABOUT_INVERT` states that for any `a`, `t`, `w`, and `z`, the equation `rotate_about a t w = z` is logically equivalent to `w = rotate_about a (--t) z`. This equivalence is established under the assumption that certain properties of functions `f` and `g` hold, specifically that `f` and `g` are inverses of each other.

### Informal sketch
* The proof begins with the application of `MATCH_MP_TAC` to establish a relationship between two expressions based on the properties of inverse functions `f` and `g`.
* It then proceeds to rewrite the `rotate_about` function using several theorems: `VECTOR_ADD_SUB`, `GSYM ROTATE2D_ADD`, `REAL_ADD_LINV`, `REAL_ADD_RINV`, and `ROTATE2D_ZERO`.
* The `VECTOR_ARITH_TAC` tactic is used to perform vector arithmetic manipulations.
* The key steps involve manipulating the `rotate_about` function to show the equivalence between the original equation and its inverted form, leveraging properties of vector addition and the behavior of the `rotate_about` function under negation of its second argument.

### Mathematical insight
This theorem provides insight into the behavior of rotations in a geometric or spatial context, showing how a rotation by an angle `t` about a point `a` can be related to a rotation by the negation of that angle `--t`. It leverages the concept of inverse functions and properties of vector operations to establish this relationship, which is fundamental in understanding geometric transformations and their representations in mathematical models.

### Dependencies
* `rotate_about`
* `VECTOR_ADD_SUB`
* `GSYM ROTATE2D_ADD`
* `REAL_ADD_LINV`
* `REAL_ADD_RINV`
* `ROTATE2D_ZERO`
* `MATCH_MP_TAC`
* `MESON`
* `VECTOR_ARITH_TAC`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to the handling of vector arithmetic and the properties of rotations. The `MATCH_MP_TAC` and `VECTOR_ARITH_TAC` tactics may have direct analogs in other systems, but the specific implementation of `rotate_about` and related theorems like `ROTATE2D_ADD` and `ROTATE2D_ZERO` will need to be carefully ported. Additionally, the representation of inverse functions and their properties as used in the `MESON` call may require adaptation to the target system's logic and tactic language.

---

## ROTATE_EQ_REFLECT_LEMMA

### Name of formal statement
ROTATE_EQ_REFLECT_LEMMA

### Type of the formal statement
Theorem

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
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC)
```

### Informal statement
For all complex numbers `a`, `b`, and `z`, and for all real numbers `t`, if `b` is not equal to `a` and twice the argument of `(b - a) / (z - a)` equals `t`, then rotating `z` about `a` by `t` is equivalent to reflecting `z` across the line defined by `a` and `b`.

### Informal sketch
* The proof begins by assuming the conditions `~(b = a)` and `&2 * Arg((b - a) / (z - a)) = t`.
* It then applies various simplifications and transformations using `REWRITE_TAC` to express `rotate_about a t z` and `reflect_across (a,b) z` in terms of complex arithmetic operations.
* The proof proceeds by case analysis on whether `z` equals `a`, handling the case where `z = a` separately.
* For `z ≠ a`, it applies properties of complex numbers, including `COMPLEX_RING` and `CNJ_MUL`, to establish the desired equality between rotation and reflection.
* Key steps involve using `MATCH_MP_TAC` to apply specific theorems about complex numbers and `GEN_REWRITE_TAC` to handle the argument function `ARG`.
* The proof concludes by demonstrating the equivalence through a series of simplifications and arithmetic manipulations, including the use of `REAL_ARITH_TAC` for real number arithmetic.

### Mathematical insight
This theorem provides a geometric insight into the relationship between rotations and reflections in the complex plane. It shows that under certain conditions, rotating a point about another point by a specific angle is equivalent to reflecting the point across a line defined by two points. This relationship is fundamental in geometry and has implications for various geometric transformations and symmetries.

### Dependencies
* Theorems:
  + `COMPLEX_RING`
  + `CNJ_MUL`
  + `COMPLEX_MUL_ASSOC`
  + `CNJ_CEXP`
  + `CNJ_II`
  + `COMPLEX_MUL_LNEG`
  + `COMPLEX_MUL_RNEG`
  + `COMPLEX_NEG_NEG`
  + `GSYM CEXP_ADD`
  + `CX_NEG`
  + `COMPLEX_RING`
  + `ARG`
* Definitions:
  + `rotate_about`
  + `reflect_across`
  + `ROTATE2D_COMPLEX`
  + `reflect2d`
  + `o_THM`
  + `CNJ_CX`
  + `COMPLEX_SUB_REFL`
  + `CX_INJ`
  + `REAL_SUB_ARG`
  + `COMPLEX_SUB_0`
  + `INTEGER_CLOSED`

---

## ROTATE_EQ_REFLECT_PI_LEMMA

### Name of formal statement
ROTATE_EQ_REFLECT_PI_LEMMA

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_MUL_LID])
```

### Informal statement
For all points `a`, `b`, and `z`, and for all real numbers `t`, if `b` is not equal to `a` and twice the argument of the complex number `(b - a) / (z - a)` equals `4 * pi + t`, then rotating `z` about `a` by `t` is equivalent to reflecting `z` across the line passing through `a` and `b`.

### Informal sketch
* The proof starts by applying `REWRITE_TAC` to transform the equation `&2 * Arg((b - a) / (z - a)) = &4 * pi + t` into a more convenient form.
* It then proceeds to apply `REPEAT STRIP_TAC` and `ASM_REWRITE_TAC` to simplify the assumptions.
* The `MATCH_MP_TAC EQ_TRANS` tactic is used to introduce an intermediate term, `rotate_about a (&2 * Arg((b - a) / (z - a))) z`, to facilitate the proof.
* The `CONJ_TAC` and `THENL` tactics are used to split the proof into two parts, with the first part using `ALL_TAC` and the second part applying `MATCH_MP_TAC ROTATE_EQ_REFLECT_LEMMA`.
* The proof then applies several `REWRITE_TAC` steps to simplify the expression, using various definitions and properties such as `rotate_about`, `ROTATE2D_ADD`, `ROTATE2D_COMPLEX`, `EULER`, `RE_MUL_II`, `IM_MUL_II`, `RE_CX`, `IM_CX`, `COS_NEG`, `SIN_NEG`, `SIN_NPI`, `COS_NPI`, `REAL_EXP_NEG`, `REAL_EXP_0`, `CX_NEG`, `COMPLEX_NEG_0`, `COMPLEX_MUL_RZERO`, and `COMPLEX_ADD_RID`.
* Finally, the proof applies `CONV_TAC REAL_RAT_REDUCE_CONV` and `REWRITE_TAC[COMPLEX_MUL_LID]` to conclude the proof.

### Mathematical insight
This theorem provides a relationship between rotating a point `z` about another point `a` by an angle `t` and reflecting `z` across the line passing through `a` and `b`. The condition `&2 * Arg((b - a) / (z - a)) = &4 * pi + t` ensures that the rotation and reflection are equivalent. This theorem is likely used in geometric or trigonometric contexts where rotations and reflections are involved.

### Dependencies
#### Theorems
* `ROTATE_EQ_REFLECT_LEMMA`
#### Definitions
* `rotate_about`
* `reflect_across`
* `ROTATE2D_ADD`
* `ROTATE2D_COMPLEX`
* `EULER`
* `RE_MUL_II`
* `IM_MUL_II`
* `RE_CX`
* `IM_CX`
* `COS_NEG`
* `SIN_NEG`
* `SIN_NPI`
* `COS_NPI`
* `REAL_EXP_NEG`
* `REAL_EXP_0`
* `CX_NEG`
* `COMPLEX_NEG_0`
* `COMPLEX_MUL_RZERO`
* `COMPLEX_ADD_RID`
* `COMPLEX_MUL_LID`

---

## EQUILATERAL_TRIANGLE_ALGEBRAIC

### Name of formal statement
EQUILATERAL_TRIANGLE_ALGEBRAIC

### Type of the formal statement
Theorem

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
  REAL_ARITH_TAC)
```

### Informal statement
For all complex numbers $A$, $B$, $C$, and $j$, if $j$ cubed equals $1$ and $j$ is not equal to $1$, and the equation $A + jB + j^2C = 0$ holds, then the distance between $A$ and $B$ is equal to the distance between $B$ and $C$, and the distance between $C$ and $A$ is equal to the distance between $B$ and $C$.

### Informal sketch
* The proof starts by assuming the given conditions: $j^3 = 1$, $j \neq 1$, and $A + jB + j^2C = 0$.
* It then uses the `REWRITE_TAC[dist]` tactic to express distances in terms of complex number operations.
* The `SUBGOAL_THEN` tactic is used to derive two key equalities: $C - A = j(B - C)$ and $A - B = j^2(B - C)$.
* These equalities are then used to show that the distances between the points are equal, leveraging properties of complex numbers and their norms, including `COMPLEX_NORM_CX`, `COMPLEX_NORM_POW`, and `REAL_POW_EQ_1`.
* The proof concludes by applying `REAL_ARITH_TAC` to finalize the equality of distances.

### Mathematical insight
This theorem provides an algebraic characterization of equilateral triangles in the complex plane. It shows that if three points $A$, $B$, and $C$ satisfy a specific algebraic condition involving a complex number $j$ (a cube root of unity), then these points form an equilateral triangle. The condition $j^3 = 1$ and $j \neq 1$ ensures that $j$ is a non-real cube root of unity, which is crucial for the equilateral nature of the triangle.

### Dependencies
* `COMPLEX_NORM_CX`
* `COMPLEX_NORM_POW`
* `REAL_POW_EQ_1`
* `REAL_ABS_NUM`
* `REAL_ABS_NORM`
* `COMPLEX_NORM_MUL`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to the handling of complex numbers and their properties. The use of `REWRITE_TAC` and `SUBGOAL_THEN` tactics may need to be adapted based on the target system's capabilities for rewriting and subgoal management. Additionally, the representation of distances and norms may vary, requiring adjustments to the proof script to match the target system's conventions.

---

## AFFINE_GROUP_ITER_3

### Name of formal statement
AFFINE_GROUP_ITER_3

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AFFINE_GROUP_ITER_3 = prove
 (`ITER 3 (\z. a * z + b) = (\z. a pow 3 * z + b * (Cx(&1) + a + a pow 2))`,
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `3`] THEN
  REWRITE_TAC[ITER; FUN_EQ_THM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC COMPLEX_RING)
```

### Informal statement
The theorem `AFFINE_GROUP_ITER_3` states that for any complex numbers `a` and `b`, and any complex number `z`, the following equation holds: `ITER 3 (\z. a * z + b) = (\z. a pow 3 * z + b * (1 + a + a pow 2))`. This equation describes the result of applying the function `(\z. a * z + b)` three times iteratively, starting with `z`, and equates it to a specific closed-form expression involving powers of `a` and additions with `b`.

### Informal sketch
* The proof begins by applying `REWRITE_TAC` with `TOP_DEPTH_CONV num_CONV 3` to potentially simplify or normalize the expression involving `ITER 3`.
* It then applies `REWRITE_TAC` with `ITER` and `FUN_EQ_THM` to expand or manipulate the iterative application of the function `(\z. a * z + b)`.
* Next, `CONV_TAC NUM_REDUCE_CONV` is used to simplify numerical parts of the expression, if applicable.
* Finally, `CONV_TAC COMPLEX_RING` is applied to handle any complex number arithmetic, ensuring that the equality holds in the context of complex numbers.
* The key steps involve recognizing the expansion of `ITER 3` and simplifying the resulting expression to match the given closed form.

### Mathematical insight
This theorem provides a foundational result about the iterative application of affine transformations (of the form `z |-> a * z + b`) in the complex plane. It shows how repeated applications of such a transformation can be simplified into a single, more manageable expression. This is crucial in various mathematical contexts, including dynamical systems, where understanding the behavior of iterated functions is essential.

### Dependencies
* `ITER`
* `FUN_EQ_THM`
* `COMPLEX_RING`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how iterative functions and complex number arithmetic are handled. Specifically, ensure that the target system can express the `ITER` function and manipulate complex numbers as required. Additionally, the use of `REWRITE_TAC`, `CONV_TAC`, and specific conversion tactics may need to be adapted to the target system's tactic language and automation capabilities.

---

## AFFINE_GROUP_COMPOSE

### Name of formal statement
AFFINE_GROUP_COMPOSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AFFINE_GROUP_COMPOSE = prove
 (`(\z. a1 * z + b1) o (\z. a2 * z + b2) =
   (\z. (a1 * a2) * z + (b1 + a1 * b2))`,
  REWRITE_TAC[o_THM; FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;
```

### Informal statement
For all `a1`, `b1`, `a2`, and `b2`, the composition of the functions `(\z. a1 * z + b1)` and `(\z. a2 * z + b2)` is equal to the function `(\z. (a1 * a2) * z + (b1 + a1 * b2))`.

### Informal sketch
* The proof involves showing that the composition of two affine functions is also an affine function.
* The `REWRITE_TAC` tactic is used with `o_THM` and `FUN_EQ_THM` to rewrite the composition of functions and apply the definition of function equality.
* The `CONV_TAC COMPLEX_RING` tactic is then applied to simplify the expression using the properties of complex numbers.

### Mathematical insight
This theorem is important because it describes how affine transformations can be composed. Affine transformations are used in many areas of mathematics and computer science, such as linear algebra, geometry, and computer graphics. The theorem provides a way to simplify the composition of multiple affine transformations, which can be useful in a variety of applications.

### Dependencies
* `o_THM`
* `FUN_EQ_THM`
* `COMPLEX_RING`

### Porting notes
When porting this theorem to another proof assistant, note that the `REWRITE_TAC` and `CONV_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `COMPLEX_RING` theory may need to be replaced with a similar theory in the target system. The use of `o_THM` and `FUN_EQ_THM` may also require special handling, as they are specific to HOL Light's handling of function composition and equality.

---

## AFFINE_GROUP_I

### Name of formal statement
AFFINE_GROUP_I

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AFFINE_GROUP_I = prove
 (`I = (\z. Cx(&1) * z + Cx(&0))`,
  REWRITE_TAC[I_THM; FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;
```

### Informal statement
The identity function `I` is equal to the function that takes any complex number `z` and returns the result of multiplying `z` by the complex number 1 and then adding the complex number 0.

### Informal sketch
* The proof involves showing that the identity function `I` can be expressed as a specific affine transformation.
* The transformation is defined as `(\z. Cx(&1) * z + Cx(&0))`, which multiplies the input `z` by 1 and adds 0.
* The `REWRITE_TAC` tactic is used with `I_THM` and `FUN_EQ_THM` to rewrite the equation and establish the equality of the two functions.
* The `CONV_TAC` tactic with `COMPLEX_RING` is then applied to complete the proof by ensuring the equation holds in the context of complex numbers.

### Mathematical insight
This theorem provides a fundamental property of the identity function in the context of affine transformations over complex numbers. It shows that the identity function can be represented as a simple affine transformation, which is a basic building block in linear algebra and geometry. This property is essential for various mathematical constructions and proofs involving affine transformations.

### Dependencies
* Theorems:
  + `I_THM`
  + `FUN_EQ_THM`
* Definitions:
  + `Cx`
* Other:
  + `COMPLEX_RING`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles function equality (`FUN_EQ_THM`) and complex number arithmetic (`COMPLEX_RING`). Additionally, ensure that the identity function `I` and the affine transformation are defined and handled correctly in the target system. The use of `REWRITE_TAC` and `CONV_TAC` may need to be adapted based on the specific tactics and automation available in the target proof assistant.

---

## AFFINE_GROUP_EQ

### Name of formal statement
AFFINE_GROUP_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AFFINE_GROUP_EQ = prove
 (`!a b a' b. (\z. a * z + b) = (\z. a' * z + b') <=> a = a' /\ b = b'`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&1)`) THEN
  CONV_TAC COMPLEX_RING)
```

### Informal statement
For all complex numbers $a$, $b$, $a'$, and $b'$, the functions $f(z) = az + b$ and $g(z) = a'z + b'$ are equal if and only if $a = a'$ and $b = b'$.

### Informal sketch
* The proof starts by assuming the equality of the two functions $f(z) = az + b$ and $g(z) = a'z + b'$.
* It then applies the `FUN_EQ_THM` theorem to simplify the equality of functions to an equality of their outputs for all inputs.
* The proof proceeds by substituting specific values for $z$, namely $0$ and $1$, to derive equations involving $a$, $b$, $a'$, and $b'$.
* By using these substitutions, it aims to show that $a = a'$ and $b = b'$, thus establishing the "only if" direction of the equivalence.
* The "if" direction, where $a = a'$ and $b = b'$ imply the equality of the functions, is straightforward and follows from the definition of function equality.
* Key HOL Light terms involved include `EQ_TAC` for equality reasoning, `SIMP_TAC` for simplification, and `CONV_TAC` for converting between different representations of terms.

### Mathematical insight
This theorem provides a fundamental property of affine functions over the complex numbers, stating that two such functions are equal if and only if their slopes ($a$ and $a'$) and y-intercepts ($b$ and $b'$) are respectively equal. This is crucial in algebra and analysis for identifying and working with linear transformations.

### Dependencies
* `FUN_EQ_THM`: A theorem about the equality of functions, stating that two functions are equal if and only if they have the same output for all inputs.
* `COMPLEX_RING`: A theory or set of theorems and definitions related to the ring of complex numbers, which provides the backdrop for the arithmetic operations involved.

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles function equality and complex arithmetic. Specifically, ensure that the equivalent of `FUN_EQ_THM` is applied correctly and that the complex ring properties are appropriately utilized. Differences in tactic languages and automation levels may require adjustments to the proof strategy, particularly in how the `EQ_TAC`, `SIMP_TAC`, and `CONV_TAC` tactics are translated or replicated.

---

## AFFINE_GROUP_ROTATE_ABOUT

### Name of formal statement
AFFINE_GROUP_ROTATE_ABOUT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AFFINE_GROUP_ROTATE_ABOUT = prove
 (`!a t. rotate_about a t =
         (\z. cexp(ii * Cx(t)) * z + (Cx(&1) - cexp(ii * Cx(t))) * a)`,
  REWRITE_TAC[rotate_about; FUN_EQ_THM; ROTATE2D_COMPLEX] THEN
  CONV_TAC COMPLEX_RING)
```

### Informal statement
For all points `a` and all values `t`, the function `rotate_about a t` is equal to the function that takes any point `z` and maps it to the point resulting from scaling `z` by the complex exponential of `ii` times the complex part of `t`, and then adding to it the result of scaling `a` by the difference between 1 (considered as a complex number) and the complex exponential of `ii` times the complex part of `t`.

### Informal sketch
* The proof starts by applying the `REWRITE_TAC` tactic to rewrite the `rotate_about` function using its definition, as well as applying `FUN_EQ_THM` to equate the two functions, and utilizing `ROTATE2D_COMPLEX` to handle the complex number operations.
* The `CONV_TAC COMPLEX_RING` tactic is then applied to convert the expression into a form that can be directly compared, using the properties of complex numbers.
* The main logical stages involve:
  + Establishing the definition of `rotate_about` and its equivalence to the given complex expression
  + Applying relevant theorems and definitions (`rotate_about`, `FUN_EQ_THM`, `ROTATE2D_COMPLEX`) to transform the expression
  + Using the properties of complex numbers (`cexp`, `Cx`, `ii`) to simplify and prove the equivalence

### Mathematical insight
This theorem provides a mathematical formulation for rotating a point around another point in a 2D space, using complex numbers to represent points and operations. The rotation is parameterized by `t`, which determines the angle of rotation, and `a`, which is the point of rotation. The theorem is important because it establishes a fundamental geometric transformation in terms of complex arithmetic, facilitating further reasoning about geometric and algebraic properties of rotations in the context of affine groups.

### Dependencies
* Theorems:
  + `rotate_about`
  + `FUN_EQ_THM`
  + `ROTATE2D_COMPLEX`
* Definitions:
  + `cexp`
  + `Cx`
  + `ii`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of complex numbers and the `rotate_about` function. The representation of complex numbers and the implementation of `cexp`, `Cx`, and `ii` might differ between systems. Additionally, the tactic structure, especially the use of `REWRITE_TAC` and `CONV_TAC`, may need to be adapted to the target system's proof scripting language and automation capabilities.

---

## ALGEBRAIC_LEMMA

### Name of formal statement
ALGEBRAIC_LEMMA

### Type of the formal statement
Theorem

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
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD)
```

### Informal statement
For all `a1`, `a2`, `a3`, `b1`, `b2`, `b3`, `A`, `B`, `C`, if the following conditions hold:
- `(\z. a3 * z + b3) ((\z. a1 * z + b1) B) = B`
- `(\z. a1 * z + b1) ((\z. a2 * z + b2) C) = C`
- `(\z. a2 * z + b2) ((\z. a3 * z + b3) A) = A`
- `ITER 3 (\z. a1 * z + b1) o ITER 3 (\z. a2 * z + b2) o ITER 3 (\z. a3 * z + b3) = I`
- `a1 * a2 * a3` is not equal to `Cx(&1)`
- `a1 * a2` is not equal to `Cx(&1)`
- `a2 * a3` is not equal to `Cx(&1)`
- `a3 * a1` is not equal to `Cx(&1)`
Then the following conclusions hold:
- `(a1 * a2 * a3) pow 3 = Cx (&1)`
- `a1 * a2 * a3` is not equal to `Cx (&1)`
- `C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B = Cx(&0)`

### Informal sketch
The proof involves several key steps:
* Applying `REWRITE_TAC` with various theorems related to affine groups to simplify the initial conditions.
* Using `GEN_TAC` and `STRIP_TAC` to manage the assumptions and conclusions.
* Employing `CONJ_TAC` to split the conclusion into parts for separate treatment.
* Utilizing `SUBGOAL_THEN` to derive an intermediate result involving products of terms like `(a1 - a1 * a2 * a3)` and `(C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B) = Cx(&0)`.
* Applying `MATCH_MP` with `COMPLEX_FIELD` and `COMPLEX_RING` to derive further equalities and simplify expressions.
The main logical stages involve manipulating the given conditions to derive the conclusions through a series of algebraic manipulations and applications of field and ring properties.

### Mathematical insight
This theorem appears to be related to properties of affine transformations and their compositions, particularly in the context of complex numbers. The conditions and conclusions involve specific algebraic relationships between the coefficients of these transformations and their iterates, suggesting a deep connection to the structure of the group of affine transformations over the complex numbers. The theorem may be crucial in establishing properties of these transformations, such as their behavior under iteration or composition, which could have implications in areas like geometry, algebra, or dynamical systems.

### Dependencies
#### Theorems
* `AFFINE_GROUP_ITER_3`
* `AFFINE_GROUP_COMPOSE`
* `AFFINE_GROUP_I`
* `AFFINE_GROUP_EQ`
* `COMPLEX_FIELD`
* `COMPLEX_RING`
* `COMPLEX_MUL_SYM`
* `COMPLEX_ENTIRE`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to the handling of complex numbers, affine transformations, and their compositions. The `REWRITE_TAC`, `GEN_TAC`, `STRIP_TAC`, `CONJ_TAC`, and `SUBGOAL_THEN` tactics may have direct analogs in other systems, but their application and the specific theorems used (`AFFINE_GROUP_ITER_3`, `COMPLEX_FIELD`, etc.) will need to be carefully translated. Additionally, the use of `MATCH_MP` and the manipulation of assumptions and conclusions may require adjustments due to differences in how these operations are handled in the target system.

---

## CYCLIC_PERM_SUBGOAL_THEN

### Name of formal statement
CYCLIC_PERM_SUBGOAL_THEN

### Type of the formal statement
Theorem

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
           DISCH_THEN(CONJUNCTS_THEN ttac)]]) (asl,w)
```

### Informal statement
For all complex numbers `A`, `B`, `C`, `P`, `Q`, `R`, and real numbers `a`, `b`, `c`, and functions `g1`, `g2`, `g3` from complex to complex, if `Ant A B C P Q R a b c g1 g2 g3` implies `Cns A B C P Q R a b c g1 g2 g3`, and `Ant A B C P Q R a b c g1 g2 g3` implies `Ant B C A Q R P b c a g2 g3 g1`, then `Ant A B C P Q R a b c g1 g2 g3` implies `Cns A B C P Q R a b c g1 g2 g3` and `Cns B C A Q R P b c a g2 g3 g1` and `Cns C A B R P Q c a b g3 g1 g2`.

### Informal sketch
* The theorem `CYCLIC_PERM_SUBGOAL_THEN` is proved using the `MESON` tactic, which applies a set of inference rules to derive the conclusion.
* The proof involves assuming certain antecedents (`Ant`) and consequents (`Cns`) relationships between complex numbers and functions, and then using these assumptions to derive the desired conclusion.
* The `MATCH_MP` tactic is used to apply the lemma to the assumption `gnw`, which is a universally quantified implication.
* The `REWRITE_CONV` tactic is used to rewrite the conclusion of the lemma using certain equalities and properties of conjunction and implication.
* The `DISCH_ALL` and `MP_TAC` tactics are used to discharge assumptions and apply modus ponens to derive the final conclusion.
* The `ANTS_TAC` tactic is used to apply a set of tactics to each subgoal, including `POP_ASSUM_LIST`, `GEN_TAC`, `STRIP_TAC`, `DISCH_THEN`, and `CONJUNCTS_THEN`.

### Mathematical insight
The theorem `CYCLIC_PERM_SUBGOAL_THEN` appears to be a technical result used to avoid duplication in proofs involving cyclic permutations of complex numbers and functions. It provides a way to derive a conclusion about the relationships between these objects by assuming certain antecedents and consequents relationships.

### Dependencies
* `MESON`
* `MATCH_MP`
* `REWRITE_CONV`
* `DISCH_ALL`
* `MP_TAC`
* `ANTS_TAC`
* `POP_ASSUM_LIST`
* `GEN_TAC`
* `STRIP_TAC`
* `DISCH_THEN`
* `CONJUNCTS_THEN`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to preserve the exact relationships between the complex numbers and functions, as well as the specific tactics used in the proof. The `MESON` tactic may need to be replaced with a similar tactic or set of inference rules in the target system. Additionally, the `REWRITE_CONV` tactic may need to be modified to accommodate differences in the way equalities and properties are handled in the target system.

---

## MORLEY

### Name of formal statement
MORLEY

### Type of the formal statement
Theorem

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
  PURE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[]
```

### Informal statement
For all points `A`, `B`, and `C` in the real plane, and for all points `P`, `Q`, and `R` in the convex hull of `A`, `B`, and `C`, if `A`, `B`, and `C` are not collinear and the following conditions are met:
- `angle(A, B, R) = angle(A, B, C) / 3`
- `angle(B, A, R) = angle(B, A, C) / 3`
- `angle(B, C, P) = angle(B, C, A) / 3`
- `angle(C, B, P) = angle(C, B, A) / 3`
- `angle(C, A, Q) = angle(C, A, B) / 3`
- `angle(A, C, Q) = angle(A, C, B) / 3`
then `dist(R, P) = dist(P, Q)` and `dist(Q, R) = dist(P, Q)`.

### Informal sketch
* The proof begins by assuming the conditions given in the theorem statement and then proceeds through several logical stages:
  * It first establishes that `A`, `B`, and `C` cannot be collinear, which is crucial for the subsequent geometric constructions.
  * It then defines several rotations (`g1`, `g2`, `g3`) around points `A`, `B`, and `C`, respectively, by angles that are fractions of the angles formed by the lines connecting these points.
  * The proof leverages the properties of these rotations and their compositions to establish the desired equalities of distances.
  * Key steps involve showing that certain points are fixed under specific compositions of these rotations, leveraging properties of reflections and rotations in the plane.
  * The use of `cexp` (complex exponential function) and its properties plays a significant role in demonstrating the relationships between these rotations and the geometric conditions given in the theorem.
* The proof concludes by applying specific lemmas (`EQUILATERAL_TRIANGLE_ALGEBRAIC` and `ALGEBRAIC_LEMMA`) to derive the final equalities of distances, thus proving the theorem.

### Mathematical insight
This theorem, known as Morley's theorem, is a statement about the geometry of triangles and the properties of certain constructions involving angles and distances within those triangles. It's a deep result in geometry that has significant implications for the understanding of geometric structures and their symmetries. The formal proof provided leverages advanced geometric and algebraic concepts, including properties of rotations, reflections, and complex numbers, to establish a surprising and non-intuitive result about the equality of certain distances within a triangle under specific conditions.

### Dependencies
* `COLLINEAR_2`
* `CONVEX_HULL_3`
* `ANGLE_SYM`
* `DIST_SYM`
* `INSERT_AC`
* `ROTATE_ABOUT`
* `REFLECT_ACROSS`
* `CEXP_II_NE_1`
* `EQUILATERAL_TRIANGLE_ALGEBRAIC`
* `ALGEBRAIC_LEMMA`
* Various properties of complex numbers, rotations, and geometric transformations.

### Porting notes
When translating this theorem into another proof assistant, careful attention must be paid to the handling of geometric objects (points, lines, angles), complex numbers, and the specific properties and lemmas used in the proof. The use of `cexp` and properties of rotations and reflections may require special consideration, as different systems may represent these concepts differently. Additionally, the proof's reliance on specific geometric lemmas and theorems means that these must be either already available in the target system or must be proven as part of the porting process.

---

