# pythagoras.ml

## Overview

Number of statements: 2

The `pythagoras.ml` file provides a formal proof of Pythagoras's theorem, potentially offering a non-trivial demonstration of the concept. It builds upon definitions and constructions imported from `Multivariate/misc.ml` and `Multivariate/vectors.ml`, suggesting a connection to geometric or algebraic notions. The file's content is likely focused on establishing a fundamental property related to vector norms. Its proof of Pythagoras's theorem contributes to the library's foundation in multivariate mathematics.

## PYTHAGORAS

### Name of formal statement
PYTHAGORAS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PYTHAGORAS = prove
 (`!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  REWRITE_TAC[NORM_POW_2; orthogonal; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  CONV_TAC REAL_RING)
```

### Informal statement
For all points A, B, and C in 2-dimensional real space, if the vectors A - B and C - B are orthogonal, then the square of the norm of vector C - A is equal to the sum of the squares of the norms of vectors B - A and C - B.

### Informal sketch
* The proof starts with the assumption that vectors `A - B` and `C - B` are `orthogonal`.
* It then applies the `REWRITE_TAC` tactic with several theorems (`NORM_POW_2`, `orthogonal`, `DOT_LSUB`, `DOT_RSUB`, `DOT_SYM`) to transform the goal into a form that can be solved using `REAL_RING` properties.
* The use of `CONV_TAC REAL_RING` suggests that the proof involves simplifying the expression using properties of real numbers and vector operations.

### Mathematical insight
This theorem formalizes Pythagoras's theorem in the context of 2-dimensional real space, providing a foundation for geometric and trigonometric reasoning. The key idea is that the orthogonality of two vectors implies a specific relationship between the lengths of the sides of the triangle they form, which is a fundamental principle in geometry and physics.

### Dependencies
* Theorems:
  + `NORM_POW_2`
  + `orthogonal`
  + `DOT_LSUB`
  + `DOT_RSUB`
  + `DOT_SYM`
* Definitions:
  + `norm`
  + `real^2` (2-dimensional real space)
* Modules:
  + `Multivariate/misc.ml`
  + `Multivariate/vectors.ml`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to the handling of vector operations, orthogonality, and norm definitions. The `REWRITE_TAC` and `CONV_TAC` tactics may need to be replaced with equivalent tactics or strategies in the target system, taking into account differences in the handling of real numbers and vector arithmetic.

---

## PYTHAGORAS

### Name of formal statement
PYTHAGORAS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PYTHAGORAS = prove
 (`!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  SIMP_TAC[NORM_POW_2; orthogonal; dot; SUM_2; DIMINDEX_2;
           VECTOR_SUB_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING)
```

### Informal statement
For all vectors A, B, and C in 2-dimensional real space, if the vector from B to A is orthogonal to the vector from B to C, then the square of the norm of the vector from A to C is equal to the sum of the squares of the norms of the vectors from A to B and from B to C.

### Informal sketch
* The proof starts by assuming `A`, `B`, and `C` are vectors in 2-dimensional real space.
* It then assumes the vectors `A - B` and `C - B` are orthogonal.
* The main step involves applying the definition of `orthogonal` and simplifying the expression for `norm(C - A) pow 2` using properties of vector norms and dot products.
* The `SIMP_TAC` tactic is used with various theorems (`NORM_POW_2`, `orthogonal`, `dot`, `SUM_2`, `DIMINDEX_2`, `VECTOR_SUB_COMPONENT`, `ARITH`) to simplify the expression.
* Finally, `CONV_TAC REAL_RING` is applied to ensure the result is in a suitable form.

### Mathematical insight
This theorem is a formalization of the Pythagorean theorem in the context of 2-dimensional real vector spaces. It provides a fundamental property relating the lengths of the sides of a right-angled triangle, which is crucial in various areas of mathematics and physics.

### Dependencies
* Theorems:
  + `NORM_POW_2`
  + `orthogonal`
  + `dot`
  + `SUM_2`
  + `DIMINDEX_2`
  + `VECTOR_SUB_COMPONENT`
  + `ARITH`
* Definitions:
  + `norm`
  + `pow`
  + `real^2` (2-dimensional real space)

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of vector operations, orthogonality, and norm properties. Ensure that the target system has equivalent definitions and theorems for these concepts. Additionally, be mindful of the differences in automation and tactic application between HOL Light and the target system, as direct translation of tactics like `SIMP_TAC` and `CONV_TAC` may not be straightforward.

---

