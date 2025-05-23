# pythagoras.ml

## Overview

Number of statements: 2

This file, `pythagoras.ml`, provides a formal proof of Pythagoras's theorem within the Multivariate analysis library. While related to the definition of "norm" from imported files `Multivariate/misc.ml` and `Multivariate/vectors.ml`, it establishes the theorem independently. The file essentially formalizes a standard proof of Pythagoras's theorem in the context of vector spaces.


## PYTHAGORAS

### Name of formal statement
PYTHAGORAS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PYTHAGORAS = prove
 (`!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  REWRITE_TAC[NORM_POW_2; orthogonal; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  CONV_TAC REAL_RING);;
```
### Informal statement
For all two-dimensional real vectors `A`, `B`, and `C`, if the vectors `A - B` and `C - B` are orthogonal, then the square of the norm of `C - A` is equal to the sum of the square of the norm of `B - A` and the square of the norm of `C - B`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the statement using the definition of `norm` squared (`NORM_POW_2`), the definition of `orthogonal`, and the distributivity of the dot product (`DOT_LSUB`, `DOT_RSUB`), and the symmetry of the dot product (`DOT_SYM`).
- Apply a ring tactic (`REAL_RING`) to simplify the resulting expression, which primarily involves algebraic manipulation of real numbers.

### Mathematical insight
This theorem is a formal statement of the Pythagorean theorem in two-dimensional vector space. The condition `orthogonal (A - B) (C - B)` expresses that the vectors `A - B` and `C - B` form a right angle at vertex `B`. The theorem then states that the square of the length of the side opposite the right angle (i.e., the hypotenuse) is equal to the sum of the squares of the lengths of the other two sides. This version of Pythagorean theorem works directly with vector subtraction, norms, and orthogonality, without explicit reference to lengths or angles.

### Dependencies
- Definitions: `orthogonal`, `norm`
- Theorems: `NORM_POW_2`, `DOT_LSUB`, `DOT_RSUB`, `DOT_SYM`

### Porting notes (optional)
- The `REAL_RING` tactic encapsulates real-number reasoning and ring simplification, which may need to be replaced by a similar tactic or a series of rewriting steps in other proof assistants.
- The main challenge will be ensuring that the definitions of orthogonality, norm, and dot product are compatible with the ring properties used by `REAL_RING`.


---

## PYTHAGORAS

### Name of formal statement
PYTHAGORAS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PYTHAGORAS = prove
 (`!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  SIMP_TAC[NORM_POW_2; orthogonal; dot; SUM_2; DIMINDEX_2;
           VECTOR_SUB_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For all vectors `A`, `B`, and `C` in the 2-dimensional real vector space `real^2`, if the vectors `A - B` and `C - B` are orthogonal, then the square of the norm of `C - A` is equal to the sum of the square of the norm of `B - A` and the square of the norm of `C - B`.

### Informal sketch
The proof proceeds by simplifying the goal using the following steps:
- Expand `norm(x) pow 2` to `dot x x` using `NORM_POW_2`.
- Expand the definition of `orthogonal` to `dot (A - B) (C - B) = 0`.
- Expand the dot product of vector subtraction using `VECTOR_SUB_COMPONENT`.
- Apply arithmetic simplification using `ARITH` along with simplification rules for the `dot` product and `SUM_2`.
- Use `DIMINDEX_2` to deal with vector components in 2 dimensions.
- Use `REAL_RING` to rearrange the equation into the standard Pythagorean theorem.

### Mathematical insight
This theorem is the Pythagorean theorem for 2-dimensional real vectors.  It states that if two vectors `A-B` and `C-B` are orthogonal, then the square of the distance between points `C` and `A` is the sum of the squares of the distances between points `B` and `A` and points `C` and `B`.  It is a fundamental result in Euclidean geometry and linear algebra.

### Dependencies
- Definitions:
  - `orthogonal`
  - `norm`
  - `dot`
  - `SUM_2`
  - `DIMINDEX_2`
  - `VECTOR_SUB_COMPONENT`

- Theorems/Lemmas:
  - `NORM_POW_2`
  - `ARITH`
  
### Porting notes (optional)
- The tactic `REAL_RING` is a powerful simplification tool which may need to be emulated by multiple more basic lemmas in other proof assistants.
- The `DIMINDEX_2` tactic is specific to 2 dimensions and may need a different approach in systems which do not have this tactic.


---

