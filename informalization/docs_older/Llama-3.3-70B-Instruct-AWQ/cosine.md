# cosine.ml

## Overview

Number of statements: 18

The `cosine.ml` file formalizes the law of cosines, law of sines, and sum of angles of a triangle. It builds upon the `transcendentals.ml` module from the `Multivariate` directory, indicating its reliance on transcendental functions. This file is likely a part of a larger geometry or trigonometry library, providing foundational theorems and definitions for triangle properties. The key content includes proofs and constructions related to these geometric and trigonometric principles.

## vangle

### Name of formal statement
vangle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let vangle = new_definition
 `vangle x y = if x = vec 0 \/ y = vec 0 then pi / &2
               else acs((x dot y) / (norm x * norm y))`
```

### Informal statement
The `vangle` function calculates the angle between two vectors `x` and `y`. If either `x` or `y` is the zero vector, the function returns π/2. Otherwise, it returns the inverse cosine (`acs`) of the dot product of `x` and `y` divided by the product of their norms.

### Informal sketch
* The function first checks if either input vector is the zero vector.
* If so, it returns π/2, as the angle between a vector and the zero vector is undefined but conventionally taken to be π/2 in this context.
* Otherwise, it calculates the cosine of the angle between the two vectors using the dot product formula and the norms of the vectors.
* The `acs` function (inverse cosine) is then applied to this cosine value to obtain the angle.
* The use of `acs` ensures the result is an angle in the range [0, π].

### Mathematical insight
The `vangle` function implements the geometric concept of the angle between two vectors in Euclidean space. This is crucial in various mathematical and physical contexts, such as geometry, trigonometry, and physics, where angles between vectors are fundamental. The function's definition aligns with the law of cosines and the definition of the dot product, making it a foundational element in vector calculus.

### Dependencies
#### Functions and definitions
* `vec`
* `acs` (inverse cosine)
* `dot` (dot product)
* `norm` (vector norm)
#### Theories or modules
* `Multivariate/transcendentals.ml` for transcendental functions like `acs`.

### Porting notes
When translating `vangle` into another proof assistant, ensure that the target system supports similar vector operations (`dot`, `norm`) and transcendental functions (`acs`). Special care should be taken with the handling of the zero vector case and the range of the inverse cosine function to match the HOL Light implementation. Additionally, consider the specific libraries or modules required for vector calculus and trigonometric functions in the target system.

---

## angle

### Name of formal statement
angle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let angle = new_definition
`angle(a,b,c) = vangle (a - b) (c - b)`;;
```

### Informal statement
The `angle` function is defined as `angle(a, b, c) = vangle(a - b, c - b)`, where `vangle` represents the traditional geometric notion of angle, with the result always between 0 and pi.

### Informal sketch
* The definition of `angle` relies on the `vangle` function, which computes the angle between two vectors.
* The `angle(a, b, c)` function takes three points `a`, `b`, and `c` as input and returns the angle at point `b` formed by the vectors `a - b` and `c - b`.
* The use of `vangle` ensures that the resulting angle is always within the range 0 to pi, adhering to the traditional geometric notion of angle.

### Mathematical insight
The `angle` definition captures the geometric concept of an angle in a way that is useful for formal proofs, particularly in geometric and trigonometric contexts. It provides a standardized method to compute angles based on the positions of points, which is crucial in various mathematical and scientific applications.

### Dependencies
* `vangle`
 
### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that an equivalent `vangle` function or its mathematical equivalent is defined or available. Pay attention to how each system handles vector operations and geometric definitions, as the implementation details may vary.

---

## VANGLE

### Name of formal statement
VANGLE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let VANGLE = prove
 (`!x y:real^N. x dot y = norm(x) * norm(y) * cos(vangle x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vangle] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; NORM_0; REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_RZERO; NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c:real = c * a * b`] THEN
  ASM_SIMP_TAC[GSYM REAL_EQ_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT] THEN
  MATCH_MP_TAC(GSYM COS_ACS) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; NORM_POS_LT; REAL_LT_MUL] THEN
  MP_TAC(SPECL [`x:real^N`; `y:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  REAL_ARITH_TAC)
```

### Informal statement
For all vectors `x` and `y` in `real^N`, the dot product of `x` and `y` is equal to the product of the norms of `x` and `y` and the cosine of the angle between `x` and `y`.

### Informal sketch
* The proof starts by considering all possible vectors `x` and `y` in `real^N`.
* It then proceeds by cases, first assuming `x` is the zero vector and then assuming `y` is the zero vector, using `ASM_CASES_TAC` to split the proof into these cases.
* In each case, it applies various simplification rules (`ASM_REWRITE_TAC`) to reduce the expression, using properties like `DOT_LZERO`, `NORM_0`, and `REAL_MUL_LZERO`.
* After handling the zero vector cases, it applies the `ONCE_REWRITE_TAC` rule to rearrange the terms using the associative property of multiplication (`AC REAL_MUL_AC`).
* The proof then uses `ASM_SIMP_TAC` to simplify the expression further, leveraging properties like `GSYM REAL_EQ_LDIV_EQ`, `REAL_LT_MUL`, and `NORM_POS_LT`.
* It then applies `MATCH_MP_TAC` with `GSYM COS_ACS` to relate the expression to the cosine of the angle between the vectors.
* Further simplifications are made using `ASM_SIMP_TAC` with properties like `REAL_LE_RDIV_EQ`, `REAL_LE_LDIV_EQ`, `NORM_POS_LT`, and `REAL_LT_MUL`.
* Finally, it uses `MP_TAC` with `NORM_CAUCHY_SCHWARZ_ABS` to apply the Cauchy-Schwarz inequality and concludes with `REAL_ARITH_TAC` for arithmetic manipulations.

### Mathematical insight
This theorem formalizes the relationship between the dot product of two vectors and the cosine of the angle between them, which is a fundamental concept in linear algebra and geometry. The proof demonstrates how this relationship can be derived from basic properties of vector operations and trigonometric functions.

### Dependencies
#### Theorems
* `COS_ACS`
* `NORM_CAUCHY_SCHWARZ_ABS`
#### Definitions
* `vangle`
* `norm`
* `dot`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to how each system handles vector operations, trigonometric functions, and real arithmetic. Note that `REAL_ARITH_TAC` and other tactics may need to be replaced with equivalent tactics or manual proofs in the target system. Additionally, the use of `ASM_CASES_TAC` and `MATCH_MP_TAC` may require careful handling of case splits and lemma application in the new system.

---

## VANGLE_RANGE

### Name of formal statement
VANGLE_RANGE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let VANGLE_RANGE = prove
 (`!x y:real^N. &0 <= vangle x y /\ vangle x y <= pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vangle] THEN COND_CASES_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN MATCH_MP_TAC ACS_BOUNDS THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> -- &1 * a <= x /\ x <= &1 * a`) THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS])
```

### Informal statement
For all real vectors `x` and `y` in `ℝ^N`, the angle between `x` and `y`, denoted `vangle x y`, satisfies the inequality `0 ≤ vangle x y ≤ π`.

### Informal sketch
* The proof starts by assuming the universal quantification over all real vectors `x` and `y` in `ℝ^N`.
* It then applies the definition of `vangle` and splits into cases using `COND_CASES_TAC`.
* The first case involves using `PI_POS` and `REAL_ARITH_TAC` to establish a lower bound for `vangle x y`.
* The proof then applies `RULE_ASSUM_TAC` with `REWRITE_RULE[DE_MORGAN_THM]` to simplify assumptions.
* The `MATCH_MP_TAC ACS_BOUNDS` tactic is used to apply a bound, followed by simplification using `ASM_SIMP_TAC` with various real arithmetic and norm properties.
* Finally, the proof uses `MATCH_MP_TAC` with a real arithmetic statement to conclude the upper bound for `vangle x y`.
* The `REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS]` is applied to finalize the proof.

### Mathematical insight
The `VANGLE_RANGE` theorem provides a fundamental property of the angle between vectors, ensuring it stays within the range `[0, π]`. This is crucial in various geometric and trigonometric contexts, as it guarantees that the angle between two vectors is always non-negative and does not exceed π radians.

### Dependencies
* Theorems:
  + `PI_POS`
  + `ACS_BOUNDS`
  + `REAL_ARITH`
* Definitions:
  + `vangle`
  + `NORM_CAUCHY_SCHWARZ_ABS`
* Tactics and rules:
  + `REWRITE_TAC`
  + `COND_CASES_TAC`
  + `MATCH_MP_TAC`
  + `RULE_ASSUM_TAC`
  + `ASM_SIMP_TAC`

### Porting notes
When porting this theorem to other proof assistants, pay close attention to the handling of real arithmetic and vector norms. The `vangle` definition and properties like `ACS_BOUNDS` may need to be adapted or re-proven in the target system. Additionally, the use of `COND_CASES_TAC` and `MATCH_MP_TAC` might be replaced with equivalent constructs in the target proof assistant, requiring careful consideration of the underlying logic and proof search mechanisms.

---

## ORTHOGONAL_VANGLE

### Name of formal statement
ORTHOGONAL_VANGLE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ORTHOGONAL_VANGLE = prove
 (`!x y:real^N. orthogonal x y <=> vangle x y = pi / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orthogonal; vangle] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_RZERO] THEN
  EQ_TAC THENL
   [SIMP_TAC[real_div; REAL_MUL_LZERO] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM real_div; GSYM COS_PI2] THEN
    MATCH_MP_TAC ACS_COS THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`x:real^N`; `y:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_BOUNDS_LE] THEN
    ONCE_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_LE_LDIV_EQ;
                 REAL_LT_MUL; NORM_POS_LT] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `cos`) THEN
    ASM_SIMP_TAC[COS_ACS; COS_PI2] THEN
    REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0] THEN
    ASM_REWRITE_TAC[NORM_EQ_0]])
```

### Informal statement
For all vectors `x` and `y` in `real^N`, `x` is orthogonal to `y` if and only if the vector angle between `x` and `y` is equal to `π/2`.

### Informal sketch
* The proof starts by considering the cases where either `x` or `y` is the zero vector, using `ASM_CASES_TAC` to handle these cases separately.
* For non-zero vectors, it applies `REWRITE_TAC` to express `orthogonal` and `vangle` in terms of their definitions, specifically using `DOT_LZERO` and `DOT_RZERO` for the zero vector cases.
* The proof then proceeds to establish the equivalence using `EQ_TAC`, splitting into two main directions:
  + One direction involves simplifying the expression for `vangle` when `x` and `y` are orthogonal, using properties of `real_div`, `REAL_MUL_LZERO`, and `COS_PI2`.
  + The other direction involves applying `NORM_CAUCHY_SCHWARZ_ABS` and manipulating inequalities to show that if the vector angle is `π/2`, then `x` and `y` must be orthogonal, utilizing `REAL_BOUNDS_LE`, `REAL_MUL_LNEG`, and properties of `cos`.
* Key steps include using `MATCH_MP_TAC` with `ACS_COS`, and applying `REAL_ARITH_TAC` for arithmetic reasoning.

### Mathematical insight
This theorem establishes a fundamental relationship between the orthogonality of two vectors and the angle between them, which is a cornerstone in linear algebra and geometry. The vector angle `vangle` being `π/2` (or 90 degrees) is a direct consequence of the vectors being orthogonal, which means their dot product is zero.

### Dependencies
#### Theorems
* `NORM_CAUCHY_SCHWARZ_ABS`
* `ACS_COS`
* `PI_POS`
#### Definitions
* `orthogonal`
* `vangle`
* `DOT_LZERO`
* `DOT_RZERO`
* `COS_PI2`
* `REAL_MUL_LZERO`
* `REAL_ENTIRE`
* `REAL_INV_EQ_0`
* `NORM_EQ_0`
* `REAL_BOUNDS_LE`
* `REAL_MUL_LNEG`
* `REAL_LE_RDIV_EQ`
* `REAL_LE_LDIV_EQ`
* `REAL_LT_MUL`
* `NORM_POS_LT`

---

## VANGLE_EQ_PI

### Name of formal statement
VANGLE_EQ_PI

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let VANGLE_EQ_PI = prove
 (`!x y:real^N. vangle x y = pi ==> norm(x) % y + norm(y) % x = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real^N`; `y:real^N`] VANGLE) THEN
  ASM_REWRITE_TAC[COS_PI] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `--y:real^N`] NORM_CAUCHY_SCHWARZ_EQ) THEN
  REWRITE_TAC[NORM_NEG; DOT_RNEG; VECTOR_MUL_RNEG] THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_NEG_NEG; REAL_MUL_RID] THEN
  VECTOR_ARITH_TAC)
```

### Informal statement
For all vectors `x` and `y` in `real^N`, if the angle between `x` and `y` is `pi`, then the vector sum of the projections of `x` onto `y` and `y` onto `x` equals the zero vector.

### Informal sketch
* The proof begins by assuming the premise that the angle between vectors `x` and `y` is `pi`, which implies orthogonality.
* It then applies the `VANGLE` theorem to relate the angle to the dot product.
* The `COS_PI` theorem is used to simplify the cosine of `pi` to `-1`.
* The proof then invokes `NORM_CAUCHY_SCHWARZ_EQ` to relate norms and dot products, considering the negation of `y` to handle the orthogonality condition.
* Simplifications are applied using `NORM_NEG`, `DOT_RNEG`, `VECTOR_MUL_RNEG`, `REAL_MUL_RNEG`, `REAL_NEG_NEG`, and `REAL_MUL_RID` to manipulate the vector and real number expressions.
* Final vector arithmetic is performed using `VECTOR_ARITH_TAC` to conclude the proof.

### Mathematical insight
This theorem provides a geometric insight that when two vectors are orthogonal (their angle is `pi`), the sum of their projections onto each other results in the zero vector, highlighting a fundamental property of orthogonal vectors in terms of their geometric relationship.

### Dependencies
* Theorems:
  * `VANGLE`
  * `COS_PI`
  * `NORM_CAUCHY_SCHWARZ_EQ`
* Definitions:
  * `norm`
  * `vangle`
* Axioms and Rules:
  None explicitly listed, but the proof relies on properties of vector spaces, real numbers, and possibly other foundational axioms implicit in HOL Light.

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of vector operations, real numbers, and the specific theorems and definitions used. The `VANGLE_EQ_PI` theorem's proof structure, which mixes geometric insights with algebraic manipulations, might require careful adaptation to the target system's tactic language and libraries. In particular, the use of `REPEAT STRIP_TAC`, `MP_TAC`, `ASM_REWRITE_TAC`, and `VECTOR_ARITH_TAC` may have direct or analogous counterparts in the target system, but their application and the intermediate goals might need adjustment to fit the specific proof assistant's paradigm and automation level.

---

## ANGLE_EQ_PI

### Name of formal statement
ANGLE_EQ_PI

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ANGLE_EQ_PI = prove
 (`!A B C:real^N. angle(A,B,C) = pi ==> dist(A,C) = dist(A,B) + dist(B,C)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[angle] THEN
  DISCH_THEN(MP_TAC o MATCH_MP VANGLE_EQ_PI) THEN
  REWRITE_TAC[VECTOR_ARITH `a + x % (b - c) = vec 0 <=> a = x % (c - b)`] THEN
  GEN_REWRITE_TAC (funpow 3 LAND_CONV) [NORM_SUB] THEN
  REWRITE_TAC[GSYM NORM_TRIANGLE_EQ] THEN
  REWRITE_TAC[VECTOR_ARITH `(B - A) + (C - B):real^N = C - A`] THEN
  REWRITE_TAC[dist; NORM_SUB])
```

### Informal statement
For all points A, B, and C in real N-dimensional space, if the angle between vectors AB and BC is pi (i.e., the vectors are anti-parallel), then the distance between A and C is equal to the sum of the distances between A and B, and B and C.

### Informal sketch
* The proof begins by assuming the angle between vectors AB and BC is pi, which implies that these vectors are anti-parallel.
* The `angle` definition is unfolded using `REWRITE_TAC[angle]`.
* The `VANGLE_EQ_PI` theorem is applied to establish a relationship between the vectors.
* Vector arithmetic properties are used, specifically `a + x % (b - c) = vec 0 <=> a = x % (c - b)`, to simplify expressions.
* The proof involves rewriting expressions using `NORM_SUB` and applying the triangle equality `NORM_TRIANGLE_EQ` to relate vector norms and distances.
* Finally, the distance formula `dist` is applied to conclude the equality of distances.

### Mathematical insight
This theorem provides a geometric insight that when three points are collinear and the middle point is between the other two, the distance between the first and last point is the sum of the distances between the first and middle point, and the middle and last point. This is a fundamental property in geometry and is crucial in various geometric and trigonometric proofs.

### Dependencies
* `angle`
* `VANGLE_EQ_PI`
* `VECTOR_ARITH`
* `NORM_SUB`
* `NORM_TRIANGLE_EQ`
* `dist`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to handling vector arithmetic and geometric properties. The `VECTOR_ARITH` and `NORM_SUB` theorems might need to be adapted or re-proven in the target system. Additionally, the use of `REPEAT GEN_TAC` and `GEN_REWRITE_TAC` might require equivalent tactics or strategies in the new system to achieve the same effect.

---

## SIN_ANGLE_POS

### Name of formal statement
SIN_ANGLE_POS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIN_ANGLE_POS = prove
 (`!A B C. &0 <= sin(angle(A,B,C))`,
  SIMP_TAC[SIN_POS_PI_LE; angle; VANGLE_RANGE])
```

### Informal statement
For all points A, B, and C, the sine of the angle between them is greater than or equal to 0.

### Informal sketch
* The proof involves a universal quantification over points A, B, and C.
* It asserts a non-negativity property of the sine function applied to the angle formed by these points.
* The `SIMP_TAC` tactic is used, which suggests a simplification step, potentially leveraging the `SIN_POS_PI_LE` and `angle` definitions, as well as the `VANGLE_RANGE` property to establish the non-negativity of the sine of the angle.

### Mathematical insight
This statement captures a basic property of the sine function in the context of geometric angles, which is fundamental in trigonometry and geometry. The sine function's non-negativity for angles between 0 and pi (or 0 to 180 degrees) is a crucial aspect of its definition and application in various mathematical and physical contexts.

### Dependencies
- Theorems: `SIN_POS_PI_LE`
- Definitions: `angle`
- Properties: `VANGLE_RANGE`

### Porting notes
When porting this theorem to another proof assistant like Lean, Coq, or Isabelle, pay special attention to how these systems handle trigonometric functions and geometric definitions. The `SIMP_TAC` tactic's behavior and the `SIN_POS_PI_LE`, `angle`, and `VANGLE_RANGE` dependencies might need to be translated or reimplemented according to the target system's libraries and tactics for simplification and trigonometric properties.

---

## ANGLE

### Name of formal statement
ANGLE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ANGLE = prove
 (`!A B C. (A - C) dot (B - C) = dist(A,C) * dist(B,C) * cos(angle(A,C,B))`,
  REWRITE_TAC[angle; dist; GSYM VANGLE])
```

### Informal statement
For all points A, B, and C, the dot product of vectors (A - C) and (B - C) is equal to the product of the distances from A to C, from B to C, and the cosine of the angle between vectors A-C and B-C.

### Informal sketch
* The proof involves rewriting the `angle` and `dist` terms using their definitions, and applying the `GSYM VANGLE` rule to rearrange the equation.
* The `REWRITE_TAC` tactic is used to apply these rewrites and simplify the expression.
* The key insight is that the dot product of two vectors can be expressed in terms of their magnitudes and the angle between them, which is a fundamental property of vector geometry.

### Mathematical insight
This theorem provides a way to relate the dot product of two vectors to the angle between them, which is a crucial concept in geometry and linear algebra. The `angle` function, `dist` function, and `cos` function are all used to express this relationship, which is a key part of the mathematical structure of vector spaces.

### Dependencies
* `angle`
* `dist`
* `GSYM VANGLE`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `angle`, `dist`, and `cos` functions are defined and behave similarly. Additionally, the `REWRITE_TAC` tactic may need to be replaced with a similar tactic or a combination of tactics in the target system. The `GSYM VANGLE` rule may also require special attention, as it is a specific rule in HOL Light that may not have a direct equivalent in other systems.

---

## ANGLE_REFL

### Name of formal statement
ANGLE_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ANGLE_REFL = prove
 (`!A B. angle(A,A,B) = pi / &2 /\
         angle(B,A,A) = pi / &2`,
  REWRITE_TAC[angle; vangle; VECTOR_SUB_REFL])
```

### Informal statement
For all points A and B, the angle formed by A, A, and B is equal to pi/2, and the angle formed by B, A, and A is also equal to pi/2.

### Informal sketch
* The proof involves rewriting the `angle` function using the `angle` and `vangle` definitions, and applying the `VECTOR_SUB_REFL` property.
* The `REWRITE_TAC` tactic is used to apply these rewrites and simplify the expression.
* The key insight is that the `angle` function is defined in terms of the `vangle` function, which is related to the `VECTOR_SUB_REFL` property.

### Mathematical insight
This theorem provides a basic property of angles in a geometric context, specifically that the angle formed by a point with itself and another point is a right angle. This is a fundamental result in geometry and is likely used as a building block for more complex theorems.

### Dependencies
* `angle`
* `vangle`
* `VECTOR_SUB_REFL`

### Porting notes
When porting this theorem to another proof assistant, note that the `REWRITE_TAC` tactic may need to be replaced with a similar tactic or a series of rewrites. Additionally, the `angle` and `vangle` definitions, as well as the `VECTOR_SUB_REFL` property, will need to be defined or imported in the target system.

---

## ANGLE_REFL_MID

### Name of formal statement
ANGLE_REFL_MID

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ANGLE_REFL_MID = prove
 (`!A B. ~(A = B) ==> angle(A,B,A) = &0`,
  SIMP_TAC[angle; vangle; VECTOR_SUB_EQ; GSYM NORM_POW_2; GSYM REAL_POW_2;
           REAL_DIV_REFL; ACS_1; REAL_POW_EQ_0; ARITH; NORM_EQ_0])
```

### Informal statement
For all vectors A and B, if A is not equal to B, then the angle between A, B, and A is equal to 0.

### Informal sketch
* The proof starts with the assumption that vectors A and B are not equal.
* It then applies various simplification and equality theorems, including `angle`, `vangle`, `VECTOR_SUB_EQ`, and others, to transform the expression `angle(A, B, A)` into a form where it can be shown to equal 0.
* Key steps involve using `GSYM` to apply symmetric versions of `NORM_POW_2` and `REAL_POW_2`, and applying `REAL_DIV_REFL` and `ACS_1` to simplify expressions involving real numbers and vector operations.
* The proof also relies on `REAL_POW_EQ_0` and `NORM_EQ_0` to handle cases where real powers or vector norms are involved.
* The `ARITH` tactic is used for arithmetic simplifications.

### Mathematical insight
This theorem provides a basic property of vector geometry, stating that the angle between a vector and itself, as measured through a different vector, collapses to 0 when the initial and final vectors are distinct. This is intuitively expected since the "angle" in such a case does not span any space between distinct vectors A and B when the endpoint is again A.

### Dependencies
* Theorems:
  - `angle`
  - `vangle`
  - `VECTOR_SUB_EQ`
  - `GSYM NORM_POW_2`
  - `GSYM REAL_POW_2`
  - `REAL_DIV_REFL`
  - `ACS_1`
  - `REAL_POW_EQ_0`
  - `ARITH`
  - `NORM_EQ_0`
* Definitions:
  - None explicitly listed, but `angle`, `vangle`, and vector operations are presumed defined elsewhere.

### Porting notes
When translating this theorem into another proof assistant, ensure that the target system supports similar simplification and equality theorems, especially those related to vector operations and real numbers. Pay particular attention to how the system handles symmetric applications of theorems (like `GSYM`) and arithmetic simplifications. Additionally, verify that the target system's `angle` and `vangle` functions or predicates match the behavior assumed in this HOL Light theorem.

---

## ANGLE_SYM

### Name of formal statement
ANGLE_SYM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ANGLE_SYM = prove
 (`!A B C. angle(A,B,C) = angle(C,B,A)`,
  REWRITE_TAC[angle; vangle; VECTOR_SUB_EQ; DISJ_SYM; REAL_MUL_SYM; DOT_SYM])
```

### Informal statement
For all points A, B, and C, the angle formed by A, B, and C is equal to the angle formed by C, B, and A.

### Informal sketch
* The proof involves establishing a symmetry property of angles.
* It utilizes the `angle` function and its relation to `vangle`, which likely represents a vector-based angle calculation.
* The `REWRITE_TAC` tactic is applied with several theorems and definitions, including `angle`, `vangle`, `VECTOR_SUB_EQ`, `DISJ_SYM`, `REAL_MUL_SYM`, and `DOT_SYM`, to transform the goal into a provable form.
* The use of `DISJ_SYM`, `REAL_MUL_SYM`, and `DOT_SYM` suggests that the proof involves exploiting symmetric properties of various mathematical operations.

### Mathematical insight
This theorem captures a fundamental geometric property: the symmetry of angles with respect to their endpoints. It's crucial for various geometric and trigonometric developments, as it allows for flexible manipulation of angles in proofs and calculations.

### Dependencies
#### Theorems and definitions
* `angle`
* `vangle`
* `VECTOR_SUB_EQ`
* `DISJ_SYM`
* `REAL_MUL_SYM`
* `DOT_SYM`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how angles and vectors are represented and how symmetry properties are established. The equivalent of `REWRITE_TAC` might be needed, possibly in combination with built-in simplification or rewriting mechanisms. Ensure that the target system's libraries include or can easily express the necessary symmetric properties of mathematical operations (`DISJ_SYM`, `REAL_MUL_SYM`, `DOT_SYM`).

---

## ANGLE_RANGE

### Name of formal statement
ANGLE_RANGE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ANGLE_RANGE = prove
 (`!A B C. &0 <= angle(A,B,C) /\ angle(A,B,C) <= pi`,
  REWRITE_TAC[angle; VANGLE_RANGE])
```

### Informal statement
For all points A, B, and C, the angle between them, denoted as `angle(A, B, C)`, is greater than or equal to 0 and less than or equal to pi.

### Informal sketch
* The proof involves a universal quantification over points A, B, and C.
* The `angle` function is used to compute the angle between these points.
* The `VANGLE_RANGE` definition is used to establish the range of the angle, which is then rewritten using `REWRITE_TAC` to prove the statement.
* The key steps involve:
  + Quantifying over all points A, B, and C.
  + Applying the `angle` function to these points.
  + Using `VANGLE_RANGE` to constrain the angle to be within the range [0, pi].
  + Rewriting the statement using `REWRITE_TAC` to establish the desired inequality.

### Mathematical insight
This theorem establishes a fundamental property of angles in geometry, specifically that they are always between 0 and pi radians. This is a crucial result in many geometric and trigonometric contexts, as it provides a basis for comparing and analyzing angles.

### Dependencies
* `angle`
* `VANGLE_RANGE`
* `REWRITE_TAC`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of universal quantification and the `angle` function. Additionally, the `REWRITE_TAC` tactic may need to be replaced with an equivalent tactic or mechanism for rewriting terms. The `VANGLE_RANGE` definition should also be ported or redefined in the target system.

---

## LAW_OF_COSINES

### Name of formal statement
LAW_OF_COSINES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAW_OF_COSINES = prove
 (`!A B C:real^N.
     dist(B,C) pow 2 = dist(A,B) pow 2 + dist(A,C) pow 2 -
                         &2 * dist(A,B) * dist(A,C) * cos(angle(B,A,C))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[angle; ONCE_REWRITE_RULE[NORM_SUB] dist; GSYM VANGLE;
              NORM_POW_2] THEN
  VECTOR_ARITH_TAC)
```

### Informal statement
For all vectors A, B, and C in the real vector space of dimension N, the square of the distance between B and C is equal to the sum of the squares of the distances between A and B and between A and C, minus twice the product of the distances between A and B and between A and C, multiplied by the cosine of the angle between vectors BA and CA.

### Informal sketch
* The proof starts by applying `GEN_TAC` to generalize the statement for all vectors A, B, and C.
* It then applies `REWRITE_TAC` to rewrite the `angle`, `dist`, and `VANGLE` terms, using `ONCE_REWRITE_RULE` and `GSYM` to simplify the expression.
* The `NORM_POW_2` rule is applied to normalize the squared terms.
* Finally, `VECTOR_ARITH_TAC` is used to perform vector arithmetic and simplify the expression to prove the law of cosines.
* Key steps involve manipulating the trigonometric and geometric terms to isolate the cosine of the angle between the vectors.

### Mathematical insight
The law of cosines is a fundamental concept in geometry and trigonometry, relating the lengths of the sides of a triangle to the cosine of one of its angles. This formalization in HOL Light provides a rigorous foundation for geometric and trigonometric reasoning, enabling the proof of various theorems and properties in these domains.

### Dependencies
* `dist`
* `angle`
* `VANGLE`
* `NORM_SUB`
* `NORM_POW_2`
* `VECTOR_ARITH_TAC`
* `GEN_TAC`
* `REWRITE_TAC`

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to the handling of vector arithmetic and trigonometric functions. The `VECTOR_ARITH_TAC` tactic may need to be replaced with equivalent tactics or rewriting rules in the target system. Additionally, the `ONCE_REWRITE_RULE` and `GSYM` tactics may require careful translation to ensure that the rewriting and simplification steps are correctly applied.

---

## LAW_OF_SINES

### Name of formal statement
LAW_OF_SINES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAW_OF_SINES = prove
 (`!A B C:real^N.
      sin(angle(A,B,C)) * dist(B,C) = sin(angle(B,A,C)) * dist(A,C)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  SIMP_TAC[SIN_ANGLE_POS; DIST_POS_LE; REAL_LE_MUL; ARITH] THEN
  REWRITE_TAC[REAL_POW_MUL; MATCH_MP
   (REAL_ARITH `x + y = &1 ==> x = &1 - y`) (SPEC_ALL SIN_CIRCLE)] THEN
  ASM_CASES_TAC `A:real^N = B` THEN ASM_REWRITE_TAC[ANGLE_REFL; COS_PI2] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM VECTOR_SUB_EQ]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NORM_EQ_0]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
   `~(a = &0) ==> a pow 2 * x = a pow 2 * y ==> x = y`)) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM dist] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [DIST_SYM] THEN
  REWRITE_TAC[REAL_RING
   `a * (&1 - x) * b = c * (&1 - y) * d <=>
    a * b - a * b * x = c * d - c * d * y`] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; GSYM ANGLE] THEN
  REWRITE_TAC[REAL_POW_MUL; dist; NORM_POW_2] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN CONV_TAC REAL_RING)
```

### Informal statement
For all points A, B, and C in real N-dimensional space, the sine of the angle between vectors A and B multiplied by the distance between points B and C is equal to the sine of the angle between vectors B and A multiplied by the distance between points A and C.

### Informal sketch
* The proof starts by applying the `GEN_TAC` tactic to introduce the variables A, B, and C.
* It then uses `MATCH_MP_TAC` with `REAL_POW_EQ` to establish an equality involving powers of real numbers.
* The `EXISTS_TAC` tactic is used to introduce the number 2, which is used in subsequent calculations.
* The proof then proceeds through a series of simplifications and rewrites using various theorems and definitions, including `SIN_ANGLE_POS`, `DIST_POS_LE`, `REAL_LE_MUL`, and `ARITH`.
* The `ASM_CASES_TAC` tactic is used to consider the case where A equals B, and the `ASM_REWRITE_TAC` tactic is used to simplify the expression using `ANGLE_REFL` and `COS_PI2`.
* The proof continues with a series of rewrites and simplifications using `VECTOR_SUB_EQ`, `NORM_EQ_0`, `REAL_RING`, and other theorems.
* The `CONV_TAC` tactic is used with `REAL_RING` to finalize the proof.

### Mathematical insight
The law of sines is a fundamental concept in geometry and trigonometry, relating the lengths of the sides of a triangle to the sines of its angles. This theorem provides a formal proof of this law in a general N-dimensional space, using the `sin` and `angle` functions, as well as the `dist` function to calculate distances between points.

### Dependencies
#### Theorems
* `REAL_POW_EQ`
* `SIN_ANGLE_POS`
* `DIST_POS_LE`
* `REAL_LE_MUL`
* `ARITH`
* `SIN_CIRCLE`
* `ANGLE_REFL`
* `COS_PI2`
* `VECTOR_SUB_EQ`
* `NORM_EQ_0`
* `REAL_RING`
#### Definitions
* `sin`
* `angle`
* `dist`
* `real^N`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of binders and the `GEN_TAC` tactic, as well as the various rewrites and simplifications used throughout the proof. The `CONV_TAC` tactic with `REAL_RING` may also require special handling, depending on the target system's support for real numbers and arithmetic.

---

## TRIANGLE_ANGLE_SUM_LEMMA

### Name of formal statement
TRIANGLE_ANGLE_SUM_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TRIANGLE_ANGLE_SUM_LEMMA = prove
 (`!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> cos(angle(B,A,C) + angle(A,B,C) + angle(B,C,A)) = -1`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`C:real^N`; `B:real^N`; `A:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `A:real^N`] LAW_OF_SINES) THEN
  REWRITE_TAC[COS_ADD; SIN_ADD; dist; NORM_SUB] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t SIN_CIRCLE))
   [`angle(B:real^N,A,C)`; `angle(A:real^N,B,C)`; `angle(B:real^N,C,A)`] THEN
  REWRITE_TAC[COS_ADD; SIN_ADD; ANGLE_SYM] THEN CONV_TAC REAL_RING)
```

### Informal statement
For all points `A`, `B`, and `C` in `real^N`, if `A`, `B`, and `C` are distinct, then the cosine of the sum of the angles `angle(B,A,C)`, `angle(A,B,C)`, and `angle(B,C,A)` equals -1.

### Informal sketch
* The proof starts by assuming `A`, `B`, and `C` are distinct points in `real^N`.
* It then applies the `LAW_OF_COSINES` and `LAW_OF_SINES` theorems to the triangles formed by these points.
* The `COS_ADD` and `SIN_ADD` theorems are used to simplify the expression involving the cosine of the sum of angles.
* The `SIN_CIRCLE` theorem is applied to each angle to further simplify the expression.
* Finally, the `ANGLE_SYM` theorem and `REAL_RING` tactic are used to conclude the proof.

### Mathematical insight
This theorem provides a fundamental property of triangles in Euclidean space, relating the angles of a triangle to the cosine function. The proof leverages key geometric identities, such as the law of cosines and the law of sines, to establish this relationship.

### Dependencies
#### Theorems
* `LAW_OF_COSINES`
* `LAW_OF_SINES`
* `SIN_CIRCLE`
* `COS_ADD`
* `SIN_ADD`
* `ANGLE_SYM`
#### Definitions
* `angle`
* `cos`
* `real^N`
* `VECTOR_SUB_EQ`
* `NORM_EQ_0`
* `dist`
* `NORM_SUB`

### Porting notes
When translating this theorem into other proof assistants, note that the `REAL_RING` tactic may need to be replaced with an equivalent tactic or a series of tactics that achieve the same goal of simplifying the expression using the properties of real numbers. Additionally, the `MP_TAC` and `REPEAT GEN_TAC` tactics may need to be adapted to the specific proof assistant's syntax and tactic language.

---

## COS_MINUS1_LEMMA

### Name of formal statement
COS_MINUS1_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COS_MINUS1_LEMMA = prove
 (`!x. cos(x) = -- &1 /\ &0 <= x /\ x < &3 * pi ==> x = pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. integer n /\ x = n * pi`
   (X_CHOOSE_THEN `nn:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[GSYM SIN_EQ_0] THENL
   [MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. nn = &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_MUL_POS_LE]) THEN
    SIMP_TAC[PI_POS; REAL_ARITH `&0 < p ==> ~(p < &0) /\ ~(p = &0)`] THEN
    ASM_MESON_TAC[INTEGER_POS; REAL_LT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_RING `n = &1 ==> n * p = p`) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(ARITH_RULE `n < 3 /\ ~(n = 0) /\ ~(n = 2) ==> n = 1`) THEN
  RULE_ASSUM_TAC(SIMP_RULE[REAL_LT_RMUL_EQ; PI_POS; REAL_OF_NUM_LT]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[COS_0; REAL_MUL_LZERO; COS_NPI] THEN
  REAL_ARITH_TAC)
```

### Informal statement
For all real numbers $x$, if $\cos(x) = -1$ and $0 \leq x < 3\pi$, then $x = \pi$.

### Informal sketch
* The proof starts by assuming $\cos(x) = -1$ and $0 \leq x < 3\pi$.
* It then uses the `SIN_CIRCLE` theorem to derive that $x$ must be of the form $n\pi$ for some integer $n$.
* The proof then uses `REAL_MUL_POS_LE` and `PI_POS` to constrain the possible values of $n$.
* By analyzing the range of $x$, the proof narrows down the possibilities for $n$ to be $1$.
* The final steps involve using `REAL_OF_NUM_EQ` and `ARITH_RULE` to conclude that $x = \pi$.

### Mathematical insight
This theorem provides a characterization of when $\cos(x) = -1$ for $x$ in the interval $[0, 3\pi)$. It is a key result in trigonometry and has implications for understanding the periodicity and symmetry of the cosine function.

### Dependencies
* Theorems:
 + `SIN_CIRCLE`
 + `REAL_MUL_POS_LE`
 + `PI_POS`
 + `INTEGER_POS`
 + `REAL_LT_LE`
 + `REAL_OF_NUM_EQ`
 + `ARITH_RULE`
* Definitions:
 + `cos`
 + `pi`
* Axioms:
 + None

### Porting notes
When translating this theorem to other proof assistants, care should be taken to preserve the precise quantifier structure and constraints. The use of `SUBGOAL_THEN` and `X_CHOOSE_THEN` may require special handling, as these tactics are specific to HOL Light. Additionally, the `REAL_ARITH_TAC` and `CONV_TAC REAL_RING` tactics may need to be replaced with equivalent arithmetic and conversion tactics in the target proof assistant.

---

## TRIANGLE_ANGLE_SUM

### Name of formal statement
TRIANGLE_ANGLE_SUM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TRIANGLE_ANGLE_SUM = prove
 (`!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> angle(B,A,C) + angle(A,B,C) + angle(B,C,A) = pi`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COS_MINUS1_LEMMA THEN
  ASM_SIMP_TAC[TRIANGLE_ANGLE_SUM_LEMMA; REAL_LE_ADD; ANGLE_RANGE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x <= p /\ &0 <= y /\ y <= p /\ &0 <= z /\ z <= p /\
    ~(x = p /\ y = p /\ z = p)
    ==> x + y + z < &3 * p`) THEN
  ASM_SIMP_TAC[ANGLE_RANGE] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP ANGLE_EQ_PI)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [GSYM VECTOR_SUB_EQ])) THEN
  REWRITE_TAC[GSYM NORM_EQ_0; dist; NORM_SUB] THEN REAL_ARITH_TAC)
```

### Informal statement
For all points A, B, and C in real N-dimensional space, if A, B, and C are distinct (i.e., A is not equal to B, A is not equal to C, and B is not equal to C), then the sum of the angles formed by the line segments BA, AC, and CB is equal to pi.

### Informal sketch
* The proof starts by assuming the existence of three distinct points A, B, and C.
* It then applies the `COS_MINUS1_LEMMA` to establish a relationship between the angles.
* The `TRIANGLE_ANGLE_SUM_LEMMA`, `REAL_LE_ADD`, and `ANGLE_RANGE` are used to simplify and derive properties of the angles.
* A real arithmetic statement is applied to show that the sum of the angles is bounded.
* Further simplifications and substitutions are made using `ANGLE_EQ_PI`, `VECTOR_SUB_EQ`, `NORM_EQ_0`, `dist`, and `NORM_SUB`.
* The final step involves real arithmetic manipulations to conclude the proof.

### Mathematical insight
This theorem is a fundamental property of geometry, stating that the sum of the interior angles of a triangle is always pi (or 180 degrees). The proof relies on a combination of geometric and real analysis principles, showcasing the power of formal proof assistants in verifying complex mathematical statements.

### Dependencies
* `COS_MINUS1_LEMMA`
* `TRIANGLE_ANGLE_SUM_LEMMA`
* `REAL_LE_ADD`
* `ANGLE_RANGE`
* `ANGLE_EQ_PI`
* `VECTOR_SUB_EQ`
* `NORM_EQ_0`
* `dist`
* `NORM_SUB`
* `REAL_ARITH`

### Porting notes
When translating this theorem to other proof assistants like Lean, Coq, or Isabelle, pay attention to the handling of real numbers, vector operations, and geometric concepts. The `REAL_ARITH` tactic may need to be replaced with equivalent arithmetic reasoning in the target system. Additionally, the use of `MATCH_MP_TAC` and `ASM_SIMP_TAC` may require adjustments to accommodate the specific tactic languages of the target proof assistants.

---

