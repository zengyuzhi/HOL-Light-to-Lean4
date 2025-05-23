# cosine.ml

## Overview

Number of statements: 18

`cosine.ml` formalizes trigonometric laws related to triangles, including the law of cosines, the law of sines, and the theorem regarding the sum of angles in a triangle. It depends on transcendental functions defined in `Multivariate/transcendentals.ml`. The file's primary goal is to provide formally verified versions of these fundamental trigonometric results.


## vangle

### Name of formal statement
vangle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let vangle = new_definition
 `vangle x y = if x = vec 0 \/ y = vec 0 then pi / &2
               else acs((x dot y) / (norm x * norm y))`;;
```

### Informal statement
The function `vangle` is defined such that, given two vectors *x* and *y*, `vangle x y` is equal to pi/2 if *x* is the zero vector or *y* is the zero vector; otherwise, `vangle x y` is equal to the arccosine of the real number resulting from the dot product of *x* and *y* divided by the product of the norms of *x* and *y*.

### Informal sketch
- The definition of `vangle` proceeds by cases based on whether either of the input vectors is the zero vector.
- If either vector is zero, the angle is defined to be π/2.
- Otherwise, the angle is defined using the arccosine (`acs`) function applied to the normalized dot product.
- The normalization ensures that the argument to `acs` is between -1 and 1, which is necessary for `acs` to be well-defined in the real numbers. The HOL Light system handles the proof obligations related to well-definedness automatically via the `new_definition` tactic.

### Mathematical insight
The `vangle` definition formalizes the notion of the angle between two vectors. If one or both vectors are zero, a conventional value of π/2 is chosen; otherwise, the standard formula using the dot product and norms (derived from the law of cosines) is employed. This function is central to geometric reasoning and is frequently used in proofs about vector spaces.

### Dependencies
- Defines: `vangle`
- Constants: `pi`, `vec`, `acs`, `dot`, `norm`
- Theorems: None explicitly required, but the definition relies on the well-definedness of `acs`, `dot`, and `norm`.


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
The angle between vectors `a` and `c` with respect to a central point `b`, denoted `angle(a,b,c)`, is defined to be the `vangle` between the vector from `b` to `a` (i.e., `a - b`) and the vector from `b` to `c` (i.e., `c - b`).

### Informal sketch
The definition introduces the term `angle(a, b, c)` as syntactic sugar for `vangle (a - b) (c - b)`. This leverages the existing `vangle` function, presumably defined elsewhere to compute the angle between two vectors. The definition effectively translates the geometric notion of an angle formed by three points into a vector calculation by considering displacement vectors from the vertex `b`.

### Mathematical insight
This definition provides a formal way to represent the angle formed by three points in a vector space. It relies on the notion of vector subtraction to represent the displacement from the central point `b` to the other points `a` and `c`, and then utilizes a previously defined `vangle` function to calculate the angle between those displacement vectors. The comment indicates it represents the "traditional geometric notion of angle" with the result constrained between 0 and pi, which likely means `vangle` computes the unsigned angle.

### Dependencies
- **Definitions:** `vangle`


---

## VANGLE

### Name of formal statement
VANGLE

### Type of the formal statement
theorem

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
  REAL_ARITH_TAC);;
```

### Informal statement
For all vectors `x` and `y` in `real^N`, the dot product of `x` and `y` equals the product of their norms and the cosine of the angle between them (`vangle x y`).

### Informal sketch
The proof proceeds as follows:
- Start by expanding the definition of `vangle`.
- Perform case analysis on whether `x` is the zero vector.
  - If `x` is the zero vector, simplify the dot product and norm of `x`, reducing the goal to verifying `0 = 0`.
  - If `x` is not the zero vector, perform case analysis on whether `y` is the zero vector.
    - If `y` is the zero vector, simplify the dot product and norm of `y` obtaining `0 = 0`.
    - If `y` is not the zero vector, rearrange the real multiplication.
    - Simplify using facts establishing the equivalence between the equality of real numbers and division, and inequalities for real multiplication and norms.
    - Apply the inverse of `COS_ACS` (probably an axiom stating that cosine has an inverse, `arccos`).
    - Simplify again using facts for real numbers and norms.
    - Apply a specialized version of the Cauchy-Schwarz inequality (`NORM_CAUCHY_SCHWARZ_ABS`).
    - Conclude by real arithmetic to show the final equality holds.

### Mathematical insight
This theorem provides a fundamental connection between the geometric notion of the angle between two vectors and their algebraic representation via the dot product and norms. It is a cornerstone of Euclidean geometry and linear algebra.

### Dependencies
- Definitions: `vangle`
- Theorems: `DOT_LZERO`, `NORM_0`, `REAL_MUL_LZERO`, `DOT_RZERO`, `REAL_MUL_RZERO`, `AC REAL_MUL_AC`, `REAL_EQ_LDIV_EQ`, `REAL_LT_MUL`, `NORM_POS_LT`, `COS_ACS`, `REAL_LE_RDIV_EQ`, `REAL_LE_LDIV_EQ`, `NORM_CAUCHY_SCHWARZ_ABS`


---

## VANGLE_RANGE

### Name of formal statement
VANGLE_RANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VANGLE_RANGE = prove
 (`!x y:real^N. &0 <= vangle x y /\ vangle x y <= pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vangle] THEN COND_CASES_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN MATCH_MP_TAC ACS_BOUNDS THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> -- &1 * a <= x /\ x <= &1 * a`) THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS]);;
```

### Informal statement
For all vectors `x` and `y` in `real^N`, the angle `vangle x y` between them is greater than or equal to 0 and less than or equal to pi.

### Informal sketch
The proof proceeds as follows:
- By universal generalization, consider arbitrary vectors `x` and `y` in `real^N`.
- Rewrite using the definition of `vangle`: `vangle x y = acs(x dot y / (norm x * norm y))`.
- Perform case analysis on the condition `norm x = &0 \/ norm y = &0`.
 - If `norm x = &0 \/ norm y = &0`, then it follows by `PI_POS` and real arithmetic.
 - If `~(norm x = &0 \/ norm y = &0)`, then we proceed as follows.
- Using `DE_MORGAN_THM`, rewrite the assumption `~(norm x = &0 \/ norm y = &0)` to `norm x <> &0 /\ norm y <> &0`.
- Apply the theorem `ACS_BOUNDS` which states that `!x. -1 <= x /\ x <= 1 ==> 0 <= acs x /\ acs x <= pi`. This requires showing that `-1 <= x dot y / (norm x * norm y) /\ x dot y / (norm x * norm y) <= 1`.
- Simplify using assumptions about real numbers and inequalities (e.g., `REAL_LE_RDIV_EQ`, `REAL_LE_LDIV_EQ`, `REAL_LT_MUL`, `NORM_POS_LT`).
- Use the theorem `REAL_ARITH abs(x) <= a ==> -- &1 * a <= x /\ x <= &1 * a` to show that `abs(x dot y / (norm x * norm y)) <= 1`.
- Rewrite using the Cauchy-Schwarz inequality `NORM_CAUCHY_SCHWARZ_ABS` in the form `abs(x dot y) <= norm x * norm y`.

### Mathematical insight
This theorem establishes the range of the `vangle` function, ensuring that the angle between any two vectors is within the expected interval [0, pi]. This aligns with the geometric interpretation of the angle between vectors. The proof relies on the Cauchy-Schwarz inequality to bound the dot product and properties of the `acs` (arccosine) function `ACS_BOUNDS`.

### Dependencies

**Theorems:**
- `PI_POS`
- `DE_MORGAN_THM`
- `ACS_BOUNDS`
- `REAL_LE_RDIV_EQ`
- `REAL_LE_LDIV_EQ`
- `REAL_LT_MUL`
- `NORM_POS_LT`
- `NORM_CAUCHY_SCHWARZ_ABS`

**Definitions:**
- `vangle`


---

## ORTHOGONAL_VANGLE

### Name of formal statement
ORTHOGONAL_VANGLE

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[NORM_EQ_0]]);;
```
### Informal statement
For all vectors `x` and `y` in the real vector space `real^N`, `x` and `y` are orthogonal if and only if the angle between `x` and `y` is equal to `pi / 2`.

### Informal sketch
The proof proceeds by establishing the equivalence between the `orthogonal` predicate and the condition `vangle x y = pi / 2`.
- First, the definition of `orthogonal` and `vangle` are expanded using `REWRITE_TAC`.
- Then, case distinction is made on whether `x` is the zero vector (`vec 0`).
    - If `x` is the zero vector, then `dot x y` is zero, which simplifies `vangle x y` to `pi / 2` if y is non-zero. Real arithmetic then shows that the equality holds in this case.
    - If `x` is not the zero vector, another case distinction is made based on whether `y` is the zero vector (`vec 0`).
        - If `y` is the zero vector, similar reasoning shows that `dot x y` is zero, and equality holds.
        - If neither `x` nor `y` are the zero vector, we need to show `dot x y = 0 <=> vangle x y = pi / 2`. Since both `x` and `y` are nonzero, `vangle x y = arccos (dot x y / (norm x * norm y))`. Thus proving the theorem reduces to showing `dot x y = 0 <=> arccos (dot x y / (norm x * norm y)) = pi/2`.
        - The right-to-left direction is accomplished using `ACS_COS` theorem which states that `arccos(x) = pi / 2 <=> x = cos (pi / 2) = 0`.
        -The left-to-right direction uses the Cauchy-Schwarz inequality (`NORM_CAUCHY_SCHWARZ_ABS`) to show that `abs (dot x y) <= norm x * norm y`, and the condition is `dot x y = 0`. Since norms are positive `(norm x * norm y) > 0`. Therefore, `abs (dot x y) / (norm x * norm y) <= 1`. Real arithmetic confirms `(dot x y) / (norm x * norm y) = 0`. Finally, `arccos 0 = pi/2` by `COS_PI2`.

### Mathematical insight
This theorem formalizes the well-known relationship between orthogonality and the angle between vectors. Two vectors are orthogonal if and only if the angle between them is 90 degrees (or `pi/2` radians). The theorem is important because it connects the geometric notion of orthogonality with the algebraic notion of the dot product.

### Dependencies
- `orthogonal`
- `vangle`
- `DOT_LZERO`
- `DOT_RZERO`
- `real_div`
- `REAL_MUL_LZERO`
- `COS_PI2`
- `ACS_COS`
- `PI_POS`
- `NORM_CAUCHY_SCHWARZ_ABS`
- `REAL_MUL_LID`
- `REAL_BOUNDS_LE`
- `REAL_MUL_LNEG`
- `REAL_LE_RDIV_EQ`
- `REAL_LE_LDIV_EQ`
- `REAL_LT_MUL`
- `NORM_POS_LT`
- `COS_ACS`
- `REAL_ENTIRE`
- `REAL_INV_EQ_0`
- `NORM_EQ_0`

### Porting notes (optional)
- The proof relies on rewriting with definitions and basic real arithmetic reasoning. Ensure the target proof assistant has similar capabilities for automated rewriting and real number reasoning.
- The proof uses HOL Light's `ASM_CASES_TAC` to perform case splits. This might need to be translated into explicit case distinctions or induction in other proof assistants.
- The manipulation of inequalities involving norms and real numbers might require some care, as different proof assistants may have varying levels of automation for such tasks.


---

## VANGLE_EQ_PI

### Name of formal statement
VANGLE_EQ_PI

### Type of the formal statement
theorem

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
  VECTOR_ARITH_TAC);;
```
### Informal statement
For any vectors `x` and `y` in `real^N`, if the `vangle` (vector angle) between `x` and `y` is equal to `pi`, then `norm(x) % y + norm(y) % x = vec 0`, where `vec 0` is the zero vector.

### Informal sketch
The proof proceeds as follows:
- Assume `vangle x y = pi`.
- Apply the definition of `vangle`, which states `vangle x y = acos (x dot y / (norm x * norm y))`. This makes the assumption `acos (x dot y / (norm x * norm y)) = pi`.
- Use `COS_PI`, which states `cos pi = -1`, to deduce `x dot y / (norm x * norm y) = -1`.
- Rearrange and multiply both sides by `norm x * norm y` to get `x dot y = - (norm x * norm y)`.
- Invoke `NORM_CAUCHY_SCHWARZ_EQ`, instantiated for `x` and `-y`, to state that `(norm x * norm (-y)) = abs (x dot (-y))`.
- Rewrite, using the properties of norms and dot products such as `NORM_NEG`, `DOT_RNEG` and `VECTOR_MUL_RNEG` to show that `(norm x) * (norm y) = - x dot y` is equivalent to `norm(x) * y + norm(y) * x = vec 0`.
- Apply vector arithmetic to complete the proof that `norm(x) % y + norm(y) % x = vec 0`

### Mathematical insight
The theorem essentially states that if the angle between two vectors is `pi` (i.e., they point in opposite directions), then a specific linear combination of these vectors is equal to the zero vector. This implies that the vectors are anti-parallel, and their magnitudes satisfy a particular relationship with respect to the zero vector.

### Dependencies
- `VANGLE`
- `COS_PI`
- `NORM_CAUCHY_SCHWARZ_EQ`
- `NORM_NEG`
- `DOT_RNEG`
- `VECTOR_MUL_RNEG`
- `REAL_MUL_RNEG`
- `REAL_NEG_NEG`
- `REAL_MUL_RID`


---

## ANGLE_EQ_PI

### Name of formal statement
ANGLE_EQ_PI

### Type of the formal statement
theorem

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
  REWRITE_TAC[dist; NORM_SUB]);;
```
### Informal statement
For all vectors `A`, `B`, and `C` in `real^N`, if the angle between `A`, `B`, and `C` is equal to `pi`, then the distance between `A` and `C` is equal to the sum of the distance between `A` and `B` and the distance between `B` and `C`.

### Informal sketch
The proof proceeds as follows:
- Assume `angle(A, B, C) = pi`.
- Rewrite `angle(A, B, C)` using the definition of `angle`.
- Apply the theorem `VANGLE_EQ_PI`, which states the condition for the angle `angle(A,B,C)` to be `pi` in terms of vectors. Specifically, `angle(A,B,C)=pi` if and only if there exists `x` such that `0 < x < 1` and `A + x * (C - A) = B`, by `MATCH_MP VANGLE_EQ_PI`.
- Rewrite the equation `a + x % (b - c) = vec 0 <=> a = x % (c - b)` where `%` denotes scalar multiplication and `vec 0` is the zero vector. This manipulation expresses `A = B + x % (A - C)`.
- Apply rewriting with `NORM_SUB` three times using `funpow 3 LAND_CONV`.
- Rewrite using the symmetric form of the triangle equality, `GSYM NORM_TRIANGLE_EQ`. The triangle equality states that `dist(x, z) <= dist(x, y) + dist(y, z)`.
- Simplify the vector expression `(B - A) + (C - B) = C - A`.
- Rewrite using the definition of `dist`, and apply simplification using `NORM_SUB`.

### Mathematical insight
This theorem states that if three points `A`, `B`, and `C` in `N`-dimensional real space form a straight line with `B` between `A` and `C`, then the distance from `A` to `C` is the sum of the distances from `A` to `B` and from `B` to `C`. This is a geometric interpretation of the triangle equality in the special case of collinear points.

### Dependencies
- Definitions: `angle`, `dist`
- Theorems: `VANGLE_EQ_PI`, `NORM_TRIANGLE_EQ`
- Other: `VECTOR_ARITH` which likely contains several vector arithmetic lemmas and tactics such as `NORM_SUB`

### Porting notes (optional)
- The theorem `VANGLE_EQ_PI` is crucial. Its accurate translation is important for porting this theorem.
- The `VECTOR_ARITH` tactic is a black box. It hides potentially many rewrites pertaining to vector arithmetic. Pay attention to how vector normalisation and simplification are handled in the target proof assistant.


---

## SIN_ANGLE_POS

### Name of formal statement
SIN_ANGLE_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_ANGLE_POS = prove
 (`!A B C. &0 <= sin(angle(A,B,C))`,
  SIMP_TAC[SIN_POS_PI_LE; angle; VANGLE_RANGE]);;
```
### Informal statement
For all points `A`, `B`, and `C` in a 2D plane, the sine of the angle formed by these points (angle `ABC`) is greater than or equal to 0.

### Informal sketch
The theorem is proved using simplification (`SIMP_TAC`) with the following facts:
- `SIN_POS_PI_LE`: The sine function is non-negative for angles between 0 and pi (inclusive).
- `angle`: Definition of the angle between three points.
- `VANGLE_RANGE`: The `angle` function returns a value between 0 and pi (inclusive).

The proof demonstrates that since the angle between any three points is within the range [0, pi], the sine of that angle is non-negative.

### Mathematical insight
This theorem formalizes the geometric intuition that the sine of an angle formed by three points in Euclidean space is always non-negative, given the standard convention that angles are measured in the range [0, pi]. This is a basic but important result in geometry and is frequently used in reasoning about triangles and other geometric figures.

### Dependencies
- Theorems: `SIN_POS_PI_LE`
- Definitions: `angle`
- Theorems: `VANGLE_RANGE`


---

## ANGLE

### Name of formal statement
ANGLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE = prove
 (`!A B C. (A - C) dot (B - C) = dist(A,C) * dist(B,C) * cos(angle(A,C,B))`,
  REWRITE_TAC[angle; dist; GSYM VANGLE]);;
```

### Informal statement
For all points `A`, `B`, and `C` in two-dimensional space, the dot product of the vector from `C` to `A` and the vector from `C` to `B` is equal to the product of the distance from `A` to `C`, the distance from `B` to `C`, and the cosine of the angle `angle(A,C,B)`.

### Informal sketch
The proof involves demonstrating the relationship between the dot product of two vectors and the cosine of the angle between them, in the context of points in a plane. Specifically, the relationship between the dot product `(A - C) dot (B - C)` and the cosine of the angle `angle(A, C, B)` is established, while also incorporating the distances `dist(A, C)` and `dist(B, C)`.

- Start with the definition of the angle `angle(A, C, B)`.
- Apply rewriting rules using `dist` to express distances between points in vector form.
- Use the theorem `VANGLE`, likely a previously established theorem that equates `(A-C) dot (B-C)` with `dist(A,C) * dist(B,C) * cos(angle(A,C,B))`.
- Use `GSYM` to reverse the equality direction of `VANGLE` given we want to end up with the dot product on the left.
- Apply equational reasoning (rewriting) to arrive at the final equation.

### Mathematical insight
This theorem provides a fundamental connection between vector algebra (dot product) and trigonometry (cosine of an angle) in a two-dimensional space. It formalizes the geometric intuition that the dot product of two vectors is related to the cosine of the angle between them scaled by the magnitudes (distances) of the vectors. This result is essential for various geometric and vector-based calculations.

### Dependencies
- `angle`
- `dist`
- `VANGLE`


---

## ANGLE_REFL

### Name of formal statement
ANGLE_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE_REFL = prove
 (`!A B. angle(A,A,B) = pi / &2 /\
         angle(B,A,A) = pi / &2`,
  REWRITE_TAC[angle; vangle; VECTOR_SUB_REFL]);;
```
### Informal statement
For all points `A` and `B`, the angle `angle(A,A,B)` is equal to `pi / 2`, and the angle `angle(B,A,A)` is equal to `pi / 2`.

### Informal sketch
The proof involves rewriting the equation using the definitions of `angle` and `vangle`, and then applying the reflexivity of vector subtraction.
- The theorem claims that `angle(A,A,B) = pi / &2` and `angle(B,A,A) = pi / &2`. The tactic `REWRITE_TAC` is used with the theorems `angle`, `vangle` and `VECTOR_SUB_REFL`.
- The definition `angle` expresses the angle between vectors using `vangle`, which involves vector subtraction.
- The theorem `VECTOR_SUB_REFL` states that the subtraction of a vector from itself is zero, i.e. `x - x = 0`.
- By applying these rewrites, the goal is simplified to a trivial equality, which can be discharged automatically.

### Mathematical insight
This theorem states that the angle formed by two identical points and a third distinct point is a right angle (π/2). This is a fundamental property of angles in Euclidean geometry. The points `A`, `A`, and `B` form degenerate triangle, and the angle at the duplicated vertex `A` will be a right angle.

### Dependencies
- Definitions: `angle`, `vangle`
- Theorems: `VECTOR_SUB_REFL`


---

## ANGLE_REFL_MID

### Name of formal statement
ANGLE_REFL_MID

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE_REFL_MID = prove
 (`!A B. ~(A = B) ==> angle(A,B,A) = &0`,
  SIMP_TAC[angle; vangle; VECTOR_SUB_EQ; GSYM NORM_POW_2; GSYM REAL_POW_2;
           REAL_DIV_REFL; ACS_1; REAL_POW_EQ_0; ARITH; NORM_EQ_0]);;
```

### Informal statement
For all points `A` and `B`, if `A` is not equal to `B`, then the angle at `B` formed by the vectors from `B` to `A` and from `B` to `A` is equal to 0.

### Informal sketch
The proof proceeds as follows:

- Assume `A` is not equal to `B`.
- By definition of `angle(A, B, A)`, we have `vangle(vector_sub(A, B), vector_sub(A, B))`.
- Simplify using `vector_sub(A, B)` being equal to itself.
- The `vangle` of a vector with itself is 0, due to the properties of the dot product and norm.
- The `NORM_POW_2` and `REAL_POW_2` lemmas are used to simplify the norm squared.
- `REAL_DIV_REFL` simplifies `x / x` to 1, when `x` is not zero (since `A` and `B` are distinct implying the norm is nonzero, `NORM_EQ_0`).
- The `ACS_1` tactic likely handles the acos(1) = 0 simplification.
- `REAL_POW_EQ_0` handles cases where real powers are zero in the denominator.
- `ARITH` likely handles any remaining arithmetic simplifications.

### Mathematical insight
This theorem states that the angle formed by a vector with itself at a common point is zero. This is a fundamental property of angles and vectors in Euclidean space. It demonstrates the consistency of the formal definition of angles with geometric intuition.

### Dependencies
- Definitions: `angle`, `vangle`
- Theorems: `VECTOR_SUB_EQ`, `GSYM NORM_POW_2`, `GSYM REAL_POW_2`, `REAL_DIV_REFL`, `ACS_1`, `REAL_POW_EQ_0`, `ARITH`, `NORM_EQ_0`

### Porting notes (optional)
- The `SIMP_TAC` is a simplification tactic; other proof assistants might require a different approach to achieve the same level of automation. `ACS_1` corresponds to the property that `arccos(1) = 0`. This might need to be explicitly stated, proved or invoked in other provers. The handling of real number arithmetic and division by zero should be checked to ensure the target prover behaves equivalently to HOL Light.


---

## ANGLE_SYM

### Name of formal statement
ANGLE_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE_SYM = prove
 (`!A B C. angle(A,B,C) = angle(C,B,A)`,
  REWRITE_TAC[angle; vangle; VECTOR_SUB_EQ; DISJ_SYM; REAL_MUL_SYM; DOT_SYM]);;
```

### Informal statement
For all points `A`, `B`, and `C`, the angle between the vectors from `B` to `A` and from `B` to `C` is equal to the angle between the vectors from `B` to `C` and from `B` to `A`.

### Informal sketch
The proof relies on rewriting with the following identities:
- Definition of `angle` in terms of `vangle`: `angle(A,B,C) = vangle(vector_sub(A, B), vector_sub(C, B))`
- Definition of `vangle` in terms of `dot` and vector magnitudes.
- `VECTOR_SUB_EQ`: vector subtraction distributes over equality.
- `DISJ_SYM`: commutativity of disjunction.
- `REAL_MUL_SYM`: commutativity of real multiplication.
- `DOT_SYM`: commutativity of the dot product.
The main idea is to use vector subtraction to represent the lines connecting the point `B` to `A` and `C` then to show that the expressions are equal due to the symmetric nature of the dot product.

### Mathematical insight
The theorem `ANGLE_SYM` expresses the symmetry of the angle between two lines emanating from a common point.  It states that the order in which the lines are considered does not affect the measure of the angle. This is a fundamental property of angles and is essential for many geometric proofs.

### Dependencies
- Definitions: `angle`, `vangle`
- Theorems: `VECTOR_SUB_EQ`, `DISJ_SYM`, `REAL_MUL_SYM`, `DOT_SYM`


---

## ANGLE_RANGE

### Name of formal statement
ANGLE_RANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANGLE_RANGE = prove
 (`!A B C. &0 <= angle(A,B,C) /\ angle(A,B,C) <= pi`,
  REWRITE_TAC[angle; VANGLE_RANGE]);;
```
### Informal statement
For all points `A`, `B`, and `C` in two-dimensional space, the angle `angle(A,B,C)` is greater than or equal to 0 and less than or equal to pi.

### Informal sketch
The proof relies on rewriting using the definition of `angle` and the range restriction of `VANGLE_RANGE`.
- The tactic `REWRITE_TAC` is used to apply the definitions of `angle` and `VANGLE_RANGE`.
- The goal is to prove that the angle `angle(A, B, C)` lies within the range [0, pi].
- `angle(A, B, C)` is equivalent to `VANGLE(vector(B,A), vector(B,C))`.
- `VANGLE_RANGE` ensures that `VANGLE` always falls within the range [0, pi].

### Mathematical insight
This theorem establishes the range of the `angle` function, ensuring that angles are always non-negative and do not exceed pi radians (180 degrees). This is consistent with the convention of measuring angles in geometry.

### Dependencies
- Definitions: `angle`
- Theorems: `VANGLE_RANGE`


---

## LAW_OF_COSINES

### Name of formal statement
LAW_OF_COSINES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LAW_OF_COSINES = prove
 (`!A B C:real^N.
     dist(B,C) pow 2 = dist(A,B) pow 2 + dist(A,C) pow 2 -
                         &2 * dist(A,B) * dist(A,C) * cos(angle(B,A,C))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[angle; ONCE_REWRITE_RULE[NORM_SUB] dist; GSYM VANGLE;
              NORM_POW_2] THEN
  VECTOR_ARITH_TAC);;
```

### Informal statement
For all real vectors `A`, `B`, and `C` in `N` dimensions, the square of the distance between `B` and `C` is equal to the sum of the square of the distance between `A` and `B` and the square of the distance between `A` and `C`, minus twice the product of the distance between `A` and `B`, the distance between `A` and `C`, and the cosine of the angle `angle(B,A,C)`.

### Informal sketch
The proof proceeds as follows:
- Universally quantify over the vectors `A`, `B`, and `C`.
- Rewrite using the definitions of the `angle` and `dist` functions. Apply `NORM_SUB` once for the definition of `dist`. Rewrite using the symmetric version of `VANGLE` and the simplifier `NORM_POW_2`.
- Apply `VECTOR_ARITH_TAC` to complete the proof using vector arithmetic.

### Mathematical insight
This theorem is the law of cosines, a fundamental result in Euclidean geometry that relates the lengths of the sides of a triangle to the cosine of one of its angles. It generalizes the Pythagorean theorem, which applies only to right triangles. The statement is formulated in terms of general `N`-dimensional real vectors.

### Dependencies
- `angle`
- `dist`
- `VANGLE`
- `NORM_POW_2`
- `NORM_SUB`

### Porting notes (optional)
- The definitions of `angle` and `dist` and `VANGLE` need to be available. The proof also makes use of a `VECTOR_ARITH_TAC`, so the target proof assistant needs similar automation for vector arithmetic.


---

## LAW_OF_SINES

### Name of formal statement
LAW_OF_SINES

### Type of the formal statement
theorem

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
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN CONV_TAC REAL_RING);;
```
### Informal statement
For any points `A`, `B`, and `C` in a real n-dimensional space, the sine of the angle at `B` (i.e., `angle(A,B,C)`) multiplied by the distance between `B` and `C` is equal to the sine of the angle at `A` (i.e., `angle(B,A,C)`) multiplied by the distance between `A` and `C`.

### Informal sketch
The proof proceeds as follows:
- First, generalize the goal using `REPEAT GEN_TAC`.
- Then apply the theorem `REAL_POW_EQ` using `MATCH_MP_TAC`. Existentially quantify `2` using `EXISTS_TAC`.
- Simplify using `SIN_ANGLE_POS`, `DIST_POS_LE`, `REAL_LE_MUL`, and basic arithmetic theorems using `SIMP_TAC`.
- Rewrite using `REAL_POW_MUL` and the sine circle property (`SIN_CIRCLE`) using `REWRITE_TAC`.
- Consider the case where `A = B` using `ASM_CASES_TAC`. In this case, simplify using `ANGLE_REFL` and `COS_PI2` using `ASM_REWRITE_TAC`. Apply simplification rules related to vector subtraction and norm definitions when `A = B` using `RULE_ASSUM_TAC`. Further, apply a real number simplification rule using `FIRST_X_ASSUM`.
- Next rewrite using the symmetry of distance function using `ONCE_REWRITE_TAC`, and then rewrite using `DIST_SYM` and `dist`.
- Use `GEN_REWRITE_TAC` to apply `DIST_SYM` deeply.
- Perform algebraic manipulations using `REAL_RING` through rewriting using `REWRITE_TAC`.
- Rewrite the powers and angles, using `REAL_POW_MUL` and `ANGLE`.
- Rewrite the powers, distances, and norms using `REAL_POW_MUL`, `dist`, and `NORM_POW_2`.
- Rewrite the dot products using properties like `DOT_LSUB`, `DOT_RSUB`, and `DOT_SYM`.
- Finally, use ring simplification using `CONV_TAC`.

### Mathematical insight
This theorem represents the Law of Sines, a fundamental trigonometric identity relating the sides of a triangle to the sines of its angles. The formalization extends this law to triangles embedded in n-dimensional real space. This shows how trigonometry generalizes beyond 2 dimensions.

### Dependencies
- `SIN_ANGLE_POS`
- `DIST_POS_LE`
- `REAL_LE_MUL`
- `ARITH`
- `REAL_POW_MUL`
- `SIN_CIRCLE`
- `ANGLE_REFL`
- `COS_PI2`
- `VECTOR_SUB_EQ`
- `NORM_EQ_0`
- `REAL_RING`
- `DIST_SYM`
- `dist`
- `NORM_POW_2`
- `DOT_LSUB`
- `DOT_RSUB`
- `DOT_SYM`

### Porting notes (optional)
The proof relies heavily on real number arithmetic and vector space properties. Pay close attention to how the target proof assistant handles the interaction between real numbers, vectors and trigonometric functions. The `REAL_RING` tactic is very powerful in HOL Light, so make sure that the target system has similar algebraic simplification capabilities to complete the proof.


---

## TRIANGLE_ANGLE_SUM_LEMMA

### Name of formal statement
TRIANGLE_ANGLE_SUM_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_ANGLE_SUM_LEMMA = prove
 (`!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> cos(angle(B,A,C) + angle(A,B,C) + angle(B,C,A)) = -- &1`,
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
  REWRITE_TAC[COS_ADD; SIN_ADD; ANGLE_SYM] THEN CONV_TAC REAL_RING);;
```

### Informal statement
For all points A, B, and C in N-dimensional real space, if A is not equal to B, A is not equal to C, and B is not equal to C, then the cosine of the sum of the angles `angle(B,A,C)`, `angle(A,B,C)`, and `angle(B,C,A)` is equal to -1.

### Informal sketch
The proof demonstrates that the cosine of the sum of the interior angles of a triangle is -1, implying that the sum of the angles is π (180 degrees). The proof proceeds as follows:
- Assume `~(A = B) /\ ~(A = C) /\ ~(B = C)`.
- Rewrite using `VECTOR_SUB_EQ` and `NORM_EQ_0`.
- Apply the `LAW_OF_COSINES` to the angles `angle(B,A,C)`, `angle(A,B,C)`, and `angle(B,C,A)`.
- Apply the `LAW_OF_SINES` to the angles `angle(B,A,C)`, `angle(A,B,C)`, and `angle(B,C,A)`.
- Rewrite using trigonometric identities for `COS_ADD` and `SIN_ADD`, along with the definitions of `dist` and `NORM_SUB`.
- Apply `SIN_CIRCLE` to each of the angles `angle(B,A,C)`, `angle(A,B,C)`, and `angle(B,C,A)`.
- Rewrite using `COS_ADD`, `SIN_ADD`, and `ANGLE_SYM`.
- Simplify the resulting expression using `REAL_RING`.

### Mathematical insight
This theorem states the well-known result that the sum of the interior angles of a triangle in Euclidean space is equal to π radians (180 degrees), expressed in terms of the cosine of that sum being -1. The conditions `~(A = B) /\ ~(A = C) /\ ~(B = C)` ensure that the points A, B, and C are distinct, which is required to form a nondegenerate triangle.

### Dependencies
**Theorems/Definitions:**
- `VECTOR_SUB_EQ`
- `NORM_EQ_0`
- `LAW_OF_COSINES`
- `LAW_OF_SINES`
- `COS_ADD`
- `SIN_ADD`
- `dist`
- `NORM_SUB`
- `SIN_CIRCLE`
- `ANGLE_SYM`
- `REAL_RING`


---

## COS_MINUS1_LEMMA

### Name of formal statement
COS_MINUS1_LEMMA

### Type of the formal statement
theorem

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
  REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers `x`, if `cos(x) = -1`, `0 <= x`, and `x < 3 * pi`, then `x = pi`.

### Informal sketch
The proof proceeds as follows:
- Assume `cos(x) = -1`, `0 <= x`, and `x < 3 * pi`.
- Prove the existence of an integer `n` such that `x = n * pi`.
  - Introduce a real number `nn` such that `x = nn * pi`.
  - Use `SIN_EQ_0` (Sine equals zero iff argument is an integer multiple of pi) and `SIN_CIRCLE` (`sin(x)^2 + cos(x)^2 = 1`). Since cos(x)=-1, sin(x)=0.
  - Deduce `x` must be an integer multiple of `pi`, say `nn * pi`.
- Prove that `nn` is a real representation of a natural number `n`.
  - Introduce a natural number `n` such that `nn = &n` (real representation of `n`).
  - Establish bounds on `n` using `REAL_MUL_POS_LE`, `PI_POS`, `INTEGER_POS`, and `REAL_LT_LE`. Using inequalities, show that `0 <= n` and `n < 3`.
- Show that `n` must be `1`. Rules out `n = 0` since `x >= 0` and `n = 2` because `x < 3 * pi`, and if `x = 2 * pi` then `x` must equal `pi`. This relies on `COS_0`, `REAL_MUL_LZERO`, and `COS_NPI`.
- Therefore, `x = pi`.

### Mathematical insight
This theorem provides a unique solution for `x` when `cos(x) = -1` within the interval `[0, 3*pi)`. It's a basic but important result in trigonometry, useful for solving trigonometric equations and understanding the behavior of the cosine function.

### Dependencies
- `SIN_EQ_0`
- `SIN_CIRCLE`
- `PI_POS`
- `INTEGER_POS`
- `COS_0`
- `REAL_MUL_LZERO`
- `COS_NPI`
- `REAL_MUL_POS_LE`
- `REAL_LT_LE`
- `REAL_OF_NUM_EQ`
- `REAL_OF_NUM_LT`
- `REAL_RING`
- `ARITH_RULE`

### Porting notes (optional)
The proof relies heavily on real arithmetic and properties of trigonometric functions. A proof assistant with strong support for real numbers and trigonometric identities will be beneficial. The use of tactics like `REAL_ARITH_TAC` suggests a need for good automation in real arithmetic.


---

## TRIANGLE_ANGLE_SUM

### Name of formal statement
TRIANGLE_ANGLE_SUM

### Type of the formal statement
theorem

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
  REWRITE_TAC[GSYM NORM_EQ_0; dist; NORM_SUB] THEN REAL_ARITH_TAC);;
```
### Informal statement
For all real vectors `A`, `B`, and `C` such that `A` is not equal to `B`, `A` is not equal to `C`, and `B` is not equal to `C`, the sum of the angle at `A` formed by `B`, `A`, and `C`, the angle at `B` formed by `A`, `B`, and `C`, and the angle at `C` formed by `B`, `C`, and `A` is equal to `pi`.

### Informal sketch
The proof proceeds as follows:

- Start by stripping the quantifiers and assumptions. This introduces the assumptions `~(A = B)`, `~(A = C)`, and `~(B = C)` into the assumptions.
- Apply `COS_MINUS1_LEMMA`.
- Simplify using `TRIANGLE_ANGLE_SUM_LEMMA`, `REAL_LE_ADD`, and `ANGLE_RANGE`.
- Apply a real arithmetic lemma establishing that if `x`, `y`, and `z` are in the interval `[0, pi]` and not all equal to `pi`, then their sum is strictly less than `3 * pi`.
- Simplify using `ANGLE_RANGE`.
- Repeatedly use the fact that if the angle is zero/pi, then the points are equal (collinear/overlapping).
- Rewrite using the fact that if `vector_sub(x, y) = vector_sub(z, y)` then `x = z`.
- Rewrite `norm (x - y) = 0` to `x = y` after rewriting `dist` and `NORM_SUB`.
- Finally, use real arithmetic to complete the proof.

### Mathematical insight
This theorem states that the sum of the interior angles of a triangle in Euclidean space is equal to `pi` (180 degrees). This is a fundamental result in Euclidean geometry.

### Dependencies
- `COS_MINUS1_LEMMA`
- `TRIANGLE_ANGLE_SUM_LEMMA`
- `REAL_LE_ADD`
- `ANGLE_RANGE`
- `ANGLE_EQ_PI`
- `VECTOR_SUB_EQ`
- `NORM_EQ_0`
- `dist`
- `NORM_SUB`


---

