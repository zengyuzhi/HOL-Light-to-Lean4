# independence.ml

## Overview

Number of statements: 46

The `independence.ml` file formalizes the independence of the parallel postulate in the context of Tarski's axioms for geometry. It shows that the Klein model of the hyperbolic plane satisfies all Tarski's axioms except the Euclidean axiom, using modified definitions of betweenness and congruence of segments. This result, combined with the proofs in `tarski.ml`, demonstrates the independence of the Euclidean axiom from the others. The file builds upon the `cauchy.ml` and `tarski.ml` files in the Multivariate library.

## ddist

### Name of formal statement
ddist

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let ddist = new_definition
 `ddist(x:real^N,y:real^N) =
    if norm(x) < &1 /\ norm(y) < &1 then
     (&1 - x dot y) pow 2 / ((&1 - norm(x) pow 2) * (&1 - norm(y) pow 2)) - &1
    else dist(x,y)`;;
```

### Informal statement
The function `ddist` is defined on pairs of vectors `x` and `y` in `real^N`. If both `x` and `y` have a norm less than 1, then `ddist(x, y)` is defined as `((1 - x dot y)^2) / ((1 - norm(x)^2) * (1 - norm(y)^2)) - 1`. Otherwise, `ddist(x, y)` is defined as the distance between `x` and `y`, denoted by `dist(x, y)`.

### Informal sketch
* The definition of `ddist` involves a conditional statement based on the norms of `x` and `y`.
* If both `x` and `y` are within the unit ball (i.e., their norms are less than 1), the function `ddist` calculates a specific expression involving the dot product and norms of `x` and `y`.
* The expression `(&1 - x dot y) pow 2 / ((&1 - norm(x) pow 2) * (&1 - norm(y) pow 2)) - &1` suggests a geometric interpretation related to the angles and lengths of vectors `x` and `y`.
* If either `x` or `y` (or both) has a norm greater than or equal to 1, the function defaults to the standard distance metric `dist(x, y)`.

### Mathematical insight
The definition of `ddist` appears to be a semimetric tailored for the context of hyperbolic geometry, particularly within the unit ball of `real^N`. The conditional definition ensures that the function behaves differently inside and outside the unit ball, reflecting the distinct geometric properties of these regions. This construction is crucial for models of hyperbolic geometry, such as the Klein model, which is mentioned in the context of Tarski's axioms for geometry.

### Dependencies
* `norm`
* `dist`
* `dot`

### Porting notes
When translating this definition into other proof assistants, pay attention to how each system handles conditional definitions and vector operations. Specifically, the use of `&1` for the real number 1, and the `pow` function for exponentiation, may need to be adjusted according to the target system's syntax and libraries. Additionally, ensuring that the norm and dot product operations are correctly defined and used is essential for a faithful porting of the `ddist` function.

---

## DDIST_INCREASES_ONLINE

### Name of formal statement
DDIST_INCREASES_ONLINE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_INCREASES_ONLINE = prove
 (`!a b x:real^N.
      norm a < &1 /\ norm b < &1 /\ norm x < &1 /\ between x (a,b) /\ ~(x = b)
      ==> ddist(a,x) < ddist(a,b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [ASM_MESON_TAC[BETWEEN_REFL_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[ddist; real_div; REAL_INV_MUL] THEN
  SUBGOAL_THEN
   `norm(a:real^N) pow 2 < &1 /\ norm(b:real^N) pow 2 < &1 /\
    norm(x:real^N) pow 2 < &1`
  MP_TAC THENL [ASM_SIMP_TAC[ABS_SQUARE_LT_1; REAL_ABS_NORM]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a * inv x * inv b - &1 < c * inv x * d - &1 <=>
                          (a / b) / x < (c * d) / x`] THEN
  SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LT_LDIV_EQ; REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * inv b) * c:real = (a * c) / b`] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_SUB_LT] THEN
  SUBGOAL_THEN `(a:real^N) dot b < &1 /\ (a:real^N) dot x < &1` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(MESON[REAL_LET_TRANS; NORM_CAUCHY_SCHWARZ]
     `norm(x) * norm(y) < &1 ==> (x:real^N) dot y < &1`) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BETWEEN_IN_SEGMENT]) THEN
  REWRITE_TAC[IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `u:real` THEN
  ASM_CASES_TAC `u = &1` THEN
  ASM_SIMP_TAC[VECTOR_ARITH `(&1 - &1) % a + &1 % b:real^N = b`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[VECTOR_ARITH `(&1 - u) % a + u % b:real^N = a + u % (b - a)`] THEN
  ABBREV_TAC `c:real^N = b - a` THEN
  SUBGOAL_THEN `b:real^N = a + c` SUBST_ALL_TAC THENL
   [EXPAND_TAC "c" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(SIMP_RULE[VECTOR_ARITH `a + c:real^N = a <=> c = vec 0`]) THEN
  REWRITE_TAC[NORM_POW_2; VECTOR_ARITH
    `(a + b:real^N) dot (a + b) = a dot a + &2 * a dot b + b dot b`] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REWRITE_TAC[DOT_LMUL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ARITH
   `(&1 - (a + x * b)) pow 2 * (&1 - (a + &2 * b + c)) <
    (&1 - (a + b)) pow 2 * (&1 - (a + &2 * x * b + x * x * c)) <=>
    &0 < (&1 - a - b * x) * ((&1 - a) * c + b pow 2) * (&1 - x) +
         (&1 - a - b) * ((&1 - a) * c + b pow 2) * (&1 - x) * x`] THEN
  MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC);
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC)] THEN
  TRY ASM_REAL_ARITH_TAC THEN TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN
  MATCH_MP_TAC REAL_LTE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT; REAL_SUB_LT])
```

### Informal statement
For all real vectors `a`, `b`, and `x` in `ℝ^N`, if the norm of `a` is less than 1, the norm of `b` is less than 1, the norm of `x` is less than 1, `x` is between `a` and `b`, and `x` is not equal to `b`, then the distance from `a` to `x` is less than the distance from `a` to `b`.

### Informal sketch
* The proof starts by considering the case when `b` equals `a`, which is handled using `BETWEEN_REFL_EQ`.
* It then applies various simplifications and arithmetic properties, including `ddist`, `real_div`, and `REAL_INV_MUL`.
* The proof proceeds by assuming certain inequalities involving the norms and dot products of `a`, `b`, and `x`, and derives further inequalities using properties like `REAL_LT_DIV2_EQ`, `REAL_LT_LDIV_EQ`, and `REAL_SUB_LT`.
* The `BETWEEN_IN_SEGMENT` property is used to express `x` as a convex combination of `a` and `b`, which is then manipulated using vector arithmetic.
* The proof involves several case analyses, including one on whether `u` equals 1, and applies various tactics like `ASM_SIMP_TAC`, `MATCH_MP_TAC`, and `REWRITE_TAC` to simplify and derive the desired inequality.
* Key steps involve using `NORM_CAUCHY_SCHWARZ` to bound dot products, `REAL_LT_MUL2` to derive inequalities from products, and `REAL_LE_POW_2` to handle squared terms.

### Mathematical insight
This theorem provides a property about the distance between points in a high-dimensional space, specifically that the distance from a point `a` to a point `x` between `a` and `b` is less than the distance from `a` to `b`, under certain conditions on the norms of `a`, `b`, and `x`. This property is likely useful in geometric or metric space arguments, where understanding how distances between points behave under various conditions is crucial.

### Dependencies
* Theorems:
  + `BETWEEN_REFL_EQ`
  + `REAL_INV_MUL`
  + `REAL_LT_DIV2_EQ`
  + `REAL_LT_LDIV_EQ`
  + `REAL_SUB_LT`
  + `NORM_CAUCHY_SCHWARZ`
  + `REAL_LT_MUL2`
  + `REAL_LE_POW_2`
  + `DOT_POS_LT`
* Definitions:
  + `ddist`
  + `real_div`
  + `BETWEEN_IN_SEGMENT`
  + `NORM_POW_2`
  + `VECTOR_ARITH`

---

## DDIST_REFL

### Name of formal statement
DDIST_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_REFL = prove
 (`!x:real^N. ddist(x,x) = &0`,
  GEN_TAC THEN REWRITE_TAC[ddist; DIST_REFL; NORM_POW_2; NORM_LT_SQUARE] THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For all vectors `x` in the real vector space of dimension `N`, the distance between `x` and itself, denoted as `ddist(x, x)`, is equal to `0`.

### Informal sketch
* The proof starts by generalizing the statement for all `x` using `GEN_TAC`.
* It then applies `REWRITE_TAC` to rewrite the `ddist` term using definitions of `ddist`, `DIST_REFL`, `NORM_POW_2`, and `NORM_LT_SQUARE`.
* The `CONV_TAC REAL_FIELD` is used to apply the field properties of real numbers to conclude the proof.
* Key steps involve recognizing that the distance of a point to itself is zero, which is a fundamental property of metric spaces.

### Mathematical insight
This theorem formalizes a basic property of distance metrics in vector spaces, specifically that the distance between a point and itself is always zero. This property is crucial in various mathematical and computational contexts, such as geometry, analysis, and computational geometry, where distances and metrics are fundamental.

### Dependencies
- **Definitions:**
  - `ddist`
  - `DIST_REFL`
  - `NORM_POW_2`
  - `NORM_LT_SQUARE`
- **Theorems/Tactics:**
  - `GEN_TAC`
  - `REWRITE_TAC`
  - `CONV_TAC REAL_FIELD`

### Porting notes
When porting this theorem to another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles vector spaces, metrics, and real numbers. Specifically, the equivalents of `ddist`, `DIST_REFL`, `NORM_POW_2`, and `NORM_LT_SQUARE` need to be identified or defined. Additionally, the automation and tactic structure may differ, requiring adjustments to the proof script to align with the target system's proof assistant mechanisms.

---

## DDIST_SYM

### Name of formal statement
DDIST_SYM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_SYM = prove
 (`!x y:real^N. ddist(x,y) = ddist(y,x)`,
  REWRITE_TAC[ddist; CONJ_ACI; REAL_MUL_AC; DIST_SYM; DOT_SYM])
```

### Informal statement
For all real vectors `x` and `y` of dimension `N`, the distance between `x` and `y` is equal to the distance between `y` and `x`.

### Informal sketch
* The proof of `DDIST_SYM` involves showing that the distance function `ddist` is symmetric.
* The `REWRITE_TAC` tactic is used with several rewrite rules, including `ddist`, `CONJ_ACI`, `REAL_MUL_AC`, `DIST_SYM`, and `DOT_SYM`, to simplify the equality `ddist(x,y) = ddist(y,x)`.
* The key insight is that the definition of `ddist` and the properties of real numbers and vector operations allow for the symmetric property to be derived.

### Mathematical insight
The `DDIST_SYM` theorem captures the intuitive notion that the distance between two points in space is the same regardless of the order in which the points are considered. This symmetry property is a fundamental aspect of distance metrics and is essential in various mathematical and scientific applications.

### Dependencies
* `ddist`
* `CONJ_ACI`
* `REAL_MUL_AC`
* `DIST_SYM`
* `DOT_SYM`

### Porting notes
When translating `DDIST_SYM` into other proof assistants, pay attention to the handling of vector operations and the properties of real numbers. The `REWRITE_TAC` tactic may need to be replaced with equivalent tactics or strategies in the target system. Additionally, the rewrite rules used in the proof, such as `ddist` and `DIST_SYM`, may require corresponding definitions or theorems in the target system.

---

## DDIST_POS_LT

### Name of formal statement
DDIST_POS_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_POS_LT = prove
 (`!x y:real^N. ~(x = y) ==> &0 < ddist(x,y)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `norm(x:real^N) < &1 /\ norm(y:real^N) < &1` THENL
   [ASM_MESON_TAC[DDIST_INCREASES_ONLINE; DDIST_REFL; BETWEEN_REFL];
    ASM_SIMP_TAC[ddist; DIST_POS_LT]]);;
```

### Informal statement
For all real-valued vectors `x` and `y` in `real^N`, if `x` is not equal to `y`, then the distance between `x` and `y` (denoted by `ddist(x, y)`) is greater than `0`.

### Informal sketch
* The proof starts by assuming that `x` and `y` are not equal.
* It then considers two cases based on the norms of `x` and `y` being less than `1`.
* In the first case, where both norms are less than `1`, it applies `ASM_MESON_TAC` with the theorems `DDIST_INCREASES_ONLINE`, `DDIST_REFL`, and `BETWEEN_REFL` to derive the conclusion.
* In the second case, it uses `ASM_SIMP_TAC` with the definitions of `ddist` and `DIST_POS_LT` to simplify and reach the conclusion.
* The use of `REPEAT STRIP_TAC` suggests a repeated application of stripping tactics to simplify the goal.

### Mathematical insight
This theorem provides a fundamental property of the distance function `ddist` in the context of real-valued vectors, specifically that the distance between two distinct vectors is always positive. This is crucial for establishing various geometric and topological properties in the subsequent development.

### Dependencies
* Theorems:
  - `DDIST_INCREASES_ONLINE`
  - `DDIST_REFL`
  - `BETWEEN_REFL`
  - `DIST_POS_LT`
* Definitions:
  - `ddist`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to the handling of vector norms and the `ddist` function. The porting process may require redefining these concepts or proving additional lemmas to align with the target system's libraries and automation capabilities. Additionally, the case analysis and tactic applications may need to be adapted to the target system's proof scripting language.

---

## DDIST_POS_LE

### Name of formal statement
DDIST_POS_LE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_POS_LE = prove
 (`!x y:real^N. &0 <= ddist(x,y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:real^N = y` THEN
  ASM_SIMP_TAC[DDIST_REFL; DDIST_POS_LT; REAL_LE_LT])
```

### Informal statement
For all vectors `x` and `y` in the space of real numbers to the power of `N`, the distance `ddist(x, y)` is greater than or equal to `0`.

### Informal sketch
* The proof starts by considering all possible vectors `x` and `y` in the real space.
* It then proceeds by cases, specifically considering when `x` equals `y`.
* The `ASM_SIMP_TAC` tactic is applied with theorems `DDIST_REFL`, `DDIST_POS_LT`, and `REAL_LE_LT` to simplify the distance expression under the equality case and to establish the non-negativity of `ddist(x, y)`.

### Mathematical insight
This theorem establishes a fundamental property of the distance function `ddist` in the context of real-valued vectors, namely that the distance between any two vectors is non-negative. This property is crucial in various mathematical and computational contexts, especially in geometry, analysis, and optimization problems.

### Dependencies
#### Theorems
* `DDIST_REFL`
* `DDIST_POS_LT`
* `REAL_LE_LT`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles quantifiers, vector operations, and the specific distance function `ddist`. Ensure that equivalent theorems to `DDIST_REFL`, `DDIST_POS_LT`, and `REAL_LE_LT` are established or imported in the target system. Additionally, the use of `ASM_SIMP_TAC` and `REPEAT GEN_TAC` might need to be adapted based on the target system's tactic language and automation capabilities.

---

## DDIST_EQ_0

### Name of formal statement
DDIST_EQ_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_EQ_0 = prove
 (`!x y:real^N. ddist(x,y) = &0 <=> x = y`,
  MESON_TAC[DDIST_REFL; DDIST_POS_LT; REAL_LT_REFL])
```

### Informal statement
For all real-valued vectors `x` and `y` of dimension `N`, the distance `ddist(x, y)` is equal to `0` if and only if `x` is equal to `y`.

### Informal sketch
* The proof involves establishing a bidirectional implication between `ddist(x, y) = 0` and `x = y`.
* The forward direction is likely based on the properties of the distance function, specifically that `ddist(x, y) = 0` implies `x = y` due to the positive definiteness of the distance metric.
* The backward direction relies on the fact that `x = y` implies `ddist(x, y) = 0`, which is a fundamental property of distance functions.
* The `MESON_TAC` tactic is used to automatically prove the theorem by combining the relevant properties, including `DDIST_REFL`, `DDIST_POS_LT`, and `REAL_LT_REFL`.

### Mathematical insight
This theorem formalizes a basic property of distance functions, specifically that two vectors are identical if and only if their distance is zero. This property is crucial in various mathematical and computational contexts, such as geometry, optimization, and machine learning.

### Dependencies
* Theorems:
	+ `DDIST_REFL`
	+ `DDIST_POS_LT`
	+ `REAL_LT_REFL`
* Definitions:
	+ `ddist`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the specific properties and definitions used, such as `DDIST_REFL` and `ddist`. Ensure that equivalent properties and definitions are available in the target system, and that the automated proof tactics can be replicated or rephrased accordingly.

---

## BETWEEN_COLLINEAR_DDIST_EQ

### Name of formal statement
BETWEEN_COLLINEAR_DDIST_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BETWEEN_COLLINEAR_DDIST_EQ = prove
 (`!a b x:real^N.
        norm(a) < &1 /\ norm(b) < &1 /\ norm(x) < &1
        ==> (between x (a,b) <=>
             collinear {a, x, b} /\
             ddist(x,a) <= ddist (a,b) /\ ddist(x,b) <= ddist(a,b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [SIMP_TAC[BETWEEN_IMP_COLLINEAR];
    REWRITE_TAC[COLLINEAR_BETWEEN_CASES]] THEN
  ASM_MESON_TAC[DDIST_INCREASES_ONLINE; DDIST_SYM; REAL_LT_IMP_LE;
                REAL_LE_REFL; BETWEEN_SYM; REAL_NOT_LE; BETWEEN_REFL])
```

### Informal statement
For all vectors `a`, `b`, and `x` in `real^N`, if the norms of `a`, `b`, and `x` are all less than 1, then `x` is between `a` and `b` if and only if `a`, `x`, and `b` are collinear, and the distance from `x` to `a` is less than or equal to the distance from `a` to `b`, and the distance from `x` to `b` is less than or equal to the distance from `a` to `b`.

### Informal sketch
* The proof starts by assuming the premises: `norm(a) < 1`, `norm(b) < 1`, and `norm(x) < 1`.
* It then proceeds to prove the equivalence `between x (a,b) <=> collinear {a, x, b} /\ ddist(x,a) <= ddist (a,b) /\ ddist(x,b) <= ddist(a,b)` using the `EQ_TAC` tactic.
* The left-to-right direction of the equivalence is proven using `SIMP_TAC` with the `BETWEEN_IMP_COLLINEAR` theorem, which implies that if `x` is between `a` and `b`, then `a`, `x`, and `b` are collinear.
* The right-to-left direction is proven using `REWRITE_TAC` with the `COLLINEAR_BETWEEN_CASES` theorem, which provides cases for when `a`, `x`, and `b` are collinear.
* The `ASM_MESON_TAC` tactic is then used to prove the remaining subgoals, utilizing theorems such as `DDIST_INCREASES_ONLINE`, `DDIST_SYM`, `REAL_LT_IMP_LE`, `REAL_LE_REFL`, `BETWEEN_SYM`, `REAL_NOT_LE`, and `BETWEEN_REFL`.

### Mathematical insight
This theorem provides a characterization of the `between` relation in terms of collinearity and distance. It states that a point `x` is between two points `a` and `b` if and only if `a`, `x`, and `b` are collinear, and `x` is within the segment defined by `a` and `b`. This is a fundamental property of geometric objects and has numerous applications in geometry, topology, and other areas of mathematics.

### Dependencies
* Theorems:
  + `BETWEEN_IMP_COLLINEAR`
  + `COLLINEAR_BETWEEN_CASES`
  + `DDIST_INCREASES_ONLINE`
  + `DDIST_SYM`
  + `REAL_LT_IMP_LE`
  + `REAL_LE_REFL`
  + `BETWEEN_SYM`
  + `REAL_NOT_LE`
  + `BETWEEN_REFL`
* Definitions:
  + `between`
  + `collinear`
  + `ddist`
  + `norm`

---

## CONTINUOUS_AT_LIFT_DDIST

### Name of formal statement
CONTINUOUS_AT_LIFT_DDIST

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONTINUOUS_AT_LIFT_DDIST = prove
 (`!a x:real^N.
      norm(a) < &1 /\ norm(x) < &1 ==> (\x. lift(ddist(a,x))) continuous at x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN EXISTS_TAC
   `\x:real^N. lift((&1 - a dot x) pow 2 /
                    ((&1 - norm a pow 2) * (&1 - norm x pow 2)) - &1)` THEN
  EXISTS_TAC `&1 - norm(x:real^N)` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
    `dist(y,x) < &1 - norm x ==> norm y < &1`)) THEN ASM_SIMP_TAC[ddist];
    REWRITE_TAC[LIFT_SUB; real_div; LIFT_CMUL; REAL_INV_MUL] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN SIMP_TAC[CONTINUOUS_CONST] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[CONTINUOUS_CONST; o_DEF; REAL_POW_2; LIFT_CMUL] THENL
     [MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_MUL);
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_INV)] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < &1 * &1 ==> ~(&1 - x = &0)`; REAL_LT_MUL2;
                 NORM_POS_LE; LIFT_SUB] THEN
    SIMP_TAC[GSYM REAL_POW_2; NORM_POW_2; CONTINUOUS_CONST; CONTINUOUS_AT_ID;
             CONTINUOUS_SUB; CONTINUOUS_LIFT_DOT2])
```

### Informal statement
For all vectors `a` and `x` in `real^N`, if the norm of `a` is less than 1 and the norm of `x` is less than 1, then the function that lifts the distance between `a` and `x` is continuous at `x`.

### Informal sketch
* The proof starts by assuming `a` and `x` are vectors in `real^N` with norms less than 1.
* It then applies the `CONTINUOUS_TRANSFORM_AT` theorem to establish continuity of the lifted distance function at `x`.
* The proof involves constructing a specific function that represents the transformation, which includes a dot product and division, ensuring the denominator is non-zero.
* Key steps involve:
  + Establishing the norm of `y` is less than 1 if `y` is close enough to `x`.
  + Using `CONTINUOUS_SUB`, `CONTINUOUS_MUL`, and `CONTINUOUS_AT_INV` to establish the continuity of the constructed function.
  + Simplifying expressions involving `LIFT_SUB`, `real_div`, and `LIFT_CMUL` to show the function is well-defined and continuous.

### Mathematical insight
This theorem is important because it establishes the continuity of a function that lifts the distance between two points in a high-dimensional space, under certain conditions. This has implications for understanding the behavior of functions in such spaces, particularly in contexts where distances and norms are critical, such as in analysis and geometry.

### Dependencies
#### Theorems
* `CONTINUOUS_TRANSFORM_AT`
* `NORM_ARITH`
* `CONTINUOUS_SUB`
* `CONTINUOUS_MUL`
* `CONTINUOUS_AT_INV`
#### Definitions
* `ddist`
* `lift`
* `norm`
* `LIFT_SUB`
* `real_div`
* `LIFT_CMUL`
* `REAL_INV_MUL`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to how distances and norms are defined and handled, as well as the specifics of continuity proofs in the target system. The use of `CONTINUOUS_TRANSFORM_AT` and other continuity theorems may need to be adapted based on the target system's library and proof strategies. Additionally, the handling of vector operations and the `real^N` type may differ, requiring careful consideration to ensure a correct and efficient port.

---

## HYPERBOLIC_MIDPOINT

### Name of formal statement
HYPERBOLIC_MIDPOINT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERBOLIC_MIDPOINT = prove
(`!a b:real^N.
        norm a < &1 /\ norm b < &1
        ==> ?x. between x (a,b) /\ ddist(x,a) = ddist(x,b)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\x:real^N. lift(ddist(x,a) - ddist(x,b))`; `segment[a:real^N,b]`]
     CONNECTED_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONNECTED_SEGMENT; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ONCE_REWRITE_TAC[DDIST_SYM] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_LIFT_DDIST THEN
    ASM_MESON_TAC[BETWEEN_NORM_LT; BETWEEN_IN_SEGMENT];
    REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `lift(&0)`]) THEN
    ASM_SIMP_TAC[DDIST_REFL; LIFT_DROP; ENDS_IN_SEGMENT; IN_IMAGE] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ARITH `&0 - x <= &0 <=> &0 <= x`] THEN
    ASM_SIMP_TAC[DDIST_POS_LE; LIFT_EQ; BETWEEN_IN_SEGMENT] THEN
    ASM_MESON_TAC[REAL_SUB_0; DDIST_SYM]])
```

### Informal statement
For all vectors `a` and `b` in `real^N` such that the norm of `a` is less than 1 and the norm of `b` is less than 1, there exists a vector `x` that lies between `a` and `b` and is equidistant from `a` and `b`.

### Informal sketch
* The proof starts by assuming `a` and `b` are vectors in `real^N` with norms less than 1.
* It then invokes the `CONNECTED_CONTINUOUS_IMAGE` theorem to establish that the continuous image of the segment `[a, b]` under the function `lift(ddist(x, a) - ddist(x, b))` is connected.
* The proof proceeds by considering two main cases:
  + The first case involves showing that the function `ddist(x, a) - ddist(x, b)` is continuous on the segment `[a, b]`.
  + The second case involves applying the intermediate value theorem to find a point `x` in the segment `[a, b]` where `ddist(x, a) = ddist(x, b)`.
* Key tactics used include `REPEAT STRIP_TAC`, `MP_TAC`, `MATCH_MP_TAC`, and `ASM_MESON_TAC`, which help to manipulate the logical structure of the proof and apply relevant theorems.

### Mathematical insight
This theorem establishes the existence of a midpoint between two points `a` and `b` in a hyperbolic space, under certain conditions. The key idea is to use the continuity of the distance function to find a point that is equidistant from `a` and `b`. This result is important in hyperbolic geometry and has implications for the study of geometric properties in such spaces.

### Dependencies
* Theorems:
  + `CONNECTED_CONTINUOUS_IMAGE`
  + `CONTINUOUS_AT_IMP_CONTINUOUS_ON`
  + `CONTINUOUS_SUB`
  + `CONTINUOUS_AT_LIFT_DDIST`
  + `DDIST_SYM`
  + `REAL_SUB_0`
* Definitions:
  + `ddist`
  + `lift`
  + `segment`
  + `between`
  + `norm` 
* Inductive rules: None

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the distance function `ddist` and the lift function are defined and behave as expected. Additionally, the `CONNECTED_CONTINUOUS_IMAGE` theorem may need to be restated or re-proved in the target system. The use of `REPEAT STRIP_TAC` and `MATCH_MP_TAC` tactics may also require adaptation, as these tactics are specific to HOL Light.

---

## DDIST_EQ_ORIGIN

### Name of formal statement
DDIST_EQ_ORIGIN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_EQ_ORIGIN = prove
 (`!x:real^N y:real^N.
        norm x < &1 /\ norm y < &1
        ==> (ddist(vec 0,x) = ddist(vec 0,y) <=> norm x = norm y)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ddist; NORM_0; REAL_LT_01] THEN
  REWRITE_TAC[DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_EQ_INV2;
              REAL_ARITH `x - &1 = y - &1 <=> x = y`] THEN
  REWRITE_TAC[REAL_ARITH `&1 - x = &1 - y <=> x = y`;
              GSYM REAL_EQ_SQUARE_ABS; REAL_ABS_NORM])
```

### Informal statement
For all vectors `x` and `y` in `real^N`, if the norm of `x` is less than 1 and the norm of `y` is less than 1, then the distance from the origin to `x` is equal to the distance from the origin to `y` if and only if the norm of `x` is equal to the norm of `y`.

### Informal sketch
* The proof starts by assuming `x` and `y` are vectors in `real^N` with norms less than 1.
* It then uses the `ddist` function to calculate the distance from the origin to `x` and `y`.
* The `REPEAT STRIP_TAC` and `ASM_SIMP_TAC` tactics are used to simplify the expression and apply the definitions of `ddist`, `NORM_0`, and `REAL_LT_01`.
* The `REWRITE_TAC` tactic is used to apply various rewriting rules, including `DOT_LZERO`, `real_div`, `REAL_MUL_LID`, and `REAL_EQ_INV2`.
* The proof also uses `CONV_TAC` with `REAL_RAT_REDUCE_CONV` to simplify rational expressions.
* The final steps involve applying `REAL_ARITH` and `GSYM REAL_EQ_SQUARE_ABS` to establish the equivalence between the distance equality and the norm equality.

### Mathematical insight
This theorem provides a condition for when two vectors in a high-dimensional space have the same distance from the origin, based on their norms. It is a fundamental property that can be used in various geometric and analytical arguments, especially in contexts where distances and norms are crucial, such as in optimization problems or geometric calculations.

### Dependencies
* `ddist`
* `NORM_0`
* `REAL_LT_01`
* `DOT_LZERO`
* `REAL_RAT_REDUCE_CONV`
* `real_div`
* `REAL_MUL_LID`
* `REAL_EQ_INV2`
* `REAL_ARITH`
* `GSYM REAL_EQ_SQUARE_ABS`
* `REAL_ABS_NORM`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system handles vector norms, distances, and real arithmetic. Specifically, ensure that the ported version correctly implements the `ddist` function and applies the appropriate rewriting rules for real arithmetic. Additionally, consider how the target system handles equivalence proofs and how to mirror the strategic flow of the HOL Light proof.

---

## DDIST_CONGRUENT_TRIPLES_0

### Name of formal statement
DDIST_CONGRUENT_TRIPLES_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_CONGRUENT_TRIPLES_0 = prove
 (`!a b:real^N a' b':real^N.
        norm a < &1 /\ norm b < &1 /\ norm a' < &1 /\ norm b' < &1
        ==> (ddist(vec 0,a) = ddist(vec 0,a') /\ ddist(a,b) = ddist(a',b') /\
             ddist(b,vec 0) = ddist(b',vec 0) <=>
             dist(vec 0,a) = dist(vec 0,a') /\ dist(a,b) = dist(a',b') /\
             dist(b,vec 0) = dist(b',vec 0))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DDIST_EQ_ORIGIN; REWRITE_RULE[DDIST_SYM] DDIST_EQ_ORIGIN] THEN
  REWRITE_TAC[DIST_0; NORM_0; REAL_LT_01] THEN MATCH_MP_TAC(TAUT
   `(a /\ b ==> (x <=> y)) ==> (a /\ x /\ b <=> a /\ y /\ b)`) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[ddist; DIST_EQ; real_div; REAL_INV_MUL; REAL_RING
   `x * a * b - &1 = y * a * b - &1 <=> x = y \/ a = &0 \/ b = &0`] THEN
  REWRITE_TAC[dist; NORM_POW_2; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  REWRITE_TAC[GSYM REAL_EQ_SQUARE_ABS; NORM_POW_2] THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; real_abs; REAL_SUB_LE; REAL_SUB_0] THEN
  ASM_SIMP_TAC[ABS_SQUARE_LT_1; REAL_ABS_NORM; REAL_LT_IMP_NE; REAL_LT_IMP_LE;
               MESON[NORM_CAUCHY_SCHWARZ; REAL_LET_TRANS; NORM_POS_LE;
                     REAL_LT_MUL2; REAL_MUL_RID; REAL_LT_IMP_LE]
                `norm x < &1 /\ norm y < &1 ==> x dot y < &1`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NORM_EQ]) THEN ASM_REAL_ARITH_TAC)
```

### Informal statement
For all vectors `a`, `b`, `a'`, and `b'` in `real^N`, if the norms of `a`, `b`, `a'`, and `b'` are all less than 1, then the following equivalence holds: the `ddist` (directed distance) from the origin to `a` is equal to the `ddist` from the origin to `a'`, and the `ddist` from `a` to `b` is equal to the `ddist` from `a'` to `b'`, and the `ddist` from `b` to the origin is equal to the `ddist` from `b'` to the origin if and only if the `dist` (distance) from the origin to `a` is equal to the `dist` from the origin to `a'`, and the `dist` from `a` to `b` is equal to the `dist` from `a'` to `b'`, and the `dist` from `b` to the origin is equal to the `dist` from `b'` to the origin.

### Informal sketch
* The proof starts by assuming the given conditions on the norms of `a`, `b`, `a'`, and `b'`.
* It then simplifies the expressions involving `ddist` using `DDIST_EQ_ORIGIN` and `DDIST_SYM`.
* The next step involves applying a tautology to rearrange the implications and equivalences.
* The proof proceeds by simplifying the expressions involving `dist` and `norm` using various properties such as `DIST_0`, `NORM_0`, and `REAL_LT_01`.
* Key simplifications involve `ddist`, `DIST_EQ`, `real_div`, `REAL_INV_MUL`, and `REAL_RING`.
* Further simplifications are made using `dist`, `NORM_POW_2`, `DOT_LSUB`, `DOT_RSUB`, and `DOT_SYM`.
* The proof also involves using `GSYM REAL_EQ_SQUARE_ABS` and `NORM_POW_2` to simplify expressions.
* Additional simplifications are made using `REAL_INV_EQ_0`, `real_abs`, `REAL_SUB_LE`, and `REAL_SUB_0`.
* The proof also relies on `ABS_SQUARE_LT_1`, `REAL_ABS_NORM`, `REAL_LT_IMP_NE`, and `REAL_LT_IMP_LE`.
* A key step involves applying `MESON` with `NORM_CAUCHY_SCHWARZ`, `REAL_LET_TRANS`, `NORM_POS_LE`, `REAL_LT_MUL2`, `REAL_MUL_RID`, and `REAL_LT_IMP_LE` to establish a crucial inequality.
* Finally, the proof concludes by applying `RULE_ASSUM_TAC` with `REWRITE_RULE[NORM_EQ]` and `ASM_REAL_ARITH_TAC` to reach the desired conclusion.

### Mathematical insight
This theorem establishes an equivalence between two sets of conditions involving directed distances (`ddist`) and distances (`dist`) between vectors. The key insight is that under certain conditions (norms of vectors being less than 1), the equivalence between these conditions holds. This theorem likely plays a role in establishing properties of vector spaces, particularly in contexts where directed distances are relevant, such as in geometric or metric space theories.

### Dependencies
* Theorems:
  - `DDIST_EQ_ORIGIN`
  - `DDIST_SYM`
  - `DIST_0`
  - `NORM_0`
  - `REAL_LT_01`
  - `TAUT`
  - `NORM_CAUCHY_SCHWARZ`
* Definitions:
  - `ddist`
  - `dist`
  - `norm`
  - `real_div`
  - `REAL_INV_MUL`
  - `REAL_RING`
  - `DOT_LSUB`
  - `DOT_RSUB`
  - `DOT_SYM`
  - `GSYM REAL_EQ_SQUARE_ABS`
  - `NORM_POW_2`
  - `REAL_INV_EQ_0`
  - `real_abs`
  - `REAL_SUB_LE`
  - `REAL_SUB_0`
  - `ABS_SQUARE_LT_1`
  - `REAL_ABS_NORM`
  - `REAL_LT_IMP_NE`
  - `REAL_LT_IMP_LE`
  - `REAL_LET_TRANS`
  - `NORM_POS_LE`
  - `REAL_LT_MUL2`
  - `REAL_MUL_RID`
  - `REAL_LT_IMP_LE`

---

## kleinify

### Name of formal statement
kleinify

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let kleinify = new_definition
 `kleinify z = Cx(&2 / (&1 + norm(z) pow 2)) * z`
```

### Informal statement
The function `kleinify` is defined as `kleinify(z) = Cx(2 / (1 + ||z||^2)) * z`, where `Cx` denotes the complex number constructor, `norm(z)` denotes the Euclidean norm of `z`, and `pow` denotes exponentiation.

### Informal sketch
* The definition of `kleinify` involves a scaling factor `Cx(2 / (1 + ||z||^2))` applied to the input `z`.
* The scaling factor depends on the norm of `z`, specifically `||z||^2`, which is used in the denominator of the fraction.
* The `Cx` constructor is used to create a complex number from the real-valued expression `2 / (1 + ||z||^2)`.
* The result of the scaling is then multiplied by the original input `z` to produce the final output.

### Mathematical insight
The `kleinify` function appears to be related to the Poincaré disc model of hyperbolic geometry, where it is used to deduce the existence of hyperbolic translations. The function can be seen as a composition of orthogonal projection onto a hemisphere and stereographic projection back from the other pole of the sphere, followed by scaling.

### Dependencies
* `Cx`
* `norm`
* `pow`

### Porting notes
When porting this definition to another proof assistant, note that the `Cx` constructor may need to be replaced with an equivalent complex number constructor in the target system. Additionally, the `norm` and `pow` functions may need to be replaced with equivalent functions or definitions in the target system. The use of `&1` and `&2` may also require special attention, as these may be specific to HOL Light's syntax for real and complex numbers.

---

## poincarify

### Name of formal statement
poincarify

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let poincarify = new_definition
 `poincarify x = Cx((&1 - sqrt(&1 - norm(x) pow 2)) / norm(x) pow 2) * x`;;
```

### Informal statement
The function `poincarify` is defined as a mapping that takes a vector `x` and returns the result of the expression `Cx * ((1 - sqrt(1 - (norm(x))^2)) / (norm(x))^2) * x`, where `Cx` is a constant, `norm(x)` denotes the norm (or magnitude) of `x`, and `sqrt` denotes the square root function.

### Informal sketch
* The definition of `poincarify` involves several key steps:
  * Computing the norm (or magnitude) of the input vector `x`, denoted `norm(x)`.
  * Calculating the expression `1 - (norm(x))^2`, which represents a quantity related to the squared distance of `x` from the unit sphere.
  * Taking the square root of the result from the previous step, `sqrt(1 - (norm(x))^2)`.
  * Subtracting this square root from 1, `1 - sqrt(1 - (norm(x))^2)`.
  * Dividing the result by the squared norm of `x`, `(norm(x))^2`, to obtain a scalar factor.
  * Multiplying this scalar factor by the constant `Cx` and the original vector `x` to produce the final result.
* The `poincarify` function appears to be related to projections or transformations involving the unit sphere, possibly for the purpose of geometric or analytical constructions.

### Mathematical insight
The `poincarify` function seems to be inspired by geometric considerations, potentially related to the Poincaré disk model or similar constructions in geometry and complex analysis. The use of the norm, square root, and scalar multiplication suggests a transformation that depends on the magnitude and possibly the direction of the input vector `x`. Understanding the role of `Cx` and the specific formula used is crucial for grasping the intended application or theoretical context of `poincarify`.

### Dependencies
* `Cx`
* `norm`
* `sqrt`

### Porting notes
When translating `poincarify` into other proof assistants like Lean, Coq, or Isabelle, pay close attention to the handling of vector norms, scalar multiplication, and the square root function, as these may be represented differently across systems. Additionally, the constant `Cx` needs to be appropriately defined or imported. Automation and tactic scripts may vary significantly between proof assistants, so a deep understanding of the underlying mathematical structure and the target system's capabilities is necessary for a successful port.

---

## KLEINIFY_0,POINCARIFY_0

### Name of formal statement
KLEINIFY_0,POINCARIFY_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let KLEINIFY_0,POINCARIFY_0 = (CONJ_PAIR o prove)
 (`kleinify (Cx(&0)) = Cx(&0) /\ poincarify (Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[kleinify; poincarify; COMPLEX_MUL_RZERO])
```

### Informal statement
It is proven that `kleinify` of the complex number 0 is equal to the complex number 0 and `poincarify` of the complex number 0 is equal to the complex number 0.

### Informal sketch
* The proof involves applying the `CONJ_PAIR` function to a pair of equalities, specifically that `kleinify` applied to the complex number 0 (`Cx(&0)`) equals the complex number 0, and `poincarify` applied to the complex number 0 equals the complex number 0.
* The `REWRITE_TAC` tactic is used with theorems `kleinify`, `poincarify`, and `COMPLEX_MUL_RZERO` to rewrite the expressions and establish the equalities.
* The key steps involve recognizing that both `kleinify` and `poincarify` preserve the complex number 0, leveraging properties of complex number operations as justified by `COMPLEX_MUL_RZERO`.

### Mathematical insight
This theorem establishes basic properties of the `kleinify` and `poincarify` functions when applied to the complex number 0. These functions seem to be related to transformations or projections in a geometric or algebraic context, and understanding their behavior on zero is foundational for further results.

### Dependencies
* Theorems: 
  - `kleinify`
  - `poincarify`
  - `COMPLEX_MUL_RZERO`
* Definitions:
  - `Cx` (complex number constructor)
  - `kleinify` and `poincarify` functions

### Porting notes
When translating this into another proof assistant, ensure that the equivalents of `kleinify`, `poincarify`, and `COMPLEX_MUL_RZERO` are properly defined and accessible. The use of `REWRITE_TAC` may need to be adapted based on the target system's rewriting or simplification mechanisms. Additionally, the representation of complex numbers and the `CONJ_PAIR` function may require adjustments to match the target system's conventions.

---

## NORM_KLEINIFY

### Name of formal statement
NORM_KLEINIFY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NORM_KLEINIFY = prove
 (`!z. norm(kleinify z) = (&2 * norm(z)) / (&1 + norm(z) pow 2)`,
  REWRITE_TAC[kleinify; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_DIV] THEN
  SIMP_TAC[REAL_LE_POW_2; REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
  REAL_ARITH_TAC)
```

### Informal statement
For all complex numbers z, the norm of the `kleinify` of z is equal to twice the norm of z divided by one plus the square of the norm of z.

### Informal sketch
* The proof starts by applying `REWRITE_TAC` to expand the `kleinify` function and relevant norm properties (`COMPLEX_NORM_MUL`, `COMPLEX_NORM_CX`, `REAL_ABS_DIV`).
* It then simplifies the expression using `SIMP_TAC` with properties `REAL_LE_POW_2` and a specific arithmetic rule.
* The final step involves `REAL_ARITH_TAC` to perform real arithmetic simplifications, leading to the desired equality.

### Mathematical insight
This theorem provides a key property of the `kleinify` function, relating its output's norm to the input's norm. This is crucial in understanding how `kleinify` transforms complex numbers, particularly in geometric or algebraic contexts where norm preservation or transformation is significant.

### Dependencies
#### Theorems and Definitions
* `kleinify`
* `COMPLEX_NORM_MUL`
* `COMPLEX_NORM_CX`
* `REAL_ABS_DIV`
* `REAL_LE_POW_2`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system handles complex numbers, norms, and real arithmetic. Specifically, ensure that the `kleinify` function and its properties are correctly defined and applied. The use of `REWRITE_TAC`, `SIMP_TAC`, and `REAL_ARITH_TAC` may have direct analogs in other systems, but their application and the specific rules used (`COMPLEX_NORM_MUL`, etc.) will need to be adapted based on the target system's libraries and capabilities.

---

## NORM_KLEINIFY_LT

### Name of formal statement
NORM_KLEINIFY_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NORM_KLEINIFY_LT = prove
 (`!z. norm(kleinify z) < &1 <=> ~(norm z = &1)`,
  ASM_SIMP_TAC[NORM_KLEINIFY; REAL_LE_POW_2; REAL_LT_LDIV_EQ; REAL_MUL_LID;
                REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
  SIMP_TAC[REAL_ARITH `&2 * z < (&1 + z pow 2) <=> &0 < (z - &1) pow 2`] THEN
  REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN REAL_ARITH_TAC)
```

### Informal statement
For all `z`, the norm of `kleinify z` is less than `1` if and only if the norm of `z` is not equal to `1`.

### Informal sketch
* The proof starts with the statement `!z. norm(kleinify z) < &1 <=> ~(norm z = &1)`, which is then simplified using `ASM_SIMP_TAC` with various theorems including `NORM_KLEINIFY`, `REAL_LE_POW_2`, `REAL_LT_LDIV_EQ`, `REAL_MUL_LID`, and a specific `REAL_ARITH` instance.
* The `SIMP_TAC` is applied with another `REAL_ARITH` instance to further simplify the expression, specifically using the equivalence `&2 * z < (&1 + z pow 2) <=> &0 < (z - &1) pow 2`.
* The proof then proceeds with `REWRITE_TAC` using `REAL_POW_2` and `REAL_LT_SQUARE`, and finally concludes with `REAL_ARITH_TAC`.
* Key steps involve manipulating inequalities and using properties of `kleinify` and norm functions, leveraging arithmetic and real number properties.

### Mathematical insight
This theorem provides an equivalence condition involving the norm of `kleinify z` and the norm of `z` itself, which is crucial in understanding how the `kleinify` function affects the norm of its input. The condition `~(norm z = &1)` suggests that the norm of `z` cannot be exactly `1` for the equivalence to hold, indicating a boundary condition in the behavior of `kleinify`.

### Dependencies
* Theorems:
  - `NORM_KLEINIFY`
  - `REAL_LE_POW_2`
  - `REAL_LT_LDIV_EQ`
  - `REAL_MUL_LID`
  - `REAL_POW_2`
  - `REAL_LT_SQUARE`
* Definitions:
  - `kleinify`
  - `norm`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles real arithmetic and the properties of norms and inequalities. The `REAL_ARITH` and `ASM_SIMP_TAC` steps might need to be adapted based on the target system's capabilities for automated reasoning about real numbers. Additionally, the `kleinify` function and its properties, as well as the norm function, must be defined or imported appropriately in the target system.

---

## NORM_POINCARIFY_LT

### Name of formal statement
NORM_POINCARIFY_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NORM_POINCARIFY_LT = prove
 (`!x. norm(x) < &1 ==> norm(poincarify x) < &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[poincarify; COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x * y <= &1 * y /\ y < &1 ==> x * y < &1`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[NORM_POS_LE; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_POW] THEN
  ASM_CASES_TAC `x:real^2 = vec 0` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT; REAL_POW_LT; NORM_0] THENL
   [REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_LID]] THEN
  MATCH_MP_TAC(REAL_ARITH `s <= &1 /\ &1 - x <= s ==> abs(&1 - s) <= x`) THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LSQRT; MATCH_MP_TAC REAL_LE_RSQRT] THEN
  REWRITE_TAC[REAL_SUB_LE; REAL_POS; REAL_MUL_LID; REAL_POW_ONE] THEN
  ASM_SIMP_TAC[REAL_ARITH `(&1 - x) pow 2 <= &1 - x <=> &0 <= x * (&1 - x)`;
   REAL_ARITH `&1 - x <= &1 <=> &0 <= x`; REAL_LE_MUL; REAL_POW_LE;
   REAL_SUB_LE; ABS_SQUARE_LE_1; REAL_LT_IMP_LE; REAL_ABS_NORM; NORM_POS_LE])
```

### Informal statement
For all `x`, if the norm of `x` is less than 1, then the norm of `poincarify x` is also less than 1.

### Informal sketch
* Start with the assumption that `norm(x) < 1`.
* Apply the definition of `poincarify` and the properties of complex norm, specifically `COMPLEX_NORM_MUL`.
* Use real arithmetic properties to derive inequalities involving `x` and `poincarify x`.
* Consider the case where `x` is the zero vector and handle it separately using `NORM_0`.
* For non-zero `x`, apply various real arithmetic and absolute value properties to establish the desired inequality `norm(poincarify x) < 1`.
* The proof involves using tactics like `MATCH_MP_TAC` to apply specific theorems, such as `REAL_ARITH` and `REAL_LE_RMUL`, and rewriting using definitions like `poincarify` and `COMPLEX_NORM_MUL`.

### Mathematical insight
This theorem provides a bound on the norm of the `poincarify` function, which is crucial in various geometric and analytical contexts. The `poincarify` function is likely used to transform or normalize vectors in a way that preserves certain properties, and this theorem ensures that the norm of the transformed vector remains bounded under certain conditions.

### Dependencies
* Theorems:
  + `REAL_ARITH`
  + `REAL_LE_RMUL`
  + `REAL_LE_LSQRT`
  + `REAL_LE_RSQRT`
* Definitions:
  + `poincarify`
  + `COMPLEX_NORM_MUL`
  + `COMPLEX_NORM_CX`
  + `NORM_POS_LE`
  + `REAL_ABS_DIV`
  + `REAL_ABS_NORM`
  + `REAL_ABS_POW`
  + `NORM_0`

### Porting notes
When translating this theorem to another proof assistant, pay attention to the handling of complex numbers, vector norms, and real arithmetic properties. The `poincarify` function and its properties may need to be defined or imported from a relevant library. Additionally, the use of tactics like `MATCH_MP_TAC` and `REWRITE_TAC` may need to be adapted to the target proof assistant's tactic language.

---

## KLEINIFY_POINCARIFY

### Name of formal statement
KLEINIFY_POINCARIFY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let KLEINIFY_POINCARIFY = prove
 (`!x. norm(x) < &1 ==> kleinify(poincarify x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[kleinify; poincarify] THEN MATCH_MP_TAC
    (COMPLEX_RING `(~(x = Cx(&0)) ==> w * z = Cx(&1)) ==> w * z * x = x`) THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM CX_MUL; CX_INJ; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_POW] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(y = &0)
    ==> (&1 + (a / y pow 2 * y) pow 2) = (y pow 2 + a pow 2) / y pow 2`] THEN
  REWRITE_TAC[REAL_POW2_ABS; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(y = &0) ==> (&2 * x * y pow 2) * z * inv(y pow 2) = &2 * x * z`] THEN
  MATCH_MP_TAC(REAL_FIELD `&0 < y /\ &2 * y = x ==> &2 * inv(x) * y = &1`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    REWRITE_TAC[REAL_POS; REAL_ARITH `&1 - x < &1 pow 2 <=> &0 < x`] THEN
    ASM_SIMP_TAC[REAL_POW_LT; COMPLEX_NORM_NZ];
    SUBGOAL_THEN `sqrt(&1 - norm(x:real^2) pow 2) pow 2 = &1 - norm x pow 2`
    MP_TAC THENL [MATCH_MP_TAC SQRT_POW_2; CONV_TAC REAL_FIELD]] THEN
  ASM_SIMP_TAC[REAL_SUB_LE; ABS_SQUARE_LE_1; REAL_ABS_NORM; REAL_LT_IMP_LE])
```

### Informal statement
For all `x`, if the norm of `x` is less than 1, then the `kleinify` of the `poincarify` of `x` equals `x`.

### Informal sketch
* The proof begins by assuming `norm(x) < 1` and aims to show `kleinify(poincarify x) = x`.
* It involves rewriting using definitions of `kleinify` and `poincarify`, and applying properties of complex numbers, such as `COMPLEX_RING` and `CX_INJ`.
* The proof then manipulates expressions involving norms and complex arithmetic, using `REAL_FIELD` and `ASM_SIMP_TAC` to simplify.
* Key steps involve showing inequalities and equalities involving `norm(x)`, `&1`, and manipulations of `x` under `kleinify` and `poincarify`.
* The use of `MATCH_MP_TAC` with specific theorems like `REAL_LT_LSQRT` and `SQRT_POW_2` indicates the application of real number properties and square root behaviors.

### Mathematical insight
This theorem provides a condition under which the composition of `kleinify` and `poincarify` operations on a complex number `x` results in the original number `x`. This suggests a kind of "identity" or "fixed point" property for these operations under certain conditions, specifically when the norm of `x` is less than 1. This is likely important in geometric or algebraic contexts where these operations are defined and used.

### Dependencies
#### Theorems
* `COMPLEX_RING`
* `CX_INJ`
* `REAL_FIELD`
* `REAL_LT_LSQRT`
* `SQRT_POW_2`
#### Definitions
* `kleinify`
* `poincarify`
* `norm`
* `Cx`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of complex numbers, norms, and the specific properties and theorems used (`COMPLEX_RING`, `REAL_FIELD`, etc.). Differences in how these concepts are represented and manipulated in the target system may require adjustments to the proof strategy. Additionally, the use of `MATCH_MP_TAC` and `ASM_SIMP_TAC` may need to be replaced with equivalent tactics or methods in the target proof assistant.

---

## POINCARIFY_KLEINIFY

### Name of formal statement
POINCARIFY_KLEINIFY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let POINCARIFY_KLEINIFY = prove
 (`!x. norm(x) < &1 ==> poincarify(kleinify x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[kleinify; poincarify] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `(~(x = Cx(&0)) ==> w * z = Cx(&1)) ==> w * z * x = x`) THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM CX_MUL; CX_INJ] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_POW; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; GSYM REAL_MUL_ASSOC;
              REAL_INV_POW; REAL_POW_MUL] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(c = &0) /\ abs d < &1 /\ a * b = &2 * c pow 2 * (&1 + d)
    ==> a * inv(&2) pow 2 * b * inv(c) pow 2 * &2 * inv(&1 + d) = &1`) THEN
  ASM_REWRITE_TAC[REAL_ABS_POW; COMPLEX_NORM_ZERO; ABS_SQUARE_LT_1] THEN
  ASM_SIMP_TAC[REAL_ABS_NORM; REAL_POW_LE; NORM_POS_LE; REAL_ARITH
   `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(x = &0) /\ abs x < &1 /\ a = &2 * x / (&1 + x)
    ==> a * (&1 + x) pow 2 = &2 * x * (&1 + x)`) THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM; COMPLEX_NORM_ZERO; REAL_ABS_POW;
                  ABS_SQUARE_LT_1; REAL_POW_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &1 - y ==> &1 - x = y`) THEN
  MATCH_MP_TAC SQRT_UNIQUE THEN
  REWRITE_TAC[REAL_ARITH `&0 <= &1 - &2 * x / y <=> (&2 * x) / y <= &1`] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LE; NORM_POS_LE; REAL_ARITH
   `&0 <= x ==> &0 < &1 + x`] THEN
  REWRITE_TAC[REAL_ARITH `&2 * x <= &1 * (&1 + x) <=> x <= &1`] THEN
  ASM_SIMP_TAC[ABS_SQUARE_LE_1; REAL_ABS_NORM; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `~(&1 + norm(x:complex) pow 2 = &0)` MP_TAC THENL
   [ALL_TAC; CONV_TAC REAL_FIELD] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) < &1 ==> ~(&1 + x = &0)`) THEN
  ASM_REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM; ABS_SQUARE_LT_1])
```

### Informal statement
For all complex numbers `x`, if the norm of `x` is less than 1, then applying the `poincarify` function to the result of applying the `kleinify` function to `x` yields `x`.

### Informal sketch
* The proof begins by assuming `norm(x) < 1`, which implies `x` is not equal to `Cx(&0)`.
* It then applies a series of rewrites and matches using various theorems such as `COMPLEX_RING`, `REAL_FIELD`, and `REAL_ARITH` to simplify the expression `poincarify(kleinify x)`.
* Key steps involve using `MATCH_MP_TAC` to apply theorems that relate the `poincarify` and `kleinify` functions, as well as properties of complex numbers and real arithmetic.
* The proof also uses `ASM_REWRITE_TAC` and `ASM_SIMP_TAC` to simplify expressions and `SUBGOAL_THEN` to prove subgoals.
* The main logical stages involve:
  + Simplifying `poincarify(kleinify x)` using properties of `poincarify` and `kleinify`
  + Applying theorems from `COMPLEX_RING` and `REAL_FIELD` to relate the expression to `x`
  + Using `REAL_ARITH` to simplify and prove the final equality

### Mathematical insight
The theorem `POINCARIFY_KLEINIFY` provides a relationship between the `poincarify` and `kleinify` functions, which are likely used to transform complex numbers in some specific way. The fact that applying `poincarify` to the result of `kleinify` on a complex number `x` with norm less than 1 yields `x` suggests that these functions are inverses of each other under certain conditions. This theorem is likely important in contexts where these transformations are used, such as in geometry or complex analysis.

### Dependencies
* Theorems:
  + `COMPLEX_RING`
  + `REAL_FIELD`
  + `REAL_ARITH`
  + `SQRT_UNIQUE`
* Definitions:
  + `poincarify`
  + `kleinify`
  + `norm`
  + `Cx`
* Axioms or rules:
  + `REAL_ABS_DIV`
  + `REAL_ABS_NORM`
  + `REAL_ABS_POW`
  + `REAL_ABS_NUM`
  + `real_div`
  + `REAL_INV_MUL`
  + `REAL_INV_INV`
  + `GSYM REAL_MUL_ASSOC`
  + `REAL_INV_POW`
  + `REAL_POW_MUL`
  + `ABS_SQUARE_LT_1`
  + `COMPLEX_NORM_ZERO`
  + `REAL_POW_LE`
  + `NORM_POS_LE`
  + `REAL_LE_LDIV_EQ`
  + `ABS_SQUARE_LE_1`
  + `REAL_LT_IMP_LE`

---

## DDIST_KLEINIFY

### Name of formal statement
DDIST_KLEINIFY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_KLEINIFY = prove
 (`!w z. ~(norm w = &1) /\ ~(norm z = &1)
         ==> ddist(kleinify w,kleinify z) =
             &4 * (&1 / &2 + norm(w - z) pow 2 /
                             ((&1 - norm w pow 2) * (&1 - norm z pow 2))) pow 2
             - &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `(&4 * norm(w - z:real^2) pow 2 *
     ((&1 - norm w pow 2) * (&1 - norm z pow 2) + norm(w - z) pow 2)) /
    ((&1 - norm w pow 2) pow 2 * (&1 - norm z pow 2) pow 2)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[ddist; NORM_KLEINIFY_LT] THEN MATCH_MP_TAC(REAL_FIELD
     `~(y = &0) /\ z = (w + &1) * y ==> z / y - &1 = w`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN CONJ_TAC THEN
      MATCH_MP_TAC (REAL_ARITH `x < &1 ==> ~(&1 - x = &0)`) THEN
      ASM_SIMP_TAC[REAL_POW_1_LT; NORM_KLEINIFY_LT; NORM_POS_LE; ARITH];
      REWRITE_TAC[kleinify; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      REWRITE_TAC[GSYM COMPLEX_CMUL; DOT_LMUL] THEN REWRITE_TAC[DOT_RMUL] THEN
      SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_POW_LE; NORM_POS_LE;
               REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
      MATCH_MP_TAC(REAL_FIELD
       `(~(y' = &0) /\ ~(y = &0)) /\
        (y * y' - &4 * d) pow 2 =
        b * (y pow 2 - &4 * x pow 2) * (y' pow 2 - &4 * x' pow 2)
        ==> (&1 - &2 / y * &2 / y' * d) pow 2 =
            b * (&1 - (&2 / y * x) pow 2) * (&1 - (&2 / y' * x') pow 2)`) THEN
      CONJ_TAC THENL
       [CONJ_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `~(abs x = &1) ==> ~(&1 + x = &0)`) THEN
        ASM_SIMP_TAC[REAL_ABS_POW; REAL_POW_EQ_1; REAL_ABS_NORM] THEN ARITH_TAC;
        REWRITE_TAC[REAL_RING `(&1 + x) pow 2 - &4 * x = (&1 - x) pow 2`] THEN
        MATCH_MP_TAC(REAL_FIELD
         `(~(y = &0) /\ ~(y' = &0)) /\ a - y * y' = b
          ==> a = (b / (y * y') + &1) * y * y'`) THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[REAL_POW_EQ_0; REAL_POW_EQ_1; REAL_ABS_NORM; ARITH;
                          REAL_ARITH `&1 - x = &0 <=> x = &1`];
          REWRITE_TAC[NORM_POW_2; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
          REAL_ARITH_TAC]]);
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[NORM_EQ_SQUARE; GSYM NORM_POW_2] THEN CONV_TAC REAL_FIELD])
```

### Informal statement
For all `w` and `z` such that `norm w` is not equal to `1` and `norm z` is not equal to `1`, the distance between `kleinify w` and `kleinify z` is equal to `4 * ((1 / 2 + norm(w - z)^2 / ((1 - norm w^2) * (1 - norm z^2)))^2) - 1`.

### Informal sketch
* The proof starts by assuming the conditions `~(norm w = &1)` and `~(norm z = &1)`, which are used throughout the proof.
* It then uses `MATCH_MP_TAC EQ_TRANS` to establish an equality between `ddist(kleinify w, kleinify z)` and a complex expression involving `norm(w - z)`, `norm w`, and `norm z`.
* The proof proceeds by applying various simplification tactics, including `ASM_SIMP_TAC`, `MATCH_MP_TAC`, and `CONJ_TAC`, to manipulate the expression and establish the desired equality.
* Key steps involve using `REAL_FIELD` to apply field properties, `REAL_ARITH` to apply arithmetic properties, and `REAL_ABS` properties to handle absolute values.
* The `kleinify` function and `ddist` function are central to the proof, and their properties are used extensively.

### Mathematical insight
This theorem provides a formula for the distance between two points in the Klein model, which is a model of hyperbolic geometry. The formula involves the norm of the difference between the two points, as well as the norms of the individual points. The theorem is important because it provides a way to compute distances in the Klein model, which is a fundamental concept in hyperbolic geometry.

### Dependencies
* `ddist`
* `kleinify`
* `NORM_KLEINIFY_LT`
* `REAL_FIELD`
* `REAL_ARITH`
* `REAL_ABS`
* `COMPLEX_NORM_MUL`
* `COMPLEX_NORM_CX`
* `GSYM COMPLEX_CMUL`
* `DOT_LMUL`
* `DOT_RMUL`
* `REAL_POW_1_LT`
* `NORM_POS_LE`
* `REAL_ENTIRE`
* `DE_MORGAN_THM`
* `REAL_POW_EQ_1`
* `REAL_ABS_NORM`
* `NORM_POW_2`
* `DOT_LSUB`
* `DOT_RSUB`
* `DOT_SYM`
* `NORM_EQ_SQUARE`
* `GSYM NORM_POW_2`
* `CONV_TAC REAL_FIELD`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `kleinify` function and `ddist` function are defined and behave as expected. Additionally, the `REAL_FIELD` and `REAL_ARITH` tactics may need to be replaced with equivalent tactics in the target proof assistant. The use of `MATCH_MP_TAC` and `CONJ_TAC` may also require special attention, as these tactics can be sensitive to the specific proof assistant being used.

---

## DDIST_KLEINIFY_EQ

### Name of formal statement
DDIST_KLEINIFY_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_KLEINIFY_EQ = prove
 (`!w z w' z'.
      ~(norm w = &1) /\ ~(norm z = &1) /\ ~(norm w' = &1) /\ ~(norm z' = &1) /\
      norm(w - z) pow 2 * (&1 - norm w' pow 2) * (&1 - norm z' pow 2) =
      norm(w' - z') pow 2 * (&1 - norm w pow 2) * (&1 - norm z pow 2)
      ==> ddist(kleinify w,kleinify z) = ddist(kleinify w',kleinify z')`,
  SIMP_TAC[DDIST_KLEINIFY; NORM_EQ_SQUARE; GSYM NORM_POW_2; REAL_POS] THEN
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all `w`, `z`, `w'`, and `z'` such that `w`, `z`, `w'`, and `z'` are not equal to 1 in norm, if the expression `norm(w - z) squared * (1 - norm w' squared) * (1 - norm z' squared)` is equal to `norm(w' - z') squared * (1 - norm w squared) * (1 - norm z squared)`, then the distance between `kleinify w` and `kleinify z` is equal to the distance between `kleinify w'` and `kleinify z'`.

### Informal sketch
* The proof starts by assuming the given conditions on `w`, `z`, `w'`, and `z'`.
* It then uses simplification (`SIMP_TAC`) and conversion (`CONV_TAC`) tactics to manipulate the expressions involving `norm` and `ddist`.
* Key steps involve applying properties of `DDIST_KLEINIFY`, `NORM_EQ_SQUARE`, and `REAL_POS` to simplify the equation.
* The `GSYM NORM_POW_2` and `REAL_FIELD` theorems are used to further simplify and rearrange terms.

### Mathematical insight
This theorem relates the distances between points in a space after applying the `kleinify` transformation, under certain conditions on the original points. It suggests a kind of equivalence or invariance property that can be useful in geometric or metric space reasoning, particularly in contexts where `kleinify` is used to transform or normalize points.

### Dependencies
* `DDIST_KLEINIFY`
* `NORM_EQ_SQUARE`
* `NORM_POW_2`
* `REAL_POS`
* `REAL_FIELD`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to the handling of `norm` and `ddist` functions, as well as the `kleinify` transformation. Ensure that the target system has equivalent notions of these concepts and that they behave similarly under the given conditions. Additionally, the use of `SIMP_TAC` and `CONV_TAC` may need to be adapted, as different systems may have different tactics or methods for achieving similar simplifications and conversions.

---

## NORM_KLEINIFY_MOEBIUS_LT

### Name of formal statement
NORM_KLEINIFY_MOEBIUS_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NORM_KLEINIFY_MOEBIUS_LT = prove
 (`!w x. norm w < &1 /\ norm x < &1
         ==> norm(kleinify(moebius_function (&0) w x)) < &1`,
  SIMP_TAC[MOEBIUS_FUNCTION_NORM_LT_1; NORM_KLEINIFY_LT; REAL_LT_IMP_NE])
```

### Informal statement
For all `w` and `x`, if the norm of `w` is less than 1 and the norm of `x` is less than 1, then the norm of the `kleinify` of the `moebius_function` applied to `(&0)`, `w`, and `x` is less than 1.

### Informal sketch
* The proof starts with the assumption that `norm w < 1` and `norm x < 1`.
* It then applies the `moebius_function` to `(&0)`, `w`, and `x`.
* The `kleinify` function is applied to the result of the `moebius_function`.
* The proof uses the `SIMP_TAC` tactic with theorems `MOEBIUS_FUNCTION_NORM_LT_1`, `NORM_KLEINIFY_LT`, and `REAL_LT_IMP_NE` to simplify and establish the norm of the `kleinify` of the `moebius_function` is less than 1.

### Mathematical insight
This theorem provides a bound on the norm of the `kleinify` of the `moebius_function` under certain conditions. The `moebius_function` is a transformation that maps the unit disk to itself, and the `kleinify` function is a projection that maps the unit disk to the upper half-plane. The theorem ensures that the composition of these functions preserves the norm condition.

### Dependencies
* Theorems:
  + `MOEBIUS_FUNCTION_NORM_LT_1`
  + `NORM_KLEINIFY_LT`
  + `REAL_LT_IMP_NE`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of the `norm` function and the `kleinify` and `moebius_function` definitions. The `SIMP_TAC` tactic may need to be replaced with equivalent simplification tactics in the target system. Additionally, the `REAL_LT_IMP_NE` theorem may need to be reformulated or replaced with a similar theorem in the target system.

---

## DDIST_KLEINIFY_MOEBIUS

### Name of formal statement
DDIST_KLEINIFY_MOEBIUS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DDIST_KLEINIFY_MOEBIUS = prove
 (`!w x y. norm w < &1 /\ norm x < &1 /\ norm y < &1
           ==> ddist(kleinify(moebius_function (&0) w x),
                     kleinify(moebius_function (&0) w y)) =
               ddist(kleinify x,kleinify y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DDIST_KLEINIFY_EQ THEN
  ASM_SIMP_TAC[MOEBIUS_FUNCTION_NORM_LT_1; REAL_LT_IMP_NE] THEN
  REWRITE_TAC[MOEBIUS_FUNCTION_SIMPLE] THEN
  SUBGOAL_THEN
   `~(Cx(&1) - cnj w * x = Cx(&0)) /\ ~(Cx(&1) - cnj w * y = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN CONJ_TAC THEN
    MATCH_MP_TAC(MESON[REAL_LT_REFL] `norm(x) < norm(y) ==> ~(y = x)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; COMPLEX_NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CNJ];
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(Cx(&1) - cnj w * x = Cx(&0)) /\ ~(Cx(&1) - cnj w * y = Cx(&0))
      ==> (x - w) / (Cx (&1) - cnj w * x) - (y - w) / (Cx (&1) - cnj w * y) =
          ((Cx(&1) - w * cnj w) * (x - y)) /
          ((Cx (&1) - cnj w * x) * (Cx (&1) - cnj w * y))`] THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_POW] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
     `~(y = &0) /\ ~(y' = &0)
      ==> (&1 - (x / y) pow 2) * (&1 - (x' / y') pow 2) =
          ((y pow 2 - x pow 2) * (y' pow 2 - x' pow 2)) / (y * y') pow 2`] THEN
    REWRITE_TAC[REAL_POW_DIV; COMPLEX_NORM_MUL] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_RING
     `x * y:real = w * z ==> (x * i) * y = w * z * i`) THEN
    REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN REWRITE_TAC[NORM_POW_2; DOT_2] THEN
    REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; complex_sub; complex_mul; CX_DEF;
                complex_add; RE; IM; cnj; complex_neg] THEN REAL_ARITH_TAC])
```

### Informal statement
For all complex numbers `w`, `x`, and `y` such that the norm of `w`, `x`, and `y` are less than 1, the distance between the `kleinify` of the `moebius_function` applied to `w` and `x` and the `kleinify` of the `moebius_function` applied to `w` and `y` is equal to the distance between the `kleinify` of `x` and the `kleinify` of `y`.

### Informal sketch
* The proof starts by assuming `norm w < 1`, `norm x < 1`, and `norm y < 1`.
* It then applies `DDIST_KLEINIFY_EQ` to establish a relationship between distances under `kleinify`.
* The `MOEBIUS_FUNCTION_NORM_LT_1` and `REAL_LT_IMP_NE` theorems are used to simplify expressions involving the `moebius_function`.
* A key step involves showing that certain complex expressions are non-zero, utilizing `COMPLEX_SUB_0` and properties of complex norms.
* The proof then proceeds by manipulating complex expressions, using properties of `moebius_function`, `kleinify`, and complex arithmetic to ultimately establish the desired equality.
* Specific tactics like `MATCH_MP_TAC`, `ASM_SIMP_TAC`, and `REWRITE_TAC` are used to apply theorems and simplify expressions.

### Mathematical insight
This theorem relates the distances between points under the `kleinify` transformation and the `moebius_function`, which are significant in geometric and complex analysis. The `moebius_function` is a fundamental transformation in complex analysis, and `kleinify` likely relates to projecting or transforming points in a specific geometric context. Understanding how distances are preserved under these transformations is crucial for various applications, including geometry, conformal mapping, and potentially physics.

### Dependencies
* Theorems:
  - `DDIST_KLEINIFY_EQ`
  - `MOEBIUS_FUNCTION_NORM_LT_1`
  - `REAL_LT_IMP_NE`
  - `COMPLEX_SUB_0`
  - `REAL_LT_REFL`
  - `COMPLEX_NORM_CX`
  - `REAL_ABS_NUM`
  - `COMPLEX_NORM_MUL`
  - `REAL_MUL_LID`
  - `REAL_LT_MUL2`
  - `NORM_POS_LE`
  - `COMPLEX_NORM_CNJ`
  - `COMPLEX_FIELD`
  - `COMPLEX_NORM_DIV`
  - `COMPLEX_NORM_POW`
  - `COMPLEX_NORM_ZERO`
  - `REAL_FIELD`
  - `REAL_POW_DIV`
  - `COMPLEX_NORM_MUL`
  - `REAL_RING`
  - `NORM_POW_2`
  - `DOT_2`
* Definitions:
  - `moebius_function`
  - `kleinify`
  - `ddist` 
* Other:
  - Properties of complex numbers and norms. 

### Porting notes
When porting this theorem to another proof assistant, pay close attention to how complex numbers and their norms are handled, as well as the specific properties and theorems used. The `moebius_function` and `kleinify` transformations may need to be defined or imported from a relevant library. Additionally, the tactic script may need to be adapted to the target system's proof scripting language, taking into account differences in automation, rewriting, and matching capabilities.

---

## COLLINEAR_KLEINIFY_MOEBIUS

### Name of formal statement
COLLINEAR_KLEINIFY_MOEBIUS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COLLINEAR_KLEINIFY_MOEBIUS = prove
 (`!w x y z. norm w < &1 /\ norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (collinear {kleinify(moebius_function (&0) w x),
                             kleinify(moebius_function (&0) w y),
                             kleinify(moebius_function (&0) w z)} <=>
                  collinear {kleinify x,kleinify y,kleinify z})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COLLINEAR_3_2D; kleinify; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[RE_MUL_CX; IM_MUL_CX] THEN
  SIMP_TAC[NORM_POS_LE; REAL_POW_LE; REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`;
     REAL_FIELD
     `~(nx = &0) /\ ~(ny = &0) /\ ~(nz = &0)
      ==> ((&2 / nz * rz - &2 / nx * rx) * (&2 / ny * iy - &2 / nx * ix) =
           (&2 / ny * ry - &2 / nx * rx) * (&2 / nz * iz - &2 / nx * ix) <=>
           (nx * rz - nz * rx) * (nx * iy - ny * ix) =
           (nx * ry - ny * rx) * (nx * iz - nz * ix))`] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; MOEBIUS_FUNCTION_SIMPLE] THEN
  ONCE_REWRITE_TAC[COMPLEX_DIV_CNJ] THEN
  REWRITE_TAC[RE_DIV_CX; GSYM CX_POW; IM_DIV_CX] THEN
  SUBGOAL_THEN
   `~(Cx (&1) - cnj w * x = Cx(&0)) /\ ~(Cx (&1) - cnj w * y = Cx(&0)) /\
    ~(Cx (&1) - cnj w * z = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_SUB_0] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(MESON[REAL_LT_REFL] `norm x < norm y ==> ~(y = x)`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_CX] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `abs(&1) = &1 * &1`] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(nx = &0) /\ ~(ny = &0) /\ ~(nz = &0)
    ==>(((&1 + (nxw / nx) pow 2) * rz / nz pow 2 -
         (&1 + (nzw / nz) pow 2) * rx / nx pow 2) *
        ((&1 + (nxw / nx) pow 2) * iy / ny pow 2 -
         (&1 + (nyw / ny) pow 2) * ix / nx pow 2) =
        ((&1 + (nxw / nx) pow 2) * ry / ny pow 2 -
         (&1 + (nyw / ny) pow 2) * rx / nx pow 2) *
        ((&1 + (nxw / nx) pow 2) * iz / nz pow 2 -
         (&1 + (nzw / nz) pow 2) * ix / nx pow 2) <=>
        ((nx pow 2 + nxw pow 2) * rz - (nz pow 2 + nzw pow 2) * rx) *
        ((nx pow 2 + nxw pow 2) * iy - (ny pow 2 + nyw pow 2) * ix) =
        ((nx pow 2 + nxw pow 2) * ry - (ny pow 2 + nyw pow 2) * rx) *
        ((nx pow 2 + nxw pow 2) * iz - (nz pow 2 + nzw pow 2) * ix))`] THEN
  REWRITE_TAC[COMPLEX_SQNORM; complex_sub; complex_mul; complex_add;
              complex_neg; cnj; CX_DEF; RE; IM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN MATCH_MP_TAC(REAL_RING
   `!a b. a * lhs = b * rhs /\ ~(a = &0) /\ ~(b = &0)
          ==> (lhs = &0 <=> rhs = &0)`) THEN
  EXISTS_TAC `Re x pow 2 + Im x pow 2 + &1` THEN
  EXISTS_TAC `--(Re w pow 2 + Im w pow 2 - &1) pow 3 *
              ((&1 - Re(x) pow 2 - Im(x) pow 2) *
               (&1 - Re(w) pow 2 - Im(w) pow 2) +
               &2 * (Re w - Re x) pow 2 + &2 * (Im w - Im x) pow 2)` THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM; REAL_POW_EQ_0; ARITH_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= x + y ==> ~(x + y + &1 = &0)`) THEN
    ASM_SIMP_TAC[GSYM COMPLEX_SQNORM; REAL_LE_POW_2];
    MATCH_MP_TAC(REAL_ARITH `x + y < &1 ==> ~(--(x + y - &1) = &0)`) THEN
    ASM_SIMP_TAC[GSYM COMPLEX_SQNORM; REAL_POW_1_LT; NORM_POS_LE; ARITH];
    MATCH_MP_TAC(REAL_ARITH `&0 < x /\ &0 <= y ==> ~(x + y = &0)`) THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS; REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &1 - x - y <=> x + y < &1`] THEN
    ASM_SIMP_TAC[GSYM COMPLEX_SQNORM; REAL_POW_1_LT; NORM_POS_LE; ARITH]]);;  
```

### Informal statement
For all complex numbers `w`, `x`, `y`, and `z` with norm less than 1, the following equivalence holds: the points `kleinify(moebius_function(0) w x)`, `kleinify(moebius_function(0) w y)`, and `kleinify(moebius_function(0) w z)` are collinear if and only if the points `kleinify(x)`, `kleinify(y)`, and `kleinify(z)` are collinear.

### Informal sketch
The proof involves several key steps:
* Simplifying the `collinear` condition using `COLLINEAR_3_2D` and properties of `kleinify` and `moebius_function`.
* Applying various algebraic manipulations and simplifications to express the condition in terms of real and imaginary parts of the complex numbers.
* Using `REAL_FIELD` and `REAL_ARITH` to establish the equivalence of certain expressions involving the real and imaginary parts.
* Employing `COMPLEX_NORM_DIV`, `MOEBIUS_FUNCTION_SIMPLE`, and other properties to further simplify the expressions.
* Utilizing `SUBGOAL_THEN` and `STRIP_ASSUME_TAC` to handle certain assumptions and subgoals.
* Applying `MATCH_MP_TAC` and `REAL_RING` to establish the final equivalence.

### Mathematical insight
This theorem provides a relationship between the collinearity of points in the complex plane and their images under the `kleinify` and `moebius_function` transformations. It is likely used in the context of geometric transformations and properties of complex numbers.

### Dependencies
* Theorems:
	+ `COLLINEAR_3_2D`
	+ `REAL_FIELD`
	+ `REAL_ARITH`
	+ `COMPLEX_NORM_DIV`
	+ `MOEBIUS_FUNCTION_SIMPLE`
* Definitions:
	+ `kleinify`
	+ `moebius_function`
	+ `collinear`
* Other:
	+ `REAL_LT_REFL`
	+ `REAL_POW_EQ_0`
	+ `DE_MORGAN_THM`
	+ `REAL_ENTIRE`

### Porting notes
When translating this theorem to another proof assistant, pay attention to the following:
* The use of `SUBGOAL_THEN` and `STRIP_ASSUME_TAC` may need to be adapted to the target system's tactic language.
* The `MATCH_MP_TAC` and `REAL_RING` applications may require equivalent tactics or rules in the target system.
* The `COMPLEX_NORM_DIV` and `MOEBIUS_FUNCTION_SIMPLE` properties may need to be redefined or imported from a relevant library in the target system.

---

## BETWEEN_KLEINIFY_MOEBIUS

### Name of formal statement
BETWEEN_KLEINIFY_MOEBIUS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BETWEEN_KLEINIFY_MOEBIUS = prove
 (`!w x y z. norm w < &1 /\ norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (between (kleinify(moebius_function (&0) w x))
                          (kleinify(moebius_function (&0) w y),
                           kleinify(moebius_function (&0) w z)) <=>
                  between (kleinify x) (kleinify y,kleinify z))`,
  SIMP_TAC[BETWEEN_COLLINEAR_DDIST_EQ; NORM_KLEINIFY_MOEBIUS_LT;
           NORM_KLEINIFY_LT; REAL_LT_IMP_NE;
           COLLINEAR_KLEINIFY_MOEBIUS; DDIST_KLEINIFY_MOEBIUS])
```

### Informal statement
For all `w`, `x`, `y`, and `z`, if the norm of `w`, `x`, `y`, and `z` are all less than 1, then the `between` relation holds between `kleinify` applied to the `moebius_function` of `w` and `x`, and `kleinify` applied to the `moebius_function` of `w` and `y`, and `kleinify` applied to the `moebius_function` of `w` and `z`, if and only if the `between` relation holds between `kleinify` applied to `x`, and `kleinify` applied to `y` and `kleinify` applied to `z`.

### Informal sketch
* The proof starts with the assumption that the norms of `w`, `x`, `y`, and `z` are all less than 1.
* It then applies the `moebius_function` to `w` and `x`, `w` and `y`, and `w` and `z`, and `kleinify` to these results.
* The `between` relation is then applied to these `kleinify` results.
* The proof then uses various properties, including `BETWEEN_COLLINEAR_DDIST_EQ`, `NORM_KLEINIFY_MOEBIUS_LT`, `NORM_KLEINIFY_LT`, `REAL_LT_IMP_NE`, `COLLINEAR_KLEINIFY_MOEBIUS`, and `DDIST_KLEINIFY_MOEBIUS`, to simplify and prove the equivalence.

### Mathematical insight
This theorem provides a relationship between the `between` relation applied to `kleinify` results of `moebius_function` outputs and the `between` relation applied to `kleinify` results of the original inputs, under certain norm conditions. This relationship is important for understanding the properties of the `moebius_function` and `kleinify` operations, particularly in the context of geometric transformations and metric spaces.

### Dependencies
* Theorems:
  + `BETWEEN_COLLINEAR_DDIST_EQ`
  + `NORM_KLEINIFY_MOEBIUS_LT`
  + `NORM_KLEINIFY_LT`
  + `REAL_LT_IMP_NE`
  + `COLLINEAR_KLEINIFY_MOEBIUS`
  + `DDIST_KLEINIFY_MOEBIUS`
* Definitions:
  + `kleinify`
  + `moebius_function`
  + `between` 

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the `kleinify` and `moebius_function` operations are correctly defined and that the `between` relation is properly applied. Additionally, the various properties used in the proof, such as `BETWEEN_COLLINEAR_DDIST_EQ` and `NORM_KLEINIFY_MOEBIUS_LT`, will need to be established or imported in the target system. The use of `SIMP_TAC` and other HOL Light tactics may not have direct equivalents in other systems, so the proof strategy may need to be adapted.

---

## hyperbolic_isometry

### Name of formal statement
hyperbolic_isometry

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let hyperbolic_isometry = new_definition
 `hyperbolic_isometry (f:real^2->real^2) <=>
    (!x. norm x < &1 ==> norm(f x) < &1) /\
    (!x y. norm x < &1 /\ norm y < &1 ==> ddist(f x,f y) = ddist(x,y)) /\
    (!x y z. norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (between (f x) (f y,f z) <=> between x (y,z)))`;;
```

### Informal statement
A function `f` from `real^2` to `real^2` is a hyperbolic isometry if and only if it satisfies three conditions:
1. For all `x`, if the norm of `x` is less than 1, then the norm of `f(x)` is less than 1.
2. For all `x` and `y`, if the norms of `x` and `y` are both less than 1, then the distance between `f(x)` and `f(y)` is equal to the distance between `x` and `y`.
3. For all `x`, `y`, and `z`, if the norms of `x`, `y`, and `z` are all less than 1, then `f(x)` is between `f(y)` and `f(z)` if and only if `x` is between `y` and `z`.

### Informal sketch
* The definition of `hyperbolic_isometry` involves three main conditions that `f` must satisfy to be considered an isometry in a hyperbolic context.
* The first condition ensures that `f` maps points within the unit circle to points within the unit circle, preserving the property of being "inside" this boundary.
* The second condition states that `f` preserves distances between points, which is a fundamental property of isometries.
* The third condition preserves the betweenness relation, ensuring that the order of points along lines is maintained under the mapping `f`.
* These conditions collectively ensure that `f` acts as a hyperbolic isometry, preserving both metric and order properties.

### Mathematical insight
The concept of `hyperbolic_isometry` is crucial in hyperbolic geometry, where it defines a transformation that preserves the geometry of the space. This definition captures the essence of an isometry in the context of hyperbolic space, which is a space with constant negative curvature. The conditions imposed on `f` ensure that it behaves like an isometry should, preserving distances and the betweenness of points, which are fundamental invariants in geometry.

### Dependencies
- `norm`
- `ddist`
- `between`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles function types, norm, distance, and betweenness predicates. Specifically, ensure that the translation correctly captures the quantifiers, implications, and conjunctions as defined in the HOL Light version. Additionally, consider the specific libraries or modules in the target system that deal with real numbers, distances, and geometric predicates to ensure accurate and efficient translation.

---

## HYPERBOLIC_TRANSLATION

### Name of formal statement
HYPERBOLIC_TRANSLATION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HYPERBOLIC_TRANSLATION = prove
 (`!w. norm w < &1
       ==> ?f:real^2->real^2 g:real^2->real^2.
                hyperbolic_isometry f /\ hyperbolic_isometry g /\
                f(w) = vec 0 /\ g(vec 0) = w /\
                (!x. norm x < &1 ==> f(g x) = x) /\
                (!x. norm x < &1 ==> g(f x) = x)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[hyperbolic_isometry] THEN MAP_EVERY EXISTS_TAC
   [`\x. kleinify(moebius_function(&0) (poincarify w) (poincarify x))`;
   `\x. kleinify(moebius_function(&0) (--(poincarify w)) (poincarify x))`] THEN
  ASM_SIMP_TAC[NORM_KLEINIFY_MOEBIUS_LT; NORM_POINCARIFY_LT;
               DDIST_KLEINIFY_MOEBIUS; KLEINIFY_POINCARIFY; VECTOR_NEG_NEG;
               BETWEEN_KLEINIFY_MOEBIUS; NORM_NEG; MOEBIUS_FUNCTION_COMPOSE;
               POINCARIFY_KLEINIFY; MOEBIUS_FUNCTION_NORM_LT_1] THEN
  ASM_SIMP_TAC[MOEBIUS_FUNCTION_SIMPLE; COMPLEX_SUB_REFL; complex_div;
               COMPLEX_VEC_0; KLEINIFY_0; POINCARIFY_0; COMPLEX_MUL_LZERO;
               COMPLEX_MUL_RZERO; COMPLEX_SUB_LZERO; COMPLEX_NEG_NEG;
               COMPLEX_SUB_RZERO; COMPLEX_INV_1; COMPLEX_MUL_RID;
               KLEINIFY_POINCARIFY])
```

### Informal statement
For all `w` such that the norm of `w` is less than 1, there exist functions `f` and `g` from `real^2` to `real^2` such that `f` and `g` are hyperbolic isometries, `f(w)` equals the zero vector, `g` applied to the zero vector equals `w`, and for all `x` with norm less than 1, `f` composed with `g` applied to `x` equals `x` and `g` composed with `f` applied to `x` equals `x`.

### Informal sketch
* The proof starts by assuming `w` with norm less than 1.
* It then asserts the existence of `f` and `g` as hyperbolic isometries, defined using `kleinify`, `moebius_function`, and `poincarify`.
* Key steps involve simplifying the expressions for `f` and `g` using properties of `hyperbolic_isometry`, `kleinify`, and `moebius_function`.
* The proof verifies that `f(w)` equals the zero vector and `g` applied to the zero vector equals `w`.
* It then checks that `f` and `g` are inverses of each other for all `x` with norm less than 1, by showing `f(g x) = x` and `g(f x) = x`.
* The use of `REPEAT STRIP_TAC`, `SIMP_TAC`, `MAP_EVERY EXISTS_TAC`, and `ASM_SIMP_TAC` suggests a systematic approach to simplifying and verifying the properties of `f` and `g`.

### Mathematical insight
This theorem provides a construction of hyperbolic isometries `f` and `g` that act as inverses of each other within the unit disk, mapping a given point `w` to the origin and vice versa. This is crucial in hyperbolic geometry, as it establishes a way to translate points within the hyperbolic space in a manner consistent with its metric and geometric properties.

### Dependencies
#### Theorems and definitions
* `hyperbolic_isometry`
* `kleinify`
* `moebius_function`
* `poincarify`
* `NORM_KLEINIFY_MOEBIUS_LT`
* `NORM_POINCARIFY_LT`
* `DDIST_KLEINIFY_MOEBIUS`
* `KLEINIFY_POINCARIFY`
* `VECTOR_NEG_NEG`
* `BETWEEN_KLEINIFY_MOEBIUS`
* `NORM_NEG`
* `MOEBIUS_FUNCTION_COMPOSE`
* `POINCARIFY_KLEINIFY`
* `MOEBIUS_FUNCTION_NORM_LT_1`
* `MOEBIUS_FUNCTION_SIMPLE`
* `COMPLEX_SUB_REFL`
* `complex_div`
* `COMPLEX_VEC_0`
* `KLEINIFY_0`
* `POINCARIFY_0`
* `COMPLEX_MUL_LZERO`
* `COMPLEX_MUL_RZERO`
* `COMPLEX_SUB_LZERO`
* `COMPLEX_NEG_NEG`
* `COMPLEX_SUB_RZERO`
* `COMPLEX_INV_1`
* `COMPLEX_MUL_RID`
* `KLEINIFY_POINCARIFY`

---

## plane_tybij

### Name of formal statement
plane_tybij

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let plane_tybij =
  let th = prove
   (`?x:real^2. norm x < &1`,
    EXISTS_TAC `vec 0:real^2` THEN NORM_ARITH_TAC) in
  new_type_definition "plane" ("mk_plane","dest_plane") th;;
```

### Informal statement
There exists a vector `x` of type `real^2` such that the norm of `x` is less than 1. This statement is used to define a new type "plane" with constructors `mk_plane` and destructor `dest_plane`.

### Informal sketch
* The proof starts by asserting the existence of a vector `x` in `real^2` with a norm less than 1.
* The `EXISTS_TAC` tactic is used to introduce a witness, in this case, the zero vector `vec 0:real^2`, which satisfies the condition.
* The `NORM_ARITH_TAC` tactic is then applied to establish the inequality `norm x < &1` for the introduced witness.
* The proof is then used to define a new type "plane" with the specified constructors and destructor.

### Mathematical insight
This definition introduces a new type "plane" based on the existence of a vector in `real^2` with a norm less than 1. The choice of the zero vector as a witness simplifies the proof. This construction is fundamental in defining geometric or spatial models where points or vectors in a 2D space are considered.

### Dependencies
* `EXISTS_TAC`
* `NORM_ARITH_TAC`
* `new_type_definition`
* `real^2`
* `norm`
* `vec 0:real^2`

### Porting notes
When porting this definition to another proof assistant, ensure that the equivalent of `EXISTS_TAC` and `NORM_ARITH_TAC` are used appropriately to introduce the witness and establish the norm inequality. Additionally, the concept of `real^2` and vector norms should be defined or imported correctly in the target system. The `new_type_definition` mechanism may vary between systems, so the port should be adjusted accordingly to introduce the "plane" type with its constructors and destructor.

---

## pbetween

### Name of formal statement
pbetween

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pbetween = new_definition
 `pbetween y (x,z) <=> between (dest_plane y) (dest_plane x,dest_plane z)`
```

### Informal statement
The `pbetween` relation holds between three points `y`, `x`, and `z` if and only if the point `y` lies between the points `x` and `z` when projected onto their respective planes, as determined by the `dest_plane` function.

### Informal sketch
* The definition of `pbetween` involves the `between` relation, which is applied to the results of `dest_plane` function calls on points `y`, `x`, and `z`.
* The `dest_plane` function is used to project points onto their respective planes before checking the `between` relation.
* The `between` relation is a ternary relation that checks if a point lies between two other points.

### Mathematical insight
The `pbetween` definition provides a way to determine if a point lies between two other points in a geometric context, taking into account the planes on which these points lie. This is important in geometric and spatial reasoning, where the relationships between points in space are crucial.

### Dependencies
* `between`
* `dest_plane`

### Porting notes
When translating this definition into other proof assistants, pay attention to how the `between` relation and `dest_plane` function are defined and used. In some systems, the `between` relation might be defined differently or might require additional parameters. Additionally, the `dest_plane` function might need to be adapted to fit the specific geometric framework of the target system.

---

## pdist

### Name of formal statement
pdist

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pdist = new_definition `pdist(x,y) = ddist(dest_plane x,dest_plane y)`;;
```

### Informal statement
The `pdist` function is defined as the distance between the destination planes of two points `x` and `y`, calculated using the `ddist` function.

### Informal sketch
* The definition relies on the `ddist` function to compute the distance between two planes.
* The `dest_plane` function is used to extract the destination plane from each point `x` and `y`.
* The `pdist` function then applies `ddist` to these destination planes to obtain the final result.
* The key logical stage involves applying the `ddist` function to the output of `dest_plane` for both `x` and `y`.

### Mathematical insight
The `pdist` definition provides a way to measure the distance between two points in terms of their associated planes, which is a meaningful construction in geometric or spatial reasoning contexts. This definition fits into a broader theory of spatial relationships and distances, potentially supporting more complex geometric proofs or theorems.

### Dependencies
* `ddist`
* `dest_plane`

### Porting notes
When translating `pdist` into another proof assistant, ensure that equivalent functions for `ddist` and `dest_plane` are defined and accessible. Pay attention to how the target system handles function definitions and compositions, as well as any specific requirements for type annotations or implicit type conversions.

---

## DEST_PLANE_NORM_LT

### Name of formal statement
DEST_PLANE_NORM_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DEST_PLANE_NORM_LT = prove
 (`!x. norm(dest_plane x) < &1`,
  MESON_TAC[plane_tybij])
```

### Informal statement
For all `x`, the norm of the destination plane of `x` is less than 1.

### Informal sketch
* The proof involves showing that for any `x`, the norm of `dest_plane x` is bounded above by 1.
* The `MESON_TAC` tactic is used, which likely involves applying a set of meson rules to prove the statement.
* The `plane_tybij` theorem or definition is also used, which may provide some properties or constraints on the `dest_plane` function.

### Mathematical insight
This statement provides a bound on the norm of the destination plane of any `x`, which may be useful in subsequent proofs involving geometric or spatial reasoning. The `dest_plane` function likely maps `x` to a plane in some space, and the norm of this plane is a measure of its "size" or "extent". The fact that this norm is bounded above by 1 may be a fundamental property of the space or the `dest_plane` function.

### Dependencies
* `plane_tybij`
* `dest_plane`
* `norm`

### Porting notes
When porting this statement to another proof assistant, care should be taken to ensure that the `MESON_TAC` tactic is replaced with an equivalent tactic or set of tactics. Additionally, the `plane_tybij` theorem or definition should be ported and made available in the target system. The `dest_plane` function and `norm` function should also be defined and available in the target system.

---

## DEST_PLANE_EQ

### Name of formal statement
DEST_PLANE_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DEST_PLANE_EQ = prove
 (`!x y. dest_plane x = dest_plane y <=> x = y`,
  MESON_TAC[plane_tybij])
```

### Informal statement
For all `x` and `y`, `dest_plane x` equals `dest_plane y` if and only if `x` equals `y`.

### Informal sketch
* The theorem `DEST_PLANE_EQ` is proved using `MESON_TAC` with `plane_tybij`.
* The proof involves showing a bi-implication between the equality of `dest_plane x` and `dest_plane y` and the equality of `x` and `y`.
* The `MESON_TAC` tactic is used to automate the proof, likely by applying various logical rules and theorems related to equality and bijections, as hinted by `plane_tybij`.

### Mathematical insight
This theorem establishes that the `dest_plane` function is injective, meaning that it maps distinct inputs to distinct outputs. This property is crucial in various mathematical and computational contexts, such as geometry and computer graphics, where `dest_plane` might represent a transformation or projection operation. The injectivity of `dest_plane` ensures that different inputs are not collapsed into the same output, preserving the distinction between them.

### Dependencies
* `plane_tybij`
* Basic equality theorems and properties

### Porting notes
When translating this theorem into other proof assistants, pay attention to how they handle injectivity proofs and bi-implications. Some systems might require explicit proof steps for each direction of the bi-implication, while others might provide tactics or automation similar to `MESON_TAC` for simplifying the proof process. Additionally, the representation of the `dest_plane` function and its properties, such as `plane_tybij`, will need to be appropriately defined or imported in the target system.

---

## FORALL_DEST_PLANE

### Name of formal statement
FORALL_DEST_PLANE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FORALL_DEST_PLANE = prove
 (`!P. (!x. P(dest_plane x)) <=> (!x. norm x < &1 ==> P x)`,
  MESON_TAC[plane_tybij])
```

### Informal statement
For all predicates P, the statement "for all x, P holds for the destination plane of x" is equivalent to "for all x, if the norm of x is less than 1, then P holds for x".

### Informal sketch
* The theorem `FORALL_DEST_PLANE` establishes a equivalence between two statements involving a predicate P and the `dest_plane` function.
* The proof involves using the `MESON_TAC` tactic with the `plane_tybij` theorem to derive the equivalence.
* The key idea is to show that the universal quantification over the `dest_plane` of x is equivalent to a conditional statement involving the norm of x.

### Mathematical insight
This theorem provides a way to rewrite a statement about the destination plane of a point in terms of a condition on the norm of the point. This can be useful in proofs involving geometric or topological properties of points in a space.

### Dependencies
* `plane_tybij`
* `dest_plane`
* `norm`

### Porting notes
When porting this theorem to another proof assistant, note that the `MESON_TAC` tactic may need to be replaced with a similar tactic or a combination of tactics that achieve the same effect. Additionally, the `plane_tybij` theorem may need to be ported or re-proved in the target system. The use of the `&1` constant may also require special handling, as it represents a specific numerical value in HOL Light.

---

## EXISTS_DEST_PLANE

### Name of formal statement
EXISTS_DEST_PLANE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EXISTS_DEST_PLANE = prove
 (`!P. (?x. P(dest_plane x)) <=> (?x. norm x < &1 /\ P x)`,
  MESON_TAC[plane_tybij])
```

### Informal statement
For all predicates P, there exists an x such that P holds for the destination plane of x if and only if there exists an x such that the norm of x is less than 1 and P holds for x.

### Informal sketch
* The theorem `EXISTS_DEST_PLANE` establishes an equivalence between two existential statements involving a predicate P.
* The proof involves using the `MESON_TAC` tactic with `plane_tybij` to establish the bidirectional implication.
* The left-to-right direction involves finding an x such that P holds for the `dest_plane` of x, given the existence of such an x.
* The right-to-left direction involves showing that if there exists an x with norm less than 1 and P holding for x, then there exists an x such that P holds for the `dest_plane` of x.

### Mathematical insight
This theorem provides a characterization of the existence of points in a plane that satisfy a certain property P, in terms of the existence of points with norm less than 1 that satisfy P. This is likely useful in geometric or topological arguments where the existence of points with certain properties needs to be established.

### Dependencies
* `plane_tybij`
* `dest_plane`
* `norm`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `MESON_TAC` tactic is replaced with an equivalent tactic or sequence of tactics that can establish the same bidirectional implication. Additionally, the `plane_tybij` term should be properly translated or defined in the target system. The use of `&1` to represent a constant may also require special handling, depending on the target system's syntax and semantics.

---

## TARSKI_AXIOM_1_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_1_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_1_NONEUCLIDEAN = prove
 (`!a b. pdist(a,b) = pdist(b,a)`,
  REWRITE_TAC[pdist; DDIST_SYM])
```

### Informal statement
For all points `a` and `b`, the pseudo-distance from `a` to `b` is equal to the pseudo-distance from `b` to `a`.

### Informal sketch
* The proof involves establishing the symmetry property of the `pdist` function, which represents pseudo-distance.
* The `REWRITE_TAC` tactic is used with the `pdist` and `DDIST_SYM` theorems to derive the equality `pdist(a,b) = pdist(b,a)` for all `a` and `b`.
* The symmetry property is crucial in geometric and metric contexts, ensuring that the distance between two points does not depend on the order in which they are considered.

### Mathematical insight
This axiom formalizes the intuitive notion that distance between two points is symmetric, a fundamental property in geometry and metric spaces. It is essential for deriving further properties and theorems related to distances and metrics, making it a foundational element in the development of geometric and spatial reasoning within the formal system.

### Dependencies
* `pdist`
* `DDIST_SYM`

### Porting notes
When translating this axiom into other proof assistants like Lean, Coq, or Isabelle, ensure that the symmetry property of the distance function is appropriately defined and used. Note that the specific tactic `REWRITE_TAC` and the theorems `pdist` and `DDIST_SYM` might need to be adapted or redefined according to the target system's syntax and libraries. Pay attention to how each system handles binders and quantifiers, as well as any automated reasoning mechanisms that might simplify or complicate the porting process.

---

## TARSKI_AXIOM_2_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_2_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_2_NONEUCLIDEAN = prove
 (`!a b p q r s.
        pdist(a,b) = pdist(p,q) /\ pdist(a,b) = pdist(r,s)
        ==> pdist(p,q) = pdist(r,s)`,
  REAL_ARITH_TAC)
```

### Informal statement
For all points $a$, $b$, $p$, $q$, $r$, and $s$, if the distance between $a$ and $b$ is equal to the distance between $p$ and $q$, and the distance between $a$ and $b$ is also equal to the distance between $r$ and $s$, then the distance between $p$ and $q$ is equal to the distance between $r$ and $s$.

### Informal sketch
* The proof starts with the assumption that `pdist(a,b) = pdist(p,q)` and `pdist(a,b) = pdist(r,s)`.
* Using these equalities, we can apply `REAL_ARITH_TAC` to derive the conclusion `pdist(p,q) = pdist(r,s)`.
* The key step involves using the transitivity of equality to chain the equalities together.

### Mathematical insight
This axiom formalizes the concept of equidistance in a geometric context, specifically in a non-Euclidean setting. It states that if two pairs of points have the same distance to a common reference pair, then those two pairs must have the same distance to each other. This axiom is crucial in establishing the foundation of geometric theories, particularly in the context of Tarski's geometry.

### Dependencies
* `pdist`
* `REAL_ARITH_TAC`

### Porting notes
When porting this axiom to another proof assistant, ensure that the equivalent of `REAL_ARITH_TAC` is used to handle the arithmetic reasoning. Additionally, be mindful of how the target system handles equality and distances between points, as this may require adjustments to the axiom's statement or the proof strategy.

---

## TARSKI_AXIOM_3_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_3_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_3_NONEUCLIDEAN = prove
 (`!a b c. pdist(a,b) = pdist(c,c) ==> a = b`,
  SIMP_TAC[FORALL_DEST_PLANE; pdist; DDIST_REFL; DDIST_EQ_0; DEST_PLANE_EQ])
```

### Informal statement
For all points `a`, `b`, and `c`, if the distance between `a` and `b` is equal to the distance between `c` and `c`, then `a` is equal to `b`.

### Informal sketch
* The proof involves assuming `pdist(a, b) = pdist(c, c)` and deriving `a = b` from this assumption.
* The `SIMP_TAC` tactic is used with various theorems (`FORALL_DEST_PLANE`, `pdist`, `DDIST_REFL`, `DDIST_EQ_0`, `DEST_PLANE_EQ`) to simplify the goal and eventually prove the statement.
* Key steps involve recognizing that `pdist(c, c)` is equivalent to `0` due to `DDIST_REFL`, and then using `DDIST_EQ_0` to infer that `a = b` when `pdist(a, b) = 0`.

### Mathematical insight
This axiom formalizes the concept of identity for equidistance in a geometric context, essentially stating that if two points are at the same distance from each other as a point is from itself (which is zero), then those two points must be the same. This is foundational in establishing the properties of distance and equality in geometric and metric spaces.

### Dependencies
* Theorems:
  - `FORALL_DEST_PLANE`
  - `pdist`
  - `DDIST_REFL`
  - `DDIST_EQ_0`
  - `DEST_PLANE_EQ`
* Definitions:
  - `pdist`

### Porting notes
When translating this axiom into another proof assistant, pay close attention to how distances and equalities are defined and handled, as the specific tactics and theorems used may differ. For example, in systems that automatically handle or simplify equalities and distances, the proof might be significantly shorter or might not require explicit invocation of tactics like `SIMP_TAC`. Additionally, ensure that the ported version correctly captures the quantification over all points `a`, `b`, and `c`, as well as the implication from the distance equality to the point equality.

---

## TARSKI_AXIOM_4_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_4_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_4_NONEUCLIDEAN = prove
 (`!a q b c. ?x. pbetween a (q,x) /\ pdist(a,x) = pdist(b,c)`,
  REWRITE_TAC[pbetween; pdist; FORALL_DEST_PLANE; EXISTS_DEST_PLANE] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?d:real^2. norm d < &1 /\ ddist(b:real^2,c) = ddist(vec 0,d)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `b:real^2` HYPERBOLIC_TRANSLATION) THEN
    ASM_REWRITE_TAC[hyperbolic_isometry] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `norm(a:real^2) < &1 /\ norm(q:real^2) < &1 /\ norm(d:real^2) < &1`
   MP_TAC THENL [ASM_REWRITE_TAC[]; REPEAT(POP_ASSUM(K ALL_TAC))] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`d:real^2`; `q:real^2`; `a:real^2`] THEN
  MATCH_MP_TAC(MESON[] `P(vec 0) /\ (P(vec 0) ==> !x. P x) ==> !x. P x`) THEN
  REWRITE_TAC[NORM_0; REAL_LT_01] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `vec 0:real^2` TARSKI_AXIOM_4_EUCLIDEAN) THEN
    MESON_TAC[DIST_0; DDIST_EQ_ORIGIN];
    DISCH_THEN(LABEL_TAC "*") THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `a:real^2` HYPERBOLIC_TRANSLATION) THEN
    ASM_REWRITE_TAC[hyperbolic_isometry; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^2->real^2`; `g:real^2->real^2`] THEN
    STRIP_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`(f:real^2->real^2) q`; `d:real^2`]) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g:real^2->real^2) x` THEN ASM_MESON_TAC[]])
```

### Informal statement
For all points `a`, `b`, `c`, and `q`, there exists a point `x` such that `x` is between `a` and `q` and the distance from `a` to `x` is equal to the distance from `b` to `c`. This statement is quantified over all points in the plane, with the constraint that `a`, `b`, `c`, and `q` must be within the unit disk.

### Informal sketch
* The proof begins by applying `REWRITE_TAC` to expand the definitions of `pbetween` and `pdist`.
* It then applies `SUBGOAL_THEN` to assume the existence of a point `d` within the unit disk such that the distance from `b` to `c` is equal to the distance from the origin to `d`.
* The proof proceeds by using `MP_TAC` to apply the `HYPERBOLIC_TRANSLATION` theorem to `b`, and then using `ASM_REWRITE_TAC` to rewrite the goal in terms of hyperbolic isometries.
* The proof then uses `SUBGOAL_THEN` to assume that `a`, `q`, and `d` are all within the unit disk, and applies `MAP_EVERY` to introduce these assumptions as premises.
* The proof then applies `MATCH_MP_TAC` to a meson rule, which allows it to conclude that the property holds for all points `x`.
* The proof then uses `CONJ_TAC` to split the goal into two subgoals, one of which is discharged using `TARSKI_AXIOM_4_EUCLIDEAN`, and the other of which is proved using `HYPERBOLIC_TRANSLATION` and `hyperbolic_isometry`.

### Mathematical insight
This axiom is a fundamental property of hyperbolic geometry, and is used to construct segments and prove other geometric properties. The key idea is that for any two points `b` and `c`, there exists a point `x` that is between `a` and `q` and has the same distance from `a` as `b` and `c` have from each other. This property is essential for establishing the consistency and completeness of hyperbolic geometry.

### Dependencies
* Theorems:
	+ `HYPERBOLIC_TRANSLATION`
	+ `TARSKI_AXIOM_4_EUCLIDEAN`
* Definitions:
	+ `pbetween`
	+ `pdist`
	+ `hyperbolic_isometry`
* Axioms:
	+ None

### Porting notes
When porting this axiom to another proof assistant, care should be taken to preserve the precise quantifier structure and constraints. The use of `SUBGOAL_THEN` and `MAP_EVERY` may need to be adapted to the target system's tactic language. Additionally, the `HYPERBOLIC_TRANSLATION` theorem and `hyperbolic_isometry` definition may need to be ported separately.

---

## TARSKI_AXIOM_5_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_5_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_5_NONEUCLIDEAN = prove
 (`!a b c x a' b' c' x'.
        ~(a = b) /\
        pdist(a,b) = pdist(a',b') /\
        pdist(a,c) = pdist(a',c') /\
        pdist(b,c) = pdist(b',c') /\
        pbetween b (a,x) /\ pbetween b' (a',x') /\ pdist(b,x) = pdist(b',x')
        ==> pdist(c,x) = pdist(c',x')`,
  REWRITE_TAC[FORALL_DEST_PLANE; pdist; pbetween; GSYM DEST_PLANE_EQ] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `b':real^2` HYPERBOLIC_TRANSLATION) THEN
  MP_TAC(ISPEC `b:real^2` HYPERBOLIC_TRANSLATION) THEN
  ASM_REWRITE_TAC[RIGHT_IMP_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[hyperbolic_isometry] THEN MAP_EVERY X_GEN_TAC
   [`f:real^2->real^2`; `f':real^2->real^2`; `g:real^2->real^2`;
    `g':real^2->real^2`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(f:real^2->real^2) x`; `(f:real^2->real^2) c`;
                `(g:real^2->real^2) x'`; `(g:real^2->real^2) c'`]
        DDIST_CONGRUENT_TRIPLES_0) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> r) /\ q ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DDIST_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^2->real^2) a`; `(f:real^2->real^2) c`;
                `(g:real^2->real^2) a'`; `(g:real^2->real^2) c'`]
        DDIST_CONGRUENT_TRIPLES_0) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM DDIST_CONGRUENT_TRIPLES_0] THEN  CONJ_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SYM(ASSUME `(f:complex->complex) b = vec 0`)] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [SYM(ASSUME `(g:complex->complex) b' = vec 0`)] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[DDIST_SYM];
    STRIP_TAC THEN MP_TAC(ISPECL
     [`(f:real^2->real^2) a`; `(f:real^2->real^2) b`; `(f:real^2->real^2) c`;
      `(f:real^2->real^2) x`;`(g:real^2->real^2) a'`; `(g:real^2->real^2) b'`;
      `(g:real^2->real^2) c'`; `(g:real^2->real^2) x'`]
     TARSKI_AXIOM_5_EUCLIDEAN) THEN
    SUBGOAL_THEN
     `ddist((f:real^2->real^2) b,f x) = ddist((g:real^2->real^2) b',g x')`
    MP_TAC THENL
     [ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DDIST_EQ_ORIGIN] THEN DISCH_TAC] THEN
    ASM_MESON_TAC[DIST_SYM; DIST_0])
```

### Informal statement
For all points $a$, $b$, $c$, $x$, $a'$, $b'$, $c'$, and $x'$, if $a$ is not equal to $b$, the distance between $a$ and $b$ is equal to the distance between $a'$ and $b'$, the distance between $a$ and $c$ is equal to the distance between $a'$ and $c'$, the distance between $b$ and $c$ is equal to the distance between $b'$ and $c'$, $b$ is between $a$ and $x$, $b'$ is between $a'$ and $x'$, and the distance between $b$ and $x$ is equal to the distance between $b'$ and $x'$, then the distance between $c$ and $x$ is equal to the distance between $c'$ and $x'$.

### Informal sketch
* The proof starts by assuming the given conditions: $a \neq b$, $pdist(a,b) = pdist(a',b')$, $pdist(a,c) = pdist(a',c')$, $pdist(b,c) = pdist(b',c')$, $pbetween(b, a, x)$, $pbetween(b', a', x')$, and $pdist(b,x) = pdist(b',x')$.
* It then applies various rewrite rules and tactics to simplify and manipulate the assumptions, including `HYPERBOLIC_TRANSLATION`, `DDIST_CONGRUENT_TRIPLES_0`, and `TARSKI_AXIOM_5_EUCLIDEAN`.
* The proof involves using `MATCH_MP_TAC` to apply modus ponens and `CONJ_TAC` to combine multiple subgoals.
* Key steps include using `DDIST_CONGRUENT_TRIPLES_0` to establish congruence of triples and `HYPERBOLIC_TRANSLATION` to apply hyperbolic translations.
* The proof also involves using `GEN_REWRITE_TAC` to apply rewrite rules and `ASM_SIMP_TAC` to simplify assumptions.

### Mathematical insight
This axiom is a fundamental property in geometry, stating that if two sets of points have the same distances between them, and one set has a point between two others, then the corresponding point in the other set is also between the corresponding points. This property is essential in establishing the consistency and completeness of geometric theories.

### Dependencies
* Theorems:
	+ `HYPERBOLIC_TRANSLATION`
	+ `DDIST_CONGRUENT_TRIPLES_0`
	+ `TARSKI_AXIOM_5_EUCLIDEAN`
* Definitions:
	+ `pdist`
	+ `pbetween`
	+ `ddist`
* Axioms:
	+ `FORALL_DEST_PLANE`
	+ `DEST_PLANE_EQ`
	+ `RIGHT_IMP_FORALL_THM`
	+ `LEFT_IMP_EXISTS_THM`
	+ `hyperbolic_isometry`

### Porting notes
When porting this axiom to other proof assistants, pay attention to the handling of binders and the application of rewrite rules. The use of `GEN_REWRITE_TAC` and `ASM_SIMP_TAC` may need to be adapted to the target system's rewriting mechanisms. Additionally, the `HYPERBOLIC_TRANSLATION` and `DDIST_CONGRUENT_TRIPLES_0` theorems may require special attention due to their geometric nature.

---

## TARSKI_AXIOM_6_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_6_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_6_NONEUCLIDEAN = prove
 (`!a b. pbetween b (a,a) ==> a = b`,
  REWRITE_TAC[pbetween; FORALL_DEST_PLANE; GSYM DEST_PLANE_EQ] THEN
  MESON_TAC[TARSKI_AXIOM_6_EUCLIDEAN])
```

### Informal statement
For all points `a` and `b`, if `b` is between `a` and `a`, then `a` is equal to `b`.

### Informal sketch
* The proof starts with the assumption that `b` is between `a` and `a`, which is denoted by `pbetween b (a, a)`.
* The `REWRITE_TAC` tactic is applied to rewrite the `pbetween` relation using its definition, as well as `FORALL_DEST_PLANE` and `GSYM DEST_PLANE_EQ`.
* The `MESON_TAC` tactic is then applied with `TARSKI_AXIOM_6_EUCLIDEAN` to derive the conclusion that `a` is equal to `b`.

### Mathematical insight
This axiom formalizes the concept of between-ness in a non-Euclidean geometry, stating that the only point between two identical points is the point itself. This axiom is important because it provides a fundamental property of the between-ness relation, which is used to define other geometric concepts.

### Dependencies
* `pbetween`
* `TARSKI_AXIOM_6_EUCLIDEAN`
* `FORALL_DEST_PLANE`
* `GSYM DEST_PLANE_EQ`

### Porting notes
When translating this axiom into other proof assistants, note that the `REWRITE_TAC` and `MESON_TAC` tactics may need to be replaced with equivalent tactics or strategies. Additionally, the `TARSKI_AXIOM_6_EUCLIDEAN` axiom may need to be ported as well, as it is used in the proof. The `pbetween` relation and other dependencies should also be defined or imported accordingly.

---

## TARSKI_AXIOM_7_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_7_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_7_NONEUCLIDEAN = prove
 (`!a b c p q.
    pbetween p (a,c) /\ pbetween q (b,c)
    ==> ?x. pbetween x (p,b) /\ pbetween x (q,a)`,
  REWRITE_TAC[pbetween; FORALL_DEST_PLANE; EXISTS_DEST_PLANE] THEN
  MESON_TAC[BETWEEN_NORM_LT; TARSKI_AXIOM_7_EUCLIDEAN])
```

### Informal statement
For all points `a`, `b`, `c`, `p`, and `q`, if `p` lies between `a` and `c` and `q` lies between `b` and `c`, then there exists a point `x` such that `x` lies between `p` and `b` and `x` lies between `q` and `a`.

### Informal sketch
* The proof involves assuming the premises `pbetween p (a,c)` and `pbetween q (b,c)`, which assert that `p` lies between `a` and `c` and `q` lies between `b` and `c`, respectively.
* The goal is to show the existence of a point `x` that satisfies `pbetween x (p,b)` and `pbetween x (q,a)`.
* The `REWRITE_TAC` tactic is applied to rewrite the `pbetween` relations using the `FORALL_DEST_PLANE` and `EXISTS_DEST_PLANE` rules.
* The `MESON_TAC` tactic is then used to derive the conclusion, utilizing the `BETWEEN_NORM_LT` and `TARSKI_AXIOM_7_EUCLIDEAN` theorems.

### Mathematical insight
This axiom, known as Pasch's axiom, is a fundamental property in geometry that describes the relationship between points and lines. It ensures that if two lines intersect a third line, then there exists a point that lies between the intersection points of the two lines. This axiom is crucial in establishing the consistency and completeness of geometric systems.

### Dependencies
* Theorems:
	+ `BETWEEN_NORM_LT`
	+ `TARSKI_AXIOM_7_EUCLIDEAN`
* Definitions:
	+ `pbetween`
* Inductive rules:
	+ `FORALL_DEST_PLANE`
	+ `EXISTS_DEST_PLANE`

### Porting notes
When translating this axiom to other proof assistants, pay attention to the handling of binders and the representation of geometric concepts. In particular, the `pbetween` relation and the `FORALL_DEST_PLANE` and `EXISTS_DEST_PLANE` rules may need to be redefined or reinterpreted in the target system. Additionally, the `REWRITE_TAC` and `MESON_TAC` tactics may have analogous tactics in other proof assistants, but their exact behavior and applicability may differ.

---

## TARSKI_AXIOM_8_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_8_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_8_NONEUCLIDEAN = prove
 (`?a b c. ~pbetween b (a,c) /\ ~pbetween c (b,a) /\ ~pbetween a (c,b)`,
  REWRITE_TAC[pbetween; EXISTS_DEST_PLANE; NORM_LT_SQUARE; NORM_POW_2] THEN
  MAP_EVERY (fun t -> EXISTS_TAC t THEN
    SIMP_TAC[DOT_LMUL; DOT_RMUL; DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[DOT_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV)
   [`vec 0:real^2`; `(&1 / &2) % basis 1:real^2`;
    `(&1 / &2) % basis 2:real^2`] THEN
  REPEAT CONJ_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
  SIMP_TAC[COLLINEAR_3_2D; VECTOR_MUL_COMPONENT; VEC_COMPONENT; ARITH;
           BASIS_COMPONENT; DIMINDEX_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV)
```

### Informal statement
For all points `a`, `b`, and `c`, it is not the case that `b` is between `a` and `c`, and not the case that `c` is between `b` and `a`, and not the case that `a` is between `c` and `b`.

### Informal sketch
* The proof starts by assuming the negation of the `pbetween` relations among points `a`, `b`, and `c`.
* It then applies various simplifications and rewrites using `REWRITE_TAC` with theorems such as `pbetween`, `EXISTS_DEST_PLANE`, `NORM_LT_SQUARE`, and `NORM_POW_2`.
* The proof uses `MAP_EVERY` to apply `EXISTS_TAC` followed by `SIMP_TAC` with several theorems including `DOT_LMUL`, `DOT_RMUL`, `DOT_BASIS_BASIS`, `DIMINDEX_2`, and `ARITH` to simplify expressions involving vector operations.
* It further simplifies using `REWRITE_TAC` with `DOT_LZERO` and applies `CONV_TAC` with `REAL_RAT_REDUCE_CONV` for rational reduction.
* The proof then repeats conjunctions and applies `DISCH_THEN` with `MATCH_MP` using the `BETWEEN_IMP_COLLINEAR` theorem.
* Finally, it simplifies using `SIMP_TAC` with theorems like `COLLINEAR_3_2D`, `VECTOR_MUL_COMPONENT`, `VEC_COMPONENT`, `ARITH`, `BASIS_COMPONENT`, and `DIMINDEX_2`, and applies `CONV_TAC` with `REAL_RAT_REDUCE_CONV` again.

### Mathematical insight
This axiom is part of the foundation for geometry in the Tarski system, specifically addressing the concept of points not being between each other in a 2-dimensional space. It's crucial for establishing the basic properties of geometric objects and their relationships, ensuring that the geometry is not Euclidean.

### Dependencies
#### Theorems
* `pbetween`
* `EXISTS_DEST_PLANE`
* `NORM_LT_SQUARE`
* `NORM_POW_2`
* `DOT_LMUL`
* `DOT_RMUL`
* `DOT_BASIS_BASIS`
* `DIMINDEX_2`
* `ARITH`
* `DOT_LZERO`
* `BETWEEN_IMP_COLLINEAR`
* `COLLINEAR_3_2D`
* `VECTOR_MUL_COMPONENT`
* `VEC_COMPONENT`
* `BASIS_COMPONENT`
#### Tactics and Conversions
* `REWRITE_TAC`
* `MAP_EVERY`
* `EXISTS_TAC`
* `SIMP_TAC`
* `CONV_TAC`
* `REAL_RAT_REDUCE_CONV`
* `DISCH_THEN`
* `MATCH_MP`
* `REPEAT`
* `CONJ_TAC`

---

## TARSKI_AXIOM_9_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_9_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_9_NONEUCLIDEAN = prove
 (`!p q a b c.
        ~(p = q) /\
        pdist(a,p) = pdist(a,q) /\ pdist(b,p) = pdist(b,q) /\
        pdist(c,p) = pdist(c,q)
        ==> pbetween b (a,c) \/ pbetween c (b,a) \/ pbetween a (c,b)`,
  REWRITE_TAC[pdist; pbetween; FORALL_DEST_PLANE; GSYM DEST_PLANE_EQ] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^2`; `q:real^2`] HYPERBOLIC_MIDPOINT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `x:real^2` THEN
  STRIP_TAC THEN MP_TAC(ISPEC `x:real^2` HYPERBOLIC_TRANSLATION) THEN
  SUBGOAL_THEN `norm(x:real^2) < &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[BETWEEN_NORM_LT]; ONCE_REWRITE_TAC[BETWEEN_SYM]] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; hyperbolic_isometry] THEN
  REWRITE_TAC[GSYM COLLINEAR_BETWEEN_CASES] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `collinear{(f:real^2->real^2) b,f c,f a}` MP_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[COLLINEAR_BETWEEN_CASES]] THEN
  SUBGOAL_THEN `ddist(f a,f p) = ddist(f a,f q) /\
                ddist(f b,f p) = ddist(f b,f q) /\
                ddist(f c,f p) = ddist(f c,f q) /\
                ~((f:real^2->real^2) q = f p)`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^2) q = --(f p)` SUBST1_TAC THENL
   [SUBGOAL_THEN `between ((f:real^2->real^2) x) (f p,f q) /\
                  ddist(f x,f p) = ddist(f x,f q)`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DDIST_EQ_ORIGIN] THEN
    REWRITE_TAC[GSYM MIDPOINT_BETWEEN; midpoint; NORM_ARITH
     `norm(a:real^N) = norm b <=> dist(a,vec 0) = dist(vec 0,b)`] THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[ddist] THEN ASM_SIMP_TAC[NORM_NEG; real_div; REAL_INV_MUL] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; ABS_SQUARE_LT_1; REAL_ABS_NORM; REAL_FIELD
     `&0 < x /\ &0 < y
      ==> (a * inv x * inv y - &1 = b * inv x * inv y - &1 <=> a = b)`] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `--x:real^N = x <=> x = vec 0`] THEN
    REWRITE_TAC[COLLINEAR_3_2D; VECTOR_SUB_COMPONENT; DOT_2; GSYM DOT_EQ_0;
                  VECTOR_NEG_COMPONENT] THEN CONV_TAC REAL_RING])
```

### Informal statement
For all points `p`, `q`, `a`, `b`, and `c`, if `p` is not equal to `q` and the perpendicular distances from `a`, `b`, and `c` to `p` are equal to the perpendicular distances from `a`, `b`, and `c` to `q`, then either `b` is between `a` and `c`, `c` is between `b` and `a`, or `a` is between `c` and `b`.

### Informal sketch
* The proof starts by assuming the conditions `~(p = q)` and the equalities of perpendicular distances from points `a`, `b`, and `c` to `p` and `q`.
* It then applies various rewrite tactics and theorems, including `HYPERBOLIC_MIDPOINT` and `HYPERBOLIC_TRANSLATION`, to derive properties about the points and distances.
* The proof uses the concept of `collinear` points and the `between` relation to establish the final conclusion.
* Key steps involve using `SUBGOAL_THEN` to assume and derive intermediate properties, and applying `ASM_REWRITE_TAC` and `REWRITE_TAC` to simplify and transform the expressions.
* The `hyperbolic_isometry` and `COLLINEAR_BETWEEN_CASES` theorems play crucial roles in establishing the relationships between the points.

### Mathematical insight
This axiom is part of the foundation for a non-Euclidean geometry, specifically in a 2-dimensional space. It provides a condition under which three points are collinear based on their distances to two distinct points. The axiom is essential for constructing and reasoning about geometric objects and their properties in this non-Euclidean context.

### Dependencies
* Theorems:
  + `HYPERBOLIC_MIDPOINT`
  + `HYPERBOLIC_TRANSLATION`
  + `BETWEEN_NORM_LT`
  + `BETWEEN_SYM`
  + `hyperbolic_isometry`
  + `COLLINEAR_BETWEEN_CASES`
* Definitions:
  + `pdist`
  + `pbetween`
  + `ddist`
  + `collinear`
  + `between`
  + `norm`
  + `dist`
  + `vec`
  + `real_div`
  + `REAL_INV_MUL`
  + `REAL_SUB_LT`
  + `ABS_SQUARE_LT_1`
  + `REAL_ABS_NORM`
  + `REAL_FIELD`

### Porting notes
When porting this axiom to another proof assistant, pay close attention to the handling of binders, quantifiers, and the specific geometric and algebraic properties used. Ensure that the target system has equivalent concepts for `pdist`, `pbetween`, `ddist`, and `collinear`, and that the `HYPERBOLIC_MIDPOINT` and `HYPERBOLIC_TRANSLATION` theorems can be adequately represented or derived. The use of `SUBGOAL_THEN` and various rewrite tactics may need to be adapted to the target system's proof scripting language.

---

## NOT_TARSKI_AXIOM_10_NONEUCLIDEAN

### Name of formal statement
NOT_TARSKI_AXIOM_10_NONEUCLIDEAN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_TARSKI_AXIOM_10_NONEUCLIDEAN = prove
 (`~(!a b c d t.
      pbetween d (a,t) /\ pbetween d (b,c) /\ ~(a = d)
      ==> ?x y. pbetween b (a,x) /\ pbetween c (a,y) /\ pbetween t (x,y))`,
  REWRITE_TAC[pbetween; FORALL_DEST_PLANE; EXISTS_DEST_PLANE;
              GSYM DEST_PLANE_EQ; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`vec 0:real^2`; `&1 / &2 % basis 1:real^2`; `&1 / &2 % basis 2:real^2`;
    `&1 / &4 % basis 1 + &1 / &4 % basis 2:real^2`;
    `&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2`]) THEN
  REWRITE_TAC[NOT_IMP; CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT(GEN_TAC THEN DISCH_TAC) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
    SIMP_TAC[COLLINEAR_3_2D; BASIS_COMPONENT; DIMINDEX_2; ARITH; VEC_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO;
                REAL_ARITH `&0 = &1 / &2 * x <=> x = &0`] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(ISPECL [`x:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`y:real^2`; `2`] COMPONENT_LE_NORM) THEN
    SIMP_TAC[DIMINDEX_2; ARITH; BETWEEN_IN_SEGMENT; IN_SEGMENT] THEN
    REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `norm(&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2) pow 2 <= &1 / &2`
    MP_TAC THENL
     [SUBGOAL_THEN `(&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2)$2 =
                    (&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2)$1`
      MP_TAC THENL
       [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; ARITH; BASIS_COMPONENT;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
      ASM_SIMP_TAC[DIMINDEX_2; FORALL_2; DOT_2; VECTOR_ADD_COMPONENT; ARITH;
                   VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
        `a * &0 + y = x + b * &0 ==> abs x + abs y <= (&1 - u) * &1 + u * &1
         ==> abs x <= abs(&1 / &2) /\ abs y <= abs(&1 / &2)`)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
        CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN REAL_ARITH_TAC];
      ALL_TAC]] THEN
  SIMP_TAC[NORM_LT_SQUARE; NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LZERO;
           DOT_LMUL; DOT_RMUL; DOT_BASIS_BASIS; DIMINDEX_2; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[BETWEEN_IN_SEGMENT; IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `&5 / &12`; EXISTS_TAC `&1 / &2`; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; ARITH; BASIS_COMPONENT;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV)
```

### Informal statement
The theorem `NOT_TARSKI_AXIOM_10_NONEUCLIDEAN` states that it is not the case that for all points `a`, `b`, `c`, `d`, and `t`, if `d` lies between `a` and `t` and `d` lies between `b` and `c`, and `a` is not equal to `d`, then there exist points `x` and `y` such that `b` lies between `a` and `x`, `c` lies between `a` and `y`, and `t` lies between `x` and `y`.

### Informal sketch
* The proof starts by assuming the negation of the conclusion and then uses `REWRITE_TAC` to simplify the expression.
* It then applies `DISCH_THEN` with `MP_TAC` and `SPECL` to instantiate the variables with specific values.
* The proof proceeds by applying various tactics such as `REWRITE_TAC`, `CONJ_TAC`, and `SUBGOAL_THEN` to simplify the expression and derive contradictions.
* Key steps involve using `BETWEEN_IMP_COLLINEAR` to derive colinearity of points, and `COMPONENT_LE_NORM` to establish bounds on vector components.
* The proof also uses `REAL_ARITH` and `REAL_ABS_MUL` to perform arithmetic and absolute value calculations.
* The final steps involve using `EXISTS_TAC` to introduce witnesses for the existential quantifiers and `CONV_TAC REAL_RAT_REDUCE_CONV` to simplify the expression.

### Mathematical insight
This theorem is related to the concept of Euclid's axioms, specifically the axiom that states that through any two points, there is exactly one straight line. The theorem `NOT_TARSKI_AXIOM_10_NONEUCLIDEAN` shows that a certain statement, which is similar to this axiom, is not true in general. The proof involves a careful analysis of the geometric and algebraic properties of points and lines in a 2D space.

### Dependencies
* `pbetween`
* `FORALL_DEST_PLANE`
* `EXISTS_DEST_PLANE`
* `GSYM DEST_PLANE_EQ`
* `RIGHT_IMP_FORALL_THM`
* `IMP_IMP`
* `NOT_IMP`
* `CONJ_ASSOC`
* `BETWEEN_IMP_COLLINEAR`
* `COLLINEAR_3_2D`
* `BASIS_COMPONENT`
* `DIMINDEX_2`
* `ARITH`
* `VEC_COMPONENT`
* `VECTOR_MUL_COMPONENT`
* `REAL_SUB_LZERO`
* `REAL_MUL_LZERO`
* `REAL_MUL_RZERO`
* `REAL_SUB_RZERO`
* `REAL_ARITH`
* `REAL_ENTIRE`
* `COMPONENT_LE_NORM`
* `NORM_POW_2`
* `DOT_LADD`
* `DOT_RADD`
* `DOT_LMUL`
* `DOT_RMUL`
* `DOT_BASIS_BASIS`
* `BETWEEN_IN_SEGMENT`
* `IN_SEGMENT`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the use of `REWRITE_TAC` and `CONV_TAC REAL_RAT_REDUCE_CONV`, as these tactics may not have direct equivalents in other systems. Additionally, the use of `SUBGOAL_THEN` and `DISCH_THEN` may require careful handling of subgoals and hypotheses in the target system.

---

## TARSKI_AXIOM_11_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_11_NONEUCLIDEAN

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let TARSKI_AXIOM_11_NONEUCLIDEAN = prove
 (`!X Y. (?a. !x y. x IN X /\ y IN Y ==> pbetween x (a,y))
         ==> (?b. !x y. x IN X /\ y IN Y ==> pbetween b (x,y))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `X:plane->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `Y:plane->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[pbetween; EXISTS_DEST_PLANE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE dest_plane X`; `IMAGE dest_plane Y`]
        TARSKI_AXIOM_11_EUCLIDEAN) THEN REWRITE_TAC[IN_IMAGE] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; DEST_PLANE_NORM_LT; BETWEEN_NORM_LT])
```

### Informal statement
For all sets `X` and `Y` of points in a plane, if there exists a point `a` such that for all `x` in `X` and `y` in `Y`, `x` is between `a` and `y`, then there exists a point `b` such that for all `x` in `X` and `y` in `Y`, `b` is between `x` and `y`.

### Informal sketch
* The proof starts by considering the cases where either `X` or `Y` is an empty set, using `ASM_CASES_TAC` to handle these base cases.
* It then applies `REWRITE_TAC` with `NOT_IN_EMPTY` to simplify the assumptions when either set is empty.
* The `EXISTS_DEST_PLANE` and `pbetween` definitions are used to transform the betweenness relation.
* The `TARSKI_AXIOM_11_EUCLIDEAN` theorem is instantiated with specific arguments using `ISPECL` and then applied using `MP_TAC`.
* The proof involves manipulating the betweenness relation and applying various tactics like `ANTS_TAC`, `MATCH_MP_TAC`, and `ASM_MESON_TAC` to derive the conclusion.
* Key steps involve choosing points `a` and `b` and using properties like `MEMBER_NOT_EMPTY`, `DEST_PLANE_NORM_LT`, and `BETWEEN_NORM_LT` to establish the required betweenness relations.

### Mathematical insight
This axiom is part of Tarski's geometry axioms, specifically addressing the continuity aspect. It ensures that if there's a point `a` between all points of `X` and `Y`, then there's a point `b` such that `b` is between all points of `X` and `Y`, reflecting a fundamental property of geometric structures regarding betweenness and continuity.

### Dependencies
#### Theorems
* `TARSKI_AXIOM_11_EUCLIDEAN`
#### Definitions
* `pbetween`
* `EXISTS_DEST_PLANE`
* `NOT_IN_EMPTY`
#### Other
* `MEMBER_NOT_EMPTY`
* `DEST_PLANE_NORM_LT`
* `BETWEEN_NORM_LT`

### Porting notes
When translating this axiom into other proof assistants, special attention should be given to the handling of the betweenness relation `pbetween` and the use of `EXISTS_DEST_PLANE`. Additionally, the instantiation of `TARSKI_AXIOM_11_EUCLIDEAN` with specific sets may require careful handling of type classes or similar mechanisms in the target system. The proof's structure, relying on case analysis and manipulation of betweenness relations, should be generally portable, but the specific tactics and their application may vary between systems.

---

