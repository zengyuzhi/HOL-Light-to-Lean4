# independence.ml

## Overview

Number of statements: 46

The file `independence.ml` demonstrates the independence of the parallel postulate from Tarski's axioms for geometry. It imports `cauchy.ml` and `tarski.ml` and shows that the Klein model of the hyperbolic plane (`:plane`) satisfies all of Tarski's axioms except the Euclidean axiom (axiom 10), using redefined betweenness (`pbetween`) and congruence (`pdist`). This result, combined with the verification of Tarski's axioms for the Euclidean plane in `tarski.ml`, establishes the independence of the Euclidean axiom.


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
For any two vectors `x` and `y` in `real^N`, the distance `ddist(x, y)` is defined as follows: if the norms of both `x` and `y` are less than 1, then `ddist(x, y)` is `((1 - x · y)^2 / ((1 - ||x||^2) * (1 - ||y||^2))) - 1`; otherwise, `ddist(x, y)` is equal to `dist(x, y)`.

### Informal sketch
The definition of `ddist` introduces a new distance function applicable to vectors in `real^N`. It employs a conditional definition:

- **Case 1:** If both input vectors `x` and `y` lie within the open unit ball (i.e., their norms are strictly less than 1), `ddist` is given by a specific formula involving the dot product (`x dot y`) and norms of `x` and `y`. Namely, the formula is: `((1 - x · y)^2 / ((1 - ||x||^2) * (1 - ||y||^2))) - 1`.
- **Case 2:** If either `x` or `y` is outside (or on the boundary of) the unit ball, then `ddist` defaults to the standard Euclidean distance `dist(x, y)`.

This definition aims to define a reasonable distance within the unit ball and defaults to the standard Euclidean distance outside of it.

### Mathematical insight
The `ddist` definition introduces a modified distance function often used in the context of hyperbolic geometry or models related to hyperbolic space.  The purpose of defining `ddist` is motivated by the construction of the Klein model of the hyperbolic plane. The condition `norm(x) < &1 /\ norm(y) < &1` restricts the points to the interior of the unit ball. The formula within the unit ball is designed to capture the notion of distance in a hyperbolic space, while the default case ensures that the function is defined for all points in `real^N`, coinciding with standard Euclidean distance outside the unit ball, thus avoiding singularities and ensuring a well-behaved semimetric.

### Dependencies
- Multivariate/cauchy.ml
- Multivariate/tarski.ml
- `norm`
- `dist`


---

## DDIST_INCREASES_ONLINE

### Name of formal statement
DDIST_INCREASES_ONLINE

### Type of the formal statement
theorem

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
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT; REAL_SUB_LT]);;
```

### Informal statement
For all real vectors `a`, `b`, and `x` of dimension `N`, if the norms of `a`, `b`, and `x` are all less than 1, `x` lies between `a` and `b`, and `x` is not equal to `b`, then the distance `ddist(a, x)` is less than `ddist(a, b)`.

### Informal sketch
The proof proceeds as follows:
- Case split on whether `b` equals `a`. If they are equal, then the theorem holds because `x` must equal `a`, thus `ddist(a,x)` is 0 which must be less than `ddist(a,b)` which is also 0 but the assumption that `x` does not equal `b` implies `x` does not equal `a` which results in a contradiction.
- Assume `b` is not equal to `a`.
- Simplify `ddist` function and use `real_div` and `REAL_INV_MUL`.
- Provide the subgoal that `norm(a)^2 < 1`, `norm(b)^2 < 1`, and `norm(x)^2 < 1`, and then use `ABS_SQUARE_LT_1` and `REAL_ABS_NORM` to prove it.
- Rewrite an arithmetic expression using `REAL_ARITH` to convert multiplication by inverse into division.
- Simplify arithmetic expressions using `REAL_LT_DIV2_EQ`, `REAL_LT_LDIV_EQ` and `REAL_SUB_LT`.
- Rewrite `(a * inv b) * c` to `(a*c) / b`.
- Simplify arithmetic expressions using `REAL_LT_RDIV_EQ` and `REAL_SUB_LT`.
- Provide the subgoal that `a dot b < 1` and `a dot x < 1`. Use theorems like `NORM_CAUCHY_SCHWARZ` and `REAL_LET_TRANS` to prove it.
- Rewrite `BETWEEN_IN_SEGMENT` to express that `x` is in the segment between `a` and `b`.
- Rewrite using `IN_SEGMENT` to define the segment and then `LEFT_IMP_EXISTS_THM` to extract a real number `u` such that `x = (1 - u) * a + u * b`.
- Case split on whether `u` equals 1.
  - If `u = 1`, show the result of `(1 - 1) % a + 1 % b` which results in `b`.
  - If `u != 1`, simply using vector arithmetic show `(1 - u) % a + u % b = a + u % (b - a)`. The result is renamed such that `c = b - a`, meaning that `b = a + c`.
- Substitute `b` with `a + c`.
- Prove `b = a + c` by expanding `c` and using vector arithmetic.
- If `a + c = a` proves that `c = vec 0`.
- Rewrite using `NORM_POW_2` and `(a + b) dot (a + b) = a dot a + 2 * a dot b + b dot b`.
- Rewrite using `DOT_RADD`, `DOT_RMUL` and `DOT_LMUL`.
- Rewrite an arithmetic expression containing pow 2.
- Use REAL_LTE_ADD, REAL_LT_MUL, REAL_LE_MUL, REAL_LT_IMP_LE, REAL_LTE_ADD, REAL_LE_POW_2.
- Prove final result using DOT_POS_LT, REAL_SUB_LT.

### Mathematical insight
The theorem `DDIST_INCREASES_ONLINE` states that if `x` lies strictly between two vectors `a` and `b`, and all three vectors have a norm less than 1, then the distance from `a` to `x` is less than the distance from `a` to `b`, where the distance is calculated with the `ddist` function. This result suggests that as a point moves from `a` towards `b` within the unit ball, its distance from `a` (according to the `ddist` metric) increases. This is a fundamental property useful when analyzing online algorithms or incremental processes in geometry or optimization.

### Dependencies
- `ddist`
- `real_div`
- `REAL_INV_MUL`
- `ABS_SQUARE_LT_1`
- `REAL_ABS_NORM`
- `REAL_LT_DIV2_EQ`
- `REAL_LT_LDIV_EQ`
- `REAL_SUB_LT`
- `NORM_CAUCHY_SCHWARZ`
- `REAL_LET_TRANS`
- `BETWEEN_IN_SEGMENT`
- `IN_SEGMENT`
- `LEFT_IMP_EXISTS_THM`
- `VECTOR_ARITH`
- `NORM_POW_2`
- `DOT_RADD`
- `DOT_RMUL`
- `DOT_LMUL`
- `DOT_POS_LT`
- `REAL_SUB_LT`
- `BETWEEN_REFL_EQ`

### Porting notes (optional)
- The proof relies heavily on real arithmetic rewriting. Ensure the target proof assistant has similar capabilities to HOL Light's `REAL_ARITH` tactic.
- The `VECTOR_ARITH` tactic is used frequently for vector simplification. Equivalent vector arithmetic simplification rules should be established.
- The tactics `ASM_CASES_TAC`, `ASM_SIMP_TAC`, `SUBST_ALL_TAC`, `RULE_ASSUM_TAC` are frequently used. Ensure that the target environment have tactics or mechanisms that simulate those operations. For example `ASM_CASES_TAC` perform case splitting based on the assumptions.


---

## DDIST_REFL

### Name of formal statement
DDIST_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_REFL = prove
 (`!x:real^N. ddist(x,x) = &0`,
  GEN_TAC THEN REWRITE_TAC[ddist; DIST_REFL; NORM_POW_2; NORM_LT_SQUARE] THEN
  CONV_TAC REAL_FIELD);;
```
### Informal statement
For all `x` of type real vector, the distance (`ddist`) between `x` and itself is equal to 0.

### Informal sketch
The proof proceeds by:
- Applying rewriting with the definitions of `ddist` which involves the squared Euclidean distance, `DIST_REFL` (which states that the Euclidean distance between a point and itself is zero), `NORM_POW_2` (which expresses the norm squared as a sum of squares), and `NORM_LT_SQUARE` (which expands the norm squared using the Euclidean norm formula).
- Using real field arithmetic to simplify the resulting expression to 0.

### Mathematical insight
This theorem states a fundamental property of distance metrics: the distance from a point to itself is zero. It's a basic requirement for any function to be considered a distance metric, and it's used extensively in many mathematical contexts.

### Dependencies
- Definitions: `ddist`
- Theorems: `DIST_REFL`, `NORM_POW_2`, `NORM_LT_SQUARE`
- Tactics: `REAL_FIELD`


---

## DDIST_SYM

### Name of formal statement
DDIST_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_SYM = prove
 (`!x y:real^N. ddist(x,y) = ddist(y,x)`,
  REWRITE_TAC[ddist; CONJ_ACI; REAL_MUL_AC; DIST_SYM; DOT_SYM]);;
```
### Informal statement
For any vectors `x` and `y` in the N-dimensional real vector space, the distance `ddist(x, y)` is equal to the distance `ddist(y, x)`.

### Informal sketch
The proof proceeds by rewriting the definition of `ddist(x, y)` followed by simplification and the application of symmetry properties:
- First, rewrite `ddist` with its definition, which involves a square root of a dot product of a difference.
- Then, use the associativity, commutativity, and idempotence of conjunction (`CONJ_ACI`) to rearrange terms.
- Employ the commutativity and associativity of real multiplication (`REAL_MUL_AC`).
- Apply the symmetry of the distance function `DIST_SYM` and the dot product `DOT_SYM`.

### Mathematical insight
This theorem states that the distance between two points in a Euclidean space is symmetric; that is, the distance from point `x` to point `y` is the same as the distance from point `y` to point `x`. This is a fundamental property of distance metrics and is essential for many geometric and topological arguments.

### Dependencies
- Definitions: `ddist`
- Theorems: `DIST_SYM`, `DOT_SYM`
- Tactics: `CONJ_ACI`, `REAL_MUL_AC`


---

## DDIST_POS_LT

### Name of formal statement
DDIST_POS_LT

### Type of the formal statement
theorem

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
For all `x` and `y` in `real^N` (N-dimensional real vector space), if `x` is not equal to `y`, then 0 is less than `ddist(x, y)` (the distance between `x` and `y`).

### Informal sketch
The proof proceeds by:

- Assuming `~(x = y)`.
- Performing case analysis using `ASM_CASES_TAC` based on whether `norm(x)` and `norm(y)` are less than 1: `norm(x:real^N) < &1 /\ norm(y:real^N) < &1`.
  - Case 1: `norm(x) < 1` and `norm(y) < 1`. In this case, use `ASM_MESON_TAC` with the theorems `DDIST_INCREASES_ONLINE`, `DDIST_REFL`, and `BETWEEN_REFL` to prove the result.
  - Case 2: Otherwise, simplify using `ASM_SIMP_TAC` with the rewrite rules `ddist` and `DIST_POS_LT`.

### Mathematical insight
This theorem states that the distance between two distinct points in a real vector space is always strictly positive. It formalizes a fundamental property of distance metrics.

### Dependencies
- Definitions: `ddist`
- Theorems: `DIST_POS_LT`, `DDIST_INCREASES_ONLINE`, `DDIST_REFL`, `BETWEEN_REFL`


---

## DDIST_POS_LE

### Name of formal statement
DDIST_POS_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_POS_LE = prove
 (`!x y:real^N. &0 <= ddist(x,y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:real^N = y` THEN
  ASM_SIMP_TAC[DDIST_REFL; DDIST_POS_LT; REAL_LE_LT]);;
```

### Informal statement
For all `x` and `y` in the real vector space `real^N`, `0` is less than or equal to the distance between `x` and `y`.

### Informal sketch
The proof proceeds as follows:
- Start by universally generalizing over `x` and `y`.
- Perform case analysis on whether `x` is equal to `y`.
- If `x = y`, simplify using `DDIST_REFL` (the distance between a point and itself is 0) and the fact that `0 <= 0`.
- If `x != y`, simplify using `DDIST_POS_LT` (the distance between distinct points is strictly positive) and `REAL_LE_LT` (strict inequality implies non-strict inequality).

### Mathematical insight
This theorem states that the Euclidean distance between any two points in a real vector space is non-negative. This is a fundamental property of distance metrics and is essential for many geometric and analytic arguments.

### Dependencies
- Definitions: `ddist`
- Theorems: `DDIST_REFL`, `DDIST_POS_LT`, `REAL_LE_LT`


---

## DDIST_EQ_0

### Name of formal statement
DDIST_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_EQ_0 = prove
 (`!x y:real^N. ddist(x,y) = &0 <=> x = y`,
  MESON_TAC[DDIST_REFL; DDIST_POS_LT; REAL_LT_REFL]);;
```
### Informal statement
For all real vectors `x` and `y` in `real^N`, the distance between `x` and `y` is equal to 0 if and only if `x` is equal to `y`.

### Informal sketch
The proof can be outlined as follows:
- The theorem is an equivalence, so we must prove both directions.
- The reverse direction `x = y ==> ddist(x,y) = &0` follows from the reflexivity of the distance function `DDIST_REFL`. Specifically, if `x = y` then `ddist(x,x) = &0` by `DDIST_REFL`, and therefore `ddist(x,y) = &0` by substitution of equals for equals.
- The forward direction `ddist(x,y) = &0 ==> x = y` is shown using the positivity of the distance function `DDIST_POS_LT`. If `ddist(x, y) = &0` and `x` is not equal to `y`, then `ddist(x,y) > &0` by  `DDIST_POS_LT`. This contradicts `ddist(x,y) = &0`. Thus, we must have `x = y`. This direction also uses `REAL_LT_REFL` to show that assuming `ddist(x, y) > &0 ` contradicts `ddist(x,y) = &0`.
- The tactic `MESON_TAC` is used, which combines these steps with automated reasoning.

### Mathematical insight
This theorem formalizes the intuitive notion that the distance between two points is zero if and only if the points are the same. It is a fundamental property of distance metrics.

### Dependencies
- `DDIST_REFL`
- `DDIST_POS_LT`
- `REAL_LT_REFL`


---

## BETWEEN_COLLINEAR_DDIST_EQ

### Name of formal statement
BETWEEN_COLLINEAR_DDIST_EQ

### Type of the formal statement
theorem

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
                REAL_LE_REFL; BETWEEN_SYM; REAL_NOT_LE; BETWEEN_REFL]);;
```
### Informal statement
For all vectors `a`, `b`, and `x` in `real^N`, if the norms of `a`, `b`, and `x` are all less than 1, then `x` is between `a` and `b` if and only if `a`, `x`, and `b` are collinear, the distance from `x` to `a` is less than or equal to the distance from `a` to `b`, and the distance from `x` to `b` is less than or equal to the distance from `a` to `b`.

### Informal sketch
The proof proceeds by showing the equivalence between `between x (a,b)` and `collinear {a, x, b} /\ ddist(x,a) <= ddist (a,b) /\ ddist(x,b) <= ddist(a,b)` under the assumption that the norms of `a`, `b`, and `x` are all less than 1.

- First, the implication `between x (a,b) ==> collinear {a, x, b}` is handled using `BETWEEN_IMP_COLLINEAR`.
- Then, rewrite the goal using `COLLINEAR_BETWEEN_CASES` to consider different cases implied `collinear {a, x, b}`.
- Finally, use `ASM_MESON_TAC` with a collection of theorems including `DDIST_INCREASES_ONLINE`, `DDIST_SYM`, `REAL_LT_IMP_LE`, `REAL_LE_REFL`, `BETWEEN_SYM`, `REAL_NOT_LE`, and `BETWEEN_REFL` for automated reasoning to complete the proof.

### Mathematical insight
This theorem characterizes the `between` relation for points in `real^N` in terms of collinearity and distance comparisons. The constraints on the norms of `a`, `b`, and `x` (being less than 1) don't appear to be fundamentally geometrically necessary but could be needed for technical reasons in the context where this theorem is used. The essence of the theorem captures the intuitive notion of "betweenness" on a line segment.

### Dependencies
- `BETWEEN_IMP_COLLINEAR`
- `COLLINEAR_BETWEEN_CASES`
- `DDIST_INCREASES_ONLINE`
- `DDIST_SYM`
- `REAL_LT_IMP_LE`
- `REAL_LE_REFL`
- `BETWEEN_SYM`
- `REAL_NOT_LE`
- `BETWEEN_REFL`


---

## CONTINUOUS_AT_LIFT_DDIST

### Name of formal statement
CONTINUOUS_AT_LIFT_DDIST

### Type of the formal statement
theorem

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
             CONTINUOUS_SUB; CONTINUOUS_LIFT_DOT2]]);;
```

### Informal statement
For all `a` and `x` in real `N`-dimensional space, if the norm of `a` is less than 1 and the norm of `x` is less than 1, then the function that maps `x` to the lift of `ddist(a, x)` is continuous at `x`.

### Informal sketch
The proof demonstrates that the function `\x. lift(ddist(a,x))` is continuous at `x` under the given conditions. The proof proceeds as follows:

- Start by stripping the quantifiers and assumptions.
- Apply `CONTINUOUS_TRANSFORM_AT` to transform the goal to finding a function `delta` such that for any y `dist(y,x) < delta ==> dist(lift(ddist(a,y)), lift(ddist(a,x))) < eps`. The `delta` is instantiated as `\x:real^N. lift((&1 - a dot x) pow 2 / ((&1 - norm a pow 2) * (&1 - norm x pow 2)) - &1)`.
- Decompose the distance between two lifted terms into a difference involving the underlying real values. This will require bounding `dist(ddist(a,y), ddist(a,x))` with an appropriate `delta`.
- Show that a suitable delta can be chosen as `&1 - norm(x:real^N)`.
- Prove the antecedent `dist(y,x) < delta ==> norm y < &1` using `NORM_ARITH` and the assumption `norm x < &1`. Then simplify using the definition of `ddist`.
- Rewrite using properties of `LIFT_SUB`, `real_div`, `LIFT_CMUL`, `REAL_INV_MUL`.
- Apply `CONTINUOUS_SUB` and `CONTINUOUS_CONST`.
- Apply `CONTINUOUS_MUL` twice.
- Simplify using definitions of `CONTINUOUS_CONST`,`o_DEF`, `REAL_POW_2`, and `LIFT_CMUL`.
- Apply `CONTINUOUS_MUL` composed with `o_DEF` and `CONTINUOUS_AT_INV`.
- Simplify using assumptions like `x < &1 * &1 ==> ~(&1 - x = &0)`, `REAL_LT_MUL2`, `NORM_POS_LE`, and `LIFT_SUB`.
- Simplify using properties of `REAL_POW_2`, `NORM_POW_2`, `CONTINUOUS_CONST`, `CONTINUOUS_AT_ID`, `CONTINUOUS_SUB`, and `CONTINUOUS_LIFT_DOT2`.

### Mathematical insight
This theorem establishes the continuity of the lifted `ddist` function, which is crucial when working with distances in spaces where one needs to reason about the distances being less than 1 and subsequently lifted to potentially more complex structures.

### Dependencies
- `CONTINUOUS_TRANSFORM_AT`
- `REAL_SUB_LT`
- `NORM_ARITH`
- `ddist`
- `LIFT_SUB`
- `real_div`
- `LIFT_CMUL`
- `REAL_INV_MUL`
- `CONTINUOUS_SUB`
- `CONTINUOUS_CONST`
- `CONTINUOUS_MUL`
- `o_DEF`
- `REAL_POW_2`
- `CONTINUOUS_AT_INV`
- `REAL_ARITH`
- `REAL_LT_MUL2`
- `NORM_POS_LE`
- `LIFT_SUB`
- `GSYM REAL_POW_2`
- `NORM_POW_2`
- `CONTINUOUS_AT_ID`
- `CONTINUOUS_LIFT_DOT2`

### Porting notes (optional)
- Ensure that the target proof assistant has comparable theorems for `CONTINUOUS_TRANSFORM_AT`, as this seems to be a key step to begin this proof.
- The manipulation of real numbers and inequalities (`REAL_ARITH`, etc.) should be straightforward to reproduce in most systems.
- Pay careful attention to the definitions of `ddist` and `lift` in HOL Light, as these will be crucial for replicating the theorem.


---

## HYPERBOLIC_MIDPOINT

### Name of formal statement
HYPERBOLIC_MIDPOINT

### Type of the formal statement
theorem

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
    ASM_MESON_TAC[REAL_SUB_0; DDIST_SYM]]);;
```

### Informal statement
For all `a` and `b` in `real^N`, if the norm of `a` is less than 1 and the norm of `b` is less than 1, then there exists an `x` such that `x` is between `a` and `b`, and the hyperbolic distance (`ddist`) from `x` to `a` is equal to the hyperbolic distance from `x` to `b`.

### Informal sketch
The proof demonstrates the existence of a hyperbolic midpoint between two points `a` and `b` within the unit disk. It leverages the intermediate value theorem by considering the continuous function `f(x) = ddist(x, a) - ddist(x, b)` over the segment connecting `a` and `b`.

- Apply the intermediate value theorem to `lift(ddist(x,a) - ddist(x,b))` over the `segment[a,b]`. The lifting operation is used to map a real number into HOL Light's term algebra. The theorem `CONNECTED_CONTINUOUS_IMAGE` guarantees the image of a segment under a continuous function is a connected set.
- Establish the continuity of the function `ddist(x, a) - ddist(x, b)` on the segment and show that the segment `segment[a, b]` is connected.
- Show that the function `lift(ddist(x, a) - ddist(x, b))` takes both non-negative and non-positive values on the segment `segment[a, b]`. This relies on evaluating the function at the endpoints `a` and `b` utilizing theorems such as `DDIST_REFL` and `DDIST_SYM`. Also, utilize facts such as `ENDS_IN_SEGMENT` to show that the endpoints `a` and `b` are indeed in the segment `segment[a, b]`.
- By the intermediate value theorem, there must be a point `x` on the segment where `ddist(x, a) - ddist(x, b) = 0`, which implies `ddist(x, a) = ddist(x, b)`. Thus, `x` is the hyperbolic midpoint.

### Mathematical insight
This theorem proves the existence of a midpoint in the hyperbolic sense between any two points within the unit disk model of hyperbolic space. This concept is vital in hyperbolic geometry, mirroring the Euclidean notion of a midpoint, but adapted to the non-Euclidean metric. The uniqueness of this midpoint is not addressed here, only its existence.

### Dependencies
**Theorems/Definitions:**
- `ddist` (hyperbolic distance)
- `between` (betweenness relation in Euclidean space)
- `norm` (Euclidean norm)
- `segment`
- `CONNECTED_CONTINUOUS_IMAGE`
- `CONNECTED_SEGMENT`
- `CONTINUOUS_AT_IMP_CONTINUOUS_ON`
- `CONTINUOUS_SUB`
- `DDIST_SYM`
- `CONTINUOUS_AT_LIFT_DDIST`
- `BETWEEN_NORM_LT`
- `BETWEEN_IN_SEGMENT`
- `IS_INTERVAL_CONNECTED_1`
- `IS_INTERVAL_1`
- `IMP_CONJ`
- `RIGHT_FORALL_IMP_THM`
- `FORALL_IN_IMAGE`
- `IMP_IMP`
- `RIGHT_IMP_FORALL_THM`
- `LIFT_DROP`
- `DDIST_REFL`
- `ENDS_IN_SEGMENT`
- `IN_IMAGE`
- `REAL_SUB_RZERO`
- `DDIST_POS_LE`
- `LIFT_EQ`
- `REAL_SUB_0`
- `LIFT_SUB`
- `lift`

### Porting notes (optional)
- The reliance on the intermediate value theorem (`CONNECTED_CONTINUOUS_IMAGE`) may necessitate a similar theorem in the target proof assistant about continuous functions on connected sets, or a manual reconstruction of the argument.
- The definition of `segment` and `between` will need to be provided in the new system, typically as a convex hull or parameterization.
- The hyperbolic distance function `ddist` must be correctly formalized.
- Automation using `ASM_MESON_TAC` and similar tactics may need to be replaced with more manual reasoning, depending on the automation capabilities of the target prover.


---

## DDIST_EQ_ORIGIN

### Name of formal statement
DDIST_EQ_ORIGIN

### Type of the formal statement
theorem

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
              GSYM REAL_EQ_SQUARE_ABS; REAL_ABS_NORM]);;
```
### Informal statement
For all real vectors `x` and `y` in `real^N`, if the norm of `x` is less than 1 and the norm of `y` is less than 1, then the distance between the zero vector and `x` is equal to the distance between the zero vector and `y` if and only if the norm of `x` equals the norm of `y`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and implications using `REPEAT STRIP_TAC` and simplifying the resulting assumptions using `ASM_SIMP_TAC` along with the definitions of `ddist`, `NORM_0`, and the theorem `REAL_LT_01`.
- Rewriting using `DOT_LZERO` to simplify dot products with the zero vector.
- Reducing the real expression using `REAL_RAT_REDUCE_CONV` to cancel common terms.
- Rewriting using `real_div` and `REAL_MUL_LID`.
- Rewriting relational expressions to isolate `norm x` and `norm y` using `REAL_EQ_INV2` and arithmetic facts.
- Rewriting to remove intermediate expressions and use equivalences of the form `a - x = a - y <=> x = y`, also using `GSYM REAL_EQ_SQUARE_ABS` to rewrite equalities between norms and absolute values. Then `REAL_ABS_NORM` is applied.
- The goal is then discharged by arithmetic simplification.

### Mathematical insight
This theorem states that, within the open unit ball, the distance from the origin to a point is uniquely determined by the norm of that point, and vice-versa. This is a property of Euclidean space, and relies heavily on the properties of norms and the definition of distance.

### Dependencies
- `ddist`
- `NORM_0`
- `REAL_LT_01`
- `DOT_LZERO`
- `real_div`
- `REAL_MUL_LID`
- `REAL_EQ_INV2`
- `REAL_ARITH` (multiple uses)
- `GSYM REAL_EQ_SQUARE_ABS`
- `REAL_ABS_NORM`


---

## DDIST_CONGRUENT_TRIPLES_0

### Name of formal statement
DDIST_CONGRUENT_TRIPLES_0

### Type of the formal statement
theorem

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
  RULE_ASSUM_TAC(REWRITE_RULE[NORM_EQ]) THEN ASM_REAL_ARITH_TAC);;
```
### Informal statement
For all real vectors `a`, `b`, `a'`, and `b'` in `real^N`, if the norms of `a`, `b`, `a'`, and `b'` are all strictly less than 1, then the following holds: The `ddist` distances (stereographic projection based distance) from the origin (`vec 0`) to `a` equals the `ddist` distance from the origin to `a'`, AND the `ddist` distance from `a` to `b` equals the `ddist` distance from `a'` to `b'`, AND the `ddist` distance from `b` to the origin equals the `ddist` distance from `b'` to the origin, if and only if the Euclidean `dist` distance from the origin to `a` equals the Euclidean distance from the origin to `a'`, AND the Euclidean distance from `a` to `b` equals the Euclidean distance from `a'` to `b'`, AND the Euclidean distance from `b` to the origin equals the Euclidean distance from `b'` to the origin.

### Informal sketch
The proof proceeds as follows:
- First, simplify using `DDIST_EQ_ORIGIN` and `DDIST_SYM` to reduce the `ddist` expressions involving the origin to simpler forms with norms.
- Simplify further by rewriting Euclidean `dist` in terms of norms, which introduces square roots.
- Use a tautology to rearrange the logical structure of the biconditional to make it easier to work with. Essentially, the tactic `MATCH_MP_TAC(TAUT \`(a /\ b ==> (x <=> y)) ==> (a /\ x /\ b <=> a /\ y /\ b)\`)` is applying a tautology to transform the biconditional within the assumptions.
- Simplify further by rewriting `dist` in terms of norms and vector operations (dot products).
- Rewrite again using `REAL_EQ_SQUARE_ABS` and `NORM_POW_2`.
- Simplify using assumptions and theorems about absolute values, norms, and inequalities, and assumptions about the norms to handle the real arithmetic.
- Apply Cauchy-Schwarz inequality and related theorems to demonstrate that all terms involved in the expressions are well-behaved (specifically, division by zero does not take place.)
- Finally, simplify with real arithmetic to prove the goal.

### Mathematical insight
This theorem establishes the equivalence between equality of `ddist` distances and equality of Euclidean `dist` distances for a set of three points (the origin, `a`, and `b`) when the points are within the unit ball. This equivalence is crucial when working with the stereographic projection based distance, as it allows reasoning about `ddist` in terms of the more familiar Euclidean distance within the unit ball. It shows that congruence of triangles (in the sense of equal side lengths) is preserved under the transformation between Euclidean and `ddist` metrics in this restricted domain.

### Dependencies
- `DDIST_EQ_ORIGIN`
- `DDIST_SYM`
- `DIST_0`
- `NORM_0`
- `REAL_LT_01`
- `ddist`
- `DIST_EQ`
- `real_div`
- `REAL_INV_MUL`
- `REAL_RING`
- `dist`
- `NORM_POW_2`
- `DOT_LSUB`
- `DOT_RSUB`
- `DOT_SYM`
- `REAL_EQ_SQUARE_ABS`
- `REAL_INV_EQ_0`
- `real_abs`
- `REAL_SUB_LE`
- `REAL_SUB_0`
- `ABS_SQUARE_LT_1`
- `REAL_ABS_NORM`
- `REAL_LT_IMP_NE`
- `REAL_LT_IMP_LE`
- `NORM_CAUCHY_SCHWARZ`
- `REAL_LET_TRANS`
- `NORM_POS_LE`
- `REAL_LT_MUL2`
- `REAL_MUL_RID`
- `NORM_EQ`


---

## kleinify

### Name of formal statement
- kleinify

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let kleinify = new_definition
 `kleinify z = Cx(&2 / (&1 + norm(z) pow 2)) * z`;;
```
### Informal statement
- Define a function `kleinify` that takes a complex number `z` as input and returns the complex number obtained by multiplying `z` by `Cx(&2 / (&1 + norm(z) pow 2))`, where `Cx` constructs a complex number from a real number, `norm(z)` is the Euclidean norm (magnitude) of the complex number `z`, and `pow` denotes exponentiation.

### Informal sketch
- The definition directly provides a formula for `kleinify z`. There is no proof, instead there is only a definition.
- The formula involves computing the norm of `z`, squaring it, adding 1, dividing 2 by the result, and finally multiplying the original complex number by the result.
- This corresponds to the orthogonal projection onto a hemisphere touching the unit disc, then stereographic projection back from the other pole of the sphere plus scaling.

### Mathematical insight
- The `kleinify` function maps a complex number `z` to its corresponding point in the Klein disk model (also known as the Beltrami-Klein model) of hyperbolic geometry, representing the hyperbolic plane. The Klein disk model is realized as the interior of the unit disk in the complex plane. Complex numbers are interpreted as points in the Euclidean plane. This model is different from the Poincare disk model.
- This function is used to deduce the existence of hyperbolic translations via the Poincare disc model.

### Dependencies
- `Cx`
- `norm`
- `pow`


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
The function `poincarify` is defined such that for any vector `x`, `poincarify x` is equal to the complex number constructor `Cx` applied to the real number `(&1 - sqrt(&1 - norm(x) pow 2)) / norm(x) pow 2` multiplied by the vector `x`.

### Informal sketch
The definition introduces a function `poincarify` that maps a vector `x` to another vector. The mapping involves calculating a scalar value, which is then multiplied by the original vector `x`. Specifically, the scalar value is derived from the norm of `x` using the formula `(&1 - sqrt(&1 - norm(x) pow 2)) / norm(x) pow 2`.  The result is then converted to a complex number using the constructor `Cx`, and finally multiplied by the original vector `x`.

### Mathematical insight
The function `poincarify` likely maps a vector to its image under the Poincaré disk model. The formula `(&1 - sqrt(&1 - norm(x) pow 2)) / norm(x) pow 2` computes a scaling factor based on the norm of the input vector `x`.

### Dependencies
None

### Porting notes (optional)
- The `Cx` constructor may have different syntax in other proof assistants. Ensure to check the definitions of complex numbers for the specific proof assistant.
- Handling of real numbers and the square root function may require adjustments depending on the target system's libraries.
- The definition relies on `norm(x)` being non-zero. Some proof assistants may require explicit handling of the case where `norm(x) = 0`.


---

## KLEINIFY_0,POINCARIFY_0

### Name of formal statement
KLEINIFY_0,POINCARIFY_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let KLEINIFY_0,POINCARIFY_0 = (CONJ_PAIR o prove)
 (`kleinify (Cx(&0)) = Cx(&0) /\ poincarify (Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[kleinify; poincarify; COMPLEX_MUL_RZERO]);;
```
### Informal statement
The theorem states that `kleinify` of the complex number 0 is equal to the complex number 0, and `poincarify` of the complex number 0 is equal to the complex number 0.  In formal notation: kleinify(0 + 0i) = 0 + 0i ∧ poincarify(0 + 0i) = 0 + 0i.

### Informal sketch
The theorem is proved by rewriting the goal using the definitions of `kleinify` and `poincarify`, and the theorem `COMPLEX_MUL_RZERO`.
Essentially, we evaluate `kleinify (Cx(&0))` which simplifies to `Cx(&0)` using its definition because the absolute value of zero is zero. Similarly, `poincarify (Cx(&0))` simplifies to `Cx(&0)` using its definition since the absolute value of zero is zero and COMPLEX_MUL_RZERO is used in the simplification.

### Mathematical insight
The theorem confirms that both the `kleinify` transformation and the `poincarify` transformation preserve the complex number 0. These transformations are likely related to mapping complex numbers to points within a specific geometric space (e.g., the Klein model or Poincaré disk model of hyperbolic geometry), and ensuring that the origin is fixed is a natural property.

### Dependencies
- Definitions: `kleinify`, `poincarify`
- Theorems: `COMPLEX_MUL_RZERO`


---

## NORM_KLEINIFY

### Name of formal statement
NORM_KLEINIFY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_KLEINIFY = prove
 (`!z. norm(kleinify z) = (&2 * norm(z)) / (&1 + norm(z) pow 2)`,
  REWRITE_TAC[kleinify; COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_DIV] THEN
  SIMP_TAC[REAL_LE_POW_2; REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For all complex numbers `z`, the norm of `kleinify z` is equal to `(2 * norm(z)) / (1 + norm(z)^2)`.

### Informal sketch
The proof proceeds as follows:
- Expand the definition of `kleinify z` as `(2 * z) / (1 + norm(z)^2)`.
- Apply rewrite rules related to complex number norms:
  - The norm of a product is the product of the norms (`COMPLEX_NORM_MUL`).
  - The norm of a complex constant `c` times `z` is `abs(c)` times `norm(z)` (`COMPLEX_NORM_CX`).
  - The norm of a division is `abs(x/y) = abs(x) / abs(y)` (`REAL_ABS_DIV`).
- Simplify the resulting expression using `REAL_LE_POW_2` and the fact that if `0 <= x` then `abs(1 + x) = 1 + x`.
- Use real arithmetic to complete the proof.

### Mathematical insight
The theorem relates the norm of the complex number resulting from the `kleinify` function to the norm of the original complex number. It encapsulates the transformation's effect on the magnitude of the complex number `z`.

### Dependencies
- Definitions: `kleinify`
- Theorems: `COMPLEX_NORM_MUL`, `COMPLEX_NORM_CX`, `REAL_ABS_DIV`, `REAL_LE_POW_2`
- Real Arith: `REAL_ARITH` `&0 <= x ==> abs(&1 + x) = &1 + x`


---

## NORM_KLEINIFY_LT

### Name of formal statement
NORM_KLEINIFY_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_KLEINIFY_LT = prove
 (`!z. norm(kleinify z) < &1 <=> ~(norm z = &1)`,
  ASM_SIMP_TAC[NORM_KLEINIFY; REAL_LE_POW_2; REAL_LT_LDIV_EQ; REAL_MUL_LID;
                REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
  SIMP_TAC[REAL_ARITH `&2 * z < (&1 + z pow 2) <=> &0 < (z - &1) pow 2`] THEN
  REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers `z`, the norm of `kleinify z` is less than 1 if and only if it is not the case that the norm of `z` equals 1.

### Informal sketch
The proof proceeds as follows:
- First, simplify using the definition of `NORM_KLEINIFY`, along with lemmas about real numbers, including `REAL_LE_POW_2`, `REAL_LT_LDIV_EQ`, `REAL_MUL_LID`, and `REAL_ARITH` (specifically, that if `0 <= x` then `0 < 1 + x`).
- Next, further simplify using `REAL_ARITH` to rewrite `2 * z < (1 + z pow 2)` as `0 < (z - 1) pow 2`.
- Then, rewrite using definitions of `REAL_POW_2` and `REAL_LT_SQUARE`.
- Finally, complete the proof using `REAL_ARITH_TAC`, which uses real arithmetic reasoning to discharge the remaining goal.

### Mathematical insight
This theorem expresses a property of the `kleinify` function, which maps real numbers to the open unit interval. The theorem states that `kleinify` produces a value with norm strictly less than 1 precisely when the input value did not have norm exactly equal to 1. In other words, `kleinify` maps real numbers with norm 1 to values with norm less than 1, and all other real numbers have the property preserved by `kleinify`.

### Dependencies
- Definitions: `NORM_KLEINIFY`
- Theorems: `REAL_LE_POW_2`, `REAL_LT_LDIV_EQ`, `REAL_MUL_LID`, `REAL_POW_2`, `REAL_LT_SQUARE`
- Tactic: `REAL_ARITH`


---

## NORM_POINCARIFY_LT

### Name of formal statement
NORM_POINCARIFY_LT

### Type of the formal statement
theorem

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
   REAL_SUB_LE; ABS_SQUARE_LE_1; REAL_LT_IMP_LE; REAL_ABS_NORM; NORM_POS_LE]);;
```
### Informal statement
For all `x` in `real^2`, if the norm of `x` is less than 1, then the norm of `poincarify x` is less than 1.

### Informal sketch
The proof establishes that if the norm of a real vector `x` is less than 1, then the norm of `poincarify x` is also less than 1.

- The proof starts by stripping the quantifier and using rewriting rules to simplify the expression `norm(poincarify x)`.
- It then uses the fact that if `x * y <= 1 * y` and `y < 1` then `x * y < 1`.
- It uses the properties of norms involving multiplication and complex conjugate. It also simplifies intermediate expressions using properties of absolute values and powers.
- The proof proceeds by considering the case where `x` is the zero vector and the case where it is not, using `ASM_CASES_TAC`. In the zero vector case, the result follows easily.
- In the non-zero vector case, arithmetic and simplification reduce the goal to showing that `abs(1 - norm(x)) <= 1 - sqrt(1 - norm(x)^2)`.
- This is shown by proving `1 - norm(x) <= 1 - sqrt(1 - norm(x)^2)` and `norm(x) <= 1`, then applying `REAL_ARITH`. The square roots are handled using `REAL_LE_LSQRT` and `REAL_LE_RSQRT`.
- Inequalities are simplified using facts such as `(&1 - x) pow 2 <= &1 - x <=> &0 <= x * (&1 - x)`, `&1 - x <= &1 <=> &0 <= x`, `REAL_LE_MUL`, `REAL_POW_LE`, `REAL_SUB_LE`, `ABS_SQUARE_LE_1`, `REAL_LT_IMP_LE`, `REAL_ABS_NORM`, `NORM_POS_LE`.

### Mathematical insight
This theorem proves a key property of the `poincarify` function, which maps a vector inside the unit disk to another vector inside the unit disk. This is the fact that the Poincare disc model `poincarify` function preserves the property of having a norm less than 1. The theorem is important for verifying that `poincarify` maps points as expected.

### Dependencies
- `poincarify`
- `COMPLEX_NORM_MUL`
- `NORM_POS_LE`
- `COMPLEX_NORM_CX`
- `REAL_ABS_DIV`
- `REAL_ABS_NORM`
- `REAL_ABS_POW`
- `REAL_LE_LDIV_EQ`
- `NORM_POS_LT`
- `REAL_POW_LT`
- `NORM_0`
- `REAL_LE_LSQRT`
- `REAL_LE_RSQRT`
- `REAL_SUB_LE`
- `REAL_POS`
- `REAL_MUL_LID`
- `REAL_POW_ONE`
- `REAL_LE_MUL`
- `REAL_POW_LE`
- `REAL_SUB_LE`
- `ABS_SQUARE_LE_1`
- `REAL_LT_IMP_LE`


---

## KLEINIFY_POINCARIFY

### Name of formal statement
KLEINIFY_POINCARIFY

### Type of the formal statement
theorem

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
  ASM_SIMP_TAC[REAL_SUB_LE; ABS_SQUARE_LE_1; REAL_ABS_NORM; REAL_LT_IMP_LE]);;
```
### Informal statement
For all `x` in `real^2`, if the norm of `x` is less than 1, then `kleinify(poincarify x)` is equal to `x`.

### Informal sketch
The proof demonstrates that applying the `poincarify` transformation followed by the `kleinify` transformation to a vector `x` in the plane, where the norm of `x` is less than 1, results in the original vector `x`. The tactic script proceeds as follows:
- Start by stripping the goal.
- Rewrite using the definitions of `kleinify` and `poincarify`. The definitions are:
  - `kleinify(x:real^2) = Cx(&2) * x / (Cx(&1) + norm x pow 2)`
  - `poincarify(x:real^2) = x / (sqrt(&1 - norm(x:real^2) pow 2))`
- Apply a ring tactic `(~(x = Cx(&0)) ==> w * z = Cx(&1)) ==> w * z * x = x`.
- Discharge the assumption.
- Simplify by rewriting using `GSYM CX_MUL`, `CX_INJ`, and `COMPLEX_NORM_MUL`.
- Simplify further by rewriting using `COMPLEX_NORM_CX`, `REAL_ABS_DIV`, `REAL_ABS_NORM`, and `REAL_ABS_POW`.
- Apply an asm simp tactic using `COMPLEX_NORM_ZERO` and the field law `~(y = &0) ==> (&1 + (a / y pow 2 * y) pow 2) = (y pow 2 + a pow 2) / y pow 2`.
- Rewrite using `REAL_POW2_ABS`, `real_div`, `REAL_INV_MUL`, and `REAL_INV_INV`.
- Apply an asm simp tactic using `COMPLEX_NORM_ZERO` and the field law `~(y = &0) ==> (&2 * x * y pow 2) * z * inv(y pow 2) = &2 * x * z`.
- Apply the field law `&0 < y /\ &2 * y = x ==> &2 * inv(x) * y = &1`.
- Perform conjunctive splitting.
  - Branch 1: Show that `&1 - norm(x:real^2) pow 2` is positive by rewriting using `REAL_SUB_LT`, applying `REAL_LT_LSQRT`, rewriting using `REAL_POS` and `REAL_ARITH` to show `&1 - x < &1 pow 2 <=> &0 < x`, and simplifying using `REAL_POW_LT` and `COMPLEX_NORM_NZ`.
  - Branch 2: Prove `sqrt(&1 - norm(x:real^2) pow 2) pow 2 = &1 - norm x pow 2` by applying `SQRT_POW_2` and a conversion using real field simplification.
- Simplify using `REAL_SUB_LE`, `ABS_SQUARE_LE_1`, `REAL_ABS_NORM`, and `REAL_LT_IMP_LE`.

### Mathematical insight
This theorem demonstrates that the `kleinify` and `poincarify` transformations are inverses of each other when restricted to the open unit disk in the Euclidean plane. The `poincarify` function maps a point in the unit disk to a point in the plane and the `kleinify` function performs (what effectively turns out to be) the inverse mapping.

### Dependencies
- `kleinify`
- `poincarify`
- `COMPLEX_RING`
- `GSYM CX_MUL`
- `CX_INJ`
- `COMPLEX_NORM_MUL`
- `COMPLEX_NORM_CX`
- `REAL_ABS_DIV`
- `REAL_ABS_NORM`
- `REAL_ABS_POW`
- `COMPLEX_NORM_ZERO`
- `REAL_FIELD`
- `REAL_POW2_ABS`
- `real_div`
- `REAL_INV_MUL`
- `REAL_INV_INV`
- `REAL_SUB_LT`
- `REAL_LT_LSQRT`
- `REAL_POS`
- `REAL_ARITH`
- `REAL_POW_LT`
- `COMPLEX_NORM_NZ`
- `SQRT_POW_2`
- `REAL_SUB_LE`
- `ABS_SQUARE_LE_1`
- `REAL_LT_IMP_LE`


---

## POINCARIFY_KLEINIFY

### Name of formal statement
POINCARIFY_KLEINIFY

### Type of the formal statement
theorem

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
  ASM_REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM; ABS_SQUARE_LT_1]);;
```
### Informal statement
For all complex numbers `x`, if the norm of `x` is less than 1, then `poincarify(kleinify x)` equals `x`.

### Informal sketch
The proof demonstrates that applying the `kleinify` and `poincarify` transformations in sequence to a complex number `x` with norm less than 1 results in `x` itself. This establishes that `poincarify` is a left inverse of `kleinify` on the open unit disk in the complex plane.
- The proof starts by rewriting with the definitions of `kleinify` and `poincarify`.
- It uses a property of complex rings `(~(x = Cx(&0)) ==> w * z = Cx(&1)) ==> w * z * x = x`, discharged, and injectivity of complex numbers based on their real components (`CX_INJ`).
- The proof involves several rewrites based on properties of complex number norms (`COMPLEX_NORM_MUL`, `COMPLEX_NORM_CX`), and real number absolute values (`REAL_ABS_DIV`, `REAL_ABS_NORM`, `REAL_ABS_POW`, `REAL_ABS_NUM`).
- Algebraic simplification using real field properties is done including dealing with inverses (`REAL_INV_MUL`, `REAL_INV_INV`), associativity of multiplication (`REAL_MUL_ASSOC`), and powers (`REAL_INV_POW`, `REAL_POW_MUL`). These rewrites manipulate the equation to a solvable form.
- It also uses the property, `~(c = &0) /\ abs d < &1 /\ a * b = &2 * c pow 2 * (&1 + d) ==> a * inv(&2) pow 2 * b * inv(c) pow 2 * &2 * inv(&1 + d) = &1`.
- The proof further rewrites using properties of absolute values, complex norms, and inequalities (`REAL_ABS_POW`, `COMPLEX_NORM_ZERO`, `ABS_SQUARE_LT_1`).
- The proof proceeds by simplifying inequalities involving norms, absolute values, and powers using facts like `&0 <= x ==> abs(&1 + x) = &1 + x`.
- Additional algebraic manipulations involve factoring and simplifying.
- The proof establishes unique square roots (`SQRT_UNIQUE`), algebraic properties, and inequalities to complete the demonstration, ensuring `&1 + norm(x) pow 2` is not equal to zero
- The tactic `REAL_FIELD` is used for real field arithmetic at several stages to handle equation solving, particularly to isolate variables and simplify expressions.

### Mathematical insight
The theorem demonstrates a fundamental relationship between two transformations (functions) in complex analysis. In particular, it states that `poincarify` is a left inverse to `kleinify` when acting on the open unit disk. This is important in contexts where one wants to relate between the open unit disk, and say the complex plane. This implies that given any point `x` within the unit disk, transforming it using `kleinify` and then transforming the result using `poincarify` brings you back to the original point `x`. This is significant across various fields that depend on conformal mappings, such as geometry, physics, and visualization.

### Dependencies
- Definitions: `kleinify`, `poincarify`
- Theorems: `COMPLEX_RING`, `GSYM CX_MUL`, `CX_INJ`, `COMPLEX_NORM_MUL`, `COMPLEX_NORM_CX`, `REAL_ABS_DIV`, `REAL_ABS_NORM`, `REAL_ABS_POW`, `REAL_ABS_NUM`, `real_div`, `REAL_INV_MUL`, `REAL_INV_INV`, `GSYM REAL_MUL_ASSOC`, `REAL_INV_POW`, `REAL_POW_MUL`, `REAL_FIELD`, `REAL_ABS_POW`, `COMPLEX_NORM_ZERO`, `ABS_SQUARE_LT_1`, `REAL_ABS_NORM`, `REAL_POW_LE`, `NORM_POS_LE`, `REAL_ARITH`, `ABS_SQUARE_LE_1`, `REAL_LT_IMP_LE`, `SQRT_UNIQUE`, `REAL_LE_LDIV_EQ`, `REAL_POW_LE`, `NORM_POS_LE`

### Porting notes (optional)
- The proof relies heavily on rewriting with various real and complex arithmetic lemmas. A port to another system will likely need to establish similar lemmas or use tactics that can automatically apply relevant algebraic identities.
- The `REAL_FIELD` tactic is used to discharge several goals involving real arithmetic. This may need to be replaced with equivalent tactics or manual proof steps in other systems.
- Care should be taken to ensure that the definitions of `kleinify` and `poincarify` are consistent with those in the HOL Light library. Any differences in definition may require adjustments to the proof.


---

## DDIST_KLEINIFY

### Name of formal statement
DDIST_KLEINIFY

### Type of the formal statement
theorem

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
          REAL_ARITH_TAC]]];
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[NORM_EQ_SQUARE; GSYM NORM_POW_2] THEN CONV_TAC REAL_FIELD]);;
```

### Informal statement
For all complex numbers `w` and `z`, if the norm of `w` is not equal to 1 and the norm of `z` is not equal to 1, then the hyperbolic distance (`ddist`) between `kleinify w` and `kleinify z` is equal to  4 * (1/2 + (norm(w - z))^2 / ((1 - (norm w)^2) * (1 - (norm z)^2)))^2 - 1.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal.
- Apply `EQ_TRANS` after existentially quantifying over `(&4 * norm(w - z:real^2) pow 2 * ((&1 - norm w pow 2) * (&1 - norm z pow 2) + norm(w - z) pow 2)) / ((&1 - norm w pow 2) pow 2 * (&1 - norm z pow 2) pow 2)`.
- Split into two subgoals using `CONJ_TAC`.

  - In the first subgoal, use `ASM_SIMP_TAC` with `ddist` and `NORM_KLEINIFY_LT`. Then, apply `MATCH_MP_TAC` with `REAL_FIELD` theorem `~(y = &0) /\ z = (w + &1) * y ==> z / y - &1 = w`. Split into two subgoals again.
   - In the first subgoal, rewrite with `REAL_ENTIRE` and `DE_MORGAN_THM`. Then split into two subgoals. Apply `MATCH_MP_TAC` with `REAL_ARITH` theorem `x < &1 ==> ~(&1 - x = &0)`. Finally, use `ASM_SIMP_TAC` with `REAL_POW_1_LT`, `NORM_KLEINIFY_LT`, `NORM_POS_LE`, and `ARITH`.
   - In the second subgoal, rewrite with `kleinify`, `COMPLEX_NORM_MUL`, and `COMPLEX_NORM_CX`. Further, rewrite with `GSYM COMPLEX_CMUL`, `DOT_LMUL` and `DOT_RMUL`. Simplify using various real number theorems, including `REAL_ABS_DIV`, `REAL_ABS_NUM`, `REAL_POW_LE`,`NORM_POS_LE`, and `REAL_ARITH` theorem `&0 <= x ==> abs(&1 + x) = &1 + x`. Apply `MATCH_MP_TAC` with a `REAL_FIELD` theorem that simplifies an expression involving division and squares. Split into subgoals again.
     - The first new subgoal involves splitting into subgoals and using a `REAL_ARITH` theorem `~(abs x = &1) ==> ~(&1 + x = &0)`, followed by `ASM_SIMP_TAC` with theorems for absolute value and norm. Then, use `ARITH_TAC`. Next, rewrite with a field theorem and apply `MATCH_MP_TAC` with a `REAL_FIELD` theorem.
        - Split into subgoals again.
        - Simplify using theorems related to powers, absolute value, norms, and arithmetic.
        - Rewrite with `NORM_POW_2`, `DOT_LSUB`, `DOT_RSUB`, `DOT_SYM`.
        - Use `REAL_ARITH_TAC`.

- Repeat popping assumptions and applying `MP_TAC`.
- Rewrite using `NORM_EQ_SQUARE` and `GSYM NORM_POW_2`.
- Convert using `REAL_FIELD`.

### Mathematical insight
This theorem establishes a formula for calculating the hyperbolic distance between two points in the complex plane that have been transformed by the `kleinify` function, which maps complex numbers to points inside the unit disk. The formula involves the norms of the original points and their difference.

### Dependencies
- `ddist`
- `NORM_KLEINIFY_LT`
- `REAL_ENTIRE`
- `DE_MORGAN_THM`
- `REAL_POW_1_LT`
- `NORM_POS_LE`
- `kleinify`
- `COMPLEX_NORM_MUL`
- `COMPLEX_NORM_CX`
- `COMPLEX_CMUL`
- `DOT_LMUL`
- `DOT_RMUL`
- `REAL_ABS_DIV`
- `REAL_ABS_NUM`
- `REAL_POW_LE`
- `REAL_ABS_POW`
- `REAL_POW_EQ_1`
- `REAL_ABS_NORM`
- `REAL_RING`
- `REAL_POW_EQ_0`
- `NORM_POW_2`
- `DOT_LSUB`
- `DOT_RSUB`
- `DOT_SYM`


---

## DDIST_KLEINIFY_EQ

### Name of formal statement
DDIST_KLEINIFY_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DDIST_KLEINIFY_EQ = prove
 (`!w z w' z'.
      ~(norm w = &1) /\ ~(norm z = &1) /\ ~(norm w' = &1) /\ ~(norm z' = &1) /\
      norm(w - z) pow 2 * (&1 - norm w' pow 2) * (&1 - norm z' pow 2) =
      norm(w' - z') pow 2 * (&1 - norm w pow 2) * (&1 - norm z pow 2)
      ==> ddist(kleinify w,kleinify z) = ddist(kleinify w',kleinify z')`,
  SIMP_TAC[DDIST_KLEINIFY; NORM_EQ_SQUARE; GSYM NORM_POW_2; REAL_POS] THEN
  CONV_TAC REAL_FIELD);;
```
### Informal statement
For all complex numbers `w`, `z`, `w'`, and `z'`, if the norms of `w`, `z`, `w'`, and `z'` are not equal to 1, and `norm(w - z)^2 * (1 - norm(w')^2) * (1 - norm(z')^2) = norm(w' - z')^2 * (1 - norm(w)^2) * (1 - norm(z)^2)`, then `ddist(kleinify w, kleinify z) = ddist(kleinify w', kleinify z')`.

### Informal sketch
The proof proceeds by:
- Simplification using `DDIST_KLEINIFY` which substitutes the definition of `ddist` and `kleinify`.
- Rewriting using `NORM_EQ_SQUARE` and `GSYM NORM_POW_2` to manipulate expressions involving norms and squares. `REAL_POS` is used to simplify expressions by asserting the positivity of certain terms.
- Applying `REAL_FIELD` conversion to perform algebraic manipulation in the field of real numbers in order to prove equality.

### Mathematical insight
This theorem states that the hyperbolic distance, as computed by `ddist` after applying the `kleinify` transform, is invariant under certain transformations of the input arguments `w`, `z`, `w'`, and `z'`. The condition `norm(w - z)^2 * (1 - norm(w')^2) * (1 - norm(z')^2) = norm(w' - z')^2 * (1 - norm(w)^2) * (1 - norm(z)^2)` establishes the specific constraint for this invariance. The conditions that the norms of `w`, `z`, `w'`, and `z'` are not equal to 1 are necessary to avoid division by zero in the definitions of `kleinify` and `ddist`.

### Dependencies

Definitions:
- `DDIST_KLEINIFY`

Theorems:
- `NORM_EQ_SQUARE`
- `NORM_POW_2`
- `REAL_POS`


---

## NORM_KLEINIFY_MOEBIUS_LT

### Name of formal statement
NORM_KLEINIFY_MOEBIUS_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_KLEINIFY_MOEBIUS_LT = prove
 (`!w x. norm w < &1 /\ norm x < &1
         ==> norm(kleinify(moebius_function (&0) w x)) < &1`,
  SIMP_TAC[MOEBIUS_FUNCTION_NORM_LT_1; NORM_KLEINIFY_LT; REAL_LT_IMP_NE]);;
```
### Informal statement
For all complex numbers `w` and `x`, if the norm of `w` is less than 1 and the norm of `x` is less than 1, then the norm of `kleinify(moebius_function (&0) w x)` is less than 1.

### Informal sketch
The proof demonstrates that if two complex numbers `w` and `x` have norms less than 1, then the `kleinify` function applied to the result of the `moebius_function` with parameter 0 applied to `w` and `x` also has norm less than 1. The proof proceeds by:
- Using `MOEBIUS_FUNCTION_NORM_LT_1` to assert that `norm (moebius_function (&0) w x) < &1` if `norm w < &1` and `norm x < &1`.
- Applying `NORM_KLEINIFY_LT` which states that `norm (kleinify z) < &1` if `norm z < &1`.
- Applying `REAL_LT_IMP_NE` to prove the result via simplification.

### Mathematical insight
This theorem shows that the `kleinify` function preserves the property of having a norm less than 1 when applied to the output of a specific `moebius_function`. This is important because the `kleinify` function is used to project complex numbers into the open unit disk, and this theorem guarantees that composing it with a specific `moebius_function` maintains this property.

### Dependencies
- Theorems: `MOEBIUS_FUNCTION_NORM_LT_1`, `NORM_KLEINIFY_LT`, `REAL_LT_IMP_NE`


---

## DDIST_KLEINIFY_MOEBIUS

### Name of formal statement
DDIST_KLEINIFY_MOEBIUS

### Type of the formal statement
theorem

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
                complex_add; RE; IM; cnj; complex_neg] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For all complex numbers `w`, `x`, and `y`, if the norm of `w` is less than 1, the norm of `x` is less than 1, and the norm of `y` is less than 1, then the distance between the kleinified image of the Moebius transformation of `x` with parameter `w` and the kleinified image of the Moebius transformation of `y` with parameter `w` is equal to the distance between the kleinified images of `x` and `y`.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumptions.
- Apply `DDIST_KLEINIFY_EQ`, which states `!x y. ddist (kleinify x, kleinify y) = norm (x - y) / sqrt ((1 - norm x pow 2) * (1 - norm y pow 2))`. This reduces the goal to showing the equality of specific expressions involving norms.
- Simplify using `MOEBIUS_FUNCTION_NORM_LT_1` and `REAL_LT_IMP_NE`, utilizing the assumption that `norm w < &1` to show needed inequalities.
- Rewrite using `MOEBIUS_FUNCTION_SIMPLE` to expand the definition of the `moebius_function`.
- Introduce the subgoal that `~(Cx(&1) - cnj w * x = Cx(&0)) /\ ~(Cx(&1) - cnj w * y = Cx(&0))` and prove it.
  - Rewrite using `COMPLEX_SUB_0` to yield `~(cnj w * x = Cx(&1)) /\ ~(cnj w * y = Cx(&1))`.
  - Apply `CONJ_TAC`, splitting the goal into two parts.
  - Apply a theorem stating that `norm(x) < norm(y) ==> ~(y = x)`.
  - Rewrite using the definitions of `COMPLEX_NORM_CX`, `REAL_ABS_NUM` and `COMPLEX_NORM_MUL`.
  - Apply `GSYM REAL_MUL_LID`.
  - Apply `REAL_LT_MUL2`, then rewrite using `NORM_POS_LE`.
  - Apply `ASM_REWRITE_TAC` with `COMPLEX_NORM_CNJ`.
  - Simplify using field axioms.
- Simplify using `COMPLEX_FIELD` to rewrite the difference of the two fractions resulting from the Moebius transformations.
- Rewrite with `COMPLEX_NORM_DIV` and `COMPLEX_NORM_POW`.
- Simplify using `COMPLEX_NORM_ZERO` and `REAL_FIELD`.
- Rewrite using `REAL_POW_DIV` and `COMPLEX_NORM_MUL`.
- Rewrite using `real_div`.
- Apply a theorem converting multiplication of real numbers to complex norm multiplication.
- Rewrite using `GSYM COMPLEX_NORM_MUL`, `NORM_POW_2`, and `DOT_2`.
- Rewrite using the definitions of `RE_DEF`, `IM_DEF`, `complex_sub`, `complex_mul`, `CX_DEF`, `complex_add`, `RE`, `IM`, `cnj`, and `complex_neg`.
- Prove the result using `REAL_ARITH_TAC`.

### Mathematical insight
This theorem demonstrates a key property of the Moebius transformation in relation to the Klein metric (cross-ratio distance). Specifically, it showcases how the Klein metric between the images of two points `x` and `y` under a Moebius transformation parameterized by `w` (where `|w| < 1`) remains invariant. This invariance is fundamental in understanding the geometric properties preserved by Moebius transformations within the unit disk, a core concept in hyperbolic geometry.

### Dependencies
- `DDIST_KLEINIFY_EQ`
- `MOEBIUS_FUNCTION_NORM_LT_1`
- `REAL_LT_IMP_NE`
- `MOEBIUS_FUNCTION_SIMPLE`
- `REAL_LT_REFL`
- `COMPLEX_NORM_CX`
- `REAL_ABS_NUM`
- `COMPLEX_NORM_MUL`
- `REAL_LT_MUL2`
- `NORM_POS_LE`
- `COMPLEX_NORM_CNJ`
- `COMPLEX_NORM_DIV`
- `COMPLEX_NORM_POW`
- `COMPLEX_NORM_ZERO`
- `REAL_POW_DIV`
- `REAL_RING`
- `RE_DEF`
- `IM_DEF`
- `complex_sub`
- `complex_mul`
- `CX_DEF`
- `complex_add`
- `RE`
- `IM`
- `cnj`
- `complex_neg`

### Porting notes (optional)
- The definition and properties of the Moebius transformation are required.
- Correctly handle complex numbers and their norms.
- Automation involving complex field arithmetic is useful.
- The specific field axioms used may differ syntactically but should be functionally equivalent in other proof assistants.


---

## COLLINEAR_KLEINIFY_MOEBIUS

### Name of formal statement
COLLINEAR_KLEINIFY_MOEBIUS

### Type of the formal statement
theorem

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
For all complex numbers `w`, `x`, `y`, and `z`, if the norms of `w`, `x`, `y`, and `z` are all less than 1, then the points `kleinify(moebius_function (&0) w x)`, `kleinify(moebius_function (&0) w y)`, and `kleinify(moebius_function (&0) w z)` are collinear if and only if the points `kleinify x`, `kleinify y`, and `kleinify z` are collinear.

### Informal sketch
The proof proceeds by:
- Eliminating the quantifiers and assumptions using `REPEAT STRIP_TAC`.
- Rewriting using definitions of `COLLINEAR_3_2D`, `kleinify`, `RE` (real part), and `IM` (imaginary part).
- Rewriting using the real and imaginary parts of complex multiplication `RE_MUL_CX` and `IM_MUL_CX`.
- Simplifying using inequalities and field arithmetic related to norms, including `NORM_POS_LE`, `REAL_POW_LE`. The simpset contains an arithmetic rewriting rule expressing collinearity.
- Rewriting using `COMPLEX_NORM_DIV` and `MOEBIUS_FUNCTION_SIMPLE`.
- Applying `COMPLEX_DIV_CNJ`.
- Rewriting using definitions of the real and imaginary parts of complex division, `CX_POW`, and `IM_DIV_CX`.
- Introducing a subgoal (`SUBGOAL_THEN`) to prove a non-zero condition to avoid division by zero relating to the Moebius transformation.
- Discharging the subgoal by proving that `1 - conj w * x`, `1 - conj w * y`, and `1 - conj w * z` are non-zero, using norm inequalities and properties of complex numbers.
- Applying arithmetic simplifications and rewriting rules to equate collinearity criteria for the transformed and original points.
- Rewriting using complex number definitions (`COMPLEX_SQNORM`, `complex_sub`, `complex_mul`, `complex_add`, `complex_neg`, `cnj`, `CX_DEF`, `RE`, `IM`).
- Using `REAL_RING` to simplify the equation regarding collinearity conditions, eventually reducing it to `lhs = 0 <=> rhs = 0`.
- Introducing existential variables to reduce the equation, based on the conditions regarding non-zero norm.
- Applying real arithmetic (`REAL_ENTIRE` to use DE_MORGAN_THM), and `REAL_POW_EQ_0; ARITH_EQ`.
- Discharging the remaining goals with real arithmetic tactics.

### Mathematical insight
This theorem demonstrates that the collinearity of three points within the unit disk is preserved under a Möbius transformation followed by a `kleinify` transformation. The `kleinify` function maps a complex number z to z/(1 - |z|^2). The norm constraints ensure that all points lie within the unit disk, where the Möbius transformation is well-defined. The theorem is significant because it relates the geometric property of collinearity to transformations that preserve certain structures within the complex plane.

### Dependencies
**Theorems:**
- `COLLINEAR_3_2D`

**Definitions:**
- `kleinify`
- `RE_DEF`
- `IM_DEF`

**Lemmas:**
- `RE_MUL_CX`
- `IM_MUL_CX`
- `NORM_POS_LE`
- `REAL_POW_LE`
- `COMPLEX_NORM_DIV`
- `MOEBIUS_FUNCTION_SIMPLE`
- `COMPLEX_DIV_CNJ`
- `RE_DIV_CX`
- `CX_POW`
- `IM_DIV_CX`
- `COMPLEX_SUB_0`
- `REAL_LT_REFL`
- `COMPLEX_NORM_MUL`
- `COMPLEX_NORM_CNJ`
- `COMPLEX_NORM_CX`
- `REAL_LT_MUL2`
- `COMPLEX_NORM_ZERO`
- `REAL_FIELD` (multiple instances)
- `COMPLEX_SQNORM`
- `complex_sub`
- `complex_mul`
- `complex_add`
- `complex_neg`
- `cnj`
- `CX_DEF`
- `RE`
- `IM`
- `GSYM REAL_SUB_0`
- `REAL_RING`
- `REAL_ENTIRE`
- `DE_MORGAN_THM`
- `REAL_POW_EQ_0`
- `ARITH_EQ`
- `REAL_ARITH` (multiple instances)
- `REAL_LE_POW_2`
- `REAL_POW_1_LT`
- `REAL_LE_ADD`
- `REAL_LE_MUL`
- `REAL_POS`

### Porting notes (optional)
- The proof relies heavily on rewriting with complex number identities and real arithmetic. Ensure that the target proof assistant has similar capabilities.
- The use of `REAL_RING` suggests a significant amount of algebraic manipulation. If the target system's ring tactic is weaker, more manual steps might be needed.
- The subgoal tactic `SUBGOAL_THEN` is used to introduce an intermediate goal. This can be translated to similar tactics with equivalent effects in other proof assistants.


---

## BETWEEN_KLEINIFY_MOEBIUS

### Name of formal statement
BETWEEN_KLEINIFY_MOEBIUS

### Type of the formal statement
theorem

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
           COLLINEAR_KLEINIFY_MOEBIUS; DDIST_KLEINIFY_MOEBIUS]);;
```
### Informal statement
For all complex numbers `w`, `x`, `y`, and `z`, if the norms of `w`, `x`, `y`, and `z` are strictly less than 1, then `kleinify(moebius_function (&0) w x)` lies between `kleinify(moebius_function (&0) w y)` and `kleinify(moebius_function (&0) w z)` if and only if `kleinify x` lies between `kleinify y` and `kleinify z`.

### Informal sketch
The proof proceeds as follows:
- It uses `BETWEEN_COLLINEAR_DDIST_EQ` to relate the `between` predicate to collinearity and equality of distances.
- It applies `NORM_KLEINIFY_MOEBIUS_LT` and `NORM_KLEINIFY_LT` for verifying norm conditions related to `kleinify` and `moebius_function`.
- It utilizes `REAL_LT_IMP_NE` to deduce inequality from a less-than relation.
- It employs `COLLINEAR_KLEINIFY_MOEBIUS` to establish collinearity.
- It employs `DDIST_KLEINIFY_MOEBIUS` relates the distance to the Möbius transformation.

### Mathematical insight
This theorem states that the betweenness relation is invariant under the composition of the `kleinify` transformation and a Möbius transformation (specifically, the Möbius transformation `moebius_function`) when applied to complex numbers within the unit disk. This shows the conformal transformations preserve geodesics in the hyperbolic plane.

### Dependencies
- `BETWEEN_COLLINEAR_DDIST_EQ`
- `NORM_KLEINIFY_MOEBIUS_LT`
- `NORM_KLEINIFY_LT`
- `REAL_LT_IMP_NE`
- `COLLINEAR_KLEINIFY_MOEBIUS`
- `DDIST_KLEINIFY_MOEBIUS`


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
A function `f` from `real^2` to `real^2` is a `hyperbolic_isometry` if and only if the following conditions hold:
1. For all `x`, if the norm of `x` is less than 1, then the norm of `f x` is less than 1.
2. For all `x` and `y`, if the norm of `x` is less than 1 and the norm of `y` is less than 1, then the hyperbolic distance between `f x` and `f y` is equal to the hyperbolic distance between `x` and `y`.
3. For all `x`, `y`, and `z`, if the norm of `x` is less than 1, the norm of `y` is less than 1, and the norm of `z` is less than 1, then `f y` is between `f x` and `f z` if and only if `y` is between `x` and `z`.

### Informal sketch
The definition `hyperbolic_isometry` introduces the concept of an isometry on the hyperbolic plane, modeled as the unit disk in `real^2`.
- The definition requires that `f` maps points within the unit disk to points within the unit disk (condition 1).
- It also demands that `f` preserves hyperbolic distances (condition 2) between points inside the unit disk, using the `ddist` function, which is implicitly assumed to represent the hyperbolic distance.
- Finally, collinearity is preserved by `f`, within the unit disk, using the `between` predicate (condition 3).

### Mathematical insight
This definition captures the essential properties of an isometry in the hyperbolic plane. An isometry preserves distances and the betweenness relation, thus preserving the geometric structure. The unit disk model is a common representation of the hyperbolic plane, and this definition formalizes what it means for a function to act as an isometry in this context.

### Dependencies
- `norm`
- `ddist`
- `between`

### Porting notes (optional)
- The definition makes implicit assumptions about the existence of functions defining `norm`, `ddist`, and `between` in the target environment. When porting, ensure that these functions are either already available or defined appropriately for the hyperbolic plane in the target proof assistant. If `ddist` or `between` are not readily available, they would need to be defined first.
- The notion of `real^2` is frequently represented as a tuple or a record that contains two reals. This could be represented in many ways, and should be represented in a way that is appropriate for the target environment.


---

## HYPERBOLIC_TRANSLATION

### Name of formal statement
HYPERBOLIC_TRANSLATION

### Type of the formal statement
theorem

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
               KLEINIFY_POINCARIFY]);;
```
### Informal statement
For any `w` in the real plane, if the norm of `w` is less than 1, then there exist functions `f` and `g` from the real plane to the real plane such that:
1. `f` is a hyperbolic isometry.
2. `g` is a hyperbolic isometry.
3. `f(w)` is the zero vector.
4. `g(vec 0)` is `w`.
5. For all `x` in the real plane, if the norm of `x` is less than 1, then `f(g(x)) = x`.
6. For all `x` in the real plane, if the norm of `x` is less than 1, then `g(f(x)) = x`.

### Informal sketch
The proof demonstrates, for any vector `w` inside the unit disk, the existence of hyperbolic isometries `f` and `g` that map `w` to the origin and vice versa, while acting as inverses of each other within the unit disk.
-  The proof starts by assuming `norm w < &1`.
-  Then, functions `f` and `g` are defined using the `kleinify` and `moebius_function` with the `poincarify` transformation. Specifically, `f` is defined as `\x. kleinify(moebius_function(&0) (poincarify w) (poincarify x))` and `g` as `\x. kleinify(moebius_function(&0) (--(poincarify w)) (poincarify x))`. These functions are essentially Möbius transformations adapted to the Poincaré disk model of hyperbolic geometry and then converted to the Klein disk coordinates.
- The proof proceeds by verifying that `f` and `g` satisfy the properties outlined in the theorem:
  - `f` and `g` are hyperbolic isometries (`hyperbolic_isometry`). This relies on pre-existing theorems about the properties of Möbius transformations and the `kleinify` and `poincarify` transformations.
  - `f(w) = vec 0` and `g(vec 0) = w`. This is demonstrated using simplification rules related to Möbius transformations, and the `kleinify` and `poincarify` functions.
  - `f` and `g` are inverses within the unit disk. This uses the composition properties of Möbius transformations which involves showing that `f(g x) = x` and `g(f x) = x` within the unit disk.
- The proof uses a combination of simplification tactics (`SIMP_TAC`, `ASM_SIMP_TAC`) and existential introduction (`EXISTS_TAC`) to construct the functions `f` and `g` and prove the desired properties.

### Mathematical insight
This theorem demonstrates the homogeneity and symmetry of the hyperbolic plane (represented by the unit disk model). Specifically, it illustrates that for any point `w` within the unit disk, there exists a hyperbolic isometry that maps `w` to the origin. Furthermore, it constructs an inverse isometry that maps the origin back to `w`, ensuring that these transformations are mutual inverses within the hyperbolic plane. This is a characteristic property of hyperbolic space, showcasing that all points are equivalent under hyperbolic isometries.

### Dependencies
*Definitions:*
- `hyperbolic_isometry`

*Theorems:*
- `NORM_KLEINIFY_MOEBIUS_LT`
- `NORM_POINCARIFY_LT`
- `DDIST_KLEINIFY_MOEBIUS`
- `KLEINIFY_POINCARIFY`
- `VECTOR_NEG_NEG`
- `BETWEEN_KLEINIFY_MOEBIUS`
- `NORM_NEG`
- `MOEBIUS_FUNCTION_COMPOSE`
- `POINCARIFY_KLEINIFY`
- `MOEBIUS_FUNCTION_NORM_LT_1`
- `MOEBIUS_FUNCTION_SIMPLE`
- `COMPLEX_SUB_REFL`
- `complex_div`
- `COMPLEX_VEC_0`
- `KLEINIFY_0`
- `POINCARIFY_0`
- `COMPLEX_MUL_LZERO`
- `COMPLEX_MUL_RZERO`
- `COMPLEX_SUB_LZERO`
- `COMPLEX_NEG_NEG`
- `COMPLEX_SUB_RZERO`
- `COMPLEX_INV_1`
- `COMPLEX_MUL_RID`

### Porting notes (optional)
- The core idea hinges on the Möbius transformation's properties and its relation to hyperbolic isometries. Ensure that the target proof assistant has a well-defined theory of complex numbers and Möbius transformations or can be constructed.
- The tactics used (`SIMP_TAC`, `ASM_SIMP_TAC`, `EXISTS_TAC`) represent simplification and existential reasoning. The porter must identify analogous automation or proof search techniques in the target assistant.
- Carefully verify definitions of `kleinify` and `poincarify` and the associated theorems as these are crucial.


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
Define a new type named `plane` with constructor `mk_plane` and destructor `dest_plane`. The type is inhabited by providing a theorem that there exists an `x` of type `real^2` such that the norm of `x` is less than 1.

### Informal sketch
- The goal is to show that the type `plane` is inhabited, which is necessary for defining it as a new type using `new_type_definition`.
- The proof obligation is `?x:real^2. norm x < &1`, stating there exists a vector `x` in `real^2` such that its norm is less than 1.
- The proof proceeds by choosing `vec 0:real^2` as the witness for `x`. This is achieved using `EXISTS_TAC \`vec 0:real^2\``.
- It remains to prove `norm (vec 0:real^2) < &1`, which is handled by `NORM_ARITH_TAC`. `NORM_ARITH_TAC` is a tactic that attempts to prove inequalities involving norms of real vectors using arithmetic reasoning.

### Mathematical insight
This definition introduces a new type `plane`. The existence proof ensures that the type is non-empty, which is a requirement for defining new types in HOL Light via `new_type_definition`. The specific existence proof uses the zero vector in `real^2` as a witness, which has a norm of 0, and is therefore less than 1. This indicates that `plane` represents some concept related to a non-empty subset of the real plane.

### Dependencies
- `new_type_definition`
- `prove`
- `EXISTS_TAC`
- `NORM_ARITH_TAC`

### Porting notes (optional)
Most proof assistants require a proof of inhabitability when defining a new type. The specific tactics used (`EXISTS_TAC`, `NORM_ARITH_TAC`) will have to be translated into corresponding tactics or proof strategies of the target proof assistant. Ensure that the target system has a definition of vector norms and associated arithmetic lemmas to prove the inequality.


---

## pbetween

### Name of formal statement
`pbetween`

### Type of the formal statement
`new_definition`

### Formal Content
```ocaml
let pbetween = new_definition
 `pbetween y (x,z) <=> between (dest_plane y) (dest_plane x,dest_plane z)`;;
```

### Informal statement
For any `y`, `x`, and `z`, `pbetween y (x, z)` is defined to be equivalent to `between (dest_plane y) (dest_plane x, dest_plane z)`.

### Informal sketch
The definition introduces `pbetween`, which relates three points in some space.
The core idea is that `pbetween y (x, z)` holds if and only if `dest_plane y` is between `dest_plane x` and `dest_plane z`, where `dest_plane` is presumably a defined function related to plane extraction from some object. The definition simply links `pbetween` to an existing `between` predicate using `dest_plane`.

### Mathematical insight
The definition `pbetween` appears to be a lifting or adaptation of the `between` predicate to a higher-level geometric context. It allows us to reason about the "betweenness" of geometric objects (represented by `y`, `x`, and `z`) by projecting them onto planes using `dest_plane` and then applying the established `between` predicate.

### Dependencies
- Definitions:
  - `between`
  - `dest_plane`


---

## pdist

### Name of formal statement
pdist

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pdist = new_definition
 `pdist(x,y) = ddist(dest_plane x,dest_plane y)`;;
```

### Informal statement
The function `pdist` is defined such that for any `x` and `y`, `pdist(x, y)` is equal to `ddist(dest_plane x, dest_plane y)`.

### Informal sketch
- The definition introduces `pdist` as a function that composes two existing functions. The first function, `dest_plane`, is applied to both `x` and `y`. The results are then passed as arguments to the second function, `ddist`. The definition is direct and does not involve any complex logical stages.

### Mathematical insight
The definition introduces a notion of distance (presumably the 'p' in `pdist` stands for point and from previous definitions `ddist` is the dihedral angle) between two objects `x` and `y`, where `x` and `y` are first transformed into some plane representation using `dest_plane`, and then the distance between these planes is computed using the `ddist` function. It’s a way to define distance on a higher-level structure by mapping it to a known distance function on planes.

### Dependencies
- `dest_plane`
- `ddist`


---

## DEST_PLANE_NORM_LT

### Name of formal statement
DEST_PLANE_NORM_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DEST_PLANE_NORM_LT = prove
 (`!x. norm(dest_plane x) < &1`,
  MESON_TAC[plane_tybij]);;
```
### Informal statement
For all `x`, the norm of `dest_plane x` is less than 1.

### Informal sketch
- The theorem is proved using the `MESON_TAC` tactic, which is a higher-order automatic theorem prover.
- The proof relies on the theorem `plane_tybij`.

### Mathematical insight
This theorem establishes a bound on the norm of the result of the function `dest_plane`. The `dest_plane` function presumably maps some input `x` to a value whose norm is always strictly less than 1. The fact that the norm is strictly less than 1 may be relevant for convergence arguments or other analytical properties that depend on magnitude.

### Dependencies
- Theorems: `plane_tybij`


---

## DEST_PLANE_EQ

### Name of formal statement
DEST_PLANE_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DEST_PLANE_EQ = prove
 (`!x y. dest_plane x = dest_plane y <=> x = y`,
  MESON_TAC[plane_tybij]);;
```

### Informal statement
For all `x` and `y`, the destination plane of `x` is equal to the destination plane of `y` if and only if `x` is equal to `y`.

### Informal sketch
- The proof uses the theorem `plane_tybij`, which states that `dest_plane` is a bijection between the type of points and the type of planes. 
- The theorem follows directly from `dest_plane` being a bijection. MESON automatically discharges the goal using `plane_tybij`

### Mathematical insight
This theorem establishes that the `dest_plane` function is injective (one-to-one). In other words, distinct points map to distinct planes under the `dest_plane` mapping. This is a fundamental property for reasoning about the relationship between points and planes in the formal geometry.

### Dependencies
- Theorems: `plane_tybij`

### Porting notes (optional)
The proof relies heavily on the automation provided by MESON. When porting, ensure that the target proof assistant has a comparable level of automation for discharging goals related to bijections. Otherwise, the proof will need to be expanded to explicitly apply the properties of bijections (injectivity and surjectivity).


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
  MESON_TAC[plane_tybij]);;
```
### Informal statement
For any predicate `P` on the complex plane, the statement that `P(dest_plane x)` holds for all `x` is equivalent to the statement that for all `x`, if the norm of `x` is strictly less than 1, then `P(x)` holds.

### Informal sketch
The proof establishes the equivalence of two universally quantified statements involving the predicate `P` and the function `dest_plane`.
- The proof uses the theorem `plane_tybij`, which asserts that the function `dest_plane` is a bijection between the disk of unit radius and the entire complex plane. Thus, every point in the complex plane is the image of some `x` in the disk under `dest_plane`. This makes the universally quantified statement about `dest_plane x` equivalent to the universally quantified statement about `x` within the disk.

### Mathematical insight
The theorem relates quantification over the entire complex plane to quantification over the open unit disk, using the bijective function `dest_plane`. This is useful for transferring properties or theorems between the unit disk and the entire complex plane, which is a common technique in complex analysis.

### Dependencies
- Theorems: `plane_tybij`

### Porting notes (optional)
- The critical element to porting this theorem is the theorem `plane_tybij` which asserts the bijectivity of `dest_plane`. If the proof assistant does not already have a proof for complex plane bijectivity results, establishing such a result first would be a good start.


---

## EXISTS_DEST_PLANE

### Name of formal statement
EXISTS_DEST_PLANE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXISTS_DEST_PLANE = prove
 (`!P. (?x. P(dest_plane x)) <=> (?x. norm x < &1 /\ P x)`,
  MESON_TAC[plane_tybij]);;
```
### Informal statement
For all predicates `P`, there exists an `x` such that `P(dest_plane x)` if and only if there exists an `x` such that the norm of `x` is less than 1 and `P(x)`.

### Informal sketch
The theorem states that the existence of an element satisfying a predicate applied to `dest_plane x` is equivalent to the existence of an element whose norm is less than `&1` and satisfies the predicate itself.
- Use the theorem `plane_tybij` which characterises the image of `dest_plane`.

### Mathematical insight
The statement reveals a key property about the function `dest_plane`: that any element in its range is equivalent to an element with norm less than `&1`. In other words, the function `dest_plane` effectively maps into the open unit ball.

### Dependencies
- Theorems: `plane_tybij`


---

## TARSKI_AXIOM_1_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_1_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_1_NONEUCLIDEAN = prove
 (`!a b. pdist(a,b) = pdist(b,a)`,
  REWRITE_TAC[pdist; DDIST_SYM]);;
```

### Informal statement
For all points `a` and `b`, the distance between `a` and `b` is equal to the distance between `b` and `a`.

### Informal sketch
The proof proceeds by rewriting the term `pdist(a,b)` using the definition of `pdist` and the symmetry property of `DDIST`, denoted by `DDIST_SYM`.  This directly establishes the equality `pdist(a,b) = pdist(b,a)`.

### Mathematical insight
This theorem expresses the first axiom in Tarski's axiomatization of Euclidean geometry, specifically the symmetry of the distance function. It states that the distance between two points does not depend on the order in which they are considered. This is a fundamental and intuitive property of distance, forming the basis for many geometric arguments.

### Dependencies
- Definitions: `pdist`
- Theorems: `DDIST_SYM`


---

## TARSKI_AXIOM_2_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_2_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_2_NONEUCLIDEAN = prove
 (`!a b p q r s.
        pdist(a,b) = pdist(p,q) /\ pdist(a,b) = pdist(r,s)
        ==> pdist(p,q) = pdist(r,s)`,
  REAL_ARITH_TAC);;
```

### Informal statement
For all points `a`, `b`, `p`, `q`, `r`, and `s`, if the distance between `a` and `b` is equal to the distance between `p` and `q`, and the distance between `a` and `b` is equal to the distance between `r` and `s`, then the distance between `p` and `q` is equal to the distance between `r` and `s`.

### Informal sketch
The proof relies on real arithmetic and aims to establish the transitivity of equidistance.

- Assume `pdist(a,b) = pdist(p,q)` and `pdist(a,b) = pdist(r,s)`.
- Use these two equations to show that `pdist(p,q) = pdist(r,s)`.
- The proof uses `REAL_ARITH_TAC` to automatically discharge the goal by applying standard arithmetic reasoning.

### Mathematical insight
This theorem expresses the transitivity property of the equidistance relation. That is, if two pairs of points are each equidistant to a common pair of points, then the two pairs are equidistant to each other. This is a fundamental property of any reasonable distance metric and is especially crucial in geometry.

### Dependencies
- `pdist` (presumably a function defining the distance between two points)

### Porting notes (optional)
This theorem is a straightforward application of arithmetic transitivity. Porting it primarily requires ensuring that the target proof assistant has a robust real number/arithmetic library and that the `pdist` function, or its equivalent, is appropriately defined. The tactic `REAL_ARITH_TAC` is specific to HOL Light, so the target proof assistant's equivalent tactic for real arithmetic should be used. In systems like Lean or Coq, the `ring` or `field` tactics or their analogs should be sufficient.


---

## TARSKI_AXIOM_3_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_3_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_3_NONEUCLIDEAN = prove
 (`!a b c. pdist(a,b) = pdist(c,c) ==> a = b`,
  SIMP_TAC[FORALL_DEST_PLANE; pdist; DDIST_REFL; DDIST_EQ_0; DEST_PLANE_EQ]);;
```
### Informal statement
For all points `a`, `b`, and `c`, if the distance between `a` and `b` is equal to the distance between `c` and `c`, then `a` and `b` are equal.

### Informal sketch
The proof proceeds as follows:
- Assume `pdist(a, b) = pdist(c, c)`.
- Utilize `DDIST_REFL` to show that `pdist(c, c) = 0`.
- Thus, `pdist(a, b) = 0`.
- Apply `DDIST_EQ_0` to conclude `a = b`.

### Mathematical insight
This theorem formalizes the third axiom in Tarski's geometry, which states that the distance between a point and itself is zero, and if the distance between two points is zero, then the points are identical. This axiom establishes an identity condition for the equidistance relation.

### Dependencies
- Theorems:
  - `FORALL_DEST_PLANE`
- Definitions:
  - `pdist`
- Theorems in the reals theory:
  - `DDIST_REFL`
  - `DDIST_EQ_0`
- Destructors:
  - `DEST_PLANE_EQ`


---

## TARSKI_AXIOM_4_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_4_NONEUCLIDEAN

### Type of the formal statement
theorem

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
    EXISTS_TAC `(g:real^2->real^2) x` THEN ASM_MESON_TAC[]]);;
```

### Informal statement
For all points `a`, `q`, `b`, and `c` in the Euclidean plane, there exists a point `x` such that `x` lies between `a` and `q` and the distance between `a` and `x` is equal to the distance between `b` and `c`.

### Informal sketch
The theorem states that for any four points `a`, `q`, `b`, and `c` in the plane, there exists a point `x` on the segment `aq` such that the distance from `a` to `x` equals the distance from `b` to `c`.
*   The proof begins by reducing the goal to finding a point `d` such that `norm d < &1` and `ddist(b,c) = ddist(vec 0,d)`. Here, `ddist` denotes the hyperbolic distance. Then, it uses `HYPERBOLIC_TRANSLATION` to translate `b` and `c` to `vec 0` and `d` under an isometry. `hyperbolic_isometry` is used to rewrite the distances. 
*   The proof requires showing that `norm(a) < &1 /\ norm(q) < &1 /\ norm(d) < &1`.
*   It applies `TARSKI_AXIOM_4_EUCLIDEAN`, which is the Euclidean segment construction axiom, to a specific case with `vec 0`.
*   It uses `HYPERBOLIC_TRANSLATION` to obtain transformations `f` and `g`. It then chooses a specific `x` based on these transformations to prove the existence of the required point.

### Mathematical insight
This theorem is a segment construction axiom in the context of hyperbolic geometry. It asserts the existence of a point on a given line segment whose distance from one endpoint is equal to a given distance. The Euclidean version `TARSKI_AXIOM_4_EUCLIDEAN` is used as part of the proof, hinting that the Euclidean axiom can be leveraged somehow to derive properties in the hyperbolic case within the unit disc model.

### Dependencies
*   Definitions: `pbetween`, `pdist`, `FORALL_DEST_PLANE`, `EXISTS_DEST_PLANE`
*   Theorems: `RIGHT_IMP_FORALL_THM`, `IMP_IMP`, `GSYM CONJ_ASSOC`, `hyperbolic_isometry`, `NORM_0`, `REAL_LT_01`, `DIST_0`, `DDIST_EQ_ORIGIN`, `LEFT_IMP_EXISTS_THM`, `TARSKI_AXIOM_4_EUCLIDEAN`
*   Axioms: `HYPERBOLIC_TRANSLATION`


---

## TARSKI_AXIOM_5_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_5_NONEUCLIDEAN

### Type of the formal statement
theorem

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
    ASM_MESON_TAC[DIST_SYM; DIST_0]]);;
```

### Informal statement
For all points `a`, `b`, `c`, `x`, `a'`, `b'`, `c'`, and `x'` in the plane, if `a` is not equal to `b`, the distance between `a` and `b` is equal to the distance between `a'` and `b'`, the distance between `a` and `c` is equal to the distance between `a'` and `c'`, the distance between `b` and `c` is equal to the distance between `b'` and `c'`, `b` lies between `a` and `x`, `b'` lies between `a'` and `x'`, and the distance between `b` and `x` is equal to the distance between `b'` and `x'`, then the distance between `c` and `x` is equal to the distance between `c'` and `x'`.

### Informal sketch
The proof proceeds as follows:
- Instantiate the universally quantified geometry theorem `FORALL_DEST_PLANE`.
- Simplify using the definitions of `pdist` and `pbetween`.
- Apply the `HYPERBOLIC_TRANSLATION` theorem twice, to points `b` and `b'`. This introduces hyperbolic isometries `f`, `f'`, `g`, and `g'`.
- Rewrite with `hyperbolic_isometry`.
- Instantiate the isometries with `X_GEN_TAC`.
- Apply the `DDIST_CONGRUENT_TRIPLES_0` theorem to `f x`, `f c`, `g x'`, `g c'`.
- Use assumption management to simplify.
- Apply Tarski's axiom 5 in the Euclidean case (`TARSKI_AXIOM_5_EUCLIDEAN`). Subgoal requires showing that the distances between transformed points `f b` and `f x` is equal to the distance between transformed points `g b'` and `g x'`.
- Simplify the distance condition using assumption management, `DDIST_EQ_ORIGIN`, and discharging the assumption.
- Use assumption management to complete the proof with `DIST_SYM` and `DIST_0`.

### Mathematical insight
This theorem states Tarski's axiom 5, also known as the five-segments axiom, within the context of noneuclidean geoemtry formalized in HOL Light. This axiom essentially postulates a form of congruence for segments when given five corresponding congruent segments in two geometric configurations. The statement highlights the principle that isometries preserve distances.

### Dependencies
- `FORALL_DEST_PLANE`
- `pdist`
- `pbetween`
- `DEST_PLANE_EQ`
- `HYPERBOLIC_TRANSLATION`
- `hyperbolic_isometry`
- `DDIST_CONGRUENT_TRIPLES_0`
- `DDIST_SYM`
- `TARSKI_AXIOM_5_EUCLIDEAN`
- `DDIST_EQ_ORIGIN`
- `DIST_SYM`
- `DIST_0`
- `RIGHT_IMP_FORALL_THM`
- `LEFT_IMP_EXISTS_THM`

### Porting notes (optional)
The proof relies heavily on rewriting and assumption management tactics, which may need to be adapted to the specific automation available in other provers. The use of hyperbolic isometries is a key step. The availability and form of Euclidean axioms and metric space theorems are crucial dependency considerations.


---

## TARSKI_AXIOM_6_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_6_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_6_NONEUCLIDEAN = prove
 (`!a b. pbetween b (a,a) ==> a = b`,
  REWRITE_TAC[pbetween; FORALL_DEST_PLANE; GSYM DEST_PLANE_EQ] THEN
  MESON_TAC[TARSKI_AXIOM_6_EUCLIDEAN]);;
```

### Informal statement
For all points `a` and `b`, if `b` lies between `a` and `a`, then `a` equals `b`.

### Informal sketch
The proof proceeds as follows:
- Assume `pbetween b (a,a)`.
- Rewrite using the definition of `pbetween` and properties of `FORALL_DEST_PLANE` and `GSYM DEST_PLANE_EQ`.
- Apply `MESON_TAC` with theorem `TARSKI_AXIOM_6_EUCLIDEAN` (which states `!a b. pbetween a (b,b) ==> a = b`) to complete the proof.

### Mathematical insight
This theorem asserts that a point lying "between" a point and itself must be that same point. This captures the notion of non-distinct points in the betweenness relation; the statement is a fundamental axiom about the nature of betweenness. It is a variation of Tarski's Axiom 6 in his axiom system of Euclidean geometry and is related to the identity property of points in that system.

### Dependencies
- Definitions: `pbetween`
- Theorems: `FORALL_DEST_PLANE`, `GSYM DEST_PLANE_EQ`, `TARSKI_AXIOM_6_EUCLIDEAN`


---

## TARSKI_AXIOM_7_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_7_NONEUCLIDEAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TARSKI_AXIOM_7_NONEUCLIDEAN = prove
 (`!a b c p q.
    pbetween p (a,c) /\ pbetween q (b,c)
    ==> ?x. pbetween x (p,b) /\ pbetween x (q,a)`,
  REWRITE_TAC[pbetween; FORALL_DEST_PLANE; EXISTS_DEST_PLANE] THEN
  MESON_TAC[BETWEEN_NORM_LT; TARSKI_AXIOM_7_EUCLIDEAN]);;
```

### Informal statement
For all points `a`, `b`, `c`, `p`, and `q`, if `p` lies between `a` and `c`, and `q` lies between `b` and `c`, then there exists a point `x` such that `x` lies between `p` and `b`, and `x` lies between `q` and `a`.

### Informal sketch
The proof uses the Euclidean version of Pasch's axiom (`TARSKI_AXIOM_7_EUCLIDEAN`) and some basic properties of the `pbetween` predicate.
- First, rewrite the goal using the definition of `pbetween`, and destructure the quantifiers.
- Then, apply the MESON prover with the listed assumptions.
    - The theorem `BETWEEN_NORM_LT` which characterizes the `pbetween` predicate in terms of norms and inequalities.
    - The theorem `TARSKI_AXIOM_7_EUCLIDEAN`.

### Mathematical insight
The theorem states Pasch's axiom, a fundamental axiom in geometry, which says that if a line intersects one side of a triangle, then it must intersect another side of the triangle. This version `TARSKI_AXIOM_7_NONEUCLIDEAN` is a non-Euclidean equivalent of `TARSKI_AXIOM_7_EUCLIDEAN`.

### Dependencies
- Definitions:
  - `pbetween`
- Theorems:
  - `FORALL_DEST_PLANE`
  - `EXISTS_DEST_PLANE`
  - `BETWEEN_NORM_LT`
  - `TARSKI_AXIOM_7_EUCLIDEAN`

### Porting notes (optional)
The main difficulty in porting this theorem may lie in the automation provided by `MESON_TAC`. Other proof assistants might require a more explicit proof construction. The definition of `pbetween` and `BETWEEN_NORM_LT` will need to be ported first. Also, `TARSKI_AXIOM_7_EUCLIDEAN` must be proven already.


---

## TARSKI_AXIOM_8_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_8_NONEUCLIDEAN

### Type of the formal statement
theorem

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
           BASIS_COMPONENT; DIMINDEX_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
There exist points `a`, `b`, and `c` in the real plane such that `b` is not between `a` and `c`, `c` is not between `b` and `a`, and `a` is not between `c` and `b`.

### Informal sketch
The proof establishes the existence of three points that violate the betweenness relation in all possible orderings.

- The proof starts by rewriting the definition of `pbetween` and applying `EXISTS_DEST_PLANE` to decompose the existential quantifier over points in the plane into existential quantifiers over real-valued coordinates.
- Specific candidate points for `a`, `b`, and `c` are introduced by existential introduction: the origin (`vec 0`), a point `(&1 / &2) % basis 1` along the first basis vector, and a point `(&1 / &2) % basis 2` along the second basis vector.
- Simplification steps use properties of dot products (`DOT_LMUL`, `DOT_RMUL`, `DOT_BASIS_BASIS`, `DOT_LZERO`), vector components (`DIMINDEX_2`), and basic arithmetic.
- The goal is then brought into a conjunctive form repeated applications of `CONJ_TAC`, after which each conjunct is discharged and combined by `MATCH_MP` with `BETWEEN_IMP_COLLINEAR`, which states that if `pbetween b (a, c)` holds then `collinear (a,b,c)` holds as well.
- The properties of `COLLINEAR_3_2D`, vector components, and the basis vectors are simplified using `SIMP_TAC` along with arithmetic reasoning,
- Finally, `REAL_RAT_REDUCE_CONV` normalizes rational expressions involving real numbers.

### Mathematical insight
This theorem represents Tarski's Axiom 8, sometimes called the Lower Dimension Axiom. This axiom ensures that the geometry being formalized is at least two-dimensional. By demonstrating the existence of three non-collinear points, it rules out one-dimensional or zero-dimensional spaces. The specific choice of points is motivated by the desire to create a simple, easily verifiable geometric configuration.

### Dependencies
**Definitions:**
- `pbetween`
- `collinear`
**Theorems:**
- `EXISTS_DEST_PLANE`
- `NORM_LT_SQUARE`
- `NORM_POW_2`
- `BETWEEN_IMP_COLLINEAR`
- `COLLINEAR_3_2D`
**Lemmas/Properties:**
- `DOT_LMUL`
- `DOT_RMUL`
- `DOT_BASIS_BASIS`
- `DIMINDEX_2`
- `DOT_LZERO`
- `VECTOR_MUL_COMPONENT`
- `VEC_COMPONENT`
- `BASIS_COMPONENT`


---

## TARSKI_AXIOM_9_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_9_NONEUCLIDEAN

### Type of the formal statement
theorem

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
                  VECTOR_NEG_COMPONENT] THEN CONV_TAC REAL_RING]);;
```

### Informal statement
For all points `p`, `q`, `a`, `b`, and `c` in the real plane, if `p` is not equal to `q`, the distance between `a` and `p` is equal to the distance between `a` and `q`, the distance between `b` and `p` is equal to the distance between `b` and `q`, and the distance between `c` and `p` is equal to the distance between `c` and `q`, then either `b` lies between `a` and `c`, or `c` lies between `b` and `a`, or `a` lies between `c` and `b`.

### Informal sketch
The proof proceeds by contradiction. Assuming the negation of the consequent (i.e., none of `pbetween b (a,c)`, `pbetween c (b,a)`, `pbetween a (c,b)` hold), the proof aims to derive a contradiction using hyperbolic geometry.

- First, rewrite the goal to introduce the definitions of `pdist` and `pbetween`.
- Use the `HYPERBOLIC_MIDPOINT` theorem to introduce a point `x` such that `between x (p,q)` and `ddist x p = ddist x q`.
- Use the `HYPERBOLIC_TRANSLATION` theorem to produce an isometry `f` that maps `p` to the origin and `q` to `--p`.
- Establish that the condition `norm x < 1` holds.
- Exploit this condition to show that `f q = --(f p)`.
- Show `between (f x) (f p, f q)` and `ddist (f x) (f p) = ddist (f x) (f q)`.
- Finally, derive a contradiction by showing that `collinear (f b, f c, f a)` and `ddist(f a, f p) = ddist(f a, f q) /\ ddist(f b, f p) = ddist(f b, f q) /\ ddist(f c, f p) = ddist(f c, f q) /\ ~(f q = f p)`.

### Mathematical insight
This theorem is a form of Tarski's axiom system for Euclidean geometry, specifically adapted to rule out geometries where three equidistant points from two distinct points must be collinear. Because Tarski's axioms are complete for Euclidean geometry, by negating this statement we guarantee the geometry must be noneuclidean. The proof uses hyperbolic geometry, which is a specific example of a noneuclidean geometry to create isometries.

### Dependencies
- `pdist`
- `pbetween`
- `FORALL_DEST_PLANE`
- `DEST_PLANE_EQ`
- `RIGHT_IMP_FORALL_THM`
- `IMP_IMP`
- `CONJ_ASSOC`
- `HYPERBOLIC_MIDPOINT`
- `LEFT_IMP_EXISTS_THM`
- `HYPERBOLIC_TRANSLATION`
- `BETWEEN_NORM_LT`
- `BETWEEN_SYM`
- `hyperbolic_isometry`
- `COLLINEAR_BETWEEN_CASES`
- `DDIST_EQ_ORIGIN`
- `MIDPOINT_BETWEEN`
- `midpoint`
- `NORM_ARITH`
- `ddist`
- `NORM_NEG`
- `real_div`
- `REAL_INV_MUL`
- `REAL_SUB_LT`
- `ABS_SQUARE_LT_1`
- `REAL_ABS_NORM`
- `REAL_FIELD`
- `COLLINEAR_3_2D`
- `VECTOR_SUB_COMPONENT`
- `DOT_2`
- `DOT_EQ_0`
- `VECTOR_NEG_COMPONENT`


---

## NOT_TARSKI_AXIOM_10_NONEUCLIDEAN

### Name of formal statement
NOT_TARSKI_AXIOM_10_NONEUCLIDEAN

### Type of the formal statement
theorem

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
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```
### Informal statement
It is not the case that for all points `a`, `b`, `c`, `d`, and `t`, if `d` lies between `a` and `t`, and `d` lies between `b` and `c`, and `a` is not equal to `d`, then there exist points `x` and `y` such that `b` lies between `a` and `x`, `c` lies between `a` and `y`, and `t` lies between `x` and `y`.

### Informal sketch
The proof proceeds by contradiction, showing that Tarski's axiom 10 does not hold in general.
- First, the universally quantified variables `a`, `b`, `c`, `d`, and `t` are instantiated with specific vectors in `real^2`: `vec 0`, `&1 / &2 % basis 1`, `&1 / &2 % basis 2`, `&1 / &4 % basis 1 + &1 / &4 % basis 2`, `&3 / &5 % basis 1 + &3 / &5 % basis 2` respectively.
- Then, the goal becomes to prove that the specific instance of the antecedent `pbetween d (a,t) /\ pbetween d (b,c) /\ ~(a = d)` holds, while the specific instance of the consequent `?x y. pbetween b (a,x) /\ pbetween c (a,y) /\ pbetween t (x,y)` does not hold.
- To show that the antecedent is true, the definitions of `pbetween` (point lies between two other points) is expanded and simplified using vector arithmetic and properties like `COLLINEAR_3_2D`.
- To show that the consequent is false, we prove that it is not the case that there exist `x` and `y` such that `pbetween b (a,x) /\ pbetween c (a,y) /\ pbetween t (x,y)`. This is manipulated to show that no such `x` and `y` exist by considering component-wise inequalities derived from the `pbetween` relations. The constraint `norm(&3 / &5 % basis 1 + &3 / &5 % basis 2:real^2) pow 2 <= &1 / &2` is derived, and then shown to be false by expanding the norm and using real arithmetic.
- Finally, the antecedent is shown to be true by expanding `BETWEEN_IN_SEGMENT` and vector arithmetic and showing the existence of such segments.

### Mathematical insight
This theorem demonstrates that Tarski's axiom 10, also known as the Euclidean axiom (or Playfair's axiom), does not hold in general. The axiom essentially states that given a line and a point not on the line, there exists at most one line through the point that is parallel to the given line. By providing a concrete counterexample in `real^2`, the theorem shows that this axiom is independent of the other axioms of Tarski's geometry. The specific vectors are carefully chosen to exploit the properties of the `pbetween` relation, leading to a configuration where the required points `x` and `y` cannot exist.

### Dependencies
- `pbetween`
- `FORALL_DEST_PLANE`
- `EXISTS_DEST_PLANE`
- `GSYM DEST_PLANE_EQ`
- `RIGHT_IMP_FORALL_THM`
- `IMP_IMP`
- `NOT_IMP`
- `CONJ_ASSOC`
- `NOT_EXISTS_THM`
- `TAUT ~ p /\ q <=> p ==> ~q`
- `IMP_CONJ`
- `BETWEEN_IMP_COLLINEAR`
- `COLLINEAR_3_2D`
- `BASIS_COMPONENT`
- `DIMINDEX_2`
- `ARITH`
- `VEC_COMPONENT`
- `VECTOR_MUL_COMPONENT`
- `REAL_RAT_REDUCE_CONV`
- `REAL_SUB_LZERO`
- `REAL_MUL_LZERO`
- `REAL_MUL_RZERO`
- `REAL_SUB_RZERO`
- `REAL_ARITH &0 = &1 / &2 * x <=> x = &0`
- `REAL_ENTIRE`
- `COMPONENT_LE_NORM`
- `BETWEEN_IN_SEGMENT`
- `IN_SEGMENT`
- `NORM_POW_2`
- `DOT_LADD`
- `DOT_RADD`
- `DOT_LMUL`
- `DOT_RMUL`
- `CART_EQ`
- `FORALL_2`
- `VECTOR_ADD_COMPONENT`
- `REAL_ABS_MUL`
- `REAL_LE_ADD2`
- `REAL_LE_MUL2`
- `REAL_LE_SQUARE_ABS`
- `NORM_LT_SQUARE`
- `DOT_LZERO`
- `DOT_BASIS_BASIS`

### Porting notes (optional)
- The proof relies heavily on real arithmetic, vector algebra, and properties of the `pbetween` relation. It might be beneficial to have these theories adequately developed in the target proof assistant.
- The tactics `REWRITE_TAC`, `SIMP_TAC`, and `ASM_SIMP_TAC` are used extensively for simplification. Ensure that the target proof assistant has similar automation capabilities or be prepared to perform these simplifications manually.
- Conversion tactics like `REAL_RAT_REDUCE_CONV` are used to normalize real expressions. The target proof assistant should either have equivalent tactics or provide a way to normalize such expressions to facilitate the proof.


---

## TARSKI_AXIOM_11_NONEUCLIDEAN

### Name of formal statement
TARSKI_AXIOM_11_NONEUCLIDEAN

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; DEST_PLANE_NORM_LT; BETWEEN_NORM_LT]);;
```

### Informal statement
For all sets of points `X` and `Y` in the plane, if there exists a point `a` such that for all points `x` in `X` and `y` in `Y`, `x` lies between `a` and `y`, then there exists a point `b` such that for all points `x` in `X` and `y` in `Y`, `b` lies between `x` and `y`.

### Informal sketch
The proof proceeds constructively.
- Assume that for all sets of points X and Y, there exists a point 'a' such that for all points x in X and y in Y, x lies between a and y.
- Handles the base cases where either `X` or `Y` are empty sets. If `X` is empty, then the antecedent is false, making the implication trivially true. Similarly, if `Y` is empty, the antecedent is false, making the implication true.
- Deals with the case where 'X' and 'Y' are not empty. It uses `TARSKI_AXIOM_11_EUCLIDEAN` to establish an equivalent property when points are mapped onto the destination plane (`dest_plane`). It then shows the existence of a point `b` that satisfies the `pbetween` condition. It relies on `MEMBER_NOT_EMPTY`, `DEST_PLANE_NORM_LT`, and `BETWEEN_NORM_LT` to complete the proof.

### Mathematical insight
This theorem represents Tarski's axiom of continuity, a crucial axiom in Tarski's axiomatic system for Euclidean geometry. It asserts that if we can find a point `a` "beyond" all points in `X` relative to `Y` in terms of the `pbetween` predicate, then we can find a point `b` "between" all points in `X` and `Y`. This captures a notion of completeness or continuity of the geometric space. In this version, it is shown that given `TARSKI_AXIOM_11_EUCLIDEAN`, one can show that the non-Euclidean version holds as well.

### Dependencies
- `pbetween`
- `TARSKI_AXIOM_11_EUCLIDEAN`
- `EXISTS_DEST_PLANE`
- `MEMBER_NOT_EMPTY`
- `DEST_PLANE_NORM_LT`
- `BETWEEN_NORM_LT`
- `NOT_IN_EMPTY`
- `IN_IMAGE`
- `IMAGE`
- `DEST_PLANE`


---

