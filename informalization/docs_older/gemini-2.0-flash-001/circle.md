# circle.ml

## Overview

Number of statements: 5

`circle.ml` defines and proves results related to the area of a circle within the multivariate real analysis framework. It leverages measure theory and real analysis results from imported files to formalize properties of circles. The file likely contains definitions related to circles (e.g., representation, area) and key theorems about their area.


## AREA_UNIT_CBALL

### Name of formal statement
AREA_UNIT_CBALL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AREA_UNIT_CBALL = prove
 (`measure(cball(vec 0:real^2,&1)) = pi`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:1`,`:M`; `:2`,`:N`] FUBINI_SIMPLE_COMPACT) THEN
  EXISTS_TAC `1` THEN
  SIMP_TAC[DIMINDEX_1; DIMINDEX_2; ARITH; COMPACT_CBALL; SLICE_CBALL] THEN
  REWRITE_TAC[VEC_COMPONENT; DROPOUT_0; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[MEASURE_EMPTY] THEN
  SUBGOAL_THEN `!t. abs(t) <= &1 <=> t IN real_interval[-- &1,&1]`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV; BALL_1] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. &2 * sqrt(&1 - t pow 2)` THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN SIMP_TAC[IN_REAL_INTERVAL; MEASURE_INTERVAL] THEN
    REWRITE_TAC[REAL_BOUNDS_LE; VECTOR_ADD_LID; VECTOR_SUB_LZERO] THEN
    DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhs o rand) CONTENT_1 o rand o snd) THEN
    REWRITE_TAC[LIFT_DROP; DROP_NEG] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[REAL_POW_ONE] THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= x`) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_SUB_LE; GSYM REAL_LE_SQUARE_ABS;
                 REAL_ABS_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x.  asn(x) + x * sqrt(&1 - x pow 2)`;
    `\x. &2 * sqrt(&1 - x pow 2)`;
    `-- &1`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
  REWRITE_TAC[ASN_1; ASN_NEG_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SQRT_0; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 - --(x / &2) = x`] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_ASN; IN_REAL_INTERVAL; REAL_BOUNDS_LE] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_POW;
             REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT];
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_BOUNDS_LT] THEN REPEAT STRIP_TAC THEN
    REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_POW_1; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_MUL_RNEG; REAL_INV_MUL] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; ABS_SQUARE_LT_1] THEN
    MATCH_MP_TAC(REAL_FIELD
     `s pow 2 = &1 - x pow 2 /\ x pow 2 < &1
      ==> (inv s + x * --(&2 * x) * inv (&2) * inv s + s) = &2 * s`) THEN
    ASM_SIMP_TAC[ABS_SQUARE_LT_1; SQRT_POW_2; REAL_SUB_LE; REAL_LT_IMP_LE]]);;
```

### Informal statement
The measure of the closed ball centered at the origin in the 2-dimensional real vector space with radius 1 is equal to pi.

### Informal sketch
The proof proceeds as follows:
- Apply Fubini's theorem for simple compact sets to reduce the 2D integral to iterated 1D integrals
- Apply appropriate simplifications, then reduce the problem to showing `abs(t) <= &1 <=> t IN real_interval[-- &1,&1]`.
- Rewrite using `IN_REAL_INTERVAL` and simplify using real arithmetic.
- Rewrite using `HAS_REAL_INTEGRAL_RESTRICT_UNIV` and `BALL_1`.
- Apply the theorem `HAS_REAL_INTEGRAL_EQ`.
- Exhibit a suitable function `\t. &2 * sqrt(&1 - t pow 2)` and perform simplification steps.
- Apply the fundamental theorem of calculus.
- Simplify via rewriting with facts about `asn`, square roots, and arithmetic.
- Prove continuity of the integrand and differentiability of the antiderivative functions within the interval to satisfy the conditions for the fundamental theorem of calculus.
- Use field arithmetic and simplification to complete the proof.

### Mathematical insight
This theorem gives the area of the unit circle in the Euclidean plane. The proof uses Fubini's theorem to express the area as an iterated integral, then applies the fundamental theorem of calculus to evaluate the integral. This illustrates a standard technique for computing areas and volumes by reduction to simpler integrals.

### Dependencies
Measure Theory:
- `measure`
- `FUBINI_SIMPLE_COMPACT`
- `COMPACT_CBALL`
- `SLICE_CBALL`
- `MEASURE_EMPTY`
- `MEASURE_INTERVAL`
- `HAS_REAL_INTEGRAL_EQ`
- `HAS_REAL_INTEGRAL_RESTRICT_UNIV`

Real Analysis:
- `IN_REAL_INTERVAL`
- `REAL_BOUNDS_LE`
- `REAL_BOUNDS_LT`
- `REAL_CONTINUOUS_ON_ADD`
- `REAL_CONTINUOUS_ON_ASN`
- `REAL_CONTINUOUS_ON_MUL`
- `REAL_CONTINUOUS_ON_ID`
- `REAL_CONTINUOUS_ON_COMPOSE`
- `REAL_CONTINUOUS_ON_SUB`
- `REAL_CONTINUOUS_ON_POW`
- `REAL_CONTINUOUS_ON_CONST`
- `REAL_CONTINUOUS_ON_SQRT`
- `REAL_DIFF_TAC`
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR`
- `SQRT_POS_LE`
- `REAL_SUB_LE`
- `REAL_LE_SQUARE_ABS`
- `REAL_ABS_NUM`
- `ABS_SQUARE_LT_1`
- `SQRT_POW_2`
- `REAL_LT_IMP_LE`

Vector Space:
- `DROP_NEG`
- `LIFT_DROP`
- `VECTOR_ADD_LID`
- `VECTOR_SUB_LZERO`
- `VEC_COMPONENT`
- `DIMINDEX_1`
- `DIMINDEX_2`
- `DROPOUT_0`

Basic Real Arithmetic:
- `ARITH`
- `REAL_POW_ONE`
- `REAL_SUB_RZERO`
- `REAL_MUL_RZERO`
- `REAL_ADD_RID`
- `REAL_MUL_RNEG`
- `REAL_MUL_LID`
- `REAL_POW_1`
- `REAL_MUL_RID`
- `REAL_SUB_LZERO`
- `REAL_SUB_LT`
- `REAL_INV_MUL`
- `SQRT_0`
- `REAL_ARITH`
- `COND_RAND`

Calculus:
- `ASN_1` , `ASN_NEG_1`

### Porting notes (optional)
- The proof relies heavily on the real analysis library, including the fundamental theorem of calculus. Ensure that the target proof assistant has similar theorems and sufficient automation for real arithmetic and calculus.
- Fubini's theorem is a non-trivial result to port to other systems, and the specific version used `FUBINI_SIMPLE_COMPACT` should be checked.
- The tactic `REAL_DIFF_TAC` is a specific way to perform differentiation in HOL Light. In other systems, one would need to invoke a suitable differentiation tactic or apply the differentiation rules manually.


---

## AREA_CBALL

### Name of formal statement
AREA_CBALL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AREA_CBALL = prove
 (`!z:real^2 r. &0 <= r ==> measure(cball(z,r)) = pi * r pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THENL
   [ASM_SIMP_TAC[CBALL_SING; REAL_POW_2; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC MEASURE_UNIQUE THEN
    REWRITE_TAC[HAS_MEASURE_0; NEGLIGIBLE_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `r:real`; `z:real^2`; `pi`]
        HAS_MEASURE_AFFINITY) THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_CBALL;
              AREA_UNIT_CBALL] THEN
  ASM_REWRITE_TAC[real_abs; DIMINDEX_2] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_CBALL_0; IN_IMAGE] THEN REWRITE_TAC[IN_CBALL] THEN
  REWRITE_TAC[NORM_ARITH `dist(z,a + z) = norm a`; NORM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `abs r * x <= r <=> abs r * x <= r * &1`] THEN
  ASM_SIMP_TAC[real_abs; REAL_LE_LMUL; dist] THEN X_GEN_TAC `w:real^2` THEN
  DISCH_TAC THEN EXISTS_TAC `inv(r) % (w - z):real^2` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV] THEN
  CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN ASM_REWRITE_TAC[real_abs] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]);;
```
### Informal statement
For all `z` of type real 2-dimensional vector and all real numbers `r`, if `0 <= r`, then the measure of the closed ball centered at `z` with radius `r` is equal to `pi * r^2`.

### Informal sketch
The proof proceeds by cases on whether the radius `r` is zero or positive.

- Case `r = 0`:  The closed ball `cball(z, r)` reduces to the singleton set `{z}`. Then, show that the measure of the singleton set `{z}` is 0 (using theorems `MEASURE_UNIQUE`, `HAS_MEASURE_0`, and `NEGLIGIBLE_SING` with appropriate theorems about zero).
- Case `0 < r`:
    - Apply the `HAS_MEASURE_AFFINITY` theorem, instantiating the parameters as `cball(vec 0, &1)`, `r`, `z`, and `pi`. This reduces the goal to showing that `pi` is the measure of unit ball `cball(vec 0:real^2, &1)`.
    - Use `HAS_MEASURE_MEASURABLE_MEASURE`, `MEASURABLE_CBALL`, and `AREA_UNIT_CBALL` to rewrite the goal.
    - The goal involves showing the equality of two integrals over the whole space.
    - Apply properties about absolute values, and simplify.
    - Prove the equality by showing inclusion in both directions. The inclusion proof involves the theorem `SUBSET_ANTISYM`.
    - Showing `cball(vec 0, r)` is a subset of the image of `cball(z, r)` under a translation by `z` involves proving some algebraic simplifications and vector manipulations:
        - The `dist` function is manipulated using `NORM_ARITH`, `NORM_MUL`, `REAL_LE_LMUL` and `real_abs`. An existentially quantified variable `w` is introduced to express this.
    - A crucial step is to show that if a point `w` is in the closed ball centered at `z` with radius `r`, then a scaled version of `w - z` is within the unit closed ball centered at the origin.  This leads to simplifications using `VECTOR_MUL_ASSOC` and `REAL_MUL_RINV`. `REAL_ABS_INV` and the properties around division and multiplication (`real_div`, `REAL_LE_LDIV_EQ`, `REAL_MUL_LID`) are used to finalize the proof.

### Mathematical insight
This theorem establishes the familiar formula for the area of a disk in the Euclidean plane. The proof proceeds by showing that a closed disk centered at any point with any radius has measure equal to pi times the square of the radius. The proof leverages the affine invariance of the measure and the previously established fact that the unit disk has measure pi (`AREA_UNIT_CBALL`).

### Dependencies
- `CBALL_SING`
- `REAL_POW_2`
- `REAL_MUL_RZERO`
- `MEASURE_UNIQUE`
- `HAS_MEASURE_0`
- `NEGLIGIBLE_SING`
- `HAS_MEASURE_AFFINITY`
- `HAS_MEASURE_MEASURABLE_MEASURE`
- `MEASURABLE_CBALL`
- `AREA_UNIT_CBALL`
- `real_abs`
- `DIMINDEX_2`
- `REAL_MUL_SYM`
- `SUBSET_ANTISYM`
- `SUBSET`
- `FORALL_IN_IMAGE`
- `IN_CBALL_0`
- `IN_IMAGE`
- `IN_CBALL`
- `NORM_ARITH`
- `NORM_MUL`
- `REAL_LE_LMUL`
- `dist`
- `VECTOR_MUL_ASSOC`
- `REAL_MUL_RINV`
- `REAL_ABS_INV`
- `real_div`
- `REAL_LE_LDIV_EQ`
- `REAL_MUL_LID`
- `NORM_SUB`

### Porting notes (optional)
The proof relies heavily on rewriting and equational reasoning. In other systems, one might need to explicitly manipulate integrals using change of variables or measure theory tactics. The `HAS_MEASURE_AFFINITY` theorem encapsulates the core geometric idea and its equivalent may or may not be present directly in other systems, but it should be possible to derive it from measure theory principles. HOL Light's real number tactics (`ASM_REAL_ARITH_TAC`) might need to be replaced with corresponding tactics or SMT solvers.


---

## AREA_BALL

### Name of formal statement
AREA_BALL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AREA_BALL = prove
 (`!z:real^2 r. &0 <= r ==> measure(ball(z,r)) = pi * r pow 2`,
  SIMP_TAC[GSYM INTERIOR_CBALL; GSYM AREA_CBALL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_INTERIOR THEN
  SIMP_TAC[BOUNDED_CBALL; NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_CBALL]);;
```
### Informal statement
For all points `z` in the real plane (`real^2`) and all real numbers `r`, if `r` is non-negative, then the measure (area) of the `ball` with center `z` and radius `r` is equal to `pi` times `r` squared (`r pow 2`).

### Informal sketch
The proof demonstrates that the area of a ball (or disk) in the real plane is πr², where r is its radius.
- First, the theorem uses `GSYM INTERIOR_CBALL` and `GSYM AREA_CBALL` to rewrite the `ball` in terms of `interior_cball` and subsequently rewriting the measure of the `interior_cball` using the area of the `cball`.
- Then it proceeds by stripping the quantifiers and the implication. 
- `MEASURE_INTERIOR` is applied to show that the measure of the interior of a set equals the measure of the set itself.
- Finally, simplification with `BOUNDED_CBALL`, `NEGLIGIBLE_CONVEX_FRONTIER`, and `CONVEX_CBALL` is used: `BOUNDED_CBALL` establishes that the closed ball is bounded, `NEGLIGIBLE_CONVEX_FRONTIER` shows that the frontier of a convex set has measure zero, and `CONVEX_CBALL` proves the closed ball is convex. These facts together with the previous simplification reduce the the goal to the original theorem `AREA_CBALL`.

### Mathematical insight
This theorem gives a standard result for the area of a disk in Euclidean geometry. It is a fundamental geometric property.
The proof relies on the fact that the measure of the interior of a convex set is the same as the measure of the set itself, and that the frontier (boundary) of a convex set has measure zero.

### Dependencies
- `GSYM INTERIOR_CBALL`
- `GSYM AREA_CBALL`
- `MEASURE_INTERIOR`
- `BOUNDED_CBALL`
- `NEGLIGIBLE_CONVEX_FRONTIER`
- `CONVEX_CBALL`

### Porting notes (optional)
- The definition of `measure` and `ball` would need to be ported first.
- Theorems about convex sets in HOL Light play a key role in this proof, so equivalent theorems would have to be established for this result to be ported elsewhere.


---

## VOLUME_CBALL

### Name of formal statement
VOLUME_CBALL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VOLUME_CBALL = prove
 (`!z:real^3 r. &0 <= r ==> measure(cball(z,r)) = &4 / &3 * pi * r pow 3`,
  GEOM_ORIGIN_TAC `z:real^3` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:2`,`:M`; `:3`,`:N`] FUBINI_SIMPLE_COMPACT) THEN
  EXISTS_TAC `1` THEN
  SIMP_TAC[DIMINDEX_2; DIMINDEX_3; ARITH; COMPACT_CBALL; SLICE_CBALL] THEN
  REWRITE_TAC[VEC_COMPONENT; DROPOUT_0; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[MEASURE_EMPTY] THEN
  SUBGOAL_THEN `!t. abs(t) <= r <=> t IN real_interval[--r,r]`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. pi * (r pow 2 - t pow 2)` THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_BOUNDS_LE] THEN
    SIMP_TAC[AREA_CBALL; SQRT_POS_LE; REAL_SUB_LE; GSYM REAL_LE_SQUARE_ABS;
             SQRT_POW_2; REAL_ARITH `abs x <= r ==> abs x <= abs r`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. pi * (r pow 2 * t - &1 / &3 * t pow 3)`;
    `\t. pi * (r pow 2 - t pow 2)`;
    `--r:real`; `r:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RING]);;
```

### Informal statement
For all points `z` in 3-dimensional real space and all non-negative real numbers `r`, the measure (volume) of the closed ball centered at `z` with radius `r` is equal to `4/3 * pi * r^3`.

### Informal sketch
The proof proceeds as follows:

- Reduce the problem to the case where the center of the ball is the origin using `GEOM_ORIGIN_TAC`; this involves a change of variables, relying on the translation invariance of Lebesgue measure.
- Apply `FUBINI_SIMPLE_COMPACT` to reduce the volume calculation to a triple integral, then apply `DIMINDEX_2` and `DIMINDEX_3` to properly index the variables.
- The variables of integration are chosen to be `x`, `y`, `z` coordinates. Simplify the expression of the intersection of the closed ball with the planes perpendicular each axis.
- Reduce the calculation to a repeated integral, calculating the area of the disk at each height using the already proven theorem `AREA_CBALL`, that is, the area of cross-section by planes perpendicular each axis.
- The innermost integral becomes the integral of `pi*(r^2-t^2)` from `-r` to `r`, where `t` is the third coordinate.
- Use the Fundamental Theorem of Calculus (`REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`) to evaluate this integral, yielding the final result. Several simplification lemmas are used, namely `SQRT_POW_2`.

### Mathematical insight
This theorem gives the standard formula for the volume of a 3-dimensional sphere.
It is a basic result in geometry and real analysis, and it is essential for many applications in mathematics, physics, and engineering.

### Dependencies
- `GEOM_ORIGIN_TAC`
- `FUBINI_SIMPLE_COMPACT`
- `DIMINDEX_2`, `DIMINDEX_3`
- `ARITH`
- `COMPACT_CBALL`
- `SLICE_CBALL`
- `VEC_COMPONENT`
- `DROPOUT_0`
- `REAL_SUB_RZERO`
- `COND_RAND`
- `MEASURE_EMPTY`
- `IN_REAL_INTERVAL`
- `HAS_REAL_INTEGRAL_RESTRICT_UNIV`
- `HAS_REAL_INTEGRAL_EQ`
- `AREA_CBALL`
- `SQRT_POS_LE`
- `REAL_SUB_LE`
- `GSYM REAL_LE_SQUARE_ABS`
- `SQRT_POW_2`
- `REAL_ARITH`
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`
- `EQ_IMP`


---

## VOLUME_BALL

### Name of formal statement
VOLUME_BALL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VOLUME_BALL = prove
 (`!z:real^3 r. &0 <= r ==> measure(ball(z,r)) =  &4 / &3 * pi * r pow 3`,
  SIMP_TAC[GSYM INTERIOR_CBALL; GSYM VOLUME_CBALL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_INTERIOR THEN
  SIMP_TAC[BOUNDED_CBALL; NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_CBALL]);;
```
### Informal statement
For all `z` which is a vector in three-dimensional real space, and for all real numbers `r`, if `r` is non-negative, then the measure (i.e., the volume) of the open ball centered at `z` with radius `r` is equal to `4/3 * pi * r^3`.

### Informal sketch
The proof demonstrates that the measure of the open ball `ball(z, r)` is `4/3 * pi * r^3`. The proof proceeds as follows:
- First, the theorem uses `GSYM INTERIOR_CBALL` and `GSYM VOLUME_CBALL`. These rewrite the open ball `ball(z, r)` into the interior of the closed ball `interior(cball(z, r))` and introduce the expression of the volume of the closed ball `volume(cball(z, r))`.
- The proof then assumes `0 <= r` and uses `MEASURE_INTERIOR` to rewrite the measure of the interior of the closed ball into the measure of the closed ball. 
- Finally, it applies simplification rules like `BOUNDED_CBALL`, `NEGLIGIBLE_CONVEX_FRONTIER` and `CONVEX_CBALL` to simplify the expression and prove the equality.

### Mathematical insight
This theorem provides the standard formula for computing the volume of a three-dimensional open ball with a given radius. It connects measure theory with basic geometry and is a fundamental result.

### Dependencies
- Theorems: `INTERIOR_CBALL`, `VOLUME_CBALL`, `MEASURE_INTERIOR`, `BOUNDED_CBALL`, `NEGLIGIBLE_CONVEX_FRONTIER`, `CONVEX_CBALL`


---

