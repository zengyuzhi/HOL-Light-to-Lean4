# circle.ml

## Overview

Number of statements: 5

This file formalizes the calculation of the area of a circle in HOL Light. It builds on the multivariate analysis library, specifically using measure theory and real analysis components, to prove that the area of a circle equals π times the square of its radius. The proof likely establishes this classic geometric result within the formal framework of HOL Light's mathematical foundations.

## AREA_UNIT_CBALL

### Area of unit circle
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem (prove)

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
This theorem states that the measure (area) of the closed unit ball in $\mathbb{R}^2$ centered at the origin equals $\pi$:

$$\text{measure}(\text{cball}(\vec{0}, 1)) = \pi$$

Where:
- $\text{cball}(\vec{0}, 1)$ is the closed unit ball in $\mathbb{R}^2$ centered at the origin
- $\text{measure}$ is the Lebesgue measure function
- $\pi$ is the mathematical constant pi

### Informal proof
The proof uses Fubini's theorem to compute the area of the unit disk by integrating the areas of horizontal slices:

1. Apply Fubini's theorem for compact sets (`FUBINI_SIMPLE_COMPACT`), using $k=1$ to slice the disk horizontally.

2. The `SLICE_CBALL` theorem tells us that when slicing a disk at height $t$ where $|t| \leq 1$, we get:
   - A circle with radius $\sqrt{1-t^2}$ when $|t| \leq 1$
   - Empty set when $|t| > 1$

3. Rewrite the condition $|t| \leq 1$ as $t \in [-1,1]$ and apply `HAS_REAL_INTEGRAL_RESTRICT_UNIV`.

4. For each $t \in [-1,1]$, the measure of the slice is the length of the interval $[-\sqrt{1-t^2}, \sqrt{1-t^2}]$, which equals $2\sqrt{1-t^2}$.

5. To compute the total area, apply the Fundamental Theorem of Calculus by finding an antiderivative of $2\sqrt{1-t^2}$. The antiderivative is:
   $$f(t) = \arcsin(t) + t\sqrt{1-t^2}$$

6. Verify that $f'(t) = 2\sqrt{1-t^2}$ for $t \in (-1,1)$ by differentiating:
   - Differentiate $\arcsin(t)$ to get $\frac{1}{\sqrt{1-t^2}}$
   - Differentiate $t\sqrt{1-t^2}$ using the product rule to get $\sqrt{1-t^2} - \frac{t^2}{\sqrt{1-t^2}}$
   - Combine to get $\frac{1}{\sqrt{1-t^2}} + \sqrt{1-t^2} - \frac{t^2}{\sqrt{1-t^2}} = 2\sqrt{1-t^2}$

7. Evaluate $f(1) - f(-1)$:
   - $f(1) = \arcsin(1) + 1 \cdot 0 = \frac{\pi}{2}$
   - $f(-1) = \arcsin(-1) + (-1) \cdot 0 = -\frac{\pi}{2}$
   - Thus $f(1) - f(-1) = \pi$

Therefore, the area of the unit disk is $\pi$.

### Mathematical insight
This theorem establishes the classical result that the area of a circle with radius $r$ is $\pi r^2$, specifically for the case where $r=1$. The proof demonstrates a powerful approach using Fubini's theorem, which reduces a two-dimensional integration problem to a one-dimensional integration by slicing the region into simpler shapes.

The technique showcases how to compute the area of a curved region by integrating the lengths of parallel cross-sections. The key insight is recognizing that horizontal slices of the unit disk at height $t$ are line segments of length $2\sqrt{1-t^2}$, which leads to the antiderivative $\arcsin(t) + t\sqrt{1-t^2}$ whose evaluation at the boundaries gives exactly $\pi$.

### Dependencies
#### Theorems
- `FUBINI_SIMPLE_COMPACT`: Relates the measure of a set to the integral of measures of its slices
- `COMPACT_CBALL`: States that the closed ball is compact
- `SLICE_CBALL`: Describes the slices of a ball
- `MEASURE_EMPTY`: Measure of empty set is zero
- `HAS_REAL_INTEGRAL_RESTRICT_UNIV`: Relates integrals of restricted functions to integrals over subsets
- `HAS_REAL_INTEGRAL_EQ`: Equality theorem for integrals
- `MEASURE_INTERVAL`: Relates measure of intervals to their content
- `CONTENT_1`: Content of 1-dimensional intervals
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR`: Fundamental theorem of calculus
- `REAL_CONTINUOUS_ON_ADD`, `REAL_CONTINUOUS_ON_MUL`, etc.: Continuity theorems for real functions

#### Definitions
- `measure`: Lebesgue measure function

### Porting notes
When porting this theorem:
1. Make sure the target system has a proper definition of the Lebesgue measure in $\mathbb{R}^n$
2. The proof relies on Fubini's theorem for compact sets and techniques for slicing balls
3. The closed unit ball definition should match HOL Light's `cball(vec 0:real^2,&1)`
4. The antiderivative calculation involves several computational steps that might require different tactics in other systems
5. The proof demonstrates that $\pi$ is exactly the area of the unit circle, which might require careful handling of the constant $\pi$ in other systems

---

## AREA_CBALL

### AREA_CBALL
- `AREA_CBALL`

### Type of the formal statement
- theorem

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
For any point $z \in \mathbb{R}^2$ and radius $r \geq 0$, the measure (area) of the closed ball centered at $z$ with radius $r$ is given by:

$$\text{measure}(\text{cball}(z,r)) = \pi \cdot r^2$$

### Informal proof
We proceed by considering two cases:

* **Case $r = 0$**: 
  - When $r = 0$, $\text{cball}(z,0)$ is a singleton set $\{z\}$
  - Using $r^2 = 0$ and $\pi \cdot 0 = 0$, the right side equals $0$
  - For the left side, we apply `MEASURE_UNIQUE` with the fact that $\{z\}$ has measure $0$
  - This follows from `HAS_MEASURE_0` and the fact that singletons are negligible

* **Case $r > 0$**: 
  - We use the affinity theorem for measures (`HAS_MEASURE_AFFINITY`) to relate the area of $\text{cball}(z,r)$ to the area of the unit ball $\text{cball}(0,1)$
  - We apply the theorem with scaling factor $r$ and translation $z$
  - Specifically, $\text{cball}(z,r) = \text{IMAGE}(\lambda x. r \cdot x + z)(\text{cball}(0,1))$
  - For a scaling by factor $r$ in $\mathbb{R}^2$, the measure is multiplied by $|r|^2 = r^2$ (since $r > 0$)
  - We know (from `AREA_UNIT_CBALL`, not shown but referenced) that $\text{measure}(\text{cball}(0,1)) = \pi$
  - Therefore, $\text{measure}(\text{cball}(z,r)) = r^2 \cdot \pi = \pi \cdot r^2$
  
  - To complete the proof, we verify that $\text{cball}(z,r) = \text{IMAGE}(\lambda x. r \cdot x + z)(\text{cball}(0,1))$ by showing subset inclusion in both directions:
    - For any $w \in \text{cball}(z,r)$, we have $\|w - z\| \leq r$
    - Setting $x = \frac{w-z}{r}$, we get $\|x\| \leq 1$, so $x \in \text{cball}(0,1)$
    - And $w = z + r \cdot x$, showing $w \in \text{IMAGE}(\lambda x. r \cdot x + z)(\text{cball}(0,1))$
    - Conversely, for any $w = r \cdot x + z$ where $\|x\| \leq 1$, we have $\|w - z\| = r \cdot \|x\| \leq r$
    - Thus $w \in \text{cball}(z,r)$

### Mathematical insight
This theorem establishes the classic formula for the area of a circle in $\mathbb{R}^2$. The proof illustrates a powerful and general technique in measure theory:

1. First, calculate the measure for a standard or reference set (here, the unit ball).
2. Then, use affine transformations to derive the measure for transformed versions of that reference set.

This approach is elegant because it reduces the problem to calculating the measure of one standard object, and then applying known scaling laws for measures under transformations. In this case, we leverage the fact that scaling a 2-dimensional object by a factor of $r$ multiplies its measure by $r^2$.

The theorem is a fundamental building block in geometric measure theory, providing the basis for calculations involving circular regions in the plane.

### Dependencies
- **Theorems**:
  - `MEASURE_UNIQUE`: If a set $s$ has measure $m$, then $\text{measure}(s) = m$.
  - `HAS_MEASURE_MEASURABLE_MEASURE`: A set $s$ has measure $m$ if and only if $s$ is measurable and $\text{measure}(s) = m$.
  - `HAS_MEASURE_0`: A set has measure 0 if and only if it is negligible.
  - `HAS_MEASURE_AFFINITY`: If a set $s$ has measure $y$, then the image of $s$ under an affine transformation $x \mapsto mx + c$ has measure $|m|^n \cdot y$, where $n$ is the dimension.
  - `MEASURABLE_CBALL`: Closed balls are measurable.
  - `AREA_UNIT_CBALL` (implied): The unit ball in $\mathbb{R}^2$ has measure $\pi$.

- **Definitions**:
  - `measure`: The measure of a set $s$ is the unique $m$ such that $s$ has measure $m$.

### Porting notes
When porting this theorem:
1. Ensure your system has the concept of a measure on Euclidean space, specifically for $\mathbb{R}^2$.
2. Verify the definition of `cball` (closed ball) in your system.
3. The proof relies on the area of the unit ball being $\pi$, which might need to be established separately.
4. The affine transformation theorem for measures is essential - ensure it's available in your system or established beforehand.
5. Be aware that HOL Light uses explicit type annotations (`:real^2`), which may need to be handled differently in other systems.

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
For any point $z \in \mathbb{R}^2$ and radius $r \geq 0$, the measure (area) of the open ball centered at $z$ with radius $r$ is equal to $\pi r^2$.

Formally:
$$\forall z \in \mathbb{R}^2, \forall r \in \mathbb{R}. r \geq 0 \Rightarrow \text{measure}(B(z,r)) = \pi r^2$$

where $B(z,r) = \{x \in \mathbb{R}^2 : |x - z| < r\}$ is the open ball.

### Informal proof
The proof proceeds as follows:

* First, we rewrite the goal using two key facts:
  - $\text{interior}(\text{cball}(z,r)) = \text{ball}(z,r)$ (where cball is the closed ball)
  - The area of the closed ball $\text{cball}(z,r)$ is $\pi r^2$

* After applying these simplifications and stripping the assumptions, we apply the theorem `MEASURE_INTERIOR`, which states that for a bounded set with negligible frontier, the measure of its interior equals the measure of the set itself.

* To use this theorem, we need to establish:
  1. The closed ball is bounded, which is a direct property of closed balls
  2. The frontier of the closed ball is negligible, which follows from:
     - The closed ball is convex (by `CONVEX_CBALL`)
     - The frontier of any convex set is negligible (by `NEGLIGIBLE_CONVEX_FRONTIER`)

* This completes the proof that $\text{measure}(\text{ball}(z,r)) = \pi r^2$.

### Mathematical insight
This theorem establishes the classical formula for the area of a circle in $\mathbb{R}^2$. While the result is well-known, the formal proof demonstrates how measure theory connects with geometric objects.

The proof uses an elegant approach by relating the measure of the open ball to that of the closed ball. Instead of calculating the area directly, it leverages the fact that the boundary (frontier) of the closed ball is negligible (has measure zero), which means the measure of the interior equals the measure of the closed ball.

This approach exemplifies a common technique in measure theory: rather than computing a measure directly, we relate it to a known measure through set operations and properties of negligible sets.

### Dependencies
#### Theorems
- `MEASURE_INTERIOR`: For a bounded set with negligible frontier, the measure of its interior equals the measure of the set itself
- `NEGLIGIBLE_CONVEX_FRONTIER`: The frontier of any convex set is negligible
- `INTERIOR_CBALL`: Relates the interior of a closed ball to an open ball
- `AREA_CBALL`: The area of a closed ball is $\pi r^2$
- `BOUNDED_CBALL`: A closed ball is bounded
- `CONVEX_CBALL`: A closed ball is convex

#### Definitions
- `measure`: The measure of a set

### Porting notes
When porting to other systems:
1. Ensure that the target system has definitions for open and closed balls in Euclidean space
2. Verify that the necessary measure theory is in place, particularly the relationship between the measure of a set and its interior when the frontier is negligible
3. The proof relies on convexity properties of balls, so these properties should be established in the target system
4. Note that some systems might have different conventions for how balls are defined (strict vs. non-strict inequalities)

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
For any $z \in \mathbb{R}^3$ and $r \geq 0$, the measure (volume) of the closed ball centered at $z$ with radius $r$ is given by:
$$\text{measure}(\text{cball}(z,r)) = \frac{4}{3} \pi r^3$$

### Informal proof
The proof proceeds as follows:

* First, we use a geometric transformation to reduce to the case where $z$ is the origin.
* We apply Fubini's theorem (specifically `FUBINI_SIMPLE_COMPACT`) to calculate the volume by integrating the measure of slices.
* We choose to slice along the first coordinate (dimension 1).
* The slice of a 3D ball at position $t$ along the first coordinate is a 2D disk.
* For $|t| \leq r$, this 2D disk has radius $\sqrt{r^2 - t^2}$.
* For $|t| > r$, the slice is empty.

The main calculation:
* For each $t \in [-r,r]$, the area of the slice is $\pi(r^2 - t^2)$ by the formula for the area of a 2D disk.
* We need to integrate this function over $t \in [-r,r]$.
* We use the Fundamental Theorem of Calculus with the antiderivative $\pi(r^2t - \frac{1}{3}t^3)$.
* Evaluating at the bounds $t = -r$ and $t = r$, we get:
$$\pi(r^3 - \frac{1}{3}r^3) - \pi(-r^3 - \frac{1}{3}(-r)^3) = \pi(\frac{2}{3}r^3 + \frac{2}{3}r^3) = \frac{4}{3}\pi r^3$$

### Mathematical insight
This theorem proves the classical formula for the volume of a 3D ball. The approach demonstrates how to compute volumes in higher dimensions by using Fubini's theorem to reduce the calculation to an iterated integral. The calculation gives the familiar formula $\frac{4}{3}\pi r^3$, which is one of the fundamental results in elementary geometry.

The proof technique of slicing is powerful and generalizable to other shapes and higher dimensions. This particular result forms the basis for many calculations in physics, engineering, and analysis involving spherical objects.

### Dependencies
#### Theorems:
- `FUBINI_SIMPLE_COMPACT`: Relates the measure of a set to the integral of measures of its slices
- `SLICE_CBALL`: Characterizes the slice of a closed ball along a coordinate
- `MEASURE_EMPTY`: States that the measure of an empty set is zero
- `AREA_CBALL`: Gives the area of a 2D ball (used implicitly)
- `HAS_REAL_INTEGRAL_RESTRICT_UNIV`: Relates integrals over the whole space to integrals over subsets
- `HAS_REAL_INTEGRAL_EQ`: Equality of integrals for functions equal on the domain
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`: The standard fundamental theorem of calculus

#### Definitions:
- `measure`: The measure (volume) of a set
- `cball`: The closed ball of given center and radius

### Porting notes
When porting this theorem:
1. Ensure your system has a compatible definition of multidimensional measure
2. The proof relies heavily on Fubini's theorem for compact sets
3. Depending on your proof assistant, the "slicing" approach may need to be expressed differently
4. The calculation of the antiderivative and its evaluation should be straightforward in most systems

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
For any point $z \in \mathbb{R}^3$ and any radius $r \geq 0$, the measure (volume) of the ball centered at $z$ with radius $r$ is:
$$\text{measure}(\text{ball}(z, r)) = \frac{4}{3} \pi r^3$$

### Informal proof
This theorem computes the volume of a 3-dimensional ball. The proof proceeds as follows:

1. First, we rewrite the goal using two facts:
   - The interior of a closed ball equals the open ball: `INTERIOR_CBALL`
   - The measure of a closed ball equals $\frac{4}{3} \pi r^3$: `VOLUME_CBALL`

2. After applying these simplifications, we need to show that:
   $$\text{measure}(\text{interior}(\text{cball}(z, r))) = \text{measure}(\text{cball}(z, r))$$

3. We apply the theorem `MEASURE_INTERIOR` which states that for any bounded set with negligible frontier, the measure of its interior equals the measure of the set.

4. Finally, we verify the conditions required by `MEASURE_INTERIOR`:
   - The closed ball is bounded (using `BOUNDED_CBALL`)
   - The frontier of the closed ball is negligible (using `NEGLIGIBLE_CONVEX_FRONTIER` and `CONVEX_CBALL`)

### Mathematical insight
This theorem establishes the well-known formula for the volume of a 3-dimensional ball as $\frac{4}{3} \pi r^3$. It's a fundamental result in geometry and measure theory, which is derived from more general principles about measure and convex sets.

The proof elegantly leverages the relationship between open and closed balls, where:
- An open ball (ball) consists of all points strictly less than distance $r$ from center
- A closed ball (cball) consists of all points less than or equal to distance $r$ from center

The proof uses the fact that the boundary of a convex set (like a ball) has measure zero, which allows us to conclude that open and closed balls have the same volume.

### Dependencies
- **Theorems:**
  - `MEASURE_INTERIOR`: For bounded sets with negligible frontier, the measure of the interior equals the measure of the set.
  - `NEGLIGIBLE_CONVEX_FRONTIER`: The frontier of any convex set is negligible.
  - `INTERIOR_CBALL`: The interior of a closed ball equals the open ball.
  - `VOLUME_CBALL`: The volume formula for a closed ball.
  - `BOUNDED_CBALL`: A closed ball is bounded.
  - `CONVEX_CBALL`: A closed ball is convex.

- **Definitions:**
  - `measure`: The measure (volume) of a set.

### Porting notes
When porting this theorem:
- Ensure that the target system has appropriate definitions for balls in $\mathbb{R}^3$
- Check that the system has the concept of negligible sets (sets of measure zero)
- Verify that theorems about interiors, convexity and measures of convex sets are available

---

