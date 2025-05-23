# feuerbach.ml

## Overview

Number of statements: 4

This file formalizes Feuerbach's theorem in geometry, which states that for any triangle, the nine-point circle touches the inscribed circle and each of the three excircles. The formalization builds on the multivariate and convex geometry libraries, providing formal definitions and a complete proof of this classical result in Euclidean geometry. The file includes the necessary geometric constructions, properties of the nine-point circle, and the tangency relationships that constitute Feuerbach's theorem.

## CIRCLES_TANGENT

### Name of formal statement
CIRCLES_TANGENT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CIRCLES_TANGENT = prove
 (`!r1 r2 c1 c2.
        &0 <= r1 /\ &0 <= r2 /\
        (dist(c1,c2) = r1 + r2 \/ dist(c1,c2) = abs(r1 - r2))
        ==> c1 = c2 /\ r1 = r2 \/
            ?!x:real^2. dist(c1,x) = r1 /\ dist(c2,x) = r2`,
  MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC(MESON[]
     `(!x y. P x y <=> Q y x) ==> ((!x y. P x y) <=> (!x y. Q x y))`) THEN
    MESON_TAC[DIST_SYM; REAL_ADD_SYM; REAL_ABS_SUB]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `r1 = &0` THENL
   [ASM_REWRITE_TAC[DIST_EQ_0; MESON[] `(?!x. a = x /\ P x) <=> P a`] THEN
    REWRITE_TAC[DIST_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r2 = &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `r1 <= r2 ==> abs(r1 - r2) = r2 - r1`] THEN
  ASM_REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
   [DISJ2_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
    EXISTS_TAC `c1 + r1 / (r1 + r2) % (c2 - c1):real^2` THEN CONJ_TAC THENL
     [REWRITE_TAC[dist;
       VECTOR_ARITH `c1 - (c1 + a % (x - y)):real^2 = a % (y - x)`;
        VECTOR_ARITH `z - (x + a % (z - x)):real^N = (a - &1) % (x - z)`] THEN
      ASM_REWRITE_TAC[NORM_MUL; GSYM dist] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NEG;
                   REAL_FIELD `&0 < r1 /\ &0 < r2
                       ==> r1 / (r1 + r2) - &1 = --r2 / (r1 + r2)`] THEN
      ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_LT_ADD] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN segment[c1,c2]` MP_TAC THENL
       [ASM_REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
        ASM_MESON_TAC[DIST_SYM];
        REWRITE_TAC[IN_SEGMENT]] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist(c1:real^2,(&1 - u) % c1 + u % c2) = r1` THEN
      REWRITE_TAC[VECTOR_ARITH
       `(&1 - u) % c1 + u % c2:real^N = c1 + u % (c2 - c1)`] THEN
      REWRITE_TAC[NORM_ARITH `dist(x:real^2,x + y) = norm y`] THEN
      ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
      REWRITE_TAC[VECTOR_ARITH `--(a % (x - y)):real^N = a % (y - x)`] THEN
      ASM_REWRITE_TAC[NORM_MUL; GSYM dist; real_abs] THEN
      DISCH_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD];
    ASM_CASES_TAC `r1:real = r2` THENL
     [ASM_MESON_TAC[REAL_SUB_REFL; DIST_EQ_0]; DISJ2_TAC] THEN
    SUBGOAL_THEN `r1 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN
    EXISTS_TAC `c2 + r2 / (r2 - r1) % (c1 - c2):real^2` THEN CONJ_TAC THENL
     [REWRITE_TAC[dist;
       VECTOR_ARITH `c1 - (c1 + a % (x - y)):real^2 = --(a % (x - y)) /\
             c1 - (c2 + a % (c1 - c2)):real^2 = (&1 - a) % (c1 - c2)`] THEN
      ASM_REWRITE_TAC[NORM_MUL; NORM_NEG; GSYM dist] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NEG;
        REAL_FIELD `r1 < r2 ==> &1 - r2 / (r2 - r1) = --(r1 / (r2 - r1))`] THEN
      ASM_SIMP_TAC[real_abs; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(c1:real^2) IN segment[c2,y]` MP_TAC THENL
       [ASM_REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_SEGMENT]] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_CASES_TAC `u = &0` THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_SUB_RZERO] THEN
        REWRITE_TAC[VECTOR_MUL_LID] THEN ASM_MESON_TAC[DIST_EQ_0; REAL_SUB_0];
        ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist((&1 - u) % c2 + u % y:real^2,c2) = r2 - r1` THEN
      REWRITE_TAC[VECTOR_ARITH
       `(&1 - u) % c1 + u % c2:real^N = c1 + u % (c2 - c1)`] THEN
      REWRITE_TAC[NORM_ARITH `dist(x + y:real^2,x) = norm y`] THEN
      ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
      REWRITE_TAC[VECTOR_ARITH `--(a % (x - y)):real^N = a % (y - x)`] THEN
      ASM_REWRITE_TAC[NORM_MUL; GSYM dist; real_abs] THEN
      REWRITE_TAC[VECTOR_ARITH
       `c + v % ((c + u % (y - c)) - c):real^2 = c + v % u % (y - c)`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_ARITH
       `y:real^2 = c + u % v % (y - c) <=>
        (&1 - u * v) % (y - c) = vec 0`] THEN
      DISJ1_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]]);;
```

### Informal statement
For all real numbers $r_1, r_2 \geq 0$ and points $c_1, c_2$ in $\mathbb{R}^2$:

If $\text{dist}(c_1, c_2) = r_1 + r_2$ or $\text{dist}(c_1, c_2) = |r_1 - r_2|$, then either:
- $c_1 = c_2$ and $r_1 = r_2$, or
- There exists a unique point $x \in \mathbb{R}^2$ such that $\text{dist}(c_1, x) = r_1$ and $\text{dist}(c_2, x) = r_2$

where $\text{dist}(p,q)$ represents the Euclidean distance between points $p$ and $q$.

### Informal proof
The theorem characterizes when two circles are tangent, which occurs in two cases: external tangency (when $\text{dist}(c_1,c_2) = r_1 + r_2$) or internal tangency (when $\text{dist}(c_1,c_2) = |r_1 - r_2|$).

We proceed by first assuming without loss of generality that $r_1 \leq r_2$, since the statement is symmetric with respect to the two circles.

* Case 1: $r_1 = 0$
  - If $r_1 = 0$, then the first "circle" is a point at $c_1$.
  - The condition $\text{dist}(c_1,c_2) = r_1 + r_2$ becomes $\text{dist}(c_1,c_2) = r_2$, meaning $c_1$ lies on the second circle.
  - The condition $\text{dist}(c_1,c_2) = |r_1 - r_2|$ becomes $\text{dist}(c_1,c_2) = r_2$, again placing $c_1$ on the second circle.
  - In this case, $c_1$ is the unique point satisfying both $\text{dist}(c_1,x) = r_1 = 0$ and $\text{dist}(c_2,x) = r_2$.

* Case 2: $r_2 = 0$
  - This case is similar to Case 1 but with the roles reversed.
  - Since we assumed $r_1 \leq r_2$, we have $r_1 = 0$ as well, reducing to the case where both circles are points.
  - This implies $c_1 = c_2$ and $r_1 = r_2 = 0$.

* Case 3: Both $r_1, r_2 > 0$ and $\text{dist}(c_1,c_2) = r_1 + r_2$ (external tangency)
  - We construct the unique tangent point as $c_1 + \frac{r_1}{r_1 + r_2}(c_2 - c_1)$.
  - To verify this is correct, we compute:
    - $\text{dist}(c_1, c_1 + \frac{r_1}{r_1 + r_2}(c_2 - c_1)) = \|\frac{r_1}{r_1 + r_2}(c_2 - c_1)\| = \frac{r_1}{r_1 + r_2} \cdot \text{dist}(c_1,c_2) = \frac{r_1}{r_1 + r_2} \cdot (r_1 + r_2) = r_1$
    - $\text{dist}(c_2, c_1 + \frac{r_1}{r_1 + r_2}(c_2 - c_1)) = \|(1 - \frac{r_1}{r_1 + r_2})(c_1 - c_2)\| = \frac{r_2}{r_1 + r_2} \cdot \text{dist}(c_1,c_2) = \frac{r_2}{r_1 + r_2} \cdot (r_1 + r_2) = r_2$
  - For uniqueness, suppose there exists another point $y$ with $\text{dist}(c_1,y) = r_1$ and $\text{dist}(c_2,y) = r_2$.
  - By the distance constraints, $y$ must lie on the line segment between $c_1$ and $c_2$.
  - This gives $y = (1-u)c_1 + uc_2$ for some $u \in [0,1]$.
  - From $\text{dist}(c_1,y) = r_1$, we derive $u = \frac{r_1}{r_1 + r_2}$, showing $y$ must equal our constructed point.

* Case 4: $\text{dist}(c_1,c_2) = |r_1 - r_2| = r_2 - r_1$ (internal tangency, since $r_1 \leq r_2$)
  - If $r_1 = r_2$, then $\text{dist}(c_1,c_2) = 0$, implying $c_1 = c_2$, so the circles coincide.
  - For $r_1 < r_2$, we construct the tangent point as $c_2 + \frac{r_2}{r_2 - r_1}(c_1 - c_2)$.
  - Verifying this construction:
    - $\text{dist}(c_1, c_2 + \frac{r_2}{r_2 - r_1}(c_1 - c_2)) = r_1$
    - $\text{dist}(c_2, c_2 + \frac{r_2}{r_2 - r_1}(c_1 - c_2)) = \|\frac{r_2}{r_2 - r_1}(c_1 - c_2)\| = \frac{r_2}{r_2 - r_1} \cdot (r_2 - r_1) = r_2$
  - For uniqueness, we prove that $c_1$ must lie on the line segment between $c_2$ and any candidate point $y$ satisfying our distance constraints.
  - This forces $y$ to have the form we constructed, as any other point would violate the distance requirements.

### Mathematical insight
This theorem provides a complete characterization of when two circles in a plane are tangent to each other. The tangency occurs in two forms:
1. External tangency: when the distance between centers equals the sum of radii
2. Internal tangency: when the distance between centers equals the absolute difference of radii

The uniqueness part is crucial, as it confirms that circles can only be tangent at a single point (unlike intersecting circles which meet at two points).

This result is fundamental in circle geometry and has applications in computational geometry, circle packing problems, and Apollonian gaskets. It's also a stepping stone for more advanced results in circle geometry, such as Feuerbach's theorem (as suggested by the comment).

### Dependencies
None explicitly mentioned in the provided dependency list.

### Porting notes
When porting this theorem:
- Ensure your system has a proper definition of distance in $\mathbb{R}^2$ (`dist` function)
- The proof relies heavily on vector arithmetic and real-number reasoning
- The vector operations like scaling (`%`), addition, and subtraction should be properly defined
- The `WLOG` (without loss of generality) technique is used, which might need special handling in other systems
- Careful handling of degenerate cases (zero radius) will be important

---

## FEUERBACH

### Name of formal statement
FEUERBACH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FEUERBACH = prove
 (`!a b c mbc mac mab pbc pac pab ncenter icenter nradius iradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      dist(icenter,pbc) = iradius /\
      dist(icenter,pac) = iradius /\
      dist(icenter,pab) = iradius /\
      collinear {a,b,pab} /\ orthogonal (a - b) (icenter - pab) /\
      collinear {b,c,pbc} /\ orthogonal (b - c) (icenter - pbc) /\
      collinear {a,c,pac} /\ orthogonal (a - c) (icenter - pac)
      ==> ncenter = icenter /\ nradius = iradius \/
          ?!x:real^2. dist(ncenter,x) = nradius /\ dist(icenter,x) = iradius`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CIRCLES_TANGENT THEN
  POP_ASSUM MP_TAC THEN MAP_EVERY (fun t ->
   ASM_CASES_TAC t THENL [ALL_TAC; ASM_MESON_TAC[DIST_POS_LE]])
   [`&0 <= nradius`; `&0 <= iradius`] THEN
  ASM_REWRITE_TAC[dist; NORM_EQ_SQUARE] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_ABS_POS; GSYM NORM_POW_2; GSYM dist] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e <=> b /\ c /\ d /\ a /\ e`] THEN
  GEOM_ORIGIN_TAC `a:real^2` THEN
  GEOM_NORMALIZE_TAC `b:real^2` THEN CONJ_TAC THENL
   [REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `b:real^2` THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; real_abs] THEN
  GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC)) THEN
  REWRITE_TAC[COLLINEAR_3_2D] THEN
  REWRITE_TAC[orthogonal; dist; NORM_POW_2] THEN
  ASM_REWRITE_TAC[midpoint] THEN
  REWRITE_TAC[DOT_2; DOT_LSUB; DOT_RSUB] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VEC_COMPONENT;
           VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
Let $a$, $b$, $c$ be three non-collinear points in the Euclidean plane $\mathbb{R}^2$. Let:
- $m_{ab}$, $m_{bc}$, $m_{ca}$ be the midpoints of sides $ab$, $bc$, and $ca$ respectively
- $(n_{center}, n_{radius})$ be the center and radius of the circle passing through these midpoints (nine-point circle)
- $(i_{center}, i_{radius})$ be the center and radius of a circle tangent to all three sides of the triangle

Where the tangent circle satisfies:
- Points $a$, $b$, and the point of tangency $p_{ab}$ are collinear
- Points $b$, $c$, and the point of tangency $p_{bc}$ are collinear
- Points $a$, $c$, and the point of tangency $p_{ac}$ are collinear
- The vector from $i_{center}$ to each tangent point is orthogonal to the corresponding side

Then either:
1. The two circles are identical (same center and radius), or
2. There exists exactly one point where the two circles are tangent to each other.

### Informal proof
This is a proof of Feuerbach's theorem, which states that the nine-point circle of a triangle is tangent to the incircle and the three excircles.

The proof proceeds as follows:

- We begin by applying the `CIRCLES_TANGENT` theorem which states that two circles are either identical or tangent at exactly one point if and only if the distance between their centers equals the sum or difference of their radii.

- We consider the constraints that both radii must be non-negative.

- The proof then performs a geometric normalization by:
  1. Translating point $a$ to the origin
  2. Normalizing point $b$ (making its norm equal to 1)
  3. Aligning $b$ with a basis vector

- With this normalization, we express the constraints on:
  - The midpoints of the sides
  - The orthogonality conditions between tangent points and sides
  - The distances from the centers to the respective points

- The algebraic system is then solved using real arithmetic, establishing that the centers and radii satisfy the condition for tangent circles.

- The proof completes by confirming that either the circles are identical (when $n_{center} = i_{center}$ and $n_{radius} = i_{radius}$) or there exists exactly one point where the circles are tangent to each other.

### Mathematical insight
Feuerbach's theorem is a fascinating result in Euclidean geometry that establishes a remarkable connection between the nine-point circle and the inscribed/excircles of a triangle.

The nine-point circle passes through nine significant points of a triangle: the three midpoints of the sides, the three feet of the altitudes, and the three midpoints of the segments from each vertex to the orthocenter (the intersection of the three altitudes).

This theorem specifically proves that this nine-point circle is always tangent to four other important circles associated with the triangle:
- The inscribed circle (which lies inside the triangle and touches all three sides)
- The three excircles (each of which touches one side and the extensions of the other two sides)

The result is particularly elegant as it connects seemingly unrelated circle constructions within a triangle. It was discovered by Karl Wilhelm Feuerbach in 1822, and represents one of the most beautiful theorems in triangle geometry.

### Dependencies
- `CIRCLES_TANGENT`: A theorem establishing conditions for when two circles are tangent
- `DIST_POS_LE`: A property about non-negative distances
- `COLLINEAR_2`: A theorem about collinearity of two points
- `COLLINEAR_3_2D`: A theorem about collinearity of three points in 2D

### Porting notes
When porting this theorem:
1. Ensure your system has the necessary vector operations and geometry foundations, including:
   - Vector subtraction and addition
   - Dot product and orthogonality
   - Distance functions
   - Midpoint calculations
   - Collinearity definitions

2. The proof uses several geometric normalization techniques (shifting origin, basis alignment) which might need different approaches in other systems.

3. The final algebraic verification uses `REAL_RING`, which is a powerful automation tool in HOL Light. In other systems, you might need to expand the algebraic verification more explicitly or use a different automation mechanism.

---

## NINE_POINT_CIRCLE_1

### Name of formal statement
NINE_POINT_CIRCLE_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NINE_POINT_CIRCLE_1 = prove
 (`!a b c:real^2 mbc mac mab fbc fac fab ncenter nradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      collinear {a,b,fab} /\ orthogonal (a - b) (c - fab) /\
      collinear {b,c,fbc} /\ orthogonal (b - c) (a - fbc) /\
      collinear {c,a,fac} /\ orthogonal (c - a) (b - fac)
      ==> dist(ncenter,fab) = nradius /\
          dist(ncenter,fbc) = nradius /\
          dist(ncenter,fac) = nradius`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e <=> b /\ c /\ d /\ a /\ e`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC)) THEN
  ASM_REWRITE_TAC[dist; NORM_EQ_SQUARE; REAL_POS] THEN
  REWRITE_TAC[COLLINEAR_3_2D] THEN
  REWRITE_TAC[orthogonal; dist; NORM_POW_2] THEN
  ASM_REWRITE_TAC[midpoint] THEN
  REWRITE_TAC[DOT_2; DOT_LSUB; DOT_RSUB] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[] THEN CONV_TAC REAL_RING);;
```

### Informal statement
For any non-collinear points $a$, $b$, $c$ in $\mathbb{R}^2$, let:
- $m_{ab}$, $m_{bc}$, and $m_{ca}$ be the midpoints of sides $ab$, $bc$, and $ca$ respectively
- $f_{ab}$, $f_{bc}$, and $f_{ca}$ be the feet of the altitudes from $c$, $a$, and $b$ respectively
- $n_{center}$ be a point and $n_{radius}$ a positive real number

If $n_{center}$ is equidistant from the three midpoints $m_{ab}$, $m_{bc}$, and $m_{ca}$ with distance $n_{radius}$, and the altitude feet satisfy:
- $f_{ab}$ lies on line $ab$ with $(a-b) \perp (c-f_{ab})$
- $f_{bc}$ lies on line $bc$ with $(b-c) \perp (a-f_{bc})$
- $f_{ca}$ lies on line $ca$ with $(c-a) \perp (b-f_{ca})$

Then $n_{center}$ is also equidistant from the three altitude feet $f_{ab}$, $f_{bc}$, and $f_{ca}$ with the same distance $n_{radius}$.

### Informal proof
This is a partial verification of the nine-point circle theorem, specifically showing that the circle passing through the midpoints of the sides of a triangle also passes through the feet of the altitudes.

The proof proceeds by algebraic manipulation in Cartesian coordinates:

1. We start by assuming the hypotheses and focusing on the coordinate-wise expressions.

2. We transform the collinearity conditions into their 2D vector form, stating that points are collinear when they lie on the same line.

3. We convert the orthogonality conditions into dot product expressions: vectors are orthogonal when their dot product equals zero.

4. We expand the midpoint definitions, which are expressed as $\text{midpoint}(p,q) = \frac{p+q}{2}$.

5. We expand the distance expressions using the Euclidean norm: $\text{dist}(p,q) = \|p-q\|$.

6. We work with component-wise expressions of vectors, expanding dot products and vector operations in terms of their coordinates.

7. Finally, the proof is completed using algebraic manipulations in the ring of real numbers. The key insight is that the coordinates of the altitude feet and midpoints satisfy a relationship that forces them to be equidistant from the center of the nine-point circle.

### Mathematical insight
This theorem verifies part of the famous nine-point circle theorem in Euclidean geometry. The nine-point circle is a significant geometric construction that passes through nine special points of a triangle:
- The three midpoints of the sides
- The three feet of the altitudes
- The three midpoints of the line segments connecting each vertex to the orthocenter

This theorem specifically proves that if a circle passes through the three midpoints of the triangle sides, it must also pass through the feet of the three altitudes. This is remarkable because these six points seem unrelated at first glance.

The nine-point circle has numerous interesting properties and connections to other geometric concepts such as the Euler line, orthocenter, and circumcenter. In fact, the center of the nine-point circle lies on the Euler line of the triangle, halfway between the orthocenter and the circumcenter.

### Dependencies
- Definitions: `midpoint`, `collinear`, `orthogonal`, `dist`
- Theorems related to vector algebra: `COLLINEAR_3_2D`, `NORM_EQ_SQUARE`, `DOT_2`, `DOT_LSUB`, `DOT_RSUB`, etc.

### Porting notes
When porting to another system:
1. Ensure proper handling of vector operations in 2D Euclidean space
2. The proof relies heavily on algebraic simplifications in the real number field
3. The system should have good support for manipulating dot products and Euclidean norms
4. Notice that much of the proof is done by component-wise calculations, so systems with good support for coordinate-based reasoning will handle this more easily

---

## NINE_POINT_CIRCLE_2

### Name of formal statement
NINE_POINT_CIRCLE_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NINE_POINT_CIRCLE_2 = prove
 (`!a b c:real^2 mbc mac mab fbc fac fab ncenter nradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      collinear {a,b,fab} /\ orthogonal (a - b) (c - fab) /\
      collinear {b,c,fbc} /\ orthogonal (b - c) (a - fbc) /\
      collinear {c,a,fac} /\ orthogonal (c - a) (b - fac) /\
      collinear {oc,a,fbc} /\ collinear {oc,b,fac} /\ collinear{oc,c,fab}
      ==> dist(ncenter,midpoint(oc,a)) = nradius /\
          dist(ncenter,midpoint(oc,b)) = nradius /\
          dist(ncenter,midpoint(oc,c)) = nradius`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e <=> b /\ c /\ d /\ a /\ e`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC)) THEN
  ASM_REWRITE_TAC[dist; NORM_EQ_SQUARE; REAL_POS] THEN
  REWRITE_TAC[COLLINEAR_3_2D] THEN
  REWRITE_TAC[orthogonal; dist; NORM_POW_2] THEN
  ASM_REWRITE_TAC[midpoint] THEN
  REWRITE_TAC[DOT_2; DOT_LSUB; DOT_RSUB] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[] THEN CONV_TAC REAL_RING);;
```

### Informal statement
Let $a$, $b$, and $c$ be three non-collinear points in $\mathbb{R}^2$. Consider the following points:
- $m_{ab}$, $m_{bc}$, and $m_{ac}$ are the midpoints of sides $ab$, $bc$, and $ca$ respectively
- $f_{ab}$, $f_{bc}$, and $f_{ac}$ are the feet of the altitudes from vertices $c$, $a$, and $b$ respectively
- $o_c$ is the orthocenter (intersection of the three altitudes)

If $n_{center}$ is a point such that the distances from it to the three midpoints $m_{bc}$, $m_{ac}$, and $m_{ab}$ are all equal to $n_{radius}$, then the distances from $n_{center}$ to the midpoints of segments connecting the orthocenter $o_c$ to each of the three vertices $a$, $b$, and $c$ are also equal to $n_{radius}$.

### Informal proof
This theorem is about the nine-point circle in Euclidean geometry.

The proof uses algebraic manipulation in vector form:

1. We start by reordering assumptions and symmetrizing the midpoints using the properties $midpoint(a,b) = m_{ab}$, etc.

2. The proof expresses the distance equality as norm equalities: $||n_{center} - m_{bc}|| = n_{radius}$ and similar for other points.

3. The conditions about collinearity are rewritten using the 2D characterization of collinearity (three points are collinear if there exists $t$ such that one point is a linear combination of the other two).

4. The orthogonality conditions like "orthogonal $(a - b) (c - f_{ab})$" are expressed using the dot product: $(a - b) \cdot (c - f_{ab}) = 0$.

5. The midpoint formula is applied: $midpoint(p,q) = \frac{p + q}{2}$.

6. All vector operations are then expanded into their component form.

7. The final step converts the problem into algebraic equations that are solved using the REAL_RING tactic, which establishes the equality of the distances through algebraic simplification.

The proof is essentially algebraic verification that the properties of the nine-point circle hold given the geometric constraints established in the theorem statement.

### Mathematical insight
This theorem states a key property of the nine-point circle in Euclidean geometry, which is a circle that passes through nine significant points of a triangle:
1. The midpoints of the three sides
2. The feet of the three altitudes
3. The midpoints of the line segments from each vertex to the orthocenter

The theorem specifically demonstrates that if a circle passes through the midpoints of the sides of a triangle, it must also pass through the midpoints of the segments connecting each vertex to the orthocenter. This is one characterization of the nine-point circle.

The nine-point circle is a fundamental concept in triangle geometry. It always has a radius equal to half the radius of the circumscribed circle and its center is the midpoint between the orthocenter and the circumcenter of the triangle. This theorem captures part of what makes the nine-point circle special and unique.

### Dependencies
- Vector arithmetic operations in HOL Light
- Midpoint definitions and properties
- Collinearity and orthogonality properties in 2D Euclidean space

### Porting notes
When porting this theorem:
1. Ensure that definitions for midpoint, collinearity, orthogonality, and distance are properly established in the target system.
2. The proof relies heavily on algebraic manipulation, so the target system should have good support for algebraic simplification or ring solving tactics.
3. Vector operations and component-wise calculations are central to the proof approach.
4. The proof structure is essentially computational rather than geometric, so it might be more elegant in systems with better support for geometric reasoning to find a more geometric proof.

---

