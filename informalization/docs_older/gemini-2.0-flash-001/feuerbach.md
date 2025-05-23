# feuerbach.ml

## Overview

Number of statements: 4

`feuerbach.ml` formalizes Feuerbach's theorem. It resides within the geometry portion of HOL Light, building upon convex geometry results. The file likely contains definitions related to circles, triangles, and points relevant to Feuerbach's theorem, culminating in a formal proof of the theorem itself.


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
For all real numbers `r1` and `r2` and all points `c1` and `c2` in the real plane, if `r1` is non-negative, and `r2` is non-negative, and the distance between `c1` and `c2` is equal to the sum of `r1` and `r2` or the distance between `c1` and `c2` is equal to the absolute value of the difference between `r1` and `r2`, then either `c1` equals `c2` and `r1` equals `r2`, or there exists a point `x` in the real plane such that the distance between `c1` and `x` is equal to `r1` and the distance between `c2` and `x` is equal to `r2`.

### Informal sketch
The proof proceeds as follows:
- We begin by assuming without loss of generality that `r1` is less than or equal to `r2`.
- We split the proof into two cases, based on whether the distance between `c1` and `c2` is `r1 + r2` or `abs(r1 - r2)`.
- We then conduct case splits on `r1 = 0` and `r2 = 0`, handling these degenerate cases using `DIST_EQ_0`.
- For the remaining case (`r1 > 0` and `r2 > 0`), we split based on whether `dist(c1, c2) = r1 + r2` or `dist(c1, c2) = abs(r1 - r2)`.
- In the case where `dist(c1, c2) = r1 + r2`, we show that the point `x = c1 + r1 / (r1 + r2) * (c2 - c1)` satisfies the conditions `dist(c1, x) = r1` and `dist(c2, x) = r2`. We also need to show that x lies on the segment between c1 and c2 using `segment[c1,c2]`
- In the case where `dist(c1, c2) = abs(r1 - r2)`, we further split on whether `r1 = r2` or `r1 < r2`.
   - If `r1 = r2`, then, since `dist(c1,c2) = abs(r1 - r2) = 0`, we have `c1 = c2`.
   - If `r1 < r2`, we show that the point `x = c2 + r2 / (r2 - r1) * (c1 - c2)` satisfies the conditions `dist(c1, x) = r1` and `dist(c2, x) = r2`. We need to verify that `c1 IN segment[c2, y]`.

### Mathematical insight
This theorem provides an algebraic condition to determine when two circles are tangent. Given the radii `r1`, `r2` and centers `c1`, `c2` of two circles, the circles are tangent if the distance between their centers is either the sum or the absolute difference of their radii.  The theorem handles both external tangency (sum) and internal tangency (difference). The theorem also asserts, given the conditions, that such a point is expressible, as required by Feuerbach's theorem.

### Dependencies
- `Multivariate/convex.ml`
- `DIST_SYM`
- `REAL_ADD_SYM`
- `REAL_ABS_SUB`
- `DIST_EQ_0`
- `REAL_LE_LT`
- `EXISTS_UNIQUE`
- `NORM_MUL`
- `GSYM dist`
- `REAL_ABS_DIV`
- `REAL_ABS_NEG`
- `REAL_FIELD`
- `REAL_LT_IMP_LE`
- `REAL_LT_ADD`
- `GSYM BETWEEN_IN_SEGMENT`
- `between`
- `REAL_SUB_REFL`
- `REAL_SUB_LE`
- `REAL_SUB_RZERO`
- `VECTOR_MUL_LZERO`
- `VECTOR_ADD_RID`
- `VECTOR_MUL_LID`
- `REAL_SUB_0`

### Porting notes (optional)
- The proof relies on specific vector arithmetic rewrites and real field arithmetic simplifications. These may need to be adapted based on the capabilities of the target proof assistant.
- The tactic `ASM_CASES_TAC` is used extensively for case splitting on real number equalities. Ensure that the target system can handle similar case splits.
- The handling of `EXISTS_UNIQUE` might need adjustment depending on the target system's support for unique existential quantifiers.


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
Given points `a`, `b`, and `c` in the real plane such that `a`, `b`, and `c` are not collinear, and given `mbc`, `mac`, and `mab` as the midpoints of the line segments `b` to `c`, `a` to `c`, and `a` to `b` respectively, and given `ncenter` and `nradius` such that the distance from `ncenter` to `mbc` is `nradius`, the distance from `ncenter` to `mac` is `nradius`, and the distance from `ncenter` to `mab` is `nradius`, and given `icenter` and `iradius` such that the distance from `icenter` to `pbc` is `iradius`, the distance from `icenter` to `pac` is `iradius`, and the distance from `icenter` to `pab` is `iradius`, and given that `a`, `b`, and `pab` are collinear and the vector from `a` to `b` is orthogonal to the vector from `icenter` to `pab`, and that `b`, `c`, and `pbc` are collinear and the vector from `b` to `c` is orthogonal to the vector from `icenter` to `pbc`, and that `a`, `c`, and `pac` are collinear and the vector from `a` to `c` is orthogonal to the vector from `icenter` to `pac`, then either `ncenter` equals `icenter` and `nradius` equals `iradius`, or there exists a point `x` in the real plane such that the distance from `ncenter` to `x` is `nradius` and the distance from `icenter` to `x` is `iradius`.

### Informal sketch
The theorem states that the nine-point circle and the incircle (or one of the excircles) of a triangle are tangent.
The proof proceeds by:
- Assuming the negation of collinearity of `a`,`b`,`c` and the definitions of midpoints, radii, and points of tangency.
- Applying `CIRCLES_TANGENT`, likely a lemma stating general conditions for two circles to be tangent.
- Showing non- negativity of `nradius` and `iradius`.
- Rewriting distance and norms using `dist` and `NORM_EQ_SQUARE`.
- Normalizing by translating `a` to the origin and fixing `b` on the x-axis.
- Simplifying the expressions using vector algebra and coordinate representations.
- Reducing the goal to an algebraic equality involving the coordinates and radii.
- Proving this equality using real number arithmetic.

### Mathematical insight
Feuerbach's theorem is a classical result in Euclidean geometry. It states that the nine-point circle of a triangle is tangent to the incircle and the three excircles of the triangle. This constitutes a surprising connection between different elements of a triangle. More generally, the nine-point circle is tangent to every circle that is tangent to all three sides of the triangle.

### Dependencies
**Theorems:**
- `CIRCLES_TANGENT`

**Definitions:**
- `midpoint`
- `dist`
- `collinear`
- `orthogonal`

**Lemmas:**
- `NORM_EQ_SQUARE`
- `REAL_LE_ADD`
- `REAL_ABS_POS`
- `NORM_POW_2`
- `REAL_POW2_ABS`
- `COLLINEAR_3_2D`
- `DOT_2`
- `DOT_LSUB`
- `DOT_RSUB`

**Tactics**
- `GEOM_ORIGIN_TAC`
- `GEOM_NORMALIZE_TAC`
- `GEOM_BASIS_MULTIPLE_TAC`

### Porting notes (optional)
Porting this theorem to another proof assistant will likely involve:
- Defining the basic geometric concepts: points, distance, collinearity, orthogonality, midpoints, and circles.
- Defining the incircle, excircles, and nine-point circle.
- Recreating the proof strategy of normalizing the triangle by placing one vertex at the origin and another on the x-axis.
- The proof relies heavily on algebraic manipulation of real numbers and vectors. A proof assistant with strong automation for real arithmetic will be helpful.


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
For all points `a`, `b`, and `c` in the real plane `real^2`, and points `mbc`, `mac`, `mab`, `fbc`, `fac`, `fab`, `ncenter` in the real plane, and a real number `nradius`, if the following conditions hold:
1.  `a`, `b`, and `c` are not collinear.
2.  `mab` is the midpoint of `a` and `b`.
3.  `mbc` is the midpoint of `b` and `c`.
4.  `mac` is the midpoint of `c` and `a`.
5.  The distance between `ncenter` and `mbc` is `nradius`.
6.  The distance between `ncenter` and `mac` is `nradius`.
7.  The distance between `ncenter` and `mab` is `nradius`.
8.  `a`, `b`, and `fab` are collinear and the vectors `a` - `b` and `c` - `fab` are orthogonal.
9.  `b`, `c`, and `fbc` are collinear and the vectors `b` - `c` and `a` - `fbc` are orthogonal.
10. `c`, `a`, and `fac` are collinear and the vectors `c` - `a` and `b` - `fac` are orthogonal.

Then, the following conditions also hold:
1.  The distance between `ncenter` and `fab` is `nradius`.
2.  The distance between `ncenter` and `fbc` is `nradius`.
3.  The distance between `ncenter` and `fac` is `nradius`.

### Informal sketch
The theorem states that if a circle passes through the midpoints of the sides of a triangle, then it also passes through the feet of the altitudes of the triangle.
The proof proceeds by:
- Moving all assumptions into the assumptions list to be used for rewriting.
- Rewriting using definitions of `dist`, `NORM_EQ_SQUARE` and `REAL_POS` to transform distance calculations into squared norm calculations.
- Rewriting using the definition of `COLLINEAR_3_2D`, `orthogonal`, `dist` and `NORM_POW_2`.
- Rewriting using definition of `midpoint`, and expanding dot products using `DOT_2`, `DOT_LSUB`, `DOT_RSUB`.
- Expanding vector operations using `VECTOR_ADD_COMPONENT`, `VECTOR_SUB_COMPONENT`, `VECTOR_MUL_COMPONENT`, and `VEC_COMPONENT`.
- Simplifying using `SIMP_TAC` and applying the real field ring tactic `CONV_TAC REAL_RING` to prove the result.

### Mathematical insight
This theorem is a part of proving the existence and properties of the nine-point circle. The nine-point circle is a circle that can be constructed for any triangle. It passes through the midpoint of each side, the foot of each altitude, and the midpoint of the line segment from each vertex to the orthocenter. This theorem shows a step confirming that the circle defined by the midpoints also contains the feet.

### Dependencies
- `dist`
- `NORM_EQ_SQUARE`
- `REAL_POS`
- `COLLINEAR_3_2D`
- `orthogonal`
- `NORM_POW_2`
- `midpoint`
- `DOT_2`
- `DOT_LSUB`
- `DOT_RSUB`
- `VECTOR_ADD_COMPONENT`
- `VECTOR_SUB_COMPONENT`
- `VECTOR_MUL_COMPONENT`
- `VEC_COMPONENT`
- `TAUT`


---

## NINE_POINT_CIRCLE_2

### Name of formal statement
NINE_POINT_CIRCLE_2

### Type of the formal statement
Theorem

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
For all points `a`, `b`, and `c` in the real plane, and for all points `mbc`, `mac`, `mab`, `fbc`, `fac`, `fab`, `ncenter`, such that `a`, `b`, and `c` are not collinear, `mab` is the midpoint of `a` and `b`, `mbc` is the midpoint of `b` and `c`, `mac` is the midpoint of `c` and `a`, the distance from `ncenter` to `mbc` is `nradius`, the distance from `ncenter` to `mac` is `nradius`, the distance from `ncenter` to `mab` is `nradius`, `a`, `b`, and `fab` are collinear and the vector from `a` to `b` is orthogonal to the vector from `c` to `fab`, `b`, `c`, and `fbc` are collinear and the vector from `b` to `c` is orthogonal to the vector from `a` to `fbc`, `c`, `a`, and `fac` are collinear and the vector from `c` to `a` is orthogonal to the vector from `b` to `fac`,  `oc`, `a`, and `fbc` are collinear, `oc`, `b`, and `fac` are collinear, `oc`, `c`, and `fab` are collinear, then the distance from `ncenter` to the midpoint of `oc` and `a` is `nradius`, the distance from `ncenter` to the midpoint of `oc` and `b` is `nradius`, and the distance from `ncenter` to the midpoint of `oc` and `c` is `nradius`.

### Informal sketch
The theorem states that the nine points (midpoints of the sides, feet of the altitudes, and midpoints between orthocenter and vertices) of a non-degenerate triangle lie on a circle (the nine-point circle).
- Assume the non-collinearity of `a`, `b`, and `c`, the midpoint definitions, the equal distance conditions defining `ncenter` and `nradius` as the center and radius of this circle passing through the midpoints of the sides, the collinearity and orthogonality conditions defining the feet of the altitudes, and the collinearity conditions defining the orthocenter `oc`.
- Rewrite using definitions of `dist`, `midpoint`, `collinear`, and `orthogonal`.
- Simplify the resulting equations. The proof primarily relies on algebraic manipulation using real field properties to show that the distances from `ncenter` to the midpoints of `oc` and each vertex are equal to `nradius`. Specifically, the tactic `REAL_RING` is applied at the end to complete the proof.

### Mathematical insight
This theorem is a classic result in Euclidean geometry. The nine-point circle is a remarkable property of triangles; it shows that certain seemingly unrelated points are in fact concyclic. This is a fundamental fact when studying triangle geometry.

### Dependencies
- `midpoint`
- `dist`
- `COLLINEAR_3_2D`
- `orthogonal`
- `NORM_POW_2`
- `DOT_2`
- `DOT_LSUB`
- `DOT_RSUB`
- `VECTOR_ADD_COMPONENT`
- `VECTOR_SUB_COMPONENT`
- `VECTOR_MUL_COMPONENT`
- `VEC_COMPONENT`
- `NORM_EQ_SQUARE`
- `REAL_POS`


---

