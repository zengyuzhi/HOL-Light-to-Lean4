# isoperimetric.ml

## Overview

Number of statements: 14

The file `isoperimetric.ml` formalizes the isoperimetric inequality. It relies on results from `cauchy.ml` and `lpspaces.ml` within the Multivariate analysis library. The file likely contains definitions and theorems related to perimeter, area/volume, and the formal proof of the isoperimetric inequality itself.


## lemma1

### Name of formal statement
lemma1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let lemma1 = prove
 (`!g:real^1->real^2.
        simple_path g /\ pathfinish g = pathstart g /\
        convex(inside(path_image g))
        ==> convex hull (path_image g) = closure(inside(path_image g))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC[CONVEX_CLOSURE] THEN
    REWRITE_TAC[GSYM FRONTIER_UNION_INTERIOR] THEN
    ASM_SIMP_TAC[JORDAN_INSIDE_OUTSIDE] THEN SET_TAC[];
    MATCH_MP_TAC CLOSURE_MINIMAL THEN
    REWRITE_TAC[INSIDE_SUBSET_CONVEX_HULL] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_CONVEX_HULL; COMPACT_PATH_IMAGE;
                 SIMPLE_PATH_IMP_PATH]]);;
```

### Informal statement
For all functions `g` from real numbers to pairs of real numbers, if `g` is a simple path, the endpoint of `g` coincides with its start point, and the inside of the path's image under `g` is convex, then the convex hull of the path's image is equal to the closure of the inside of the path's image.

### Informal sketch
The proof proceeds by showing that each side of the equality is a subset of the other, and then joining the two subset relations.

*   First, we show that `convex hull (path_image g)` is a subset of `closure(inside(path_image g))`.
    *   We start by using the lemma stating that the convex hull is the minimal convex set containing `path_image g`.
    *   Then, we need to show that `closure(inside(path_image g))` is convex and contains `path_image g`. The convexity follows from the fact that closure of any convex set is convex.
    *   To show that `path_image g` is a subset of `closure(inside(path_image g))`, we need to show that `path_image g` is a subset of `frontier (inside(path_image g)) U inside(path_image g)`. This can be reduced to showing that `outside(path_image g)` and `inside(path_image g)` are disjoint.
    *   We use `JORDAN_INSIDE_OUTSIDE` and `FRONTIER_UNION_INTERIOR` to simplify.
*   Second, we show that `closure(inside(path_image g))` is a subset of `convex hull (path_image g)`.
    *   We know that the closure is the minimal closed set containing `inside(path_image g)`.
    *   Therefore we must show that `convex hull (path_image g)` is closed and contains `inside(path_image g)`.
    *   `inside(path_image g)` is a subset of `convex hull (path_image g)` because `inside(path_image g)` is a subset of `path_image g`.
    *   `convex hull (path_image g)` is closed because `convex hull (path_image g)` is compact. The compactness follows from the assumptions that `path_image g` is a compact set and the fact that the convex hull of a compact set is compact `COMPACT_CONVEX_HULL`. The other needed lemmas are `COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH`.

### Mathematical insight
This lemma relates the convex hull of a simple closed curve in the plane to the closure of the region enclosed by the curve, provided that the inside of the curve is convex. It's a step towards the isoperimetric inequality, linking geometric properties (convexity, area inside a curve) to the length of the curve.

### Dependencies
*   `Multivariate/cauchy.ml`
*   `Multivariate/lpspaces.ml`

**Theorems:**
*   `HULL_MINIMAL`
*   `CLOSURE_MINIMAL`
*   `COMPACT_IMP_CLOSED`

**Definitions:**
*   `simple_path`
*   `pathfinish`
*   `pathstart`
*   `convex`
*   `inside`
*   `path_image`
*   `convex hull`
*   `closure`
*   `FRONTIER_UNION_INTERIOR`
*   `JORDAN_INSIDE_OUTSIDE`
*   `INSIDE_SUBSET_CONVEX_HULL`
*   `COMPACT_CONVEX_HULL`
*   `COMPACT_PATH_IMAGE`
*   `SIMPLE_PATH_IMP_PATH`

**Tactics:**
*   `REPEAT STRIP_TAC`
*   `MATCH_MP_TAC`
*   `SUBSET_ANTISYM`
*   `CONJ_TAC`
*   `ASM_SIMP_TAC`
*   `REWRITE_TAC`
*   `SET_TAC`

**Conversion:**
*   `CONVEX_CLOSURE` (likely a conversion for simplifying expressions involving the convexity of a closure)

### Porting notes (optional)
*   The proof relies heavily on the Jordan curve theorem and properties of convex sets, which may need to be formalized separately in other proof assistants.
*   The tactics used give a good indication of the proof strategy but will need to be adapted to the specific automation available in the target proof assistant. The `ASM_SIMP_TAC` calls are places to examine for applicable background facts.
*   The use of `GSYM` to reverse the direction of equality `FRONTIER_UNION_INTERIOR` suggests that equalities might need to be massaged into the correct orientation.


---

## lemma2

### Name of formal statement
lemma2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let lemma2 = prove
 (`!g:real^1->real^2.
        simple_path g /\ pathfinish g = pathstart g /\
        convex(inside(path_image g))
        ==> frontier(convex hull (path_image g)) = path_image g`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lemma1; FRONTIER_CLOSURE_CONVEX] THEN
  ASM_SIMP_TAC[JORDAN_INSIDE_OUTSIDE]);;
```
### Informal statement
For any function `g` from real numbers to pairs of real numbers (i.e., `real^1->real^2`), if `g` defines a simple path and the endpoint of the path is equal to the starting point of the path and the inside of the path's image is convex, then the frontier of the convex hull of the path's image is equal to the path's image.

### Informal sketch
The proof proceeds by:
- Assuming the antecedents (`simple_path g`, `pathfinish g = pathstart g`, `convex(inside(path_image g))`).
- Simplifying using `lemma1` and `FRONTIER_CLOSURE_CONVEX`.
- Further simplification using `JORDAN_INSIDE_OUTSIDE`.
The overall strategy is to leverage existing lemmas about simple paths, convex sets, and the Jordan curve theorem to show that under the given conditions, the frontier of the convex hull of the path's image coincides with the path's image itself.

### Mathematical insight
This lemma relates the topological properties of a simple closed path in the plane to the convexity of its interior and the frontier of the convex hull of its image. It formalizes the intuition that for a simple closed curve with a convex interior, the curve itself forms the boundary of its convex hull. The condition `pathfinish g = pathstart g` encodes the "closed" part, and `simple_path` ensures the curve does not cross itself.

### Dependencies
- Theorems: `lemma1`, `FRONTIER_CLOSURE_CONVEX`, `JORDAN_INSIDE_OUTSIDE`


---

## lemma3

### Name of formal statement
lemma3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let lemma3 = prove
 (`!g:real^1->real^2.
        simple_path g /\
        pathfinish g = pathstart g /\
        path_image g SUBSET frontier (convex hull path_image g)
        ==> frontier (convex hull path_image g) = path_image g`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SET_RULE `t = s <=> s SUBSET t /\ ~(s PSUBSET t)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(inside(path_image g):real^2->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[JORDAN_INSIDE_OUTSIDE]; REWRITE_TAC[]] THEN
  MATCH_MP_TAC EMPTY_INSIDE_PSUBSET_CONVEX_FRONTIER THEN
  ASM_MESON_TAC[CONVEX_CONVEX_HULL]);;
```
### Informal statement
For all functions `g` from real numbers to pairs of real numbers, if `g` is a simple path, the endpoint of the path `g` is equal to the starting point of the path `g`, and the image of the path `g` is a subset of the frontier of the convex hull of the image of the path `g`, then the frontier of the convex hull of the image of the path `g` is equal to the image of the path `g`.

### Informal sketch
The proof proceeds by assuming that `g` is a simple path, `pathfinish g = pathstart g`, and `path_image g SUBSET frontier (convex hull path_image g)`. The goal is to show `frontier (convex hull path_image g) = path_image g`.

- First, rewrite the goal `frontier (convex hull path_image g) = path_image g` using the set equality rule `t = s <=> s SUBSET t /\ ~(s PSUBSET t)`.

- Then, consider the subgoal `~(inside(path_image g):real^2->bool = {})`, which says that the inside of the convex hull of the path image is not empty. 
  This step leverages `JORDAN_INSIDE_OUTSIDE` to establish that the inside is not empty.

- Next, apply `EMPTY_INSIDE_PSUBSET_CONVEX_FRONTIER`, which states that if the inside of a set `s` is non-empty, then `s` is not a proper subset of the frontier of the convex hull of `s`.

- Finally, use `CONVEX_CONVEX_HULL` and `ASM_MESON_TAC` to complete the proof.

### Mathematical insight
This theorem states that if a simple, closed path lies on the frontier of the convex hull of its image, then its image is exactly the frontier of that convex hull. Intuitively, this means that if a simple closed curve is "taut" with respect to its convex hull, then it forms the complete boundary of that convex hull.

### Dependencies
- `SET_RULE`
- `JORDAN_INSIDE_OUTSIDE`
- `EMPTY_INSIDE_PSUBSET_CONVEX_FRONTIER`
- `CONVEX_CONVEX_HULL`
- `simple_path`
- `pathfinish`
- `pathstart`
- `path_image`
- `frontier`
- `convex hull`
- `SUBSET`
- `PSUBSET`
- `inside`


---

## REAL_HOELDER_BOUND_2

### Name of formal statement
REAL_HOELDER_BOUND_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_HOELDER_BOUND_2 = prove
 (`!f s. real_measurable s /\
         f real_measurable_on s /\
         (\x. f x pow 2) real_integrable_on s
         ==> (real_integral s f) pow 2
             <= real_measure s * real_integral s (\x. f x pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `&2`]
        HOELDER_BOUND) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW; REAL_POW_1] THEN
  ASM_REWRITE_TAC[GSYM real_measurable_on; GSYM REAL_MEASURABLE_MEASURABLE;
                  GSYM ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_INTEGRABLE_ON]) THEN
  SIMP_TAC[o_DEF; NORM_1; LIFT_DROP; REAL_POW2_ABS] THEN
  DISCH_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; REAL_INTEGRABLE_ON; o_DEF] THEN
  REWRITE_TAC[GSYM REAL_MEASURE_MEASURE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_MEASURE_POS_LE] THEN
  REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2]);;
```

### Informal statement
For any function `f` and set `s`, if `s` is real measurable, `f` is real measurable on `s`, and the function mapping `x` to `f x` raised to the power of 2 is real integrable on `s`, then the square of the real integral of `f` on `s` is less than or equal to the product of the real measure of `s` and the real integral of the function mapping `x` to `f x` raised to the power of 2 on `s`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal.
- Apply `HOELDER_BOUND` after specializing it with `lift o f o drop`, `IMAGE lift s`, and `&2`. `HOELDER_BOUND` is likely a general Hölder inequality. This instantiation transforms the goal into a specific case.
- Use `REAL_RAT_REDUCE_CONV` to simplify rational numbers.
- Rewrite using assumptions such as `lspace`, `IN_ELIM_THM`, `RPOW_POW`, `REAL_POW_1`, `real_measurable_on`, `REAL_MEASURABLE_MEASURABLE`, and `ABSOLUTELY_REAL_INTEGRABLE_ON`. Some of these rewrites involve using the GSYM versions to reverse the direction of the rewriting.
- Eliminate an assumption related to `REAL_INTEGRABLE_ON`.
- Simplify using definitions of composition (`o_DEF`), normalization (`NORM_1`), `LIFT_DROP`, and `REAL_POW2_ABS`.
- Discharge the initial assumption, then split it into two assumptions using `CONJUNCTS_THEN2 ASSUME_TAC MP_TAC`.
- Simplify using the definition of `REAL_INTEGRAL` and the implication `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`.
- Simplify further with `REAL_INTEGRAL`, `REAL_INTEGRABLE_ON`, and `o_DEF`.
- Rewrite using the symmetric version of `REAL_MEASURE_MEASURE`.
- Apply a transitivity rule with `REAL_LE_TRANS` and `IMP_CONJ_ALT`.
- Apply `REAL_LE_LMUL` (multiplication on the left by a real number) combined with simplification based on `REAL_MEASURE_POS_LE`.
- Rewrite using `REAL_ARITH` to deal with absolute values.
- Apply `INTEGRAL_DROP_POS`.
- Rewrite with `LIFT_DROP` and `REAL_LE_POW_2`.

### Mathematical insight
This theorem is a specific instance of Hölder's inequality, likely for the case where p=q=2, which simplifies to a form of the Cauchy-Schwarz inequality for integrals. It provides an upper bound on the square of an integral of a function in terms of the product of the measure of the domain and the integral of the square of the function. This type of inequality is fundamental in real analysis and has applications in various areas of mathematics and physics.

### Dependencies
- `HOELDER_BOUND`
- `lspace`
- `IN_ELIM_THM`
- `RPOW_POW`
- `REAL_POW_1`
- `real_measurable_on`
- `REAL_MEASURABLE_MEASURABLE`
- `ABSOLUTELY_REAL_INTEGRABLE_ON`
- `REAL_INTEGRABLE_ON`
- `o_DEF`
- `NORM_1`
- `LIFT_DROP`
- `REAL_POW2_ABS`
- `REAL_INTEGRAL`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `REAL_MEASURE_MEASURE`
- `IMP_CONJ_ALT`
- `REAL_LE_TRANS`
- `REAL_LE_LMUL`
- `REAL_MEASURE_POS_LE`
- `REAL_ARITH`
- `INTEGRAL_DROP_POS`
- `REAL_LE_POW_2`


---

## WIRTINGER_INEQUALITY

### Name of formal statement
WIRTINGER_INEQUALITY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WIRTINGER_INEQUALITY = prove
 (`!f f'.
        (!x. x IN real_interval[&0,&2 * pi]
             ==> (f' has_real_integral (f x - f(&0))) (real_interval[&0,x])) /\
        f(&2 * pi) = f(&0) /\
        (f has_real_integral &0) (real_interval[&0,&2 * pi]) /\
        (\x. f'(x) pow 2) real_integrable_on real_interval[&0,&2 * pi]
        ==> (\x. f(x) pow 2) real_integrable_on real_interval[&0,&2 * pi] /\
            real_integral (real_interval[&0,&2 * pi]) (\x. f(x) pow 2) <=
            real_integral (real_interval[&0,&2 * pi]) (\x. f'(x) pow 2) /\
            (real_integral (real_interval[&0,&2 * pi]) (\x. f(x) pow 2) =
             real_integral (real_interval[&0,&2 * pi]) (\x. f'(x) pow 2)
             ==> ?c a. !x. x IN real_interval[&0,&2 * pi]
                           ==> f x = c * sin(x - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `f' real_integrable_on real_interval[&0,&2 * pi]`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&2 * pi`) THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL; IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN

  SUBGOAL_THEN `f' absolutely_real_integrable_on real_interval[&0,&2 * pi]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC `\x. &1 + (f':real->real) x pow 2` THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_CONST] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MP_TAC(SPEC `&1 - (f':real->real) x` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `&1 + (f':real->real) x` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `f real_continuous_on real_interval[&0,&2 * pi]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. real_integral (real_interval [&0,x]) f' + f(&0)` THEN
    ASM_SIMP_TAC[REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT;
                 REAL_CONTINUOUS_ON_ADD; REAL_CONTINUOUS_ON_CONST] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL]) THEN
    ASM_SIMP_TAC[REAL_SUB_ADD];
    ALL_TAC] THEN

  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN

  SUBGOAL_THEN
   `?a. &0 <= a /\ a < pi /\ f (a + pi):real = f(a)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. (f:real->real)(x + pi) - f x`; `&0`; `pi`; `&0`]
        REAL_IVT_INCREASING) THEN
    MP_TAC(ISPECL [`\x. (f:real->real)(x + pi) - f x`; `&0`; `pi`; `&0`]
        REAL_IVT_DECREASING) THEN
    ASM_SIMP_TAC[PI_POS_LE; REAL_ADD_LID; GSYM REAL_MUL_2] THEN
    REWRITE_TAC[REAL_SUB_LE; REAL_ARITH `a - b <= &0 <=> a <= b`] THEN
    MATCH_MP_TAC(TAUT
     `(q1 \/ q2) /\ p /\ (r ==> s)
      ==> (p /\ q1 ==> r) ==> (p /\ q2 ==> r) ==> s`) THEN
    REWRITE_TAC[REAL_LE_TOTAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[REAL_CONTINUOUS_ON_ADD; REAL_CONTINUOUS_ON_ID;
                 REAL_CONTINUOUS_ON_CONST] THEN
        ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
        REWRITE_TAC[GSYM REAL_INTERVAL_TRANSLATION];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        REAL_CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL; LEFT_IMP_EXISTS_THM; REAL_SUB_0]] THEN
    X_GEN_TAC `a:real` THEN ASM_CASES_TAC `a = pi` THENL
     [ASM_REWRITE_TAC[GSYM REAL_MUL_2] THEN
      DISCH_THEN(ASSUME_TAC o SYM o last o CONJUNCTS) THEN
      EXISTS_TAC `&0:real` THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
      REWRITE_TAC[REAL_LE_REFL; PI_POS];
      ASM_REWRITE_TAC[REAL_ARITH `a < pi <=> a <= pi /\ ~(a = pi)`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN

  (*** The auxiliary functions g and g' ***)

  MAP_EVERY ABBREV_TAC
   [`g = \x. (f(x) - f(a)) pow 2 / tan(x - a)`;
    `g' = \x. f'(x) pow 2 - (f(x) - f(a)) pow 2 -
              (f'(x) - (f(x) - f(a)) / tan(x - a)) pow 2`] THEN

  (*** The integral over completely trouble-free intervals ***)

  SUBGOAL_THEN
   `!c d. c <= d /\
          real_interval[c,d] SUBSET real_interval[&0,&2 * pi] /\
          (!x. x IN real_interval[c,d] ==> ~(sin(x - a) = &0))
          ==> (g' has_real_integral g d - g c) (real_interval[c,d])`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["g"; "g'"] THEN REWRITE_TAC[real_div] THEN
    MP_TAC(ISPECL [`\x. ((f:real->real) x - f a) pow 2`; `\x. inv(tan(x - a))`;
                   `\x. &2 * ((f:real->real) x - f a) * f' x`;
                   `\x. --(inv(sin(x - a) pow 2))`;
                   `c:real`; `d:real`]
      ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[REAL_POW_2; REAL_ARITH `&2 * a * b = a * b + b * a`] THEN
        MATCH_MP_TAC ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM THEN
        ASM_REWRITE_TAC[REAL_ARITH `x - a - (c - a):real = x - c`] THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
          STRIP_TAC] THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          DISCH_TAC] THEN
        MP_TAC(SPECL [`f':real->real`; `&0:real`; `x:real`; `c:real`]
                 REAL_INTEGRAL_COMBINE) THEN
        SUBGOAL_THEN
         `(f' has_real_integral f c - f(&0)) (real_interval [&0,c]) /\
          (f' has_real_integral f x - f(&0)) (real_interval [&0,x])`
        MP_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          SIMP_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
          ASM_REAL_ARITH_TAC];

        REWRITE_TAC[absolutely_real_integrable_on; REAL_ABS_NEG] THEN
        REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_POW2_ABS] THEN
        REWRITE_TAC[REAL_INTEGRABLE_NEG_EQ; CONJ_ASSOC] THEN
        ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_NEG_EQ] THEN
        REWRITE_TAC[] THEN
        MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ q`) THEN CONJ_TAC THENL
         [DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
          ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN
          SIMP_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL];
          ALL_TAC] THEN
        X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        X_GEN_TAC `y:real` THEN STRIP_TAC THEN
        REWRITE_TAC[tan; REAL_INV_DIV; REAL_INV_INV] THEN
        REAL_DIFF_TAC THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          MP_TAC(SPEC `y - a:real` SIN_CIRCLE) THEN CONV_TAC REAL_FIELD]];
      DISCH_THEN(MP_TAC o SPEC `d:real` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[tan; real_div; REAL_INV_MUL; REAL_INV_INV] THEN
      MP_TAC(SPEC `x - a:real` SIN_CIRCLE) THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN

  (*** Continuity of g ***)

  SUBGOAL_THEN `g real_continuous_on real_interval[&0,&2 * pi]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `c:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "g" THEN
    REWRITE_TAC[tan; real_div; REAL_INV_MUL; REAL_INV_INV; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
      REAL_DIFFERENTIABLE_TAC] THEN
    ASM_CASES_TAC `sin(c - a) = &0` THENL
     [REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL];
      MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_POW THEN
        MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
        REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o
         GEN_REWRITE_RULE I [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
      REAL_DIFFERENTIABLE_TAC] THEN

    ASM_REWRITE_TAC[REAL_INV_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    ONCE_REWRITE_TAC[GSYM REALLIM_NULL_ABS] THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\x. abs((f x - f c) pow 2 * inv(sin(x - c)))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN EXISTS_TAC `&1:real` THEN
      REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; REAL_ABS_MUL] THEN STRIP_TAC THEN
      BINOP_TAC THENL
       [AP_TERM_TAC THEN
        SUBGOAL_THEN `c = a \/ c = a + pi \/ a = &0 /\ c = &2 * pi`
        MP_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        SUBGOAL_THEN
         `&0 < abs(c - a) /\ abs(c - a) < pi \/
          &0 < abs(--(c - a) + pi) /\ abs(--(c - a) + pi) < pi`
        MP_TAC THENL [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP SIN_POS_PI)) THEN
        REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[SIN_NEG; REAL_NEG_0; SIN_PERIODIC_PI; REAL_LT_REFL];
        REWRITE_TAC[REAL_ABS_INV] THEN AP_TERM_TAC THEN
        SUBST1_TAC(REAL_ARITH `x - a:real = (x - c) + (c - a)`) THEN
        ASM_REWRITE_TAC[SIN_ADD; REAL_MUL_RZERO; REAL_ADD_RID] THEN
        REWRITE_TAC[REAL_EQ_SQUARE_ABS] THEN
        MP_TAC(SPEC `c - a:real` SIN_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC REAL_RING];
      ALL_TAC] THEN
    REWRITE_TAC[REALLIM_NULL_ABS] THEN
    MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC
     `\x. real_integral (real_segment[c,x]) (\x. f' x pow 2) *
          abs((x - c) / sin(x - c))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN EXISTS_TAC `&1:real` THEN
      REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; REAL_ABS_MUL; real_div] THEN
      STRIP_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(real_integral (real_interval[&0,x]) f' -
                   real_integral (real_interval[&0,c]) f') pow 2` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN
         `(f' has_real_integral f c - f(&0)) (real_interval [&0,c]) /\
          (f' has_real_integral f x - f(&0)) (real_interval [&0,x])`
        MP_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          SIMP_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(real_integral (real_segment[c,x]) f') pow 2` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
        REWRITE_TAC[REAL_SEGMENT_INTERVAL] THEN COND_CASES_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH
           `y + z:real = x ==> abs(x - y) <= abs z`);
          MATCH_MP_TAC(REAL_ARITH
           `x + z:real = y ==> abs(x - y) <= abs z`)] THEN
        MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
        REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
              REAL_INTEGRABLE_SUBINTERVAL)) THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MP_TAC(ISPECL [`f':real->real`; `real_segment[c,x]`]
         REAL_HOELDER_BOUND_2) THEN
      REWRITE_TAC[REAL_MEASURABLE_REAL_SEGMENT] THEN
      REWRITE_TAC[REAL_MEASURE_REAL_SEGMENT] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE; ALL_TAC] THEN
      REWRITE_TAC[REAL_SEGMENT_INTERVAL] THEN COND_CASES_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
              REAL_INTEGRABLE_SUBINTERVAL)) THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN

    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 = &0 * abs(inv(&1))`] THEN
    MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REALLIM_WITHINREAL] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
       [`\x. (f':real->real) x pow 2`; `&0:real`; `&2 * pi`;
        `c:real`; `c:real`; `e:real`]
       REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_SUB_RZERO; REAL_SEGMENT_INTERVAL] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`c:real`; `x:real`]);
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `c:real`])] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_INTEGRAL_NULL; REAL_LE_REFL;
                   REAL_SUB_REFL; REAL_ABS_0; REAL_SUB_RZERO];

      MATCH_MP_TAC REALLIM_ABS THEN ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN
      MATCH_MP_TAC REALLIM_INV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
      MP_TAC REALLIM_SIN_OVER_X THEN
      REWRITE_TAC[REALLIM_ATREAL; REAL_SUB_RZERO] THEN MESON_TAC[]];
    ALL_TAC] THEN

  (*** The integral over mainly trouble-free intervals ***)

  SUBGOAL_THEN
   `!c d. c <= d /\
          real_interval[c,d] SUBSET real_interval[&0,&2 * pi] /\
          (!x. x IN real_interval(c,d) ==> ~(sin(x - a) = &0))
          ==> (g' has_real_integral g d - g c) (real_interval[c,d])`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN STRIP_TAC THEN

    SUBGOAL_THEN `g' absolutely_real_integrable_on real_interval[c,d]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMPROPER_SIMPLE THEN
      SUBGOAL_THEN
       `(\x. f' x pow 2) absolutely_real_integrable_on
        real_interval[&0,&2 * pi] /\
        (\x. (f x - f a) pow 2) absolutely_real_integrable_on
        real_interval[&0,&2 * pi]`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE THEN
        ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
        ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!u v. real_interval[u,v] SUBSET real_interval(c,d)
              ==> g' real_integrable_on real_interval[u,v]`
      ASSUME_TAC THENL
       [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN STRIP_TAC THENL
         [ASM_MESON_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_INTEGRABLE_ON_EMPTY];
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `v:real`]) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; SUBSET_REAL_INTERVAL] THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN STRIP_TAC THENL
         [ASM_MESON_TAC[REAL_INTERVAL_EQ_EMPTY;
                        ABSOLUTELY_REAL_INTEGRABLE_ON_EMPTY];
          ALL_TAC] THEN
        EXPAND_TAC "g'" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN CONJ_TAC THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE THEN
          ASM_REWRITE_TAC[REAL_LE_POW_2]] THEN
        MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
        EXISTS_TAC
         `\x. (f':real->real) x pow 2 - (f x - f a) pow 2 - g' x` THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL
         [EXPAND_TAC "g'" THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
          REPEAT(MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN CONJ_TAC) THEN
          ASM_SIMP_TAC[SUBSET_REAL_INTERVAL] THEN
          MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
        DISCH_TAC] THEN
      REWRITE_TAC[real_bounded; FORALL_IN_GSPEC] THEN
      MP_TAC(SPECL
       [`\x. abs((g:real->real) x)`; `real_interval[&0,&2 * pi]`]
        REAL_CONTINUOUS_ATTAINS_SUP) THEN
      ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_ON_ABS] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC
       `&2 * abs(abs((g:real->real) w) +
                 real_integral (real_interval[&0,&2 * pi])
                               (\x. f' x pow 2))` THEN
      MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN STRIP_TAC THENL
       [ASM_MESON_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_INTEGRAL_EMPTY; REAL_ARITH
          `abs(&0):real <= &2 * abs x`];
        ALL_TAC] THEN
      SUBGOAL_THEN
        `(\x. f' x pow 2) absolutely_real_integrable_on
         real_interval[u,v] /\
         (\x. (f x - f a) pow 2) absolutely_real_integrable_on
         real_interval[u,v] /\
         g' absolutely_real_integrable_on real_interval[u,v]`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SUBSET_REAL_INTERVAL] THEN CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_POS; REAL_ABS_POS;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   ABSOLUTELY_REAL_INTEGRABLE_ABS] THEN
      TRANS_TAC REAL_LE_TRANS
       `real_integral (real_interval [u,v]) (\x. &2 * f' x pow 2 - g' x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
        ASM_SIMP_TAC[REAL_ABS_POS; ABSOLUTELY_REAL_INTEGRABLE_ABS;
                     ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                     ABSOLUTELY_REAL_INTEGRABLE_SUB;
                     ABSOLUTELY_REAL_INTEGRABLE_LMUL] THEN
        EXPAND_TAC "g'" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 <= x /\ &0 <= y /\ &0 <= z
          ==> abs(x - y - z) <= &2 * x - (x - y - z)`) THEN
        REWRITE_TAC[REAL_LE_POW_2];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_SUB; REAL_INTEGRAL_LMUL;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_LMUL] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= x' /\ abs(g) <= &2 * abs b
        ==> &2 * x - g <= &2 * abs(abs b + x')`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
        ASM_SIMP_TAC[SUBSET_REAL_INTERVAL; REAL_LE_POW_2;
                     ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(g' has_real_integral g v - g u) (real_interval[u,v])`
      MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x) <= a /\ abs(y) <= a ==> abs(x - y) <= &2 * a`) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]] THEN

      ASM_CASES_TAC `c:real = d` THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL; REAL_SUB_REFL] THEN
      SUBGOAL_THEN `c:real < d` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_LT_LE]; ALL_TAC] THEN

    TRANS_TAC EQ_TRANS
     `real_integral (real_interval[c,(c+d) / &2]) g' +
      real_integral (real_interval[(c+d) / &2,d]) g'` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBST1_TAC(REAL_ARITH
     `(g:real->real) d - g c =
      (g((c + d) / &2) - g c) + (g d - g((c + d) / &2))`) THEN
    BINOP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THENL
     [SUBGOAL_THEN
        `(\x. real_integral(real_interval[x,(c + d) / &2]) g' -
             (g ((c + d) / &2) - g x))
         real_continuous_on (real_interval [c,(c + d) / &2])`
      MP_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THENL
         [MATCH_MP_TAC REAL_INDEFINITE_INTEGRAL_CONTINUOUS_LEFT THEN
          MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            REAL_CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]] THEN
      DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP
        (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`]
                REALLIM_UNIQUE)) THEN
      CONJ_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand)
           TRIVIAL_LIMIT_WITHIN_REALINTERVAL o rand o snd) THEN
        REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `(IN) ((c + d) / &2)`) THEN
        REWRITE_TAC[IN_SING; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REALLIM_EVENTUALLY THEN
        REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
        EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `(c + d) / &2`]) THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[REAL_SUB_REFL]] THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
        REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];

      SUBGOAL_THEN
        `(\x. real_integral(real_interval[(c + d) / &2,x]) g' -
             (g x - g((c + d) / &2)))
         real_continuous_on (real_interval [(c + d) / &2,d])`
      MP_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THENL
         [MATCH_MP_TAC REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
          MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            REAL_CONTINUOUS_ON_SUBSET)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]] THEN
      DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP
        (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`]
                REALLIM_UNIQUE)) THEN
      CONJ_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand)
           TRIVIAL_LIMIT_WITHIN_REALINTERVAL o rand o snd) THEN
        REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `(IN) ((c + d) / &2)`) THEN
        REWRITE_TAC[IN_SING; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REALLIM_EVENTUALLY THEN
        REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
        EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`(c + d) / &2`; `x:real`]) THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[REAL_SUB_REFL]] THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
        REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN

  (*** Now stitch a few intervals together ***)

  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`a + pi`; `&2 * pi`] th) THEN
    MP_TAC(SPECL [`a:real`; `a + pi`] th) THEN
    MP_TAC(SPECL [`&0:real`; `a:real`] th)) THEN
  MATCH_MP_TAC(TAUT
   `p1 /\ p2 /\ p3 /\ (q1 /\ q2 /\ q3 ==> r)
    ==> (p1 ==> q1) ==> (p2 ==> q2) ==> (p3 ==> q3) ==> r`) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
    REWRITE_TAC[SIN_NEG; REAL_NEG_EQ_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x - a = (x - (a + pi)) + pi`] THEN
    REWRITE_TAC[SIN_PERIODIC_PI; REAL_NEG_EQ_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o MATCH_MP
    (REWRITE_RULE[TAUT `p /\ q /\ r /\ s ==> t <=>
                        r /\ s ==> p /\ q ==> t`]
     HAS_REAL_INTEGRAL_COMBINE))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM IMP_CONJ_ALT]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (REWRITE_RULE[TAUT `p /\ q /\ r /\ s ==> t <=>
                        r /\ s ==> p /\ q ==> t`]
     HAS_REAL_INTEGRAL_COMBINE)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(a1 - a0) + (a2 - a1) + (a3 - a2):real = a3 - a0`] THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&2 * pi - a = &0 - a + &2 * pi`] THEN
  REWRITE_TAC[TAN_PERIODIC_NPI; REAL_SUB_REFL] THEN
  MAP_EVERY UNDISCH_TAC
   [`(\x. f x pow 2) real_integrable_on real_interval[&0,&2 * pi]`;
   `(\x. f' x pow 2) real_integrable_on real_interval[&0,&2 * pi]`] THEN
  REWRITE_TAC[real_integrable_on; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`i':real`; `i:real`] THEN
  GEN_REWRITE_TAC I [TAUT `p ==> q ==> r <=> p /\ q ==> p /\ q ==> r`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_SUB) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_SUB) THEN
  EXPAND_TAC "g'" THEN
  REWRITE_TAC[REAL_ARITH
   `x' pow 2 - x pow 2 - (x' pow 2 - (x - a) pow 2 - b):real =
    (a pow 2 + b) - (&2 * a) * x`] THEN
  MP_TAC(ASSUME
   `(f has_real_integral &0) (real_interval [&0,&2 * pi])`) THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * (f:real->real) a` o
      MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_ADD) THEN
  REWRITE_TAC[REAL_SUB_ADD; REAL_MUL_RZERO] THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_LE] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HAS_REAL_INTEGRAL_POS) THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_CASES_TAC `i':real = i` THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HAS_REAL_INTEGRAL_NEGLIGIBLE_EQ o
        lhand o snd) THEN
  SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SOS_EQ_0] THEN
  ASM_CASES_TAC `(f:real->real) a = &0` THEN ASM_REWRITE_TAC[] THENL
   [POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_0];
    REWRITE_TAC[IN_GSPEC; REAL_NEGLIGIBLE_REAL_INTERVAL] THEN
    REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC] THEN
  STRIP_TAC THEN

  (**** Prove equality with c * sin over the sub-intervals ***)

  SUBGOAL_THEN
   `!u v. &0 <= u /\ u < v /\ v <= &2 * pi /\
          (!x. u < x /\ x < v ==> ~(sin(x - a) = &0))
          ==> ?c. !x. u <= x /\ x <= v ==> f(x) = c * sin(x - a)`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?c. !x. u < x /\ x < v ==> f x = c * sin (x - a)`
    MP_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GSYM IN_REAL_INTERVAL] THEN
      GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_AGREE_ON_CLOSURE_INTERVAL THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          REAL_CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
        REAL_DIFFERENTIABLE_TAC]] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(y = &0) ==> (x = c * y <=> x / y = c)`] THEN
    REWRITE_TAC[MESON[]
     `(?c. !u. P u ==> f u = c) <=> (!u v. P u /\ P v ==> f u = f v)`] THEN
    MATCH_MP_TAC REAL_WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`f:real->real`; `\x. inv(sin(x - a))`;
                  `f':real->real`; `\x. --(cos(x - a) / sin(x - a) pow 2)`;
                  `x:real`; `y:real`]
       ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;

        X_GEN_TAC `z:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN
         `(f' has_real_integral f x - f(&0)) (real_interval[&0,x]) /\
          (f' has_real_integral f z - f(&0)) (real_interval[&0,z])`
        MP_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
          STRIP_TAC] THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          MP_TAC(SPECL [`f':real->real`; `&0:real`; `z:real`; `x:real`]
                  REAL_INTEGRAL_COMBINE) THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];

        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
        REAL_DIFFERENTIABLE_TAC THEN REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;

        X_GEN_TAC `z:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
        ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        STRIP_TAC THEN REAL_DIFF_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `y:real`))] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `x / x' = y / y' <=> &0 = y * inv y' - x * inv x'`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_UNIQUE) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HAS_REAL_INTEGRAL_NEGLIGIBLE)) THEN
    X_GEN_TAC `z:real` THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ONCE_REWRITE_TAC[DE_MORGAN_THM] THEN REWRITE_TAC[] THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[real_div; tan; REAL_INV_MUL; REAL_INV_INV; REAL_INV_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Two slightly different stitchings depending if a = 0 ***)

  SUBGOAL_THEN
   `!u v c. u <= v
            ==> real_integral(real_interval[u,v]) (\x. c * sin(x - a)) =
                c * (cos(u - a) - cos(v - a))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`\x. --(c * cos(x - a))`; `\x. c * sin(x - a)`;
            `u:real`; `v:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN

  ASM_CASES_TAC `a = &0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [REAL_ADD_LID; REAL_ADD_RID; REAL_SUB_RZERO]) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPECL [`pi`; `&2 * pi`] th) THEN
      MP_TAC(SPECL [`&0:real`; `pi`] th)) THEN
    MATCH_MP_TAC(TAUT
     `p1 /\ p2 /\ (q1 /\ q2 ==> r)
      ==> (p1 ==> q1) ==> (p2 ==> q2) ==> r`) THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MP_TAC(SPEC `x - pi` SIN_PERIODIC_PI) THEN
      REWRITE_TAC[REAL_SUB_ADD; REAL_SUB_RZERO] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `c1:real`) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_TAC `c2:real`) THEN

    SUBGOAL_THEN `c2:real = c1:real` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN
       `real_integral(real_interval[&0,pi]) f +
        real_integral(real_interval[pi,&2*pi]) f = &0`
      MP_TAC THENL
       [UNDISCH_TAC `(f has_real_integral &0) (real_interval[&0,&2 * pi])` THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
        W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_COMBINE o
            lhand o snd) THEN
        ANTS_TAC THENL
         [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `real_integral(real_interval[&0,pi]) f =
        real_integral(real_interval[&0,pi]) (\x. c1 * sin(x)) /\
        real_integral(real_interval[pi,&2*pi]) f =
        real_integral(real_interval[pi,&2*pi]) (\x. c2 * sin(x))`
      MP_TAC THENL
       [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th ->
        MP_TAC(SPECL [`pi`; `&2 * pi`; `c2:real`] th) THEN
        MP_TAC(SPECL [`&0:real`; `pi:real`; `c1:real`] th)) THEN
      REPLICATE_TAC 2
       (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[COS_0; COS_PI; COS_NPI] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `&0:real`] THEN X_GEN_TAC `x:real` THEN
    REPLICATE_TAC 2 (FIRST_X_ASSUM(MP_TAC o SPEC `x:real`)) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Now another stitching process ***)

  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`a + pi`; `&2 * pi`] th) THEN
    MP_TAC(SPECL [`a:real`; `a + pi`] th) THEN
    MP_TAC(SPECL [`&0:real`; `a:real`] th)) THEN
  MATCH_MP_TAC(TAUT
   `p1 /\ p2 /\ p3 /\ (q1 /\ q2 /\ q3 ==> r)
    ==> (p1 ==> q1) ==> (p2 ==> q2) ==> (p3 ==> q3) ==> r`) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
    REWRITE_TAC[SIN_NEG; REAL_NEG_EQ_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x - a = (x - (a + pi)) + pi`] THEN
    REWRITE_TAC[SIN_PERIODIC_PI; REAL_NEG_EQ_0] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `c1:real`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `c2:real`) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `c3:real`) THEN

  MP_TAC(REAL_RING
   `f(&2 * pi) = c3 * sin(&2 * pi - a) /\ f(&0) = c1 * sin(&0 - a) /\
    f(&2 * pi) = f(&0) /\ sin(&2 * pi - a) = sin(&0 - a) /\
    ~(sin(&0 - a) = &0)
    ==> c3 = c1`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM ACCEPT_TAC;
      REWRITE_TAC[REAL_ARITH `a - b:real = --b + a`] THEN
      REWRITE_TAC[SIN_PERIODIC; REAL_ADD_RID];
      ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
      REWRITE_TAC[SIN_NEG; REAL_NEG_EQ_0] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST_ALL_TAC] THEN

  SUBGOAL_THEN `c2:real = c1:real` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN
     `real_integral(real_interval[&0,a]) f +
      real_integral(real_interval[a,a+pi]) f +
      real_integral(real_interval[a+pi,&2*pi]) f = &0`
    MP_TAC THENL
     [UNDISCH_TAC `(f has_real_integral &0) (real_interval[&0,&2 * pi])` THEN
      REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_COMBINE o
          rand o lhand o snd) THEN
      ANTS_TAC THENL
       [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) REAL_INTEGRAL_COMBINE o
          lhand o snd) THEN
      ANTS_TAC THENL
       [REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `real_integral(real_interval[&0,a]) f =
      real_integral(real_interval[&0,a]) (\x. c1 * sin(x - a)) /\
      real_integral(real_interval[a,a+pi]) f =
      real_integral(real_interval[a,a+pi]) (\x. c2 * sin(x - a)) /\
      real_integral(real_interval[a+pi,&2*pi]) f =
      real_integral(real_interval[a+pi,&2*pi]) (\x. c1 * sin(x - a))`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`a + pi`; `&2 * pi`; `c1:real`] th) THEN
      MP_TAC(SPECL [`a:real`; `a + pi`; `c2:real`] th) THEN
      MP_TAC(SPECL [`&0:real`; `a:real`; `c1:real`] th)) THEN
    REPLICATE_TAC 3
     (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_ADD_SUB; COS_PI; REAL_SUB_REFL; COS_0] THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_ARITH `&2 * pi - a = --a + &2 * pi`] THEN
    REWRITE_TAC[COS_PERIODIC; COS_NEG] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `a:real`] THEN X_GEN_TAC `x:real` THEN
  REPLICATE_TAC 3 (FIRST_X_ASSUM(MP_TAC o SPEC `x:real`)) THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For all functions `f` and `f'`, if
1.  For all `x` in the real interval `[0, 2 * pi]`, `f'` has a real integral equal to `f(x) - f(0)` on the interval `[0, x]`, and
2.  `f(2 * pi) = f(0)`, and
3.  `f` has a real integral equal to `0` on the interval `[0, 2 * pi]`, and
4.  The function `\x. f'(x) pow 2` is real integrable on the interval `[0, 2 * pi]`,
then
1.  The function `\x. f(x) pow 2` is real integrable on the interval `[0, 2 * pi]`, and
2.  The real integral of `\x. f(x) pow 2` on `[0, 2 * pi]` is less than or equal to the real integral of `\x. f'(x) pow 2` on `[0, 2 * pi]`, and
3.  If the real integral of `\x. f(x) pow 2` on `[0, 2 * pi]` equals the real integral of `\x. f'(x) pow 2` on `[0, 2 * pi]`, then there exist real numbers `c` and `a` such that for all `x` in the interval `[0, 2 * pi]`, `f(x) = c * sin(x - a)`.

### Informal sketch
The proof of the Wirtinger inequality proceeds as follows:
- Assume the premises about `f` and `f'`.
- Show that `f'` is real integrable over `[0, 2 * pi]`.
- Show that `f'` is absolutely real integrable over `[0, 2 * pi]`.
- Show that `f` is real continuous on `[0, 2 * pi]`.
- Deduce that `\x. f(x) pow 2` is real integrable on `[0, 2 * pi]`.
- Show that there exist `a` such that `0 <= a` and `a < pi` and `f (a + pi) = f(a)`.

Then, for the core inequality:
- Define auxiliary functions `g` and `g'` involving `f`, `f'`, `a`, and trigonometric terms.
- Show that for any subinterval `[c, d]` of `[0, 2 * pi]` where `sin(x - a)` is non-zero, `g'` has a real integral equal to `g d - g c` over `[c, d]`. This step uses `ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM` and requires proving integrability conditions.
- Show that `g` is real continuous on `[0, 2 * pi]`.
- Extend the integrability result to intervals `[c, d]` where the interior `(c, d)` has `sin(x - a)` non-zero, using `ABSOLUTELY_REAL_INTEGRABLE_IMPROPER_SIMPLE`.
- Stitch together the integrals over intervals `[0, a]`, `[a, a + pi]`, and `[a + pi, 2 * pi]` to obtain an integral over `[0, 2 * pi]`, exploiting periodicity of `f` and trigonometric functions, and utilizing the assumption `(f has_real_integral &0) (real_interval [&0,&2 * pi])`.
- If equality holds between the integrals of `f(x)^2` and `f'(x)^2`, deduce that `f(a) = 0`.
- Prove that if the equality holds, then on each subinterval mentioned above, there exist `c` such that `f(x) = c * sin(x - a)`.
- Then there are two cases: if `a = 0` or `a != 0`. Stitch together again intervals `[0, pi]` and `[pi, 2 * pi]` or `[0, a]`, `[a, a + pi]` and `[a + pi, 2 * pi]` and show that `c2 = c1`.

### Mathematical insight
The Wirtinger inequality provides a lower bound on the L2 norm of the derivative of a periodic function with zero mean. Specifically, it states that the integral of the square of the function is bounded above by the integral of the square of its derivative. The equality condition reveals that the functions for which the bound is tight are sinusoidal functions. This inequality plays a significant role in Fourier analysis and has applications in various fields such as differential equations and signal processing.

### Dependencies
- **Real Analysis:**
    - `HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL`
    - `ABSOLUTELY_REAL_INTEGRABLE_INTEGRABLE_BOUND`
    - `REAL_CONTINUOUS_ON_EQ`
    - `REAL_INTEGRABLE_CONTINUOUS`
    - `REAL_CONTINUOUS_ON_POW`
    - `REAL_IVT_INCREASING`
    - `REAL_IVT_DECREASING`
    - `REAL_CONTINUOUS_ON_SUB`
    - `REAL_CONTINUOUS_ON_COMPOSE`
    - `REAL_CONTINUOUS_ON_ADD`
    - `REAL_CONTINUOUS_ON_ID`
    - `REAL_CONTINUOUS_ON_CONST`
    - `REAL_INTERVAL_TRANSLATION`
    - `ABSOLUTE_REAL_INTEGRATION_BY_PARTS_SUM`
    - `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`
    - `REAL_HOELDER_BOUND_2`
    - `REAL_MEASURABLE_REAL_SEGMENT`
    - `ABSOLUTELY_REAL_INTEGRABLE_IMPROPER_SIMPLE`
    - `REAL_CONTINUOUS_ATTAINS_SUP`
    - `REAL_INDEFINITE_INTEGRAL_CONTINUOUS`
    - `REAL_INDEFINITE_INTEGRAL_CONTINUOUS_LEFT`
    - `REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT`
    - `REAL_CONTINUOUS_AGREE_ON_CLOSURE_INTERVAL`
- **Trigonometry:**
    - `SIN_CIRCLE`
    - `SIN_POS_PI`
    - `SIN_NEG`
    - `SIN_PERIODIC_PI`
    - `SIN_PERIODIC_NPI`
    - `COS_0`
    - `COS_PI`
    - `COS_NPI`
    - `COS_PERIODIC`
    - `COS_NEG`
- **Basic Real Arithmetic & Ordering:**
    - `PI_POS`
    - `PI_POS_LE`
    - `REAL_ADD_LID`
    - `GSYM REAL_MUL_2`
    - `REAL_SUB_LE`
    - `REAL_ARITH a - b <= &0 <=> a <= b`
    - `IN_REAL_INTERVAL`
    - `LEFT_IMP_EXISTS_THM`
    - `REAL_SUB_0`
    - `REAL_LE_REFL`
    - `REAL_RING`
    - `REAL_LE_POW_2`
    - `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL`
    - `REAL_SUBSUMPTION_LE`
    - `REAL_MUL_ASSOC`
    - `REAL_ABS_MUL`
    - `REAL_LT_01`
    - `REAL_LE_RMUL`
    - `REAL_ABS_POS`
    - `REAL_POW2_ABS`
    - `REAL_SEGMENT_INTERVAL`
    - `REAL_ARITH abs(x - y) <= abs z`
    - `REAL_MUL_SYM`
    - `REAL_INTEGRAL_LE`
    - `REAL_ABS_POS`
    - `REAL_INTEGRAL_SUBSET_LE`
    - `REAL_LT_IMP_LE`
    - `REAL_INTEGRAL_NULL`
    - `REAL_SUB_REFL`
    - `REAL_ABS_0`
    - `REAL_SUB_RZERO`
    - `ABS REAL_SUBSUMPTION`
    - `REAL_ABS_NEG`
    - `IN_GSPEC`
    - `SUBSET_REAL_INTERVAL`
    - `REAL_MUL_RZERO`

### Porting notes (optional)
- The proof relies heavily on real analysis theorems in HOL Light. Ensure that the target proof assistant has similar theorems available or that they can be derived.
- The use of `REAL_ARITH` within tactics is common for simplifying inequalities and algebraic expressions. Ensure the target system has a corresponding automated tool for real arithmetic.
- The frequent use of `SUBGOAL_THEN`, `ASSUME_TAC`, and `STRIP_TAC` suggests a goal-directed proof style that should translate well to systems like Coq or Lean.
- Care may be needed when porting custom tactics like those using `GEN_REWRITE_TAC` and `ASM_CASES_TAC`, to ensure the same level of automation is achieved.


---

## SCALED_WIRTINGER_INEQUALITY

### Name of formal statement
SCALED_WIRTINGER_INEQUALITY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SCALED_WIRTINGER_INEQUALITY = prove
 (`!f f'.
      (!x. x IN real_interval[&0,&1]
           ==> (f' has_real_integral (f x - f(&0))) (real_interval[&0,x])) /\
      f(&1) = f(&0) /\
      (f has_real_integral &0) (real_interval[&0,&1]) /\
      (\x. f'(x) pow 2) real_integrable_on real_interval[&0,&1]
      ==> (\x. f(x) pow 2) real_integrable_on real_interval[&0,&1] /\
          real_integral (real_interval[&0,&1]) (\x. (&2 * pi * f(x)) pow 2) <=
          real_integral (real_interval[&0,&1]) (\x. f'(x) pow 2) /\
          (real_integral (real_interval[&0,&1]) (\x. (&2 * pi * f(x)) pow 2) =
           real_integral (real_interval[&0,&1]) (\x. f'(x) pow 2)
           ==> ?c a. !x. x IN real_interval[&0,&1]
                         ==> f x = c * sin(&2 * pi * x - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL
   [`(\x. f(inv(&2 * pi) * x)):real->real`;
    `(\x. inv(&2 * pi) * f'(inv(&2 * pi) * x)):real->real`]
   WIRTINGER_INEQUALITY) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      SUBGOAL_THEN `!x. x = inv(&2 * pi) * &2 * pi * x` MP_TAC THENL
       [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x / (&2 * pi)`) THEN
      SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
               PI_POS; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `inv(&2 * pi)` o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_STRETCH)) THEN
      ANTS_TAC THENL [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[IMAGE_STRETCH_REAL_INTERVAL; REAL_SUB_RZERO] THEN
      REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_MUL_RZERO; REAL_ADD_RID;
                  REAL_ABS_INV; REAL_INV_INV; REAL_ABS_MUL;
                  REAL_ABS_NUM; REAL_ABS_PI] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_IMP_LE; REAL_DIV_LMUL; PI_POS;
                   REAL_LT_IMP_NZ; REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
      COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `inv x * y:real = y / x`] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC];
      UNDISCH_TAC `(f:real->real) (&1) = f (&0)` THEN
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
      AP_TERM_TAC THEN MP_TAC PI_POS THEN CONV_TAC REAL_FIELD;
      FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2 * pi)` o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_STRETCH));
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2 * pi)` o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] REAL_INTEGRABLE_STRETCH))] THEN
    (ANTS_TAC THENL [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
     REWRITE_TAC[IMAGE_STRETCH_REAL_INTERVAL; REAL_SUB_RZERO] THEN
     REWRITE_TAC[REAL_INV_INV; REAL_MUL_RZERO; REAL_INTERVAL_EQ_EMPTY] THEN
     CONV_TAC REAL_RAT_REDUCE_CONV THEN
     COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN
     MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN

  MATCH_MP_TAC(TAUT
   `(p ==> p') /\ (p' ==> q ==> q') ==> (p /\ q ==> p' /\ q')`) THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `&2 * pi` o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] REAL_INTEGRABLE_STRETCH)) THEN
    REWRITE_TAC[IMAGE_STRETCH_REAL_INTERVAL; REAL_LE_INV_EQ] THEN
    ANTS_TAC THENL [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; GSYM REAL_NOT_LE; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC; MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC] THEN
    SIMP_TAC[PI_POS; REAL_LT_IMP_NZ; REAL_MUL_LINV; REAL_MUL_RZERO;
             REAL_FIELD `&0 < t ==> inv t * t * x = x`;
             REAL_ARITH `&0 < &2 * x <=> &0 < x`];
    DISCH_TAC] THEN

  SUBGOAL_THEN
   `real_integral (real_interval [&0,&2 * pi])
                  (\x. f (inv (&2 * pi) * x) pow 2) =
    real_integral (real_interval [&0,&1]) (\x. (&2 * pi * f x) pow 2) /
    (&2 * pi) /\
    real_integral (real_interval [&0,&2 * pi])
                  (\x. (inv (&2 * pi) * f' (inv (&2 * pi) * x)) pow 2) =
    real_integral (real_interval [&0,&1]) (\x. f' x pow 2) / (&2 * pi)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[REAL_POW_MUL; REAL_MUL_ASSOC; REAL_INTEGRAL_LMUL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC
       `(\x. f x pow 2) real_integrable_on real_interval[&0,&1]`;
      UNDISCH_TAC
       `(\x. f' x pow 2) real_integrable_on real_interval[&0,&1]`] THEN
    REWRITE_TAC[real_integrable_on] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` MP_TAC) THEN
    DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP REAL_INTEGRAL_UNIQUE th) THEN
      MP_TAC (SPEC `inv(&2 * pi)` (MATCH_MP
        (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_STRETCH) th))) THEN
    REWRITE_TAC[IMAGE_STRETCH_REAL_INTERVAL; REAL_LE_INV_EQ] THEN
    (ANTS_TAC THENL [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC]) THEN
    REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    (COND_CASES_TAC THENL
      [ALL_TAC; MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC]) THEN
    REWRITE_TAC[REAL_INV_INV; REAL_ABS_INV; REAL_ABS_NUM;
                REAL_ABS_MUL; REAL_ABS_PI] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID] THEN
    SIMP_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL; REAL_INTEGRAL_LMUL] THEN
    STRIP_TAC THEN MP_TAC PI_POS THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN

  MATCH_MP_TAC MONO_AND THEN
  SIMP_TAC[REAL_LE_DIV2_EQ; PI_POS; REAL_ARITH `&0 < &2 * x <=> &0 < x`;
           REAL_FIELD `&0 < z ==> (x / z = y / z <=> x = y)`] THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN(fun th ->
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN MP_TAC(SPEC `&2 * pi * x` th)) THEN
  ASM_SIMP_TAC[PI_POS; REAL_FIELD `&0 < pi ==> inv(&2 * pi) * &2 * pi * x = x`;
               REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_ARITH `&2 * pi * x <= &2 * pi <=> pi * x <= pi * &1`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
For all functions `f` and `f'` from real numbers to real numbers, if the following conditions hold:
1. For all `x` in the real interval `[0, 1]`, `f'` has a real integral on the interval `[0, x]` which equals `f(x) - f(0)`.
2. `f(1) = f(0)`.
3. `f` has a real integral of `0` on the interval `[0, 1]`.
4. The function `\x. f'(x) pow 2` is real integrable on the interval `[0, 1]`.

Then the following are true:
1. The function `\x. f(x) pow 2` is real integrable on the interval `[0, 1]`.
2. The real integral over the interval `[0, 1]` of the function `\x. (2 * pi * f(x)) pow 2` is less than or equal to the real integral over the interval `[0, 1]` of the function `\x. f'(x) pow 2`.
3. If the real integral over the interval `[0, 1]` of the function `\x. (2 * pi * f(x)) pow 2` is equal to the real integral over the interval `[0, 1]` of the function `\x. f'(x) pow 2`, then there exist real numbers `c` and `a` such that for all `x` in the real interval `[0, 1]`, `f(x) = c * sin(2 * pi * x - a)`.

### Informal sketch
The proof proceeds by:
- Scaling the `WIRTINGER_INEQUALITY` theorem by substituting `f(inv(&2 * pi) * x)` for `f x` and `inv(&2 * pi) * f'(inv(&2 * pi) * x)` for `f' x`.
- Proving the antecedents of the scaled `WIRTINGER_INEQUALITY`. This involves showing that integrability and the integral conditions are satisfied for the scaled function. This involves using properties like `HAS_REAL_INTEGRAL_LMUL` and `HAS_REAL_INTEGRAL_STRETCH`.
- Applying a tautology to combine the integrability conditions.
- Proving that the integrals are related by scaling factors, using `REAL_INTEGRAL_STRETCH`.
- Applying monotonicity properties and arithmetic simplifications to derive the final result.

### Mathematical insight
The theorem is a scaled variant of Wirtinger's inequality. Wirtinger's inequality relates the integral of the square of a function to the integral of the square of its derivative, given some boundary conditions on the function. This scaled version adapts the inequality to the interval `[0, 1]` with a constant `2 * pi`. This is a fundamental result in Fourier analysis and has applications in various areas of mathematics and physics. The equality case characterizes the functions that achieve the lower bound.

### Dependencies
**Theorems and Definitions:**
- `WIRTINGER_INEQUALITY`
- `HAS_REAL_INTEGRAL_LMUL`
- `HAS_REAL_INTEGRAL_STRETCH`
- `IN_REAL_INTERVAL`
- `REAL_INTEGRAL_UNIQUE`
- `REAL_INTEGRABLE_STRETCH`
- `MONO_AND`
- `MONO_IMP`
- `MONO_EXISTS`

### Porting notes (optional)
This theorem relies heavily on the real analysis library of HOL Light, particularly the definitions and theorems related to real integrals and integrability. A port to another proof assistant will require equivalent definitions and theorems. The tactics used in the proof, such as `REPEAT GEN_TAC`, `STRIP_TAC`, `MP_TAC`, `REWRITE_TAC`, `ANTS_TAC`, `ASM_REAL_ARITH_TAC`, and `CONV_TAC`, will need to be translated into corresponding tactics or proof strategies in the target proof assistant. The extensive use of rewriting and simplification using real arithmetic tactics suggests that a good automated real arithmetic decision procedure is crucial for porting this proof.


---

## AREA_BELOW_ARCLET

### Name of formal statement
AREA_BELOW_ARCLET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AREA_BELOW_ARCLET = prove
 (`!(g:real^1->real^2) g' u v s.
    drop u <= drop v /\
    g u$1 <= g v$1 /\
    g absolutely_continuous_on interval[u,v] /\
    IMAGE g (interval[u,v]) SUBSET {z | &0 <= z$2} /\
    (!x y. x IN interval[u,v] /\ y IN interval[u,v] /\
           g x = g y ==> x = y) /\
    (!x y. x IN IMAGE g (interval[u,v]) /\ y IN IMAGE g (interval[u,v]) /\
           x$1 = y$1 ==> x = y) /\
    negligible s /\
    (!t. t IN interval[u,v] DIFF s
         ==> (g has_vector_derivative g'(t)) (at t))
    ==> measurable {z:real^2 | ?w. w IN IMAGE g (interval[u,v]) /\
                                   w$1 = z$1 /\ &0 <= z$2 /\ z$2 <= w$2} /\
        (\t. lift(g'(t)$1 * g(t)$2)) absolutely_integrable_on interval[u,v] /\
        integral (interval[u,v]) (\t. lift(g'(t)$1 * g(t)$2)) =
        lift(measure {z:real^2 | ?w. w IN IMAGE g (interval[u,v]) /\
                                     w$1 = z$1 /\ &0 <= z$2 /\ z$2 <= w$2})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INJECTIVE_ON_ALT] THEN STRIP_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE(ISPECL
   [`\t. lift((g:real^1->real^2)(t)$1)`; `interval[u:real^1,v]`]
   INJECTIVE_ON_LEFT_INVERSE))) THEN
  REWRITE_TAC[LIFT_EQ] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `h:real^1->real^1`) THEN
  ABBREV_TAC
   `ax = IMAGE (\t. (g:real^1->real^2)(t)$1) (interval[u,v])` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_CONTINUOUS_ON_IMP_CONTINUOUS)) THEN
  REWRITE_TAC[IS_INTERVAL_INTERVAL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\t. lift((g:real^1->real^2)(t)$1)`;
    `h:real^1->real^1`;
    `interval[u:real^1,v]`;
    `IMAGE lift ax`] CONTINUOUS_ON_INVERSE_INTO_1D) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN ANTS_TAC THENL
   [EXPAND_TAC "ax" THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC `f = \x. (g:real^1->real^2)(h(lift x))$2` THEN
  SUBGOAL_THEN `f real_continuous_on ax` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[u:real^1,v]` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "ax" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{z:real^2 | ?w:real^2. w IN IMAGE g (interval[u:real^1,v]) /\
                           w$1 = z$1 /\ &0 <= z$2 /\ z$2 <= w$2} =
    {z:real^2 | z$1 IN ax /\ &0 <= z$2 /\ z$2 <= f(z$1)}`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ax"; "f"] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`\t. lift((g:real^1->real^2)(t)$1)`;
                `interval[u:real^1,v]`]
        CONTINUOUS_INJECTIVE_IMP_MONOTONIC) THEN
  REWRITE_TAC[LIFT_DROP; IS_INTERVAL_INTERVAL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(q ==> p) /\ (p ==> r) ==> p \/ q ==> r`) THEN
  CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`v:real^1`; `u:real^1`]) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; IN_INTERVAL_1] THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `v <= u <=> u <= v ==> u = v`] THEN
    ASM_SIMP_TAC[DROP_EQ; REAL_NOT_LE; REAL_LE_ANTISYM] THEN
    MESON_TAC[REAL_LT_REFL];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `ax = real_interval[(g:real^1->real^2) u$1,g v$1]`
  SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`lift o (\t. (g:real^1->real^2)(t)$1)`;
                   `u:real^1`; `v:real^1`]
                  CONTINUOUS_INCREASING_IMAGE_INTERVAL_1) THEN
    ASM_REWRITE_TAC[IMAGE_o; o_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP; o_DEF] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[REAL_LE_LT; DROP_EQ] THEN ASM_MESON_TAC[]];
      DISCH_THEN(MP_TAC o AP_TERM `IMAGE drop`) THEN
      REWRITE_TAC[GSYM IMAGE_o; IMAGE_LIFT_DROP] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IMAGE_DROP_INTERVAL; LIFT_DROP]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE) THEN
  REWRITE_TAC[real_integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  MP_TAC(SPECL [`f:real->real`;
                `real_interval[(g:real^1->real^2) u$1,(g v)$1]`;
                `m:real`]
        HAS_REAL_INTEGRAL_AREA_UNDER_CURVE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`lift o f o drop`;
    `\t. lift((g:real^1->real^2)(t)$1)`;
    `\t. lift((g':real^1->real^2)(t)$1)`;
    `u:real^1`; `v:real^1`; `s:real^1->bool`]
   ABSOLUTE_INTEGRAL_SUBSTITUTION) THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; REAL_POS] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
      ASM_REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; GSYM REAL_CONTINUOUS_ON];
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
       [ABSOLUTELY_CONTINUOUS_ON_COMPONENTWISE]) THEN
      REWRITE_TAC[DIMINDEX_2; ARITH];
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN
       `((g:real^1->real^2) has_vector_derivative g' x) (at x)`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
      SIMP_TAC[DIMINDEX_2; ARITH];
      REWRITE_TAC[REAL_LE_LT; DROP_EQ] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_INTEGRABLE_EQ) THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC EQ_IMP] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL]) THEN
    SIMP_TAC[IMP_CONJ; REAL_INTEGRAL] THEN DISCH_TAC THEN
    REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; GSYM LIFT_EQ; LIFT_DROP]]);;
```

### Informal statement
For any function `g` from real numbers to pairs of real numbers (i.e., `real^1 -> real^2`), any real numbers `u` and `v`, and any set of real numbers `s`, if the following conditions hold:
1.  The real part of `u` is less than or equal to the real part of `v`.
2.  The real part of `g(u)` is less than or equal to the real part of `g(v)`.
3.  `g` is absolutely continuous on the interval `[u, v]`.
4.  The image of the interval `[u, v]` under `g` is a subset of the set of pairs of real numbers `z` where the imaginary part of `z` is greater than or equal to 0.
5.  `g` is injective on the interval `[u, v]`. That is, if `x` and `y` are in the interval `[u, v]` and `g(x) = g(y)`, then `x = y`.
6.  The projection of `g` is injective on the interval `[u, v]`. That is, if `x` and `y` are in the image of `g` on the interval `[u, v]` and the real parts of `x` and `y` are equal, then `x = y`.
7.  The set `s` is negligible.
8.  For all `t` in the interval `[u, v]` excluding `s`, `g` has a vector derivative `g'(t)` at `t`.
Then the following are true:
1.  The set of pairs of real numbers `z` such that there exists a `w` in the image of `g` on the interval `[u, v]` with the real part of `w` equal to the real part of `z`, the imaginary part of `z` is non-negative, and the imaginary part of `z` is less than or equal to the imaginary part of `w`, is measurable.
2.  The function that maps `t` to the real part of `g'(t)` times the imaginary part of `g(t)` is absolutely integrable on the interval `[u, v]`.
3.  The integral of the function that maps `t` to the real part of `g'(t)` times the imaginary part of `g(t)` over the interval `[u, v]` is equal to the measure of the set of pairs of real numbers `z` such that there exists a `w` in the image of `g` on the interval `[u, v]` with the real part of `w` equal to the real part of `z`, the imaginary part of `z` is non-negative, and the imaginary part of `z` is less than or equal to the imaginary part of `w`.

### Informal sketch
The proof proceeds by showing that under the given conditions, the area under the curve traced by `g` can be expressed as an integral. The main steps are as follows:

- Prove injectivity on the component `IMAGE (\t. (g:real^1->real^2)(t)$1) (interval[u,v])` using `INJECTIVE_ON_LEFT_INVERSE`.
- Define `ax` to be the image of the interval `[u,v]` under the projection of `g` onto the real axis.
- Use `CONTINUOUS_ON_INVERSE_INTO_1D` to establish continuity properties.
- Define a function `f` such that `f(x)` represents the second component of `g` evaluated at a specific point.
- Show that `f` is real continuous on `ax` using `REAL_CONTINUOUS_ON`, `CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE`, and `CONTINUOUS_ON_COMPOSE`.
- Show that the area under the curve is equivalent to the set `{z:real^2 | z$1 IN ax /\ &0 <= z$2 /\ z$2 <= f(z$1)}`.
- Use `CONTINUOUS_INJECTIVE_IMP_MONOTONIC` to prove that `g` is monotonic between `u` and `v`.
- Then show `ax = real_interval[(g:real^1->real^2) u$1,g v$1]` using `CONTINUOUS_INCREASING_IMAGE_INTERVAL_1`.
- Then show `f real_continuous_on ax` using `ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS`.
- Establish integrability of the relevant functions and apply the fundamental theorem of calculus to relate the integral to the area. Use theorem `HAS_REAL_INTEGRAL_AREA_UNDER_CURVE`.
- Apply `ABSOLUTE_INTEGRAL_SUBSTITUTION` to finish, along with lemmas about component-wise continuity and differentiability (`ABSOLUTELY_CONTINUOUS_ON_COMPONENTWISE`, `HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT`).

### Mathematical insight
This theorem provides a rigorous foundation for calculating the area under a curve defined by a parametric function `g` in the plane. It generalizes the standard integral formula for area under a curve to a setting where the x-coordinate is also parameterized, and where the function `g` is only required to be absolutely continuous. The key insight is to relate the area to the integral of `g'(t)$1 * g(t)$2` over the parameter interval `[u, v]`. This result is a special case of Green's theorem.
It's important in complex analysis, vector calculus and differential geometry to relate line integrals to area calculations.

### Dependencies

- **Real Analysis:**
    - `ABSOLUTELY_CONTINUOUS_ON_IMP_CONTINUOUS`
    - `CONTINUOUS_ON_INVERSE_INTO_1D`
    - `COMPACT_INTERVAL`
    - `CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE`
    - `CONTINUOUS_INJECTIVE_IMP_MONOTONIC`
    - `CONTINUOUS_INCREASING_IMAGE_INTERVAL_1`
    - `ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS`
    - `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
    - `HAS_REAL_INTEGRAL_AREA_UNDER_CURVE`
    - `ABSOLUTE_INTEGRAL_SUBSTITUTION`
    - `ABSOLUTELY_CONTINUOUS_ON_COMPONENTWISE`
    - `HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT`
    - `HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL`
    - `ABSOLUTELY_INTEGRABLE_EQ`
    - `REAL_CONTINUOUS_ON`
    - `HAS_VECTOR_DERIVATIVE_AT_WITHIN`

- **Basic Definitions/Theorems:**
    - `INTERVAL_NE_EMPTY_1`
    - `IMAGE_o`
    - `o_DEF`
    - `LIFT_DROP`
    - `IMAGE_DROP_INTERVAL`
    - `REAL_INTEGRAL`
    - `IMAGE_LIFT_REAL_INTERVAL`
    - `REAL_ARITH`
    - `DIMINDEX_2`
    - `ARITH`
    - `GSYM`
    - `INJECTIVE_ON_ALT`
    - `LIFT_EQ`
    - `IS_INTERVAL_INTERVAL`
    - `REAL_LE_REFL`
    - `IN_INTERVAL_1`
    - `REAL_NOT_LE`
    - `REAL_LE_ANTISYM`
    - `DROP_EQ`
    - `REAL_LT_REFL`
    - `SUBSET`
    - `FORALL_IN_IMAGE`
    - `EXISTS_IN_IMAGE`
    - `IMAGE_o`
    - `o_THM`
    - `LIFT_CMUL`
    - `REAL_POS`
    - `HAS_MEASURE_MEASURABLE_MEASURE`

### Porting notes (optional)
- The theorem relies heavily on real analysis concepts such as absolute continuity, integrability, measurability and derivatives. Ensure that the target proof assistant has adequate support for these concepts.
- The use of `lift` and `drop` functions to move between `real` and `real^2` might need adaptation depending on how tuples/vectors are handled in the target system.
- The tactic `ASM SET_TAC` is used for set-theoretic reasoning, so ensure the target system has good automation for set theory.
- HOL Light's `MESON_TAC` is a powerful automated theorem prover. You may need to manually decompose proofs that rely on it.


---

## AREA_ABOVE_ARCLET

### Name of formal statement
AREA_ABOVE_ARCLET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AREA_ABOVE_ARCLET = prove
 (`!(g:real^1->real^2) g' u v s.
    drop u <= drop v /\
    g v$1 <= g u$1 /\
    g absolutely_continuous_on interval[u,v] /\
    IMAGE g (interval[u,v]) SUBSET {z | z$2 <= &0} /\
    (!x y. x IN interval[u,v] /\ y IN interval[u,v] /\
           g x = g y ==> x = y) /\
    (!x y. x IN IMAGE g (interval[u,v]) /\ y IN IMAGE g (interval[u,v]) /\
           x$1 = y$1 ==> x = y) /\
    negligible s /\
    (!t. t IN interval[u,v] DIFF s
         ==> (g has_vector_derivative g'(t)) (at t))
    ==> measurable {z:real^2 | ?w. w IN IMAGE g (interval[u,v]) /\
                                   w$1 = z$1 /\ w$2 <= z$2 /\ z$2 <= &0} /\
        (\t. lift(g'(t)$1 * g(t)$2)) absolutely_integrable_on interval[u,v] /\
        integral (interval[u,v]) (\t. lift(g'(t)$1 * g(t)$2)) =
        lift(measure {z:real^2 | ?w. w IN IMAGE g (interval[u,v]) /\
                                     w$1 = z$1 /\ w$2 <= z$2 /\ z$2 <= &0})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(--) o (g:real^1->real^2)`;
    `(--) o (g':real^1->real^2)`;
    `u:real^1`; `v:real^1`; `s:real^1->bool`]
   AREA_BELOW_ARCLET) THEN
  ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_EQ_NEG2] THEN
    ASM_SIMP_TAC[o_DEF; HAS_VECTOR_DERIVATIVE_NEG; REAL_LE_NEG2;
                 ABSOLUTELY_CONTINUOUS_ON_NEG; VECTOR_NEG_COMPONENT] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r ==> s <=> p /\ q ==> r ==> s`] THEN
    ONCE_REWRITE_TAC[FORALL_IN_IMAGE_2] THEN
    ASM_REWRITE_TAC[REAL_EQ_NEG2; VECTOR_EQ_NEG2; IMP_IMP; GSYM CONJ_ASSOC;
                    VECTOR_NEG_COMPONENT] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `IMAGE f s SUBSET {x | P x} <=> s SUBSET {x | P(f x)}`] THEN
    ASM_REWRITE_TAC[REAL_NEG_GE0; VECTOR_NEG_COMPONENT];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
   `(?w:real^N. w IN IMAGE (--) s /\ P w) <=> (?w. w IN s /\ P(--w))`] THEN
  SUBGOAL_THEN `!P. {z:real^2 | P z} = IMAGE (--) {z | P(--z)}`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [MP_TAC(VECTOR_ARITH `!w:real^2. --(--w) = w`) THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MEASURABLE_NEGATIONS; MEASURE_NEGATIONS] THEN
  REWRITE_TAC[REAL_LE_NEG2; REAL_EQ_NEG2; VECTOR_NEG_COMPONENT] THEN
  REWRITE_TAC[REAL_NEG_GE0; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[CONJ_ACI]);;
```
### Informal statement
For any function `g` from real numbers to pairs of real numbers, and any functions `g'` from real numbers to pairs of real numbers, and any real numbers `u` and `v`, and any negligible set `s` of real numbers, if the following conditions hold:
1. `u` is less than or equal to `v`,
2. the first component of `g(v)` is less than or equal to the first component of `g(u)`,
3. `g` is absolutely continuous on the interval `[u, v]`,
4. the image of the interval `[u, v]` under `g` is a subset of the set of pairs `z` such that the second component of `z` is less than or equal to 0,
5. `g` is injective on the interval `[u, v]`,
6. the projection of `g` onto the first component is injective on the interval `[u, v]`,
7. `s` is a negligible set,
8. for all `t` in the interval `[u, v]` excluding `s`, `g` has vector derivative `g'(t)` at `t`,
then:
1. the set of pairs `z` such that there exists `w` in the image of the interval `[u, v]` under `g` with the first component of `w` equal to the first component of `z`, and the second component of `w` is less than or equal to the second component of `z`, which is less than or equal to 0, is measurable,
2. the function that maps `t` to `lift(g'(t)$1 * g(t)$2)` is absolutely integrable on the interval `[u, v]`,
3. the integral of the function `\t. lift(g'(t)$1 * g(t)$2)` over the interval `[u, v]` is equal to `lift(measure {z:real^2 | ?w. w IN IMAGE g (interval[u,v]) /\ w$1 = z$1 /\ w$2 <= z$2 /\ z$2 <= &0})`.

### Informal sketch
The proof relies on `AREA_BELOW_ARCLET`.
- First, the theorem `AREA_BELOW_ARCLET` is specialized to `-g`, `-g'`, `u`, `v`, and `s`.
- Then, assumptions about `g` are rewritten in terms of `-g` using vector negation properties and rules about `IMAGE` and subset relations.
- Next, a transformation involving `IMAGE` and negation is applied.
- Then, the statement `!P. {z:real^2 | P z} = IMAGE (--) {z | P(--z)}` is proven.
- The proof concludes by applying some rewriting steps using rules about measurability, measure, real numbers, and conjugation.

### Mathematical insight
This theorem relates the area above an arclet (a curve which lies below the x-axis) to the integral of a specific function involving the derivative and the function itself. Specifically, it states that under certain conditions of absolute continuity, injectivity, and differentiability almost everywhere, the area of the region bounded by the arclet and the x-axis can be computed as the integral of the product of the first component of the derivative of the curve and the second component of the curve. This provides a way to calculate area using integration, which is a fundamental concept in calculus and analysis.

### Dependencies
- `AREA_BELOW_ARCLET`
- `o_THM`
- `IMAGE_o`
- `VECTOR_EQ_NEG2`
- `o_DEF`
- `HAS_VECTOR_DERIVATIVE_NEG`
- `REAL_LE_NEG2`
- `ABSOLUTELY_CONTINUOUS_ON_NEG`
- `VECTOR_NEG_COMPONENT`
- `TAUT p /\ q /\ r ==> s <=> p /\ q ==> r ==> s`
- `FORALL_IN_IMAGE_2`
- `REAL_EQ_NEG2`
- `IMP_IMP`
- `GSYM CONJ_ASSOC`
- `SET_RULE IMAGE f s SUBSET {x | P x} <=> s SUBSET {x | P(f x)}`
- `REAL_NEG_GE0`
- `SET_RULE (?w:real^N. w IN IMAGE (--) s /\ P w) <=> (?w. w IN s /\ P(--w))`
- `VECTOR_ARITH !w:real^2. --(--w) = w`
- `MEASURABLE_NEGATIONS`
- `MEASURE_NEGATIONS`
- `REAL_MUL_LNEG`
- `REAL_MUL_RNEG`
- `REAL_NEG_NEG`
- `CONJ_ACI`


---

## GREEN_AREA_THEOREM

### Name of formal statement
GREEN_AREA_THEOREM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GREEN_AREA_THEOREM = prove
 (`!(g:real^1->real^2) g' u a b.
        simple_path g /\ pathstart g = a /\ pathfinish g = a /\
        b IN path_image g /\ a$1 < b$1 /\ a$2 = b$2 /\
        dist(a,b) = diameter(path_image g) /\
        convex(inside(path_image g)) /\
        g absolutely_continuous_on interval[vec 0,vec 1] /\
        negligible u /\
        (!t. t IN interval[vec 0,vec 1] DIFF u
             ==> (g has_vector_derivative g'(t)) (at t))
        ==> (\t. lift(g'(t)$1 * g(t)$2)) absolutely_integrable_on
            interval[vec 0,vec 1] /\
            norm(integral (interval[vec 0,vec 1])
                          (\t. lift(g'(t)$1 * g(t)$2))) =
            measure(inside(path_image g))`,

  (*** Make a the origin (automation doesn't handle integral so more work) ***)

  MATCH_MP_TAC(MESON[]
   `((!g g' u b. P g g' u (vec 0) b) ==> (!g g' u a b. P g g' u a b)) /\
    (!g g' u b. P g g' u (vec 0) b)
    ==> !g g' u a b. P g g' u a b`) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(\x. --a + x) o (g:real^1->real^2)`;
      `g':real^1->real^2`;
      `u:real^1->bool`; `--a + b:real^2`]) THEN
    ASM_REWRITE_TAC(!invariant_under_translation) THEN ANTS_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LINV; VEC_COMPONENT] THEN
      ASM_REWRITE_TAC[NORM_ARITH `dist(vec 0,--a + b) = dist(a,b)`] THEN
      REWRITE_TAC[VECTOR_NEG_COMPONENT; VECTOR_ADD_COMPONENT] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[ABSOLUTELY_CONTINUOUS_ISOMETRIC_COMPOSE;
                   NORM_ARITH `dist(--a + x,--a + y) = dist(x,y)`] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_LID] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
      ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `x * (--a + y):real = x * y - a * x`] THEN
    REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN MATCH_MP_TAC MONO_AND THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\t. (a:real^2)$2 % lift((g':real^1->real^2) t$1))
        absolutely_integrable_on interval [vec 0,vec 1]`
      MP_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LIFT_COMPONENT THEN
        REWRITE_TAC[DIMINDEX_2; ARITH] THEN MATCH_MP_TAC
          ABSOLUTELY_INTEGRABLE_ABSOLUTELY_CONTINUOUS_DERIVATIVE THEN
        ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN];
        REWRITE_TAC[GSYM IMP_CONJ_ALT]] THEN
      DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ADD) THEN
      REWRITE_TAC[VECTOR_SUB_ADD];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[integral] THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      SUBGOAL_THEN
       `((\t. (a:real^2)$2 % lift((g':real^1->real^2) t$1))
         has_integral a$2 % lift((pathfinish g:real^2)$1 - pathstart g$1))
        (interval[vec 0,vec 1])`
      MP_TAC THENL
       [MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
        REWRITE_TAC[pathstart; pathfinish; LIFT_SUB] THEN MATCH_MP_TAC
          FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS THEN
        EXISTS_TAC `u:real^1->bool` THEN
        ASM_SIMP_TAC[DROP_VEC; REAL_POS; DIMINDEX_2; ARITH;
                     ABSOLUTELY_CONTINUOUS_ON_LIFT_COMPONENT;
                     HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT;
                     HAS_VECTOR_DERIVATIVE_AT_WITHIN];
        ASM_REWRITE_TAC[REAL_SUB_REFL; LIFT_NUM; VECTOR_MUL_RZERO]] THEN
      DISCH_THEN(fun th -> EQ_TAC THEN MP_TAC th) THEN
      REWRITE_TAC[GSYM IMP_CONJ_ALT] THENL
       [DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD);
        DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB)] THEN
      REWRITE_TAC[VECTOR_SUB_ADD; VECTOR_ADD_RID; VECTOR_SUB_RZERO]];
    REWRITE_TAC[VEC_COMPONENT; REAL_ARITH `&0:real = x <=> x = &0`] THEN
    REWRITE_TAC[DIST_0]] THEN

  (*** WLOG assume we start with upper left-to-right part ***)

  MATCH_MP_TAC(MESON[]
   `!Q. ((!g g' u b t:real^1. Q g b t ==> P g g' u b)
         ==> (!g g' u b. P g g' u b)) /\
        (!g g' u b t. Q g b t ==> P g g' u b)
        ==> !g g' u b. P g g' u b`) THEN
  EXISTS_TAC
   `\g b t. &0 < drop t /\ drop t < &1 /\ g t = b /\
            IMAGE g (interval[vec 0:real^1,t]) SUBSET {z:real^2 | &0 <= z$2} /\
            IMAGE g (interval[t,vec 1]) SUBSET {z | z$2 <= &0}` THEN
  REWRITE_TAC[IMP_IMP] THEN CONJ_TAC THENL
   [DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ASSUME `(b:real^2) IN path_image g`) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [path_image; IN_IMAGE] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` (STRIP_ASSUME_TAC o GSYM)) THEN

    SUBGOAL_THEN `&0 < drop t /\ drop t < &1` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_LE] THEN
      ASM_REWRITE_TAC[DROP_EQ; GSYM DROP_VEC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
      ASM_MESON_TAC[VEC_COMPONENT; REAL_LT_REFL];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `IMAGE (g:real^1->real^2) (interval[vec 0,t]) SUBSET {z | &0 <= z$2} /\
      IMAGE (g:real^1->real^2) (interval[t,vec 1]) SUBSET {z | z$2 <= &0} \/
      IMAGE (g:real^1->real^2) (interval[vec 0,t]) SUBSET {z | z$2 <= &0} /\
      IMAGE (g:real^1->real^2) (interval[t,vec 1]) SUBSET {z | &0 <= z$2}`
    MP_TAC THENL
     [MP_TAC(ISPECL
       [`inside(path_image g):real^2->bool`; `vec 0:real^2`; `b:real^2`]
       CONVEX_OPEN_SEGMENT_CASES_ALT) THEN ASM_SIMP_TAC[GSYM lemma1] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[HULL_INC; PATHSTART_IN_PATH_IMAGE];
        ASM_SIMP_TAC[JORDAN_INSIDE_OUTSIDE; INTERIOR_OPEN; OPEN_INSIDE;
                     CLOSED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH]] THEN
      STRIP_TAC THENL
       [SUBGOAL_THEN
         `IMAGE (g:real^1->real^2) (interval[vec 0,t]) = segment[vec 0,b] \/
          IMAGE g (interval[t,vec 1]) = segment[vec 0,b]`
        MP_TAC THENL
         [SUBGOAL_THEN
           `connected_in (subtopology euclidean (path_image g))
                         (segment(vec 0:real^2,b))`
          MP_TAC THENL
           [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
            ASM_REWRITE_TAC[CONNECTED_IN_EUCLIDEAN; CONNECTED_SEGMENT];
            ALL_TAC] THEN
          REWRITE_TAC[CONNECTED_IN_EQ_SUBSET_SEPARATED_UNION] THEN
          DISCH_THEN(MP_TAC o SPECL
           [`IMAGE (g:real^1->real^2) (interval(vec 0,t))`;
            `IMAGE (g:real^1->real^2) (interval(t,vec 1))`] o CONJUNCT2) THEN
          REWRITE_TAC[separated_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
          REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
          ANTS_TAC THENL
           [REWRITE_TAC[GSYM CONJ_ASSOC] THEN ONCE_REWRITE_TAC[TAUT
             `p /\ q /\ r <=> (p /\ q) /\ (p /\ q ==> r)`] THEN
            CONJ_TAC THENL
             [REWRITE_TAC[path_image] THEN CONJ_TAC THEN
              MATCH_MP_TAC IMAGE_SUBSET THEN
              REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
              ASM_REAL_ARITH_TAC;
              SIMP_TAC[SET_RULE
                `s SUBSET t ==> s INTER t = s /\ t INTER s = s /\
                                s INTER t INTER u = s INTER u`] THEN
              STRIP_TAC] THEN
            REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
             [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
               `!t'. t SUBSET t' /\ s INTER t' = {} ==> s INTER t = {}`)
              THENL
               [EXISTS_TAC `IMAGE (g:real^1->real^2) (interval[t,vec 1])`;
                EXISTS_TAC `IMAGE (g:real^1->real^2) (interval[vec 0,t])`] THEN
              (CONJ_TAC THENL
               [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
                 [MATCH_MP_TAC IMAGE_SUBSET THEN
                  REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
                  ASM_REAL_ARITH_TAC;
                  MATCH_MP_TAC COMPACT_IMP_CLOSED] THEN
                MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
                REWRITE_TAC[COMPACT_INTERVAL] THEN
                MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
                EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
                ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; REAL_LE_REFL] THEN
                ASM_MESON_TAC[simple_path; path];
                REWRITE_TAC[SET_RULE
                 `IMAGE g s INTER IMAGE g t = {} <=>
                  !x y. x IN s /\ y IN t /\ g x = g y ==> F`] THEN
                MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
                REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
                FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`; `y:real^1`] o
                  CONJUNCT2 o GEN_REWRITE_RULE I [simple_path]) THEN
                ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
                ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; NOT_IMP] THEN
                ASM_REAL_ARITH_TAC]);
              UNDISCH_TAC `segment(vec 0:real^2,b) SUBSET path_image g` THEN
              REWRITE_TAC[open_segment; path_image; GSYM IMAGE_UNION] THEN
              MATCH_MP_TAC(SET_RULE
               `IMAGE g (i DIFF j) SUBSET t
                ==> s DIFF t SUBSET IMAGE g i
                    ==> s DIFF t SUBSET IMAGE g j`) THEN
              MATCH_MP_TAC SUBSET_TRANS THEN
              EXISTS_TAC `IMAGE (g:real^1->real^2) {vec 0,t,vec 1}` THEN
              CONJ_TAC THENL
               [MATCH_MP_TAC IMAGE_SUBSET THEN
                REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF; IN_INTERVAL_1;
                  IN_INSERT; DROP_VEC; GSYM DROP_EQ; NOT_IN_EMPTY] THEN
                REAL_ARITH_TAC;
                REWRITE_TAC[IMAGE_CLAUSES; INSERT_SUBSET; EMPTY_SUBSET] THEN
                RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
                ASM_REWRITE_TAC[IN_INSERT]]];
              REWRITE_TAC[open_segment; OPEN_CLOSED_INTERVAL_1]] THEN
          DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
           `s DIFF t SUBSET IMAGE g (i DIFF i') \/
            s DIFF t SUBSET IMAGE g (j DIFF j')
            ==> i' SUBSET i /\ j' SUBSET j /\
                t SUBSET IMAGE g i' /\ t SUBSET IMAGE g j'
                ==> s SUBSET IMAGE g i \/ s SUBSET IMAGE g j`)) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
            ASM_REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT] THEN
            ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_LE_REFL];
            ALL_TAC] THEN
          MATCH_MP_TAC MONO_OR THEN
          ASM_SIMP_TAC[GSYM PATH_IMAGE_SUBPATH; DROP_VEC] THEN
          CONJ_TAC THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
          MATCH_MP_TAC CONNECTED_SUBSET_PATH_IMAGE_ARC THEN
          ASM_REWRITE_TAC[CONNECTED_SEGMENT; PATHSTART_SUBPATH;
                          PATHFINISH_SUBPATH] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
          ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
          MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
          ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_LE_REFL; REAL_POS] THEN
          ASM_MESON_TAC[VEC_COMPONENT; REAL_LT_REFL];
          ALL_TAC] THEN
        DISCH_TAC THEN MP_TAC(ISPECL
         [`inside(path_image g):real^2->bool`;
          `vec 0:real^2`; `b:real^2`; `midpoint(vec 0,b):real^2`;
          `basis 2:real^2`; `&0:real`]
         CONVEX_TRIPLE_RELATIVE_FRONTIER) THEN
        ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[midpoint; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                          VEC_COMPONENT; CART_EQ; FORALL_2; DIMINDEX_2] THEN
          CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `segment[vec 0:real^2,b]` THEN
          REWRITE_TAC[GSYM midpoint; INSERT_SUBSET; EMPTY_SUBSET] THEN
          REWRITE_TAC[ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT] THEN
          ASM_SIMP_TAC[RELATIVE_FRONTIER_OPEN; JORDAN_INSIDE_OUTSIDE] THEN
          REWRITE_TAC[path_image] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
           (SET_RULE `IMAGE g s = v \/ IMAGE g t = v
            ==> s SUBSET u /\ t SUBSET u ==> v SUBSET IMAGE g u`)) THEN
          ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; REAL_LE_REFL];
          ALL_TAC] THEN
        DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP SUBSET_CLOSURE)) THEN
        SIMP_TAC[CLOSURE_CLOSED; CLOSED_HALFSPACE_COMPONENT_GE;
                 CLOSED_HALFSPACE_COMPONENT_LE] THEN
        ASM_SIMP_TAC[GSYM lemma1] THEN DISCH_THEN(MP_TAC o MATCH_MP
         (MESON[SUBSET_TRANS; HULL_SUBSET]
           `convex hull s SUBSET t ==> s SUBSET t`)) THEN
        (SUBGOAL_THEN
          `path_image g =
           IMAGE (g:real^1->real^2) (interval[vec 0,t]) UNION
           IMAGE (g:real^1->real^2) (interval[t,vec 1])`
         SUBST1_TAC THENL
          [REWRITE_TAC[GSYM IMAGE_UNION; path_image] THEN AP_TERM_TAC THEN
           REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN
           ASM_REAL_ARITH_TAC;
           SIMP_TAC[UNION_SUBSET; real_ge] THEN DISCH_THEN(K ALL_TAC)])
        THENL [ALL_TAC; ONCE_REWRITE_TAC[DISJ_SYM]] THEN
        POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_OR THEN
        CONJ_TAC THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
        ASM_REWRITE_TAC[VEC_COMPONENT; IN_ELIM_THM; REAL_LE_REFL] THEN
        REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE] THEN
        ONCE_REWRITE_TAC[GSYM real_ge] THEN
        REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE];

        SUBGOAL_THEN
         `IMAGE (g:real^1->real^2)
                (interval(vec 0,t) UNION interval(t,vec 1)) INTER
          {z | z$2 = &0} = {}`
        MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `s SUBSET inside p
            ==> inside p INTER p = {} /\ i SUBSET p /\ i INTER h SUBSET s
                ==> i INTER h = {}`)) THEN
          REWRITE_TAC[INSIDE_NO_OVERLAP] THEN CONJ_TAC THENL
           [REWRITE_TAC[path_image; IMAGE_UNION; UNION_SUBSET] THEN
            CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
            REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC[open_segment; OPEN_CLOSED_INTERVAL_1] THEN
          MATCH_MP_TAC(SET_RULE
           `((!w. w IN (i UNION j) /\ g w = b ==> w = y) /\
             (!w. w IN i /\ g w = a ==> w = x) /\
             (!w. w IN j /\ g w = a ==> w = z)) /\
            IMAGE g (i UNION j) INTER h SUBSET s
            ==> IMAGE g ((i DIFF {x,y}) UNION (j DIFF {y,z})) INTER h
                SUBSET s DIFF {a,b}`) THEN
          CONJ_TAC THENL
           [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; IN_UNION; GSYM DROP_EQ] THEN
            REPEAT CONJ_TAC THEN X_GEN_TAC `z:real^1` THEN STRIP_TAC THEN
            FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o
              GEN_REWRITE_RULE I [simple_path]) THEN
            RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THENL
             [DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `z:real^1`]);
              DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `z:real^1`]);
              DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `z:real^1`]);
              DISCH_THEN(MP_TAC o SPECL [`vec 0:real^1`; `z:real^1`])] THEN
            ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ] THEN
            ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN
           `IMAGE (g:real^1->real^2)
                  (interval[vec 0,t] UNION interval[t,vec 1]) =
            path_image g`
          SUBST1_TAC THENL
           [REWRITE_TAC[path_image] THEN AP_TERM_TAC THEN
            REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN
            ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
          X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
          SUBGOAL_THEN
           `dist(vec 0:real^2,z) <= norm(b:real^2) /\
            dist(b,z) <= norm(b:real^2)`
          MP_TAC THENL
           [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
            MATCH_MP_TAC DIST_LE_DIAMETER THEN
            ASM_SIMP_TAC[BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
            ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
            REWRITE_TAC[dist; NORM_LE_SQUARE]] THEN
          REWRITE_TAC[NORM_POS_LE; DOT_2; NORM_POW_2] THEN
          REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2] THEN
          ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                          VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN
          REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO; REAL_ADD_RID] THEN
          REWRITE_TAC[GSYM REAL_POW_2; GSYM REAL_LE_SQUARE_ABS] THEN
          REWRITE_TAC[REAL_ABS_NEG] THEN DISCH_THEN(MP_TAC o MATCH_MP
           (REAL_ARITH `abs z <= abs b /\ abs(b - z) <= abs b
                        ==> &0 < b ==> &0 <= z /\ z <= b`)) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
          EXISTS_TAC `(z:real^2)$1 / (b:real^2)$1` THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_DIV_RMUL;
                       REAL_LT_IMP_NZ] THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[IMAGE_UNION; EMPTY_UNION; SET_RULE
           `(s UNION t) INTER u = s INTER u UNION t INTER u`] THEN
          STRIP_TAC] THEN
        MATCH_MP_TAC(TAUT
           `(~(p1 /\ q2) /\ ~(p2 /\ q1)) /\ (p1 \/ p2) /\ (q1 \/ q2)
            ==> p1 /\ q1 \/ p2 /\ q2`) THEN
        CONJ_TAC THENL
         [REWRITE_TAC[GSYM UNION_SUBSET; GSYM IMAGE_UNION] THEN
          ASM_SIMP_TAC[UNION_INTERVAL_1; IN_INTERVAL_1; DROP_VEC] THEN
          REWRITE_TAC[GSYM path_image] THEN CONJ_TAC THEN
          DISCH_THEN(MP_TAC o SPEC `convex:(real^2->bool)->bool` o
           MATCH_MP HULL_MONO) THEN
          ASM_SIMP_TAC[REWRITE_RULE[pathstart; pathfinish] lemma1] THEN
          DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
          W(MP_TAC o PART_MATCH rand INSIDE_SUBSET_INTERIOR_CONVEX_HULL o
            lhand o lhand o snd) THEN
          REWRITE_TAC[IMP_IMP] THEN
          DISCH_THEN(MP_TAC o MATCH_MP SUBSET_TRANS) THEN
          SIMP_TAC[HULL_P; CONVEX_HALFSPACE_COMPONENT_LE;
                   REWRITE_RULE[real_ge] CONVEX_HALFSPACE_COMPONENT_GE;
                   REWRITE_RULE[real_ge] INTERIOR_HALFSPACE_COMPONENT_GE;
                  INTERIOR_HALFSPACE_COMPONENT_LE] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `s SUBSET i ==> ~(s SUBSET j) ==> ~(i SUBSET j)`)) THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          DISCH_THEN(MP_TAC o SPEC `midpoint(vec 0,b):real^2`) THEN
          REWRITE_TAC[MIDPOINT_IN_SEGMENT; NOT_IMP] THEN
          (CONJ_TAC THENL
            [ASM_MESON_TAC[VEC_COMPONENT; REAL_LT_REFL];
             REWRITE_TAC[midpoint; VECTOR_MUL_COMPONENT]]) THEN
          ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[CLOSED_OPEN_INTERVAL_1; DROP_VEC] THEN
        REWRITE_TAC[IMAGE_UNION; UNION_SUBSET; IMAGE_CLAUSES; INSERT_SUBSET;
                    IN_ELIM_THM; EMPTY_SUBSET] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
        ASM_REWRITE_TAC[VEC_COMPONENT; REAL_LE_REFL] THEN
        REWRITE_TAC[REAL_LE_LT] THEN CONJ_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `s SUBSET {x | P x} \/ s SUBSET {x | P' x}
          ==> s SUBSET {x | P x \/ Q x} \/ s SUBSET {x | P' x \/ Q' x}`) THEN
        MATCH_MP_TAC CONNECTED_IN_SUBSET_SEPARATED_UNION THEN
        EXISTS_TAC `euclidean:(real^2)topology` THEN
        ASM_SIMP_TAC[CONNECTED_IN_EUCLIDEAN; separated_in; SUBSET_UNIV;
                     EUCLIDEAN_CLOSURE_OF; TOPSPACE_EUCLIDEAN] THEN
        REWRITE_TAC[SET_RULE `{x | P x} UNION {x | Q x} = {x | P x \/ Q x}`;
                    REAL_ARITH `&0 < x \/ x < &0 <=> ~(x = &0)`;
                    REAL_ARITH `x < &0 \/ &0 < x <=> ~(x = &0)`] THEN
        ASM_REWRITE_TAC[SET_RULE
         `s SUBSET {x | ~P x} <=> s INTER {x | P x} = {}`] THEN
        ASM_SIMP_TAC[CLOSURE_HALFSPACE_COMPONENT_LT;
         REWRITE_RULE[real_ge; real_gt] CLOSURE_HALFSPACE_COMPONENT_GT] THEN
        REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        REWRITE_TAC[REAL_LET_ANTISYM; REAL_LTE_ANTISYM] THEN
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[CONNECTED_INTERVAL] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
        REWRITE_TAC[path] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`u:real^1->bool`; `b:real^2`; `t:real^1`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o SPECL
     [`reflect_along (basis 2) o (g:real^1->real^2)`;
      `reflect_along (basis 2) o (g':real^1->real^2)`;
       `u:real^1->bool`; `b:real^2`; `t:real^1`]) THEN
    ASM_REWRITE_TAC[o_THM; IMAGE_o] THEN
    MP_TAC(ISPEC `basis 2:real^2`
      ORTHOGONAL_TRANSFORMATION_REFLECT_ALONG) THEN
    DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP
      ORTHOGONAL_TRANSFORMATION_INJECTIVE) THEN
    REWRITE_TAC[INJECTIVE_ALT] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      ORTHOGONAL_TRANSFORMATION_SURJECTIVE) THEN
    ASM_SIMP_TAC(!invariant_under_linear) THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE
       `IMAGE f s SUBSET {x | P x} <=> s SUBSET {x | P(f x)}`] THEN
      REWRITE_TAC[IN_IMAGE; CART_EQ; FORALL_2; DIMINDEX_2] THEN
      ASM_SIMP_TAC[REFLECT_ALONG_BASIS_COMPONENT; VEC_COMPONENT;
                   DIMINDEX_2; ARITH; REAL_NEG_0] THEN
      ASM_REWRITE_TAC[REAL_NEG_LE0; REAL_NEG_GE0] THEN
      REWRITE_TAC[REAL_ARITH `&0 = --x <=> x = &0`] THEN
      ASM_SIMP_TAC[ABSOLUTELY_CONTINUOUS_ON_COMPOSE_LINEAR] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
      REWRITE_TAC[has_vector_derivative] THEN MP_TAC(ISPECL
       [`g:real^1->real^2`; `reflect_along (basis 2):real^2->real^2`;
        `\y. drop y % (g':real^1->real^2) x`;
        `reflect_along (basis 2):real^2->real^2`; `x:real^1`]
       DIFF_CHAIN_AT) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; GSYM has_vector_derivative] THEN
      REWRITE_TAC[has_vector_derivative; o_DEF] THEN
      ASM_SIMP_TAC[LINEAR_CMUL];

      ASM_SIMP_TAC[REFLECT_ALONG_BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
      REWRITE_TAC[REAL_MUL_RNEG; LIFT_NEG; IMP_CONJ] THEN
      SIMP_TAC[ABSOLUTELY_INTEGRABLE_NEG_EQ; INTEGRAL_NEG;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; NORM_NEG]];

    ALL_TAC] THEN

  REPEAT GEN_TAC THEN STRIP_TAC THEN

  SUBGOAL_THEN
   `!z. z IN path_image g ==> &0 <= (z:real^2)$1 /\ z$1 <= (b:real^2)$1`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `dist(vec 0:real^2,z) <= norm(b:real^2) /\
      dist(b,z) <= norm(b:real^2)`
    MP_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
     MATCH_MP_TAC DIST_LE_DIAMETER THEN
     ASM_SIMP_TAC[BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
     ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
     REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG] THEN
     DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
      `norm(z:real^2) <= b /\ norm(w:real^2) <= b
       ==> abs(z$1) <= norm z /\ abs(w$1) <= norm w
           ==> abs(z$1) <= b /\ abs(w$1) <= b`)) THEN
     REWRITE_TAC[COMPONENT_LE_NORM] THEN
     REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
     REWRITE_TAC[vector_norm; DOT_2] THEN
     ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
     REWRITE_TAC[GSYM REAL_POW_2; POW_2_SQRT_ABS] THEN
     ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN

  MP_TAC(SPECL [`g:real^1->real^2`; `g':real^1->real^2`;
                `t:real^1`; `vec 1:real^1`; `u:real^1->bool`]
        AREA_ABOVE_ARCLET) THEN
  MP_TAC(SPECL [`g:real^1->real^2`; `g':real^1->real^2`;
                `vec 0:real^1`; `t:real^1`; `u:real^1->bool`]
        AREA_BELOW_ARCLET) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(p1 /\ p2) /\ (q1 /\ q2 ==> r) ==> (p1 ==> q1) ==> (p2 ==> q2) ==> r`) THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN CONJ_TAC THEN
    (CONJ_TAC THENL
      [ASM_SIMP_TAC[REAL_LT_IMP_LE; VEC_COMPONENT; DROP_VEC]; ALL_TAC] THEN
     CONJ_TAC THENL
      [ASM_SIMP_TAC[REAL_LT_IMP_LE; VEC_COMPONENT]; ALL_TAC] THEN
     CONJ_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ABSOLUTELY_CONTINUOUS_ON_SUBSET)) THEN
       REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     CONJ_TAC THENL
      [MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
       REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[simple_path]) THEN
       DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `y:real^1`]) THEN
       ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; GSYM DROP_EQ] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     CONJ_TAC THENL
      [ALL_TAC;
       X_GEN_TAC `x:real^1` THEN
       REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; DROP_VEC] THEN
       STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; DROP_VEC] THEN
       ASM_REAL_ARITH_TAC] THEN
     MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
     ABBREV_TAC `c = (y:real^2)$1` THEN STRIP_TAC THEN
     GEN_REWRITE_TAC I [TAUT `p <=> ~p ==> F`] THEN DISCH_TAC THEN

     ASM_CASES_TAC `c:real = &0` THENL
      [SUBGOAL_THEN
        `dist(b:real^2,x) <= norm(b:real^2) /\
         dist(b:real^2,y) <= norm(b:real^2)`
       MP_TAC THENL
        [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
         MATCH_MP_TAC DIST_LE_DIAMETER THEN
         ASM_SIMP_TAC[BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
         REWRITE_TAC[path_image] THEN
         FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
          `w IN IMAGE g s ==> s SUBSET t ==> w IN IMAGE g t`)) THEN
         ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; REAL_LE_REFL] THEN
         ASM_REAL_ARITH_TAC;
         REWRITE_TAC[dist; NORM_LE_SQUARE]] THEN
       REWRITE_TAC[NORM_POS_LE; DOT_2; NORM_POW_2] THEN
       ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                       VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
       REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_LZERO; REAL_MUL_LZERO;
                   REAL_NEG_NEG; REAL_ADD_LID; REAL_MUL_LNEG;
                   REAL_MUL_RNEG; REAL_ADD_RID] THEN
       DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP
        (REAL_ARITH `b + x:real <= b ==> &0 <= x ==> x = &0`))) THEN
       REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE] THEN
       REPEAT STRIP_TAC THEN UNDISCH_TAC `~(x:real^2 = y)` THEN
       ASM_REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2];
       ALL_TAC] THEN

     ASM_CASES_TAC `c:real = (b:real^2)$1` THENL
      [SUBGOAL_THEN
        `dist(vec 0:real^2,x) <= norm(b:real^2) /\
         dist(vec 0:real^2,y) <= norm(b:real^2)`
       MP_TAC THENL
        [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
         MATCH_MP_TAC DIST_LE_DIAMETER THEN
         ASM_SIMP_TAC[BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
         (CONJ_TAC THENL
           [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; pathstart];
            ALL_TAC]) THEN
         REWRITE_TAC[path_image] THEN
         FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
          `w IN IMAGE g s ==> s SUBSET t ==> w IN IMAGE g t`)) THEN
         ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; REAL_LE_REFL] THEN
         ASM_REAL_ARITH_TAC;
         REWRITE_TAC[dist; NORM_LE_SQUARE]] THEN
       REWRITE_TAC[NORM_POS_LE; DOT_2; NORM_POW_2] THEN
       ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                       VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
       REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_LZERO; REAL_MUL_LZERO;
                   REAL_NEG_NEG; REAL_ADD_LID; REAL_MUL_LNEG;
                   REAL_MUL_RNEG; REAL_ADD_RID] THEN
       DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP
        (REAL_ARITH `b + x:real <= b ==> &0 <= x ==> x = &0`))) THEN
       REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE] THEN
       REPEAT STRIP_TAC THEN UNDISCH_TAC `~(x:real^2 = y)` THEN
       ASM_REWRITE_TAC[CART_EQ; FORALL_2; DIMINDEX_2];
       ALL_TAC] THEN

     SUBGOAL_THEN `&0 < c /\ c < (b:real^2)$1` STRIP_ASSUME_TAC THENL
      [ASM_REWRITE_TAC[REAL_LT_LE] THEN EXPAND_TAC "c" THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[path_image] THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `w IN IMAGE g s ==> s SUBSET t ==> w IN IMAGE g t`)) THEN
       ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; REAL_LE_REFL] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC])
    THENL
     [SUBGOAL_THEN
       `?z. z IN IMAGE (g:real^1->real^2) (interval(t,vec 1)) /\
            z$1 = c`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN MATCH_MP_TAC(SET_RULE
         `(?z. z IN IMAGE g s /\ P z) /\ ~P(g a) /\ ~P(g b)
          ==> ?z. z IN IMAGE g (s DIFF {a,b}) /\ P z`) THEN
        ASM_SIMP_TAC[VEC_COMPONENT; REAL_LT_IMP_NE] THEN

        MATCH_MP_TAC CONNECTED_IVT_COMPONENT THEN
        REWRITE_TAC[DIMINDEX_2; ARITH] THEN
        REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
        REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
        MAP_EVERY EXISTS_TAC [`vec 1:real^1`; `t:real^1`] THEN
        ASM_SIMP_TAC[IN_INTERVAL_1; DROP_VEC; REAL_LT_IMP_LE;
                     VEC_COMPONENT; REAL_LE_REFL] THEN
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[CONNECTED_INTERVAL] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
        REWRITE_TAC[path] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC];

      SUBGOAL_THEN
       `?z. z IN IMAGE (g:real^1->real^2) (interval(vec 0,t)) /\
            z$1 = c`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN MATCH_MP_TAC(SET_RULE
         `(?z. z IN IMAGE g s /\ P z) /\ ~P(g a) /\ ~P(g b)
          ==> ?z. z IN IMAGE g (s DIFF {a,b}) /\ P z`) THEN
        ASM_SIMP_TAC[VEC_COMPONENT; REAL_LT_IMP_NE] THEN

        MATCH_MP_TAC CONNECTED_IVT_COMPONENT THEN
        REWRITE_TAC[DIMINDEX_2; ARITH] THEN
        REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
        REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
        MAP_EVERY EXISTS_TAC [`vec 0:real^1`; `t:real^1`] THEN
        ASM_SIMP_TAC[IN_INTERVAL_1; DROP_VEC; REAL_LT_IMP_LE;
                     VEC_COMPONENT; REAL_LE_REFL] THEN
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[CONNECTED_INTERVAL] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
        REWRITE_TAC[path] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CONTINUOUS_ON_SUBSET) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC]] THEN
    (MP_TAC(ISPECL
       [`convex hull (path_image g:real^2->bool)`;
        `x:real^2`; `y:real^2`; `z:real^2`; `basis 1:real^2`; `c:real`]
       CONVEX_TRIPLE_RELATIVE_FRONTIER) THEN
     SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH] THEN
     ASM_REWRITE_TAC[CONVEX_CONVEX_HULL; NOT_IMP; GSYM CONJ_ASSOC] THEN
     SUBGOAL_THEN `relative_frontier (convex hull path_image g):real^2->bool =
                   path_image g`
     SUBST1_TAC THENL
      [TRANS_TAC EQ_TRANS
        `frontier(convex hull path_image g):real^2->bool` THEN
       CONJ_TAC THENL
        [ALL_TAC; ASM_SIMP_TAC[lemma2; pathstart; pathfinish]] THEN
       MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
       ASM_SIMP_TAC[lemma1; CONVEX_INTERIOR_CLOSURE; pathstart; pathfinish;
                    INTERIOR_OPEN; JORDAN_INSIDE_OUTSIDE];
       ALL_TAC] THEN
     CONJ_TAC THENL
      [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; path_image] THEN
       REPEAT CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
          `w IN IMAGE g s ==> s SUBSET t ==> w IN IMAGE g t`)) THEN
       ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; REAL_LE_REFL] THEN
       ASM_REAL_ARITH_TAC;
       GEN_REWRITE_TAC I [CONJ_ASSOC]] THEN
     CONJ_TAC THENL
      [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `z IN s ==> ~(x IN s) ==> ~(x = z)`)) THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `x IN s ==> DISJOINT s t ==> ~(x IN t)`)) THEN
       REWRITE_TAC[SET_RULE
        `DISJOINT (IMAGE f s) (IMAGE f t) <=>
         !x y. x IN s /\ y IN t ==> ~(f x = f y)`] THEN
       MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
       REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`; `y:real^1`] o
         CONJUNCT2 o GEN_REWRITE_RULE I [simple_path]) THEN
       ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
       ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; NOT_IMP] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN DISCH_THEN
      (MP_TAC o MATCH_MP (MESON[HULL_SUBSET; SUBSET_TRANS]
        `convex hull s SUBSET t ==> s SUBSET t`)) THEN
     REWRITE_TAC[SUBSET; NOT_FORALL_THM; IN_ELIM_THM] THENL
      [EXISTS_TAC `b:real^2` THEN ASM_REWRITE_TAC[REAL_NOT_LE];
       EXISTS_TAC `vec 0:real^2` THEN
       ASM_REWRITE_TAC[real_ge; NOT_IMP; REAL_NOT_LE; VEC_COMPONENT] THEN
       ASM_MESON_TAC[pathstart; PATHSTART_IN_PATH_IMAGE]]);

    ALL_TAC] THEN

  DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[HAS_ABSOLUTE_INTEGRAL] THEN MATCH_MP_TAC(TAUT
   `(p2 /\ p1 ==> p) /\ (q2 /\ q1 ==> q)
    ==> p1 /\ q1 ==> p2 /\ q2 ==> p /\ q`) THEN
  CONJ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_COMBINE THEN
    EXISTS_TAC `t:real^1` THEN ASM_SIMP_TAC[DROP_VEC; REAL_LT_IMP_LE];
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `p /\ q /\ r /\ s ==> t <=>
                         r /\ s ==> p /\ q ==> t`] HAS_INTEGRAL_COMBINE)) THEN
    ASM_SIMP_TAC[DROP_VEC; REAL_LT_IMP_LE]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM LIFT_ADD; NORM_LIFT] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ &0 <= y /\ x + y = z ==> abs(x + y) = z`) THEN
  ASM_SIMP_TAC[MEASURE_POS_LE] THEN

  W(MP_TAC o PART_MATCH (rand o rand) MEASURE_NEGLIGIBLE_UNION o
      lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{z:real^2 | z$2 = &0}` THEN
    REWRITE_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN

  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `measure(convex hull (path_image g):real^2->bool)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[lemma1] THEN MATCH_MP_TAC MEASURE_CLOSURE THEN
    ASM_SIMP_TAC[BOUNDED_INSIDE; BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH;
                 NEGLIGIBLE_CONVEX_FRONTIER]] THEN

  SUBGOAL_THEN
   `frontier(convex hull (path_image g)):real^2->bool = path_image g`
  ASSUME_TAC THENL [ASM_SIMP_TAC[lemma2]; ALL_TAC] THEN

  MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{z:real^2 | z$2 = &0}` THEN
  REWRITE_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. ~(x IN h) ==> (x IN s <=> x IN t))
    ==> s DIFF t UNION t DIFF s SUBSET h`) THEN

  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
  DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN
     (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC CONVEX_HULL_CONTAINS THEN
    MAP_EVERY EXISTS_TAC [`w:real^2`; `vector[(z:real^2)$1;&0]:real^2`] THEN
   (REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[path_image] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `y IN IMAGE f s ==> s SUBSET t ==> y IN IMAGE f t`)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;

      MATCH_MP_TAC CONVEX_HULL_CONTAINS THEN
      MAP_EVERY EXISTS_TAC [`vec 0:real^2`; `b:real^2`] THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[HULL_INC; PATHSTART_IN_PATH_IMAGE;
                      PATHFINISH_IN_PATH_IMAGE];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
        VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      EXISTS_TAC `(z:real^2)$1 / (b:real^2)$1` THEN
      REWRITE_TAC[CONJ_ASSOC; REAL_MUL_RZERO; REAL_ADD_LID] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
      UNDISCH_THEN `(w:real^2)$1 = (z:real^2)$1` (SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[path_image] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `w IN IMAGE g s ==> s SUBSET t ==> w IN IMAGE g t`)) THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;

      ALL_TAC]) THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    ASM_REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                    VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]
    THENL
     [EXISTS_TAC `(z:real^2)$2 / (w:real^2)$2` THEN
      SUBGOAL_THEN `&0 < (w:real^2)$2` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC];
      EXISTS_TAC `--((z:real^2)$2) / --((w:real^2)$2)` THEN
      SUBGOAL_THEN `&0 < --((w:real^2)$2)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
     SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
     ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
     ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_NEG_GE0] THEN
     CONV_TAC REAL_FIELD;
    ALL_TAC] THEN

  DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `~(x:real = &0) ==> &0 < x \/ x < &0`))
  THENL [DISJ1_TAC; DISJ2_TAC] THEN
  MP_TAC(ISPECL
   [`convex hull (path_image g):real^2->bool`;
    `vector[(z:real^2)$1;&0]:real^2`; `z:real^2`]
    SEGMENT_OUT_TO_FRONTIER) THEN
  ASM_SIMP_TAC[CLOSURE_INC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [CART_EQ] THEN
  ASM_REWRITE_TAC[FORALL_2; VECTOR_2; DIMINDEX_2] THEN
  ASM_SIMP_TAC[BOUNDED_CONVEX_HULL; BOUNDED_PATH_IMAGE;
               SIMPLE_PATH_IMP_PATH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^2` THEN
  REWRITE_TAC[path_image] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_2; FORALL_2; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(z' = &0)
    ==> (z = (&1 - u) * z + u * w /\ z' = u * w' <=>
         ~(u = &0) /\ w = z /\ w' = z' / u)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  (MATCH_MP_TAC(TAUT `q /\ r /\ (r ==> p) ==> p /\ q /\ r`) THEN
   CONJ_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_LE] THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
     REWRITE_TAC[REAL_ARITH `z <= z * u <=> --z * u <= --z * &1`;
                 REAL_ARITH `z * u <= z <=> z * u <= z * &1`] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
     POP_ASSUM(K ALL_TAC) THEN POP_ASSUM(K ALL_TAC) THEN STRIP_TAC]) THEN
  UNDISCH_TAC `w IN IMAGE (g:real^1->real^2) (interval [vec 0,vec 1])` THEN
  (SUBGOAL_THEN
    `interval[vec 0:real^1,vec 1] = interval[vec 0,t] UNION interval[t,vec 1]`
   SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN
     ASM_REAL_ARITH_TAC;
     REWRITE_TAC[IMAGE_UNION; IN_UNION]]) THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;
```
### Informal statement
For any function `g` from real numbers to pairs of real numbers (i.e., real vectors in 2D space), and any function `g'` from real numbers to pairs of real numbers, and any set `u` of real numbers, and any points `a` and `b` in 2D space, if the following conditions hold:

1. `g` is a simple path,
2. the starting point of the path `g` is `a`,
3. the ending point of the path `g` is `a` (i.e., `g` is a closed path),
4. `b` is in the image of the path `g`,
5. the first component of `a` is less than the first component of `b`,
6. the second component of `a` equals the second component of `b`,
7. the distance between `a` and `b` is equal to the diameter of the image of the path `g`,
8. the inside of the image of the path `g` is convex,
9. `g` is absolutely continuous on the interval from the vector (0, 0) to the vector (1, 1),
10. `u` is a negligible set of real numbers,
11. for all `t`, if `t` is in the interval from the vector (0, 0) to the vector (1, 1) excluding the set `u`, then `g` has vector derivative `g'(t)` at `t`,

then the function that maps `t` to the lift of the first component of `g'(t)` multiplied by the second component of `g(t)` is absolutely integrable on the interval from the vector (0, 0) to the vector (1, 1), and the norm of the integral of this function over the interval from the vector (0, 0) to the vector (1, 1) is equal to the measure of the inside of the image of the path `g`.

### Informal sketch
The proof proceeds as follows:
- First, without loss of generality, it's assumed that `a` (the starting and ending point of the curve) is the origin (0, 0). This is accomplished by translating the path `g` by `-a`. The theorem is shown to be invariant under translation.
- Then, it's argued (again, without loss of generality) that the path starts with a segment that moves upwards from the origin.
- The proof splits into cases depending on intermediate existential assumptions about image subset relationships.
- The areas above and below the curve with respect to the x-axis are considered. The difference of these areas equals the area inside the curve.
- The final step combines the integrability and integral results to obtain the Green's theorem statement for area.

### Mathematical insight
This theorem is a version of Green's theorem for the area of a region enclosed by a simple closed path `g`. It states that the area can be computed as the integral of a particular function involving the derivative of the path. The conditions ensure that the path is well-behaved (simple, closed, absolutely continuous) and the region it encloses is convex, which makes Green's theorem applicable. The condition `dist(a,b) = diameter(path_image g)` along with `a$1 < b$1 /\ a$2 = b$2` seems to specify that `b` is the rightmost point on the path when `a$2` (the y-coordinate of "a") is zero.

### Dependencies
* **Theorems/Definitions about paths:**
    * `simple_path`
    * `pathstart`
    * `pathfinish`
    * `path_image`
    * `convex`
    * `inside`
    * `absolutely_continuous_on`
    * `negligible`
    * `has_vector_derivative`
    * `absolutely_integrable_on`
    * `integral`
    * `measure`
* **Theorems about vector arithmetic and analysis:**
    * `VECTOR_ADD_LINV`
    * `VEC_COMPONENT`
    * `VECTOR_NEG_COMPONENT`
    * `VECTOR_ADD_COMPONENT`
    * `ABSOLUTELY_CONTINUOUS_ISOMETRIC_COMPOSE`
    * `NORM_ARITH`
    * `o_DEF`
    * `VECTOR_ADD_LID`
    * `HAS_VECTOR_DERIVATIVE_ADD`
    * `HAS_VECTOR_DERIVATIVE_CONST`
    * `LIFT_SUB`
    * `LIFT_CMUL`
    * `ABSOLUTELY_INTEGRABLE_CMUL`
    * `ABSOLUTELY_INTEGRABLE_LIFT_COMPONENT`
    * `DIMINDEX_2`
    * `ABSOLUTELY_INTEGRABLE_ABSOLUTELY_CONTINUOUS_DERIVATIVE`
    * `HAS_VECTOR_DERIVATIVE_AT_WITHIN`
    * `ABSOLUTELY_INTEGRABLE_ADD`
    * `EQ_IMP`
    * `HAS_INTEGRAL_CMUL`
    * `FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS`
    * `REAL_NEG`
    * `HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT`
    * `REAL_SUB_REFL`
    * `LIFT_NUM`
    * `VECTOR_MUL_RZERO`
    * `HAS_INTEGRAL_ADD`
    * `HAS_INTEGRAL_SUB`
    * `VECTOR_SUB_ADD`
    * `VECTOR_ADD_RID`
    * `VECTOR_SUB_RZERO`
    * `DIST_0`
* **Theorems for the proof structure**
    * `MESON`
    * `MATCH_MP_TAC`
    * `CONJ_TAC`
    * `DISCH_TAC`
    * `REPEAT GEN_TAC`
    * `STRIP_TAC`
    * `FIRST_X_ASSUM`
    * `MP_TAC`
    * `SPECL`
    * `ASM_REWRITE_TAC`
    * `ANTS_TAC`
    * `REWRITE_TAC`
    * `ASM_SIMP_TAC`
    * `GEN_REWRITE_TAC`
    * `LAND_CONV`
    * `SUBGOAL_THEN`
    * `EXISTS_TAC`
    * `IMP_IMP`
    * `GEN_REWRITE_TAC`
    * `TOP_DEPTH_CONV`
    * `IN_INTERVAL_1`
    * `DROP_VEC`
    * `X_CHOOSE_THEN`
    * `GSYM`
    * `REAL_LT_LE`
    * `DROP_EQ`
    * `REAL_LT_REFL`
    * `RULE_ASSUM_TAC`
    * `CONVEX_OPEN_SEGMENT_CASES_ALT`
    * `HULL_INC`
    * `PATHSTART_IN_PATH_IMAGE`
    * `JORDAN_INSIDE_OUTSIDE`
    * `INTERIOR_OPEN`
    * `OPEN_INSIDE`
    * `CLOSED_PATH_IMAGE`
    * `SIMPLE_PATH_IMP_PATH`
    * `CONNECTED_IN_SUBTOPOLOGY`
    * `CONNECTED_IN_EUCLIDEAN`
    * `CONNECTED_SEGMENT`
    * `CONNECTED_IN_EQ_SUBSET_SEPARATED_UNION`
    * `IMAGE_SUBSET`
    * `CLOSURE_OF_SUBTOPOLOGY`
    * `EUCLIDEAN_CLOSURE_OF`
    * `CONJ_ASSOC`
    * `TAUT`
    * `CLOSURE_MINIMAL`
    * `COMPACT_IMP_CLOSED`
    * `COMPACT_CONTINUOUS_IMAGE`
    * `COMPACT_INTERVAL`
    * `CONTINUOUS_ON_SUBSET`
    * `continuous`
    * `SET_RULE`
    * `IMAGE_CLAUSES`
    * `INSERT_SUBSET`
    * `EMPTY_SUBSET`
    * `OPEN_CLOSED_INTERVAL_1`
    * `CLOSED_HALFSPACE_COMPONENT_GE`
    * `ENDS_IN_SEGMENT`
    * `MIDPOINT_IN_SEGMENT`
    * `ENDS_IN_SEGMENT`
    * `MIDPOINT_IN_SEGMENT`
    * `RELATIVE_FRONTIER_OPEN`
    * `CONNECTED_SUBSET_PATH_IMAGE_ARC`
    * `PATHSTART_SUBPATH`
    * `PATHFINISH_SUBPATH`
    * `ENDS_IN_SEGMENT`
    * `ARC_SIMPLE_PATH_SUBPATH`
    * `IM_CONJ_ALT`
    * `AREA_ABOVE_ARCLET`
    * `AREA_BELOW_ARCLET`

### Porting notes (optional)
*   The extensive use of tactics like `ASM_REWRITE_TAC`, `ASM_SIMP_TAC`, and `MESON` suggests that this proof relies heavily on automation and simplification.  Porting this proof to a system with weaker automation might require significantly more manual effort.
*   The reliance on real analysis concepts (absolutely continuous functions, integrals) requires that the target proof assistant have a well-developed theory of real analysis.
*   The extensive use of `MESON` suggests that the proof relies heavily on automated first-order logic reasoning. Systems with weaker automated theorem proving capabilities may require more manual guidance.


---

## ISOPERIMETRIC_THEOREM_CONVEX

### Name of formal statement
ISOPERIMETRIC_THEOREM_CONVEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOPERIMETRIC_THEOREM_CONVEX = prove
 (`!L g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        convex(inside(path_image g)) /\
        path_length g = L
        ==> measure(inside(path_image g)) <= L pow 2 / (&4 * pi) /\
            (measure(inside(path_image g)) =  L pow 2 / (&4 * pi)
             ==> ?a r. path_image g = sphere(a,r))`,
  MAP_EVERY X_GEN_TAC [`L:real`; `g0:real^1->real^2`] THEN STRIP_TAC THEN

  (*** Scrub the degenerate cases and assume 0 < L ***)

  MP_TAC(ISPEC `g0:real^1->real^2` SIMPLE_PATH_LENGTH_POS_LT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** Rotate so that a diameter is horizontal ***)

  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
  MP_TAC(ISPEC `path_image g0:real^2->bool`
        DIAMETER_COMPACT_ATTAINED) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; PATH_IMAGE_NONEMPTY;
               COMPACT_PATH_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THEN
  ABBREV_TAC `baseline:real^2 = b - a` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `baseline:real^2` THEN
  X_GEN_TAC `baseline:real` THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= b <=> b = &0 \/ &0 < b`] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (VECTOR_ARITH
     `b - a:real^2 = &0 % c ==> b = a`)) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (NORM_ARITH
     `norm(a - a:real^2) = d ==> d = &0`)) THEN
    ASM_SIMP_TAC[DIAMETER_EQ_0; BOUNDED_PATH_IMAGE] THEN
    DISCH_THEN(REPEAT_TCL STRIP_THM_THEN
     (MP_TAC o AP_TERM `INFINITE:(real^2->bool)->bool`)) THEN
    ASM_SIMP_TAC[INFINITE_SIMPLE_PATH_IMAGE] THEN
    REWRITE_TAC[INFINITE; FINITE_EMPTY; FINITE_SING];
    REPEAT DISCH_TAC] THEN

  (*** Reparametrize to start and finish at the left of that diameter ***)

  MP_TAC(ASSUME `(a:real^2) IN path_image g0`) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [path_image] THEN
  REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN

  ABBREV_TAC `g1:real^1->real^2 = shiftpath t g0` THEN
  SUBGOAL_THEN
   `path_image g0 = path_image g1 /\
    rectifiable_path g1 /\
    simple_path g1 /\
    pathstart g1 = a /\
    pathfinish g1 :real^2 = a /\
    convex(inside(path_image g1)) /\
    path_length g1 = L`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[RECTIFIABLE_PATH_SHIFTPATH; SIMPLE_PATH_SHIFTPATH;
                 CLOSED_SHIFTPATH; PATH_IMAGE_SHIFTPATH;
                 PATH_LENGTH_SHIFTPATH] THEN
    EXPAND_TAC "a" THEN MATCH_MP_TAC PATHSTART_SHIFTPATH THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o
      check (free_in `g0:real^1->real^2` o concl))) THEN
    UNDISCH_THEN `(t:real^1) IN interval[vec 0,vec 1]` (K ALL_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH)] THEN

  (*** Reparametrize by arc length ***)

  MP_TAC(ISPEC `g1:real^1->real^2` ARC_LENGTH_REPARAMETRIZATION) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->real^2` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPLICATE_TAC 3
   (DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (free_in `g1:real^1->real^2` o concl))) THEN

  (*** Tweak so x = 0 at leftmost point and the average of y is zero ***)

  SUBGOAL_THEN
   `(\t. lift((g2:real^1->real^2)(t)$2)) integrable_on interval[vec 0,vec 1]`
  MP_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[GSYM dist];
    REWRITE_TAC[integrable_on; LEFT_IMP_EXISTS_THM]] THEN

  REWRITE_TAC[FORALL_LIFT] THEN X_GEN_TAC `av:real` THEN DISCH_TAC THEN

  ABBREV_TAC `origin:real^2 = vector[(a:real^2)$1;av]` THEN
  SUBGOAL_THEN `(origin:real^2)$1 = (a:real^2)$1 /\
                (origin:real^2)$2 = av`
  MP_TAC THENL
   [EXPAND_TAC "origin" THEN REWRITE_TAC[VECTOR_2];
    POP_ASSUM(K ALL_TAC)] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  GEOM_ORIGIN_TAC `origin:real^2` THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT; REAL_EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[REAL_LE_LADD; REAL_ADD_RID] THEN
  MAP_EVERY X_GEN_TAC
   [`origin:real^2`; `b:real^2`; `baseline:real`; `a:real^2`;
    `av:real`; `L:real`; `g:real^1->real^2`] THEN
  STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SYM) SUBST_ALL_TAC) THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN
    SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`; `--lift av`]
        HAS_INTEGRAL_CONST) THEN
  REWRITE_TAC[CONTENT_UNIT_1; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  REWRITE_TAC[VECTOR_ADD_ASSOC; LIFT_ADD; VECTOR_ADD_LINV;
              VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
  STRIP_TAC THEN

  (*** Pick almost-derivatives, observe absolute continuity    ***)

  SUBGOAL_THEN
   `(g:real^1->real^2) absolutely_continuous_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIPSCHITZ_IMP_ABSOLUTELY_CONTINUOUS THEN
    REWRITE_TAC[BOUNDED_INTERVAL; GSYM dist] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ]
     ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON)) THEN
  REWRITE_TAC[BOUNDED_INTERVAL] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LEBESGUE_DIFFERENTIATION_THEOREM_COMPACT) THEN
  ABBREV_TAC
    `s = {x | x IN interval[vec 0,vec 1] /\
              ~((g:real^1->real^2) differentiable at x)}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
    `?g':real^1->real^2.
        !x. x IN interval[vec 0,vec 1] /\ ~(x IN s)
            ==> (g has_vector_derivative g' x) (at x)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\x. vector_derivative (g:real^1->real^2) (at x)` THEN
    ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    EXPAND_TAC "s" THEN SIMP_TAC[IN_ELIM_THM; IMP_CONJ];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1]
        ==> (g':real^1->real^2) absolutely_integrable_on interval[vec 0,t] /\
            integral (interval[vec 0,t]) g' = g t - a`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`g:real^1->real^2`; `g':real^1->real^2`; `vec 0:real^1`; `vec 1:real^1`]
     ABSOLUTE_INTEGRAL_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[IN_DIFF; HAS_VECTOR_DERIVATIVE_AT_WITHIN];
      REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL]] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart]) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
     ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN interval[vec 0,vec 1]
        ==> (\x. lift(norm((g':real^1->real^2) x))) absolutely_integrable_on
            interval[vec 0,x] /\
            integral (interval[vec 0,x]) (\x. lift(norm(g' x))) =
            L % x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    REWRITE_TAC[DROP_VEC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^1->real^2`; `vec 0:real^1`; `x:real^1`]
        PATH_LENGTH_SUBPATH) THEN
    ASM_SIMP_TAC[SEGMENT_1; DROP_VEC] THEN
    REWRITE_TAC[GSYM LIFT_EQ; LIFT_CMUL; LIFT_DROP] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`g:real^1->real^2`; `g':real^1->real^2`;
                   `vec 0:real^1`; `x:real^1`; `s:real^1->bool`]
        VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE_GEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ABSOLUTELY_CONTINUOUS_ON_SUBSET)) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; IN_DIFF] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; IN_DIFF] THEN
        ASM_REAL_ARITH_TAC];
      SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; LIFT_DROP]];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!x. x IN interval[vec 0,vec 1] /\ ~(x IN s)
        ==> norm((g':real^1->real^2) x) <= L`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `L = norm(lift L)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[NORM_LIFT; REAL_ARITH `&0 < l ==> abs l = l`];
      MATCH_MP_TAC NORM_VECTOR_DERIVATIVES_LE_WITHIN] THEN
    MAP_EVERY EXISTS_TAC
     [`g:real^1->real^2`; `\x:real^1. L % x`;
      `x:real^1`; `interval[vec 0:real^1,vec 1]`] THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN] THEN
    REWRITE_TAC[LIFT_EQ_CMUL] THEN
    SIMP_TAC[HAS_VECTOR_DERIVATIVE_ID; HAS_VECTOR_DERIVATIVE_CMUL] THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) LIMPT_OF_CONVEX o snd) THEN
      ASM_REWRITE_TAC[CONVEX_INTERVAL; GSYM INTERVAL_SING] THEN
      DISCH_THEN SUBST1_TAC THEN
      DISCH_THEN(MP_TAC o AP_TERM `interior:(real^1->bool)->real^1->bool`) THEN
      REWRITE_TAC[INTERVAL_SING; INTERIOR_INTERVAL] THEN
      REWRITE_TAC[INTERVAL_NE_EMPTY_1; DROP_VEC; REAL_LT_01];
      REWRITE_TAC[EVENTUALLY_WITHIN] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
      ASM_SIMP_TAC[GSYM dist; REAL_ARITH `&0 < l ==> abs l = l`] THEN
      MESON_TAC[REAL_LT_01]];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `(\x. lift(norm((g':real^1->real^2) x) pow 2))
    absolutely_integrable_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC
     MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE THEN
    EXISTS_TAC `\x:real^1. lift(L pow 2)` THEN
    EXISTS_TAC `s:real^1->bool` THEN
    REWRITE_TAC[INTEGRABLE_CONST; NORM_LIFT; REAL_ABS_NORM; LIFT_DROP;
                REAL_ABS_POW; IN_DIFF; GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
    MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MEASURABLE_ON_NORM THEN
    ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL; ABSOLUTELY_INTEGRABLE_MEASURABLE];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `integral (interval[vec 0,vec 1])
             (\x. lift(norm((g':real^1->real^2) x) pow 2)) =
    lift(L pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
      `integral (interval[vec 0,vec 1]) (\x:real^1. lift(L pow 2))` THEN
     CONJ_TAC THENL
      [GEN_REWRITE_TAC I [GSYM DROP_EQ];
       REWRITE_TAC[INTEGRAL_CONST; CONTENT_UNIT_1; GSYM LIFT_CMUL] THEN
       REWRITE_TAC[REAL_MUL_LID]] THEN
     REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
     MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
     ASM_SIMP_TAC[INTEGRABLE_CONST; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
     REWRITE_TAC[LIFT_DROP; GSYM REAL_LE_SQUARE_ABS; REAL_ABS_NORM] THEN
     ASM_SIMP_TAC[IN_DIFF; REAL_ARITH `&0 < l ==> abs l = l`] THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN

     SUBGOAL_THEN
      `((\x. lift(L - norm((g':real^1->real^2) x))) has_integral (vec 0))
       (interval[vec 0,vec 1] DIFF s)`
     MP_TAC THENL
      [MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET THEN
       EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
        [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `s:real^1->bool` THEN
         ASM_REWRITE_TAC[] THEN SET_TAC[];
         REWRITE_TAC[LIFT_SUB]] THEN
       SUBGOAL_THEN
        `vec 0 = content(interval[vec 0:real^1,vec 1]) % lift L - lift L`
       MP_TAC THENL
        [REWRITE_TAC[CONTENT_UNIT_1; LIFT_CMUL] THEN
         CONV_TAC VECTOR_ARITH;
         DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th])] THEN
       MATCH_MP_TAC HAS_INTEGRAL_SUB THEN REWRITE_TAC[HAS_INTEGRAL_CONST] THEN
       ASM_SIMP_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL; ENDS_IN_UNIT_INTERVAL;
                    ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
       REWRITE_TAC[GSYM LIFT_EQ_CMUL];
       ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) HAS_INTEGRAL_NEGLIGIBLE_EQ o
      lhand o snd) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IMP_IMP; FORALL_1; DIMINDEX_1] THEN
    REWRITE_TAC[LIFT_DROP; GSYM drop; IN_DIFF] THEN
    ASM_SIMP_TAC[REAL_SUB_LE] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = &0 <=> y = x`] THEN
    REWRITE_TAC[LIFT_NUM] THEN STRIP_TAC THEN
    EXISTS_TAC
      `s UNION {x | (x IN interval[vec 0,vec 1] /\ ~(x IN s)) /\
                    ~(norm ((g':real^1->real^2) x) = L)}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN MESON_TAC[REAL_LE_REFL];
    ALL_TAC] THEN

  (*** Use the Green formula for the area inside the curve ***)

  SUBGOAL_THEN
   `(\t. lift(g'(t)$1 * (g:real^1->real^2)(t)$2)) absolutely_integrable_on
    interval[vec 0,vec 1] /\
    norm(integral (interval[vec 0,vec 1])
                  (\t. lift((g':real^1->real^2)(t)$1 * g(t)$2))) =
    measure(inside(path_image g))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC GREEN_AREA_THEOREM THEN
    MAP_EVERY EXISTS_TAC [`s:real^1->bool`; `a:real^2`; `b:real^2`] THEN
    ASM_SIMP_TAC[IN_DIFF; dist] THEN FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP
     (VECTOR_ARITH `b - a:real^N = c ==> b = a + c`)) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Get a more convenient variant with some arbitrary sign ***)

  SUBGOAL_THEN
   `?sgn. sgn pow 2 = &1 /\
          ((\x. lift((g':real^1->real^2)(x)$1 * g(x)$2)) has_integral
           sgn % lift(measure(inside(path_image(g:real^1->real^2)))))
          (interval[vec 0,vec 1])`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [NORM_1]) THEN
    REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THENL
     [EXISTS_TAC `&1:real`; EXISTS_TAC `--(&1):real`] THEN
    ASM_REWRITE_TAC[LIFT_DROP; LIFT_NEG] THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_RNEG; VECTOR_NEG_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN

  (*** Reformulate the area/length disparity as an integral ***)

  SIMP_TAC[PI_POS; REAL_ARITH `&0:real < &4 * x <=> &0 < x`; REAL_LE_RDIV_EQ;
    REAL_FIELD `&0 < z ==> (x = y / (&4 * z) <=> y - x * &4 * z = &0)`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN

  SUBGOAL_THEN
   `((\x. lift(((g':real^1->real^2) x$1 -
                &2 * pi * sgn * (g:real^1->real^2)(x)$2) pow 2 +
               (g'(x)$2 pow 2 - (&2 * pi * g(x)$2) pow 2)))
     has_integral lift(L pow 2 - measure (inside (path_image g)) * &4 * pi))
    (interval[vec 0,vec 1])`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_RING
        `s pow 2 = &1
         ==> (x' - &2 * pi * s * y) pow 2 + (y' pow 2 - (&2 * pi * y) pow 2) =
             (x' pow 2 + y' pow 2) - &4 * pi * s * x' * y`] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM DOT_2; REAL_POW_2] THEN
      REWRITE_TAC[GSYM REAL_POW_2; GSYM NORM_POW_2] THEN
      ASM_SIMP_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL;
                   ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];

      FIRST_X_ASSUM(fun th ->
        REWRITE_TAC[MATCH_MP (REAL_RING
          `s pow 2 = &1 ==> x * &4 * pi = &4 * pi * s * s * x`) th]) THEN
      REWRITE_TAC[REAL_ARITH `x * &4 * pi = &4 * pi * x`] THEN
      REWRITE_TAC[LIFT_CMUL] THEN
      REPLICATE_TAC 3 (MATCH_MP_TAC HAS_INTEGRAL_CMUL) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[LIFT_CMUL]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN

  (*** Dispose of trivial case when the inside is empty ***)

  ASM_CASES_TAC `inside(path_image g):real^2->bool = {}` THENL
   [ASM_REWRITE_TAC[MEASURE_EMPTY; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POW_EQ_0; ARITH_EQ; REAL_LT_IMP_NZ];
    ALL_TAC] THEN

  (*** Now deploy the scaled Wirtinger inequality ***)

  MP_TAC(SPECL
   [`\x. (g:real^1->real^2)(lift x)$2`; `\x. (g':real^1->real^2)(lift x)$2`]
   SCALED_WIRTINGER_INEQUALITY) THEN
  ASM_REWRITE_TAC[LIFT_NUM] THEN

  GEN_REWRITE_TAC LAND_CONV
   [TAUT `(p ==> q /\ r) <=> p ==> q /\ (q ==> r)`] THEN
  SIMP_TAC[REAL_INTEGRAL; REAL_POW_MUL; REAL_INTEGRAL_LMUL;
           REAL_INTEGRABLE_LMUL] THEN
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_NUM] THEN
  REWRITE_TAC[has_real_integral; REAL_INTEGRABLE_ON; o_DEF; LIFT_DROP;
              IMAGE_LIFT_REAL_INTERVAL; LIFT_NUM] THEN
  REWRITE_TAC[REAL_ARITH `drop x <= drop y <=> &0 <= drop y - drop x`] THEN
  REWRITE_TAC[MESON[DROP_EQ; REAL_SUB_0]
        `drop x = drop y <=> drop y - drop x = &0`] THEN
  SIMP_TAC[GSYM DROP_SUB; GSYM INTEGRAL_SUB; LIFT_CMUL; INTEGRABLE_CMUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; GSYM LIFT_CMUL; GSYM LIFT_SUB] THEN
  SUBST1_TAC(SYM(ISPEC `g:real^1->real^2` pathstart)) THEN
  SUBST1_TAC(SYM(ISPEC `g:real^1->real^2` pathfinish)) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [IMP_CONJ] THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_DROP; IN_REAL_INTERVAL; LIFT_DROP] THEN
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\x. lift((g:real^1->real^2) x$2)`;
      `\x. lift((g':real^1->real^2) x$2)`;
      `s:real^1->bool`; `vec 0:real^1`; `x:real^1`]
     FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS) THEN
    ASM_REWRITE_TAC[DROP_VEC] THEN
    SUBST1_TAC(SYM(ISPEC `g:real^1->real^2` pathstart)) THEN
    ASM_REWRITE_TAC[LIFT_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `2` o
        GEN_REWRITE_RULE I [ABSOLUTELY_CONTINUOUS_ON_COMPONENTWISE]) THEN
      REWRITE_TAC[DIMINDEX_2; ARITH] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
       ABSOLUTELY_CONTINUOUS_ON_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC; REAL_LE_REFL];
      X_GEN_TAC `y:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; IN_DIFF] THEN
      STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT THEN
      REWRITE_TAC[DIMINDEX_2; ARITH] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN

  MATCH_MP_TAC(TAUT
   `p /\ (p /\ q ==> r ==> s) ==> (p ==> q /\ (q ==> r)) ==> s`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC
        MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\x. lift(norm((g':real^1->real^2) x) pow 2)` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[NORM_1; LIFT_DROP; REAL_ABS_POW; GSYM REAL_LE_SQUARE_ABS] THEN
    REWRITE_TAC[REAL_ABS_ABS; REAL_ABS_NORM; COMPONENT_LE_NORM] THEN
    MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN REWRITE_TAC[ARITH_EQ] THEN
    SUBGOAL_THEN
     `(g':real^1->real^2) absolutely_integrable_on interval[vec 0,vec 1]`
    MP_TAC THENL [ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
    DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_IMP_MEASURABLE) THEN
    GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_COMPONENTWISE] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[DIMINDEX_2; ARITH];
    STRIP_TAC] THEN

  SUBGOAL_THEN
    `(\x. lift((g':real^1->real^2)x$2 pow 2 -
              (&2 * pi * (g:real^1->real^2)x$2) pow 2))
     integrable_on interval[vec 0,vec 1]`
  MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; LIFT_SUB] THEN
    ONCE_REWRITE_TAC[REAL_POW_MUL] THEN REWRITE_TAC[LIFT_CMUL] THEN
    ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_CMUL];
    GEN_REWRITE_TAC LAND_CONV [integrable_on]] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^1` MP_TAC) THEN
  DISCH_THEN(fun th ->
   SUBST1_TAC(MATCH_MP INTEGRAL_UNIQUE th) THEN MP_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o
    check (can (term_match [] `(f has_integral y) s`) o concl)) THEN
  GEN_REWRITE_TAC I [IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  REWRITE_TAC[LIFT_ADD; VECTOR_ARITH `(a + b) - b:real^N = a`] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_DROP_POS) th)) THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2; DROP_SUB] THEN
  ABBREV_TAC
   `d = L pow 2 -
        measure(inside(path_image g:real^2->bool)) * &4 * pi - drop w` THEN
  SUBGOAL_THEN
   `L pow 2 - measure(inside(path_image g:real^2->bool)) * &4 * pi =
    d + drop w`
  SUBST_ALL_TAC THENL [EXPAND_TAC "d" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_ARITH
   `&0 <= x /\ &0 <= y ==> (x + y:real = &0 <=> x = &0 /\ y = &0)`] THEN
  ASM_CASES_TAC `d:real = &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `drop w = &0` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    check (can (term_match [] `(f has_integral y) s`) o concl)) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  MP_TAC(ASSUME `drop w = &0`) THEN REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_SUB_REFL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HAS_INTEGRAL_NEGLIGIBLE_EQ o
    lhand o snd) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1] THEN
  REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2] THEN
  GEN_REWRITE_TAC I [IMP_CONJ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP; REAL_POW_EQ_0] THEN
  REWRITE_TAC[ARITH_EQ] THEN REWRITE_TAC[TAUT `p /\ ~q <=> ~(p ==> q)`] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `A:real`
    MP_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_DROP] THEN
  SIMP_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP; DROP_VEC] THEN
  REWRITE_TAC[GSYM DROP_VEC; GSYM IN_INTERVAL_1] THEN
  REWRITE_TAC[DROP_VEC; NOT_IMP] THEN DISCH_TAC THEN DISCH_TAC THEN

  SUBGOAL_THEN
   `!x. x IN interval[vec 0,vec 1]
        ==> (g:real^1->real^2)x$1 =
            --sgn * C * (cos(&2 * pi * drop x - A) - cos A)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM] THEN
    MP_TAC(ISPECL
     [`\x. lift((g':real^1->real^2) x$1 -
               &2 * pi * sgn * C * sin(&2 * pi * drop x - A))`;
      `interval[vec 0:real^1,x]`] HAS_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN FIRST_X_ASSUM(MATCH_MP_TAC o
        MATCH_MP (MESON[]
         `negligible t ==> P t ==> ?s. negligible s /\ P s`)) THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
      X_GEN_TAC `y:real^1` THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(g':real^1->real^2) absolutely_integrable_on interval[vec 0,x] /\
        integral (interval [vec 0,x]) g' = g x - a`
      MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) MP_TAC) THEN
      REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL;
                  GSYM IMP_CONJ_ALT] THEN
      GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_COMPONENTWISE] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      ASM_REWRITE_TAC[DIMINDEX_2; ARITH; VECTOR_SUB_COMPONENT] THEN
      REWRITE_TAC[REAL_SUB_RZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\x. &2 * pi * sgn * C * sin (&2 * pi * x - A))
       has_real_integral
       (--sgn * C * cos (&2 * pi * drop x - A) -
        --sgn * C * cos (&2 * pi * &0 - A))) (real_interval[&0,drop x])`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[has_real_integral; o_DEF; IMAGE_LIFT_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO; COS_NEG]] THEN
    REWRITE_TAC[LIFT_NUM; LIFT_DROP] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  MAP_EVERY EXISTS_TAC
   [`vector[sgn * C * cos A; &0]:real^2`; `abs C:real`] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t /\ ~(s PSUBSET t) ==> s = t`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; IN_SPHERE] THEN
    REWRITE_TAC[dist; NORM_EQ_SQUARE; REAL_ABS_POS; REAL_POW2_ABS] THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[DOT_2; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(SPEC `&2 * pi * drop x - A` SIN_CIRCLE) THEN
    UNDISCH_TAC `(sgn:real) pow 2 = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN

  ABBREV_TAC `z:real^2 = vector[sgn * C * cos A; &0]` THEN DISCH_TAC THEN
  UNDISCH_TAC `~(inside(path_image g):real^2->bool = {})` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC INSIDE_BOUNDED_COMPLEMENT_CONNECTED_EMPTY THEN
  ASM_SIMP_TAC[BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
  MATCH_MP_TAC JORDAN_BROUWER_NONSEPARATION THEN
  MAP_EVERY EXISTS_TAC
   [`sphere(z:real^2,abs C)`; `z:real^2`; `abs C:real`] THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH; HOMEOMORPHIC_REFL]);;
```
### Informal statement
For all real numbers `L` and all functions `g` from real numbers to pairs of real numbers, if `g` is a rectifiable path, `g` is a simple path, the endpoint of `g` equals the starting point of `g`, the interior of the path image of `g` is convex, and the path length of `g` is `L`, then the measure of the interior of the path image of `g` is less than or equal to `L` squared divided by `4 * pi`, and if the measure of the interior of the path image of `g` equals `L` squared divided by `4 * pi`, then there exist a point `a` in the plane and a real number `r` such that the path image of `g` equals the sphere centered at `a` with radius `r`.

### Informal sketch
The proof demonstrates the isoperimetric inequality for convex curves: for a convex curve of length `L`, enclosing an area `A`, `A <= L^2 / (4*pi)`, with equality if and only if the curve is a circle. The proof proceeds as follows:

- Scrub degenerate cases and assume `0 < L`.
- Rotate the image of the path so that a diameter lies on the horizontal axis.
- Reparametrize the path to start and finish at the leftmost point `a` of that diameter using `shiftpath`. This involves proving that the shifted path `g1` retains the key properties of `g0`: same image, rectifiable, simple, closed, convex interior, and same length `L`.
- Reparametrize by arc length using `ARC_LENGTH_REPARAMETRIZATION` to obtain `g2`.
- Adjust the path such that the x-coordinate equals 0 at the leftmost point, and the average value of the y-coordinate is zero, by subtracting a constant vector `origin` from the path.  This involves proving that the component of the vector `origin` are the x coordinate of `a` and `av` respectively.
- Show that `g` is absolutely continuous on the interval `[0, 1]`. Apply `LEBESGUE_DIFFERENTIATION_THEOREM_COMPACT` and demonstrate the existence of almost everywhere derivatives `g'` for `g`.
- Show `g'` is absolutely integrable and `integral (interval[vec 0,t]) g' = g t - a`.
- Show the integral of the norm of `g'` equals the length and `norm((g':real^1->real^2) x) <= L` almost everywhere.
- Use the Green's formula (`GREEN_AREA_THEOREM`) to express the area inside the curve as an integral involving `g'` and `g`.
- Reformulate the area/length disparity as an integral and use scaled Wirtinger inequality (`SCALED_WIRTINGER_INEQUALITY`) to finish the proof.
- Treat the trivial case when the inside is empty.

### Mathematical insight
The isoperimetric theorem establishes a fundamental relationship between the length of a closed curve and the area it encloses. This specific version focuses on convex curves, using a series of reparameterizations and Green's theorem to connect geometric properties (length, area) with analytic tools (derivatives, integrals). The scaled Wirtinger inequality is the key inequality that makes the central estimate work.

### Dependencies
- `SIMPLE_PATH_LENGTH_POS_LT`
- `DIAMETER_COMPACT_ATTAINED`
- `LEFT_IMP_EXISTS_THM`
- `PATH_IMAGE_NONEMPTY`
- `COMPACT_PATH_IMAGE`
- `SIMPLE_PATH_IMP_PATH`
- `DIAMETER_EQ_0`
- `BOUNDED_PATH_IMAGE`
- `INFINITE_SIMPLE_PATH_IMAGE`
- `IN_IMAGE`
- `RECTIFIABLE_PATH_SHIFTPATH`
- `SIMPLE_PATH_SHIFTPATH`
- `CLOSED_SHIFTPATH`
- `PATH_IMAGE_SHIFTPATH`
- `PATH_LENGTH_SHIFTPATH`
- `PATHSTART_SHIFTPATH`
- `IN_INTERVAL_1`
- `DROP_VEC`
- `ARC_LENGTH_REPARAMETRIZATION`
- `INTEGRABLE_CONTINUOUS`
- `CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE`
- `LIPSCHITZ_IMP_CONTINUOUS_ON`
- `dist`
- `VECTOR_2`
- `VECTOR_ADD_COMPONENT`
- `VEC_COMPONENT`
- `REAL_EQ_ADD_LCANCEL`
- `REAL_LE_LADD`
- `REAL_ADD_RID`
- `HAS_INTEGRAL_CONST`
- `CONTENT_UNIT_1`
- `HAS_INTEGRAL_ADD`
- `VECTOR_ADD_ASSOC`
- `LIFT_ADD`
- `VECTOR_ADD_LINV`
- `VECTOR_ADD_LID`
- `VECTOR_MUL_LID`
- `LIPSCHITZ_IMP_ABSOLUTELY_CONTINUOUS`
- `BOUNDED_INTERVAL`
- `LEBESGUE_DIFFERENTIATION_THEOREM_COMPACT`
- `ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON`
- `ABSOLUTE_INTEGRAL_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ`
- `HAS_VECTOR_DERIVATIVE_AT_WITHIN`
- `HAS_INTEGRAL_INTEGRABLE_INTEGRAL`
- `ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL`
- `SUBSET_INTERVAL_1`
- `LIFT_DROP`
- `PATH_LENGTH_SUBPATH`
- `SEGMENT_1`
- `VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE_GEN`
- `ABSOLUTELY_CONTINUOUS_ON_SUBSET`
- `ABSOLUTELY_INTEGRABLE_NORM`
- `NORM_VECTOR_DERIVATIVES_LE_WITHIN`
- `CONVEX_INTERVAL`
- `INTERVAL_SING`
- `INTERIOR_INTERVAL`
- `INTERVAL_NE_EMPTY_1`
- `REAL_LT_01`
- `EVENTUALLY_WITHIN`
- `NORM_MUL`
- `MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE`
- `MEASURABLE_ON_LIFT_POW`
- `MEASURABLE_ON_NORM`
- `ENDS_IN_UNIT_INTERVAL`
- `ABSOLUTELY_INTEGRABLE_MEASURABLE`
- `INTEGRAL_CONST`
- `EQ_TRANS`
- `INTEGRAL_DROP_LE_AE`
- `ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE`
- `HAS_INTEGRAL_SPIKE_SET`
- `NEGLIGIBLE_SUBSET`
- `HAS_INTEGRAL_SUB`
- `DROP_EQ`
- `GREEN_AREA_THEOREM`
- `INSIDE_BOUNDED_COMPLEMENT_CONNECTED_EMPTY`
- `JORDAN_BROUWER_NONSEPARATION`
- `HOMEOMORPHIC_REFL`
- `SCALED_WIRTINGER_INEQUALITY`
- `SIN_CIRCLE`
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`

### Porting notes (optional)
- Automation may be needed to discharge some real analysis side-conditions.
- The reparameterization steps may require some finesse to translate smoothly.
- Check handling of negligible sets.


---

## STEP_LEMMA

### Name of formal statement
STEP_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STEP_LEMMA = prove
 (`!g:real^1->real^2 a b L.
        simple_path g /\ pathfinish g = pathstart g /\
        (!x y. x IN interval [vec 0,vec 1] /\
               y IN interval [vec 0,vec 1]
               ==> dist(g x,g y) <= L * dist(x,y)) /\
        drop a < drop b /\
        a IN interval[vec 0,vec 1] /\ b IN interval[vec 0,vec 1] /\
        g(a) IN frontier(convex hull (path_image g)) /\
        g(b) IN frontier(convex hull (path_image g)) /\
        IMAGE g (interval(a,b)) INTER frontier(convex hull (path_image g)) = {}
        ==> ?h. simple_path h /\
                pathstart h = pathstart g /\ pathfinish h = pathstart g /\
                (!x y. x IN interval [vec 0,vec 1] /\
                       y IN interval [vec 0,vec 1]
                       ==> dist(h x,h y) <= L * dist(x,y)) /\
                path_length h < path_length g /\
                convex hull (path_image h) = convex hull (path_image g) /\
                (!x. ~(x IN interval(a,b)) ==> h x = g x) /\
                IMAGE h (interval[a,b]) SUBSET
                frontier(convex hull (path_image g))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval(a:real^1,b) = {}` THENL
   [ASM_MESON_TAC[INTERVAL_NE_EMPTY_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^1->real^2) (interval(a,b)) SUBSET
    interior(convex hull (path_image g))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s INTER f = {} ==> s SUBSET f UNION i ==> s SUBSET i`)) THEN
    REWRITE_TAC[frontier; GSYM path_image] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET closure s /\ u SUBSET s
      ==> u SUBSET closure s DIFF interior s UNION interior s`) THEN
    REWRITE_TAC[CLOSURE_SUBSET; path_image] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET convex hull s /\ t SUBSET s ==> t SUBSET convex hull s`) THEN
    REWRITE_TAC[HULL_SUBSET] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior(convex hull (path_image g)):real^2->bool = {})`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM INTERVAL_NE_EMPTY_1]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(g:real^1->real^2) a = g b` THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`a:real^1`; `b:real^1`] o CONJUNCT2 o
        REWRITE_RULE[simple_path]) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN UNDISCH_TAC `drop a < drop b` THEN
    ASM_REWRITE_TAC[DROP_VEC; REAL_LT_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `~(interior(convex hull path_image g):real^2->bool = {})` THEN
    SUBGOAL_THEN
     `convex hull path_image g:real^2->bool = convex hull IMAGE g {a, b}`
     (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES; GSYM SEGMENT_CONVEX_HULL;
                            INTERIOR_SEGMENT; DIMINDEX_2; LE_REFL]) THEN
    MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
    CONJ_TAC THENL [REWRITE_TAC[path_image] THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        SUBSET_TRANS)) THEN
    ASM_REWRITE_TAC[path_image; OPEN_CLOSED_INTERVAL_1] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE (g:real^1->real^2)
                  (interval[vec 0,vec 1] DIFF interval(a,b))) =
    convex hull (path_image g) /\
    convex hull (segment[(g:real^1->real^2) a,g b] UNION
                 IMAGE g (interval[vec 0,vec 1] DIFF interval(a,b))) =
    convex hull (path_image g)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[] `c = b /\ b = a ==> b = a /\ c = a`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN SIMP_TAC[HULL_MONO; SUBSET_UNION] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC[UNION_SUBSET; HULL_SUBSET] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_DIFF; ENDS_IN_INTERVAL];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET THEN
      ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
      REWRITE_TAC[path_image] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `IMAGE f t SUBSET u
        ==> IMAGE f s DIFF IMAGE f (s DIFF t) SUBSET u`) THEN
      ASM_REWRITE_TAC[GSYM path_image]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^2`; `a:real^1`; `b:real^1`]
        EXISTS_DOUBLE_ARC_EXPLICIT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g0:real^1->real^2`; `g1:real^1->real^2`] THEN
  REPLICATE_TAC 6 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SYM) STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th ->
     RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPEC `convex hull (path_image g):real^2->bool`
      RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CONVEX_HULL; BOUNDED_CONVEX_HULL;
                 BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
    ASM_MESON_TAC[AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_2];
    DISCH_THEN(X_CHOOSE_THEN `d:real^1->real^2` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `?d0 d1.
      arc d0 /\
      arc d1 /\
      pathstart d0 = g a /\
      pathfinish d0 = g b /\
      pathstart d1 = g b /\
      pathfinish d1 = g a /\
      path_image d0 INTER path_image d1 = {(g:real^1->real^2) a, g b} /\
      path_image d0 UNION path_image d1 = path_image d /\
      inside (path_image d0 UNION path_image g0) INTER
      inside (path_image d1 UNION path_image g0) = {} /\
      inside (path_image d0 UNION path_image g0) UNION
      inside (path_image d1 UNION path_image g0) UNION
      path_image g0 DIFF {g a, g b} =
      interior (convex hull path_image g) /\
      (path_image g1 DIFF {g b, g a}) INTER path_image d0 = {}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^1->real^2`;
                   `(g:real^1->real^2) a`; `(g:real^1->real^2) b`]
        EXISTS_DOUBLE_ARC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`d0:real^1->real^2`; `d1:real^1->real^2`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL
     [`d0:real^1->real^2`; `reversepath d1:real^1->real^2`;
      `g0:real^1->real^2`; `(g:real^1->real^2) a`; `(g:real^1->real^2) b`]
     SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
    ASM_REWRITE_TAC[PATH_IMAGE_REVERSEPATH;
      SIMPLE_PATH_REVERSEPATH_EQ; PATHSTART_REVERSEPATH;
      PATHFINISH_REVERSEPATH] THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [INSIDE_FRONTIER_EQ_INTERIOR; CONVEX_CONVEX_HULL;
      BOUNDED_CONVEX_HULL; BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN
      SUBST1_TAC(SYM(ASSUME
       `IMAGE (g:real^1->real^2) (interval[a,b]) = path_image g0`)) THEN
      MP_TAC(ISPECL [`a:real^1`; `b:real^1`] CLOSED_OPEN_INTERVAL_1) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE g i SUBSET n
        ==> g a IN d0 /\ g b IN d0 /\ g a IN d1 /\ g b IN d1 /\
            ~(i = {}) /\ (d0 UNION d1) INTER n = {}
            ==> d0 INTER IMAGE g (i UNION {a,b}) = {g a,g b} /\
                d1 INTER IMAGE g (i UNION {a,b}) = {g a,g b} /\
                ~(IMAGE g (i UNION {a,b}) INTER n = {})`)) THEN
      ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1] THEN
      REWRITE_TAC[frontier; SET_RULE `(s DIFF t) INTER t = {}`] THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      STRIP_TAC] THEN
    MP_TAC(ISPEC `g1:real^1->real^2` CONNECTED_SIMPLE_PATH_ENDLESS) THEN
    ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH] THEN
    REWRITE_TAC[CONNECTED_OPEN_IN; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`(path_image(g1:real^1->real^2) DIFF {g(b:real^1),g a}) DIFF
       closure(inside(path_image d1 UNION path_image g0))`;
      `(path_image(g1:real^1->real^2) DIFF {g(b:real^1),g a}) DIFF
       closure(inside(path_image d0 UNION path_image g0))`]) THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    GEN_REWRITE_TAC LAND_CONV [IMP_IMP] THEN ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN
      REWRITE_TAC[CLOSED_CLOSURE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(path_image g1 DIFF {(g:real^1->real^2) b, g a}) DIFF
      closure(inside(path_image d1 UNION path_image g0)) =
      (path_image g1 DIFF {(g:real^1->real^2) b, g a}) INTER
      (path_image d0 UNION inside(path_image d0 UNION path_image g0)) /\
      (path_image g1 DIFF {(g:real^1->real^2) b, g a}) DIFF
      closure(inside(path_image d0 UNION path_image g0)) =
      (path_image g1 DIFF {(g:real^1->real^2) b, g a}) INTER
      (path_image d1 UNION inside(path_image d1 UNION path_image g0))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `reversepath d1 ++ reversepath g0:real^1->real^2`
         JORDAN_INSIDE_OUTSIDE);
        MP_TAC(ISPEC `d0 ++ reversepath g0:real^1->real^2`
         JORDAN_INSIDE_OUTSIDE)] THEN
     (ANTS_TAC THENL
       [ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN;
                        PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
        MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
        ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
        ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATH_IMAGE_REVERSEPATH] THEN
        FIRST
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
          `e UNION f = d
           ==> d INTER g SUBSET s ==> e INTER g SUBSET s`));
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
          `f UNION e = d
           ==> d INTER g SUBSET s ==> e INTER g SUBSET s`))] THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME
         `IMAGE (g:real^1->real^2) (interval [a,b]) = path_image g0`)) THEN
        MP_TAC(ISPECL [`a:real^1`; `b:real^1`] CLOSED_OPEN_INTERVAL_1) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC[frontier] THEN ASM SET_TAC[];
        ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH;
                     PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th])]) THEN
      ASM_SIMP_TAC[SET_RULE
       `g0 INTER g1 = {a,b}
        ==> (g1 DIFF {b,a}) DIFF (i UNION d1 UNION g0) =
            (g1 DIFF {b,a}) DIFF (d1 UNION i)`] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> (~(x IN u) <=> x IN t))
        ==> s DIFF u = s INTER t`)
      THENL [ONCE_REWRITE_TAC[TAUT `(~p <=> q) <=> ~q <=> p`]; ALL_TAC] THEN
     (X_GEN_TAC `z:real^2` THEN
      REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
      STRIP_TAC THEN
      REWRITE_TAC[TAUT `(~p <=> q) <=> (p \/ q) /\ ~(p /\ q)`] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[SET_RULE
         `z IN s UNION t \/ z IN u UNION v <=>
          z IN (s UNION u) UNION (t UNION v)`] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `i UNION j UNION p = k
          ==> ~(z IN p) /\ z IN f UNION k
              ==> z IN f UNION i UNION j`)) THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[FRONTIER_UNION_INTERIOR] THEN
        MATCH_MP_TAC CLOSURE_INC THEN MATCH_MP_TAC HULL_INC THEN
        ASM SET_TAC[];
        FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `i INTER j = {}
          ==> ~(z IN s INTER t) /\ ~(z IN s INTER j) /\ ~(z IN t INTER i)
              ==> ~(z IN s UNION i /\ z IN t UNION j)`)) THEN
        ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
         [MP_TAC(ISPECL
           [`inside(path_image d1 UNION path_image g0):real^2->bool`;
            `inside(path_image d0 UNION path_image g0):real^2->bool`]
           OPEN_INTER_CLOSURE_EQ_EMPTY);
          MP_TAC(ISPECL
           [`inside(path_image d0 UNION path_image g0):real^2->bool`;
            `inside(path_image d1 UNION path_image g0):real^2->bool`]
           OPEN_INTER_CLOSURE_EQ_EMPTY)] THEN
        ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
         [OPEN_INSIDE; CLOSED_UNION; CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
        ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE
         `p SUBSET c ==> c INTER i = {} ==> ~(z IN i INTER p)`) THEN
        REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET f ==> s SUBSET t UNION f`) THENL
         [MP_TAC(ISPEC `d0 ++ reversepath g0:real^1->real^2`
           JORDAN_INSIDE_OUTSIDE);
          MP_TAC(ISPEC `reversepath d1 ++ reversepath g0:real^1->real^2`
           JORDAN_INSIDE_OUTSIDE)] THEN
        ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH;
                     PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
        (ANTS_TAC THENL [ALL_TAC; SET_TAC[]]) THEN
        ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN;
                        PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
        MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
        ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
        ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATH_IMAGE_REVERSEPATH] THEN
        FIRST
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
          `e UNION f = d
           ==> d INTER g SUBSET s ==> e INTER g SUBSET s`));
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
          `f UNION e = d
           ==> d INTER g SUBSET s ==> e INTER g SUBSET s`))] THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME
         `IMAGE (g:real^1->real^2) (interval [a,b]) = path_image g0`)) THEN
        MP_TAC(ISPECL [`a:real^1`; `b:real^1`] CLOSED_OPEN_INTERVAL_1) THEN
        (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
        REWRITE_TAC[frontier] THEN ASM SET_TAC[]]);
      ALL_TAC] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s SUBSET t UNION u
        ==> s SUBSET (s INTER t) UNION (s INTER u)`) THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_INSERT;
                  NOT_IN_EMPTY; DE_MORGAN_THM] THEN
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[SET_RULE
       `(s UNION t) UNION (u UNION v) = (s UNION u) UNION (t UNION v)`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `i UNION j UNION p = k
        ==> ~(z IN p) /\ z IN f UNION k
            ==> z IN f UNION i UNION j`)) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[FRONTIER_UNION_INTERIOR] THEN
      MATCH_MP_TAC CLOSURE_INC THEN MATCH_MP_TAC HULL_INC THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SET_RULE
       `(s INTER t) INTER (s INTER u) = {} <=>
        !x. x IN s ==> ~(x IN t INTER u)`] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_INSERT;
                  NOT_IN_EMPTY; DE_MORGAN_THM] THEN
      X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN REWRITE_TAC[IN_INTER] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `i INTER j = {}
        ==> ~(z IN s INTER t) /\ ~(z IN s INTER j) /\ ~(z IN t INTER i)
            ==> ~(z IN s UNION i /\ z IN t UNION j)`)) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL
         [`inside(path_image d1 UNION path_image g0):real^2->bool`;
          `inside(path_image d0 UNION path_image g0):real^2->bool`]
         OPEN_INTER_CLOSURE_EQ_EMPTY);
        MP_TAC(ISPECL
         [`inside(path_image d0 UNION path_image g0):real^2->bool`;
          `inside(path_image d1 UNION path_image g0):real^2->bool`]
         OPEN_INTER_CLOSURE_EQ_EMPTY)] THEN
      ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
       [OPEN_INSIDE; CLOSED_UNION; CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `p SUBSET c ==> c INTER i = {} ==> ~(z IN i INTER p)`) THEN
      REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET f ==> s SUBSET t UNION f`) THENL
       [MP_TAC(ISPEC `d0 ++ reversepath g0:real^1->real^2`
         JORDAN_INSIDE_OUTSIDE);
        MP_TAC(ISPEC `reversepath d1 ++ reversepath g0:real^1->real^2`
         JORDAN_INSIDE_OUTSIDE)] THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH;
                   PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
      (ANTS_TAC THENL [ALL_TAC; SET_TAC[]]) THEN
      ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN;
                      PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
      MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
      ASM_REWRITE_TAC[PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH] THEN
      ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATH_IMAGE_REVERSEPATH] THEN
      FIRST
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `e UNION f = d ==> d INTER g SUBSET s ==> e INTER g SUBSET s`));
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `f UNION e = d ==> d INTER g SUBSET s ==> e INTER g SUBSET s`))] THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(ASSUME
       `IMAGE (g:real^1->real^2) (interval [a,b]) = path_image g0`)) THEN
      MP_TAC(ISPECL [`a:real^1`; `b:real^1`] CLOSED_OPEN_INTERVAL_1) THEN
      (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
      REWRITE_TAC[frontier] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `(~(s INTER (t UNION u) = {}) ==> s INTER (v UNION w) = {})
      ==> s INTER t = {} \/ s INTER v = {}`)) THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [MAP_EVERY EXISTS_TAC [`d0:real^1->real^2`; `d1:real^1->real^2`];
      MAP_EVERY EXISTS_TAC
       [`reversepath d1:real^1->real^2`;
        `reversepath d0:real^1->real^2`]] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH;
                    PATHFINISH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (path_image d1):real^2->bool = convex hull (path_image g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      UNDISCH_TAC
       `path_image d:real^2->bool = frontier (convex hull path_image g)` THEN
      ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
       [frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; COMPACT_PATH_IMAGE;
        COMPACT_CONVEX_HULL; SIMPLE_PATH_IMP_PATH] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS
     `convex hull ((path_image g0 UNION path_image g1) INTER
                   (path_image d0 UNION path_image d1)):real^2->bool` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
      MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET THEN
      ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH; INTER_SUBSET] THEN
      REWRITE_TAC[frontier] THEN
      MATCH_MP_TAC(SET_RULE
       `s SUBSET c ==> s DIFF (s INTER (c DIFF i)) SUBSET i`) THEN
      MESON_TAC[SUBSET_TRANS; CLOSURE_SUBSET; HULL_SUBSET];
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC(SET_RULE
       `s INTER t SUBSET u ==> s INTER (t UNION u) SUBSET u`) THEN
      TRANS_TAC SUBSET_TRANS `{(g:real^1->real^2) a,g b}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `s INTER t SUBSET a /\ s INTER u SUBSET a
          ==> (u UNION t) INTER s SUBSET a`) THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `d UNION d' = g ==> g INTER s SUBSET a ==> d INTER s SUBSET a`)) THEN
        SUBST1_TAC(SYM(ASSUME
         `IMAGE (g:real^1->real^2) (interval [a,b]) = path_image g0`)) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[OPEN_CLOSED_INTERVAL_1]) THEN
        ASM SET_TAC[];
        REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
        ASM_MESON_TAC[ARC_IMP_PATH; PATHSTART_IN_PATH_IMAGE;
                      PATHFINISH_IN_PATH_IMAGE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[(g:real^1->real^2) a,g b] SUBSET
    frontier(convex hull (path_image g))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; frontier; IN_DIFF] THEN
    REWRITE_TAC[SET_RULE
     `(!x. x IN s ==> x IN t /\ ~P x) <=>
      s SUBSET t /\ (!x. x IN s ==> ~P x)`] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[frontier; IN_DIFF]) THEN
      ASM_SIMP_TAC[CONVEX_CONTAINS_SEGMENT_IMP;
                   CONVEX_CLOSURE; CONVEX_CONVEX_HULL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_THEN DISJ_CASES_TAC THENL
     [DISCH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[frontier; IN_DIFF]) THEN ASM SET_TAC[]] THEN
    ABBREV_TAC `ga = (g:real^1->real^2) a` THEN
    ABBREV_TAC `gb = (g:real^1->real^2) b` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    GEOM_ORIGIN_TAC `ga:real^2` THEN
    GEOM_BASIS_MULTIPLE_TAC 1 `gb:real^2` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(g:real^1->real^2) a $2 = &0 /\
      (g:real^1->real^2) b $2 = &0`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VEC_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH; REAL_MUL_RZERO];
      UNDISCH_THEN `(g:real^1->real^2) a = vec 0` (SUBST_ALL_TAC o SYM) THEN
      UNDISCH_THEN `(g:real^1->real^2) b = gb % basis 1`
       (SUBST_ALL_TAC o SYM)] THEN
    REWRITE_TAC[SUBSET; frontier; IN_DIFF] THEN
    MP_TAC(ISPECL
     [`(g:real^1->real^2) a`; `(g:real^1->real^2) b`; `z:real^2`]
        SEGMENT_HORIZONTAL) THEN
    ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN
     `~(path_image d1 SUBSET {x:real^2 | &0 <= x$2}) /\
      ~(path_image d1 SUBSET {x:real^2 | x$2 <= &0})`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      DISCH_THEN(MP_TAC o SPEC `convex:(real^2->bool)->bool` o
          MATCH_MP HULL_MONO) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[HULL_P; CONVEX_HALFSPACE_COMPONENT_LE;
               REWRITE_RULE[real_ge] CONVEX_HALFSPACE_COMPONENT_GE] THEN
      DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
      REWRITE_TAC[INTERIOR_HALFSPACE_COMPONENT_LE;
                REWRITE_RULE[real_ge] INTERIOR_HALFSPACE_COMPONENT_GE] THEN
      REWRITE_TAC[real_gt; REAL_LT_LE] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `d1:real^1->real^2` CONNECTED_SIMPLE_PATH_ENDLESS) THEN
    ASM_SIMP_TAC[ARC_IMP_SIMPLE_PATH; connected] THEN
    MAP_EVERY EXISTS_TAC
     [`{x:real^2 | &0 < x$2}`; `{x:real^2 | x$2 < &0}`] THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT;
                REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `w:real^2` THEN REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
      REWRITE_TAC[REAL_ARITH `&0 < x \/ x < &0 <=> ~(x = &0)`] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL
       [`convex hull (path_image g):real^2->bool`;
        `(g:real^1->real^2) a`; `(g:real^1->real^2) b`; `w:real^2`]
      SEGMENT_SUBSET_RELATIVE_FRONTIER_CONVEX_GEN) THEN
      ASM_REWRITE_TAC[NOT_IMP; CONVEX_CONVEX_HULL] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[COLLINEAR_3_2D] THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN ASM SET_TAC[];
        ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
        REWRITE_TAC[frontier] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
          (SET_RULE `z IN i ==> z IN c ==> ~(c SUBSET a DIFF i)`)) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `z IN s ==> s SUBSET t ==> z IN t`)) THEN
        REWRITE_TAC[open_segment] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF f SUBSET t`) THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[]];
      CONJ_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `~(path_image d1 SUBSET {x:real^2 | x$2 <= &0})`;
        UNDISCH_TAC `~(path_image d1 SUBSET {x:real^2 | &0 <= x$2})`] THEN
      MATCH_MP_TAC(SET_RULE
       `s INTER h' = {} /\ h UNION h' = UNIV ==> ~(d SUBSET h)
          ==> ~(h' INTER (d DIFF s) = {})`) THEN
      REWRITE_TAC[EXTENSION; IN_UNIV; NOT_IN_EMPTY; IN_ELIM_THM; IN_INTER;
                  IN_INSERT; IN_UNION] THEN
      (CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_REFL]; REAL_ARITH_TAC])];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image d0 SUBSET segment[(g:real^1->real^2) a,g b] \/
    path_image(reversepath d1) SUBSET segment[(g:real^1->real^2) a,g b]`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_SUBSET_ARC_PAIR THEN
    ASM_SIMP_TAC[ARC_REVERSEPATH_EQ; PATHSTART_REVERSEPATH;
                 PATHFINISH_REVERSEPATH; PATH_IMAGE_REVERSEPATH] THEN
    REWRITE_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT];
    REWRITE_TAC[PATH_IMAGE_REVERSEPATH]] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `interior(convex hull (path_image d1)) SUBSET
      interior(convex hull (segment[(g:real^1->real^2) a,g b]))`
    MP_TAC THENL
     [ASM_SIMP_TAC[SUBSET_INTERIOR; HULL_MONO];
      ASM_SIMP_TAC[HULL_P; CONVEX_SEGMENT; INTERIOR_SEGMENT] THEN
      REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN ASM SET_TAC[]]] THEN
  SUBGOAL_THEN `path_image d0 = segment[(g:real^1->real^2) a,g b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_SUBSET_SEGMENT THEN
    ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; ARC_IMP_PATH] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE;
                  ARC_IMP_PATH];
    ALL_TAC] THEN
  ABBREV_TAC
   `h = \t. if t IN interval(a,b)
            then g(a) + (drop t - drop a) / (drop b - drop a) % (g b - g a)
            else (g:real^1->real^2) t` THEN
  EXISTS_TAC `h:real^1->real^2` THEN
  SUBGOAL_THEN
   `pathstart h:real^2 = pathstart g /\ pathfinish h = pathfinish g`
  MP_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[pathstart; pathfinish] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `IMAGE h (interval(a,b)) = segment((g:real^1->real^2) a,g b)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SEGMENT_IMAGE_INTERVAL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `(\x. if x IN s then f x else g x) = h
      ==> IMAGE f s = t
          ==> IMAGE h s = t`)) THEN
    MP_TAC(ISPECL [`a:real^1`; `b:real^1`]
      (CONJUNCT2 SEGMENT_IMAGE_INTERVAL)) THEN
    ASM_SIMP_TAC[GSYM DROP_EQ; REAL_LT_IMP_LE; REAL_LT_IMP_NE;  SEGMENT_1] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE `(!x. f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[VECTOR_ARITH
     `(&1 - a) % x + a % y:real^N = x + a % (y - x)`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_CMUL] THEN
    UNDISCH_TAC `drop a < drop b` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^1->real^2) a = g a /\ h b = g b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[ENDS_IN_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE h (interval[a,b]) = segment[(g:real^1->real^2) a,g b]`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSED_OPEN_INTERVAL_1; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [EXPAND_TAC "h" THEN SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[simple_path; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT
   `(r ==> p) /\ q /\ r /\ s ==> p /\ q /\ r /\ s`) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [REWRITE_TAC[dist; path] THEN MESON_TAC[LIPSCHITZ_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[]
     `!Q. (!x y. P x y <=> P y x) /\
          (!x y. ~Q x /\ ~Q y ==> P x y) /\
          (!x y. Q x /\ Q y ==> P x y) /\
          (!x y. ~Q x /\ Q y ==> P x y)
      ==> !x y. P x y`) THEN
    EXISTS_TAC `\x:real^1. x IN interval(a,b)` THEN
    CONJ_TAC THENL [MESON_TAC[]; REWRITE_TAC[]] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "h" THEN SIMP_TAC[] THEN
      UNDISCH_TAC `simple_path(g:real^1->real^2)` THEN
      REWRITE_TAC[simple_path] THEN MESON_TAC[];
      EXPAND_TAC "h" THEN SIMP_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL; VECTOR_SUB_EQ] THEN
      ASM_SIMP_TAC[REAL_FIELD
       `a < b ==> ((x - a) / (b - a) = (y - a) / (b - a) <=> x = y)`] THEN
      ASM_SIMP_TAC[DROP_EQ; VECTOR_SUB_EQ];
      MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC
       `IMAGE (g:real^1->real^2) (interval [vec 0,vec 1] DIFF interval (a,b)) =
        path_image g1` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^1` o MATCH_MP (SET_RULE
       `IMAGE f s = t ==> !x. x IN s ==> f x IN t`)) THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
      UNDISCH_TAC
        `(path_image g1 DIFF {(g:real^1->real^2) b, g a}) INTER path_image d0 =
         {}` THEN
      ASM_REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `(g:real^1->real^2) x`) THEN
      ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_DIFF; IN_INTER] THEN
      SUBGOAL_THEN `(g:real^1->real^2) x = h x` SUBST1_TAC THENL
       [EXPAND_TAC "h" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `~(~(x IN {b,a}) /\ x IN t UNION {a,b})
        ==> ~(a IN t) /\ ~(b IN t) ==> ~(x IN t)`)) THEN
      REWRITE_TAC[ENDS_NOT_IN_SEGMENT] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^1 = b)` ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[dist] THEN
    MATCH_MP_TAC LIPSCHITZ_ON_COMBINE THEN EXISTS_TAC `a:real^1` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "h" THEN
      SIMP_TAC[IN_INTERVAL_1; GSYM REAL_NOT_LE; DROP_VEC] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM dist] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LIPSCHITZ_ON_COMBINE THEN EXISTS_TAC `b:real^1` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "h" THEN
      SIMP_TAC[IN_INTERVAL_1; GSYM REAL_NOT_LE; DROP_VEC] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM dist] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
      ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN
     `!t. t IN interval[a,b]
          ==> (h:real^1->real^2) t =
              g a + (drop t - drop a) / (drop b - drop a) % (g b - g a)`
     (fun th -> SIMP_TAC[th])
    THENL
     [ASM_SIMP_TAC[CLOSED_OPEN_INTERVAL_1; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
      REWRITE_TAC[REAL_ARITH `(a - a) / b = &0`; VECTOR_MUL_LZERO] THEN
      REWRITE_TAC[VECTOR_ADD_RID] THEN
      ASM_SIMP_TAC[REAL_FIELD `a < b ==> (b - a) / (b - a) = &1`] THEN
      CONV_TAC VECTOR_ARITH;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(a + x % c) - (a + y % c):real^N = (x - y) % c`] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_FIELD
     `a < b
      ==> (x - a) / (b - a) - (y - a) / (b - a) = (x - y) / (b - a)`] THEN
    REWRITE_TAC[GSYM DROP_SUB; ABS_DROP; REAL_ARITH
     `a / b * c:real = (a * c) / b`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[path_length] THEN
    MP_TAC(GEN `f:real^1->real^2`
     (ISPECL [`f:real^1->real^2`; `vec 0:real^1`; `vec 1:real^1`; `a:real^1`]
        VECTOR_VARIATION_COMBINE)) THEN
    ASM_REWRITE_TAC[CONJ_ASSOC; GSYM IN_INTERVAL_1] THEN
    DISCH_THEN(fun th ->
     MP_TAC(SPEC `h:real^1->real^2` th) THEN
     MP_TAC(SPEC `g:real^1->real^2` th)) THEN
    REPEAT(ANTS_TAC THENL
     [MATCH_MP_TAC LIPSCHITZ_IMP_HAS_BOUNDED_VARIATION THEN
      REWRITE_TAC[BOUNDED_INTERVAL; GSYM dist] THEN ASM_MESON_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    MATCH_MP_TAC(REAL_ARITH `a:real = b /\ c < d ==> a + c < b + d`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VECTOR_VARIATION_EQ THEN EXPAND_TAC "h" THEN
      SIMP_TAC[IN_INTERVAL_1; GSYM REAL_NOT_LE];
      ALL_TAC] THEN
    MP_TAC(GEN `f:real^1->real^2`
     (ISPECL [`f:real^1->real^2`; `a:real^1`; `vec 1:real^1`; `b:real^1`]
        VECTOR_VARIATION_COMBINE)) THEN
    ASM_SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; REAL_LT_IMP_LE] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_INTERVAL_1]; ALL_TAC] THEN
    DISCH_THEN(fun th ->
     MP_TAC(SPEC `h:real^1->real^2` th) THEN
     MP_TAC(SPEC `g:real^1->real^2` th)) THEN
    REPEAT(ANTS_TAC THENL
     [MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIPSCHITZ_IMP_HAS_BOUNDED_VARIATION THEN
        REWRITE_TAC[BOUNDED_INTERVAL; GSYM dist] THEN ASM_MESON_TAC[];
        REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
        ASM_REAL_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    MATCH_MP_TAC(REAL_ARITH `a:real = b /\ c < d ==> c + a < d + b`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VECTOR_VARIATION_EQ THEN EXPAND_TAC "h" THEN
      SIMP_TAC[IN_INTERVAL_1; GSYM REAL_NOT_LE];
      ALL_TAC] THEN
    TRANS_TAC REAL_LET_TRANS
     `vector_variation (interval[a,b])
                       (\t. g a + (drop t - drop a) / (drop b - drop a) %
                                  ((g:real^1->real^2) b - g a))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC VECTOR_VARIATION_EQ THEN
      X_GEN_TAC `t:real^1` THEN
      ASM_SIMP_TAC[CLOSED_OPEN_INTERVAL_1; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
      REWRITE_TAC[REAL_ARITH `(a - a) / b = &0`; VECTOR_MUL_LZERO] THEN
      REWRITE_TAC[VECTOR_ADD_RID] THEN
      ASM_SIMP_TAC[REAL_FIELD `a < b ==> (b - a) / (b - a) = &1`] THEN
      CONV_TAC VECTOR_ARITH;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_VARIATION_TRANSLATION] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      VECTOR_VARIATION_VMUL o lhand o snd) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div; LIFT_CMUL] THEN
    REWRITE_TAC[LIFT_DROP; LIFT_SUB] THEN
    REWRITE_TAC[VECTOR_ARITH `c % (x - a):real^N = --(c % a) + c % x`] THEN
    SIMP_TAC[VECTOR_VARIATION_TRANSLATION;
             HAS_BOUNDED_VARIATION_ON_TRANSLATION;
             HAS_BOUNDED_VARIATION_ON_CMUL_EQ; VECTOR_VARIATION_CMUL;
             HAS_BOUNDED_VARIATION_ON_ID; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[VECTOR_VARIATION_ID] THEN
    ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; REAL_ARITH `a < b ==> ~(b < a)`] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; real_abs; REAL_SUB_LE; REAL_LT_IMP_LE;
                 REAL_FIELD `a < b ==> inv(b - a) * (b - a) = &1`] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_LT_LE] THEN
    SUBGOAL_THEN `(g:real^1->real^2) has_bounded_variation_on interval[a,b]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LIPSCHITZ_IMP_HAS_BOUNDED_VARIATION THEN
        REWRITE_TAC[BOUNDED_INTERVAL; GSYM dist] THEN ASM_MESON_TAC[];
        REWRITE_TAC[SUBSET_INTERVAL_1; DROP_VEC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN
      ASM_SIMP_TAC[SEGMENT_1; REAL_LT_IMP_LE; SUBSET_REFL];
      ALL_TAC] THEN
    ABBREV_TAC `c:real^1 = midpoint(a,b)` THEN
    MP_TAC(ISPECL [`g:real^1->real^2`; `a:real^1`; `b:real^1`; `c:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
    SUBGOAL_THEN `drop a < drop c /\ drop c < drop b` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[midpoint; DROP_CMUL; DROP_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!c:real^N. (norm(c - a) <= v /\ norm(b - c) <= w) /\
                 ~(dist(a,b) = dist(a,c) + dist(c,b))
                 ==> ~(norm(b - a) = v + w)`) THEN
    EXISTS_TAC `(g:real^1->real^2) c` THEN CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN
      ASM_SIMP_TAC[SEGMENT_1; REAL_LT_IMP_LE; SUBSET_REFL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM between; BETWEEN_IN_SEGMENT]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(x IN t) ==> ~(x IN s)`)) THEN
    REWRITE_TAC[frontier; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE g i SUBSET j ==> c IN i ==> g c IN j`)) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE g (interval [vec 0,vec 1] DIFF interval (a,b)) UNION
                IMAGE (h:real^1->real^2) (interval(a,b))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC[path_image] THEN SET_TAC[];
      REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; HULL_SUBSET]; ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS `segment[(g:real^1->real^2) a,g b]` THEN
    REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUBSET_TRANS)) THEN
    REWRITE_TAC[FRONTIER_SUBSET_EQ] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH];
    TRANS_TAC SUBSET_TRANS
     `convex hull
       (IMAGE (g:real^1->real^2)
              (interval[vec 0,vec 1] DIFF interval(a,b)))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC HULL_MONO THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[path_image] THEN SET_TAC[]]);;
```

### Informal statement
For any function `g` from real numbers to pairs of real numbers, any real numbers `a` and `b`, and any real number `L`, if:
1. `g` is a simple path, and
2. The endpoint of the path `g` is equal to its starting point, and
3. For all real numbers `x` and `y` in the interval `[0, 1]`, the distance between `g(x)` and `g(y)` is less than or equal to `L` times the distance between `x` and `y`, and
4. The first component of `a` is less than the first component of `b`, and
5. `a` is in the interval `[0, 1]`, and
6. `b` is in the interval `[0, 1]`, and
7. `g(a)` is in the frontier of the convex hull of the image of `g`, and
8. `g(b)` is in the frontier of the convex hull of the image of `g`, and
9. The image of `g` over the open interval `(a, b)` has an empty intersection with the frontier of the convex hull of the image of `g`,

then there exists a function `h` such that:
1. `h` is a simple path, and
2. The starting point of `h` is the same as the starting point of `g`, and the endpoint of `h` is the same as the starting point of `g`, and
3. For all real numbers `x` and `y` in the interval `[0, 1]`, the distance between `h(x)` and `h(y)` is less than or equal to `L` times the distance between `x` and `y`, and
4. The path length of `h` is less than the path length of `g`, and
5. The convex hull of the image of `h` is equal to the convex hull of the image of `g`, and
6. For all real numbers `x`, if `x` is not in the interval `(a, b)`, then `h(x)` is equal to `g(x)`, and
7. The image of `h` over the interval `[a, b]` is a subset of the frontier of the convex hull of the image of `g`.

### Informal sketch
The theorem states that given a simple closed path `g` that is Lipschitz continuous and has a segment `(a,b)` whose image under `g` lies in the interior of the convex hull of the path's image, one can construct another simple closed Lipschitz continuous path `h` that agrees with `g` outside `(a,b)`, whose image has the same convex hull, and which is shorter than `g`. The image of `h` over `[a,b]` lies on the frontier of the convex hull of the image of `g`.

The proof proceeds as follows:
- First, it handles the case where the interval `(a, b)` is empty, quickly discharging the goal.
- The main part of the proof addresses the case where `(a, b)` is non-empty.
    - It first proves that the image of `g` over `(a,b)` is a subset of the interior of the convex hull of the image of `g`.
    - Also, the proof considers the case where `g a = g b`
    - Applying `EXISTS_DOUBLE_ARC_EXPLICIT`.
    - It then applies `RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX`.
    - It uses the lemma `EXISTS_DOUBLE_ARC` to establish existence of two arcs `d0` and `d1` connecting `g a` and `g b`.
    - It applies `SPLIT_INSIDE_SIMPLE_CLOSED_CURVE`, `CONNECTED_SIMPLE_PATH_ENDLESS`
    - Proving that the `convex hull (path_image d1) = convex hull (path_image g)`
    - Proving that `segment[(g:real^1->real^2) a,g b] SUBSET frontier(convex hull (path_image g))`
    - The function `h` is explicitly constructed to be equal to `g` outside the interval `(a,b)`, and to traverse the line segment from `g a` to `g b` inside the interval.
    - The lemma `SEGMENT_HORIZONTAL` states that if `z` belongs to `[a,b]` then `h(z)` also belong to `[a,b]`.
    - Exploiting `CONNECTED_SUBSET_ARC_PAIR` to show that `path_image d0 SUBSET segment[(g:real^1->real^2) a,g b] \/ path_image(reversepath d1) SUBSET segment[(g:real^1->real^2) a,g b]`
    - It then shows that `h` is equal to `g` when `t` does not belong to the interval `(a,b)` by using `pathstart` and `pathfinish`.
    - Then, it's proved that `IMAGE h (interval(a,b)) = segment((g:real^1->real^2) a,g b)`.
    - The rest of the proof consists of verifying that `h` has the required properties (`simple_path`, `pathstart h = pathstart g`, `pathfinish h = pathfinish g`, `lipschitz`, `path_length`, `convex hull`).

### Mathematical insight
This lemma provides a key step in showing that any rectifiable simple closed curve can be "convexified", i.e., transformed into a convex set without increasing its length. It shows that, given a non-convex simple closed curve, one can always find a shortcut that decreases the perimeter while preserving the convex hull. This is a step toward proving that a curve has at least as great a length as the perimeter of its convex hull.
### Dependencies
- `INTERVAL_NE_EMPTY_1`
- `frontier`
- `GSYM path_image`
- `SET_RULE`
- `CLOSURE_SUBSET`
- `HULL_SUBSET`
- `IMAGE_SUBSET`
- `SUBSET_INTERVAL_1`
- `DROP_VEC`
- `IN_INTERVAL_1`
- `CONVEX_HULL_REDUNDANT_SUBSET`
- `COMPACT_PATH_IMAGE`
- `SIMPLE_PATH_IMP_PATH`
- `IMAGE_CLAUSES`
- `GSYM SEGMENT_CONVEX_HULL`
- `INTERIOR_SEGMENT`
- `DIMINDEX_2`
- `LE_REFL`
- `SUBSET_ANTISYM`
- `HULL_MONO`
- `SUBSET_UNION`
- `HULL_MINIMAL`
- `CONVEX_CONVEX_HULL`
- `REWRITE_TAC`
- `UNION_SUBSET`
- `INSERT_SUBSET`
- `EMPTY_SUBSET`
- `FUN_IN_IMAGE`
- `IN_DIFF`
- `ENDS_IN_INTERVAL`
- `EXISTS_DOUBLE_ARC_EXPLICIT`
- `REAL_LT_IMP_LE`
- `LEFT_IMP_EXISTS_THM`
- `RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX`
- `RELATIVE_FRONTIER_NONEMPTY_INTERIOR`
- `BOUNDED_CONVEX_HULL`
- `BOUNDED_PATH_IMAGE`
- `AFF_DIM_NONEMPTY_INTERIOR`
- `EXISTS_DOUBLE_ARC`
- `PATH_IMAGE_REVERSEPATH`
- `SIMPLE_PATH_REVERSEPATH_EQ`
- `PATHSTART_REVERSEPATH`
- `PATHFINISH_REVERSEPATH`
- `INSIDE_FRONTIER_EQ_INTERIOR`
- `ARC_IMP_SIMPLE_PATH`
- `CLOSED_OPEN_INTERVAL_1`
- `PATHSTART_IN_PATH_IMAGE`
- `PATHFINISH_IN_PATH_IMAGE`
- `CONNECTED_SIMPLE_PATH_ENDLESS`
- `REWRITE_TAC`
- `CONNECTED_OPEN_IN`
- `NOT_EXISTS_THM`
- `JORDAN_INSIDE_OUTSIDE`
- `CLOSURE_UNION_FRONTIER`
- `ARC_REVERSEPATH_EQ`
- `PATH_IMAGE_REVERSEPATH`
- `PATHFINISH_JOIN`
- `PATHSTART_JOIN`
- `SIMPLE_PATH_JOIN_LOOP`
- `SET_RULE`
- `OPEN_INTER_CLOSURE_EQ_EMPTY`
- `OPEN_INSIDE`
- `CLOSED_UNION`
- `CLOSED_PATH_IMAGE`
- `ARC_IMP_PATH`
- `EXTENSION`
- `CONVEX_CONTAINS_SEGMENT_IMP`
- `CONVEX_CLOSURE`
- `SEGMENT_CLOSED_OPEN`
- `IN_UNION`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `GEOM_ORIGIN_TAC`
- `GEOM_BASIS_MULTIPLE_TAC`
- `VEC_COMPONENT`
- `VECTOR_MUL_COMPONENT`
- `BASIS_COMPONENT`
- `ARITH`
- `REAL_MUL_RZERO`
- `SEGMENT_HORIZONTAL`
- `OPEN_HALFSPACE_COMPONENT_LT`
- `OPEN_HALFSPACE_COMPONENT_GT`
-`connected`
- `REAL_ARITH`
- `SEGMENT_SUBSET_RELATIVE_FRONTIER_CONVEX_GEN`
- `ENDS_IN_SEGMENT`
- `CONNECTED_SEGMENT`
- `VECTOR_ARITH`
- `DIST`
- `LIPSCHITZ_IMP_CONTINUOUS_ON`
- `ENDS_NOT_IN_SEGMENT`
- `LIPSCHITZ_ON_COMBINE`
- `DOMAIN`
- `ABS_DROP`
- `NORM_POS_LT`
- `VECTOR_SUB_EQ`
- `REAL_LE_LDIV_EQ`
- `NORM_POS_LE`
- `CONNECTED_SUBSET_ARC_PAIR`
- `path`
- `ENDS_IN_INTERVAL`
- `SEGMENT_IMAGE_INTERVAL`
- `LIPSCHITZ_IMP_HAS_BOUNDED_VARIATION`
- `midpoint`
- `REAL_NOT_LE`
- `DOMAIN`
- `OPEN_CLOSED_INTERVAL_1`
- `REAL_LT_IMP_LE`
- `VECTOR_ADD_RID`
- `CLOSED_OPEN_INTERVAL_1`
- `VECTOR_ARITH`
- `between`
- `has_bounded_variation_on`
- `COMPACT_IMP_CLOSED`
- `COMPACT_CONVEX_HULL`
- `COMPACT_PATH_IMAGE`
- `BETWEEN_IN_SEGMENT`
- `REAL_LET_TRANS`
- `o_DEF`
- `PATH_IN_FRONTIER`
- `VECTOR_VARIATION_COMBINE`

### Porting notes (optional)
- The proof makes heavy use of geometric reasoning and set theory. Porting may require corresponding geometric lemmas in the target proof assistant.
- The tactic `GEOM_ORIGIN_TAC` and `GEOM_BASIS_MULTIPLE_TAC` likely point to a geometric context within HOL Light; recreating this may require geometric constructions.
- The extensive use of real arithmetic tactics (`ASM_REAL_ARITH_TAC`) can be a challenge in systems with weaker automation for real number reasoning.
- The handling of `IMAGE` and set operations would need to be aligned between systems.


---

## ISOPERIMETRIC_CONVEXIFICATION

### Name of formal statement
ISOPERIMETRIC_CONVEXIFICATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOPERIMETRIC_CONVEXIFICATION = prove
 (`!g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g
        ==> ?h:real^1->real^2.
                rectifiable_path h /\
                simple_path h /\
                pathfinish h = pathstart h /\
                path_length h <= path_length g /\
                convex hull (path_image h) = convex hull (path_image g) /\
                path_image h = frontier(convex hull (path_image g))`,
  SUBGOAL_THEN
   `!g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        pathstart g IN frontier(convex hull (path_image g))
        ==> ?h:real^1->real^2.
                rectifiable_path h /\
                simple_path h /\
                pathfinish h = pathstart h /\
                path_length h <= path_length g /\
                convex hull (path_image h) = convex hull (path_image g) /\
                path_image h = frontier(convex hull (path_image g))`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`path_image g:real^2->bool`; `{}:real^2->bool`]
        CONVEX_HULL_REDUNDANT_SUBSET) THEN
    REWRITE_TAC[EMPTY_SUBSET; DIFF_EMPTY; CONVEX_HULL_EMPTY] THEN
    REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; PATH_IMAGE_NONEMPTY] THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV o RAND_CONV)
        [path_image] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `shiftpath t (g:real^1->real^2)`) THEN
    ASM_SIMP_TAC[RECTIFIABLE_PATH_SHIFTPATH; SIMPLE_PATH_SHIFTPATH] THEN
    ASM_SIMP_TAC[PATH_LENGTH_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[PATHSTART_SHIFTPATH; PATHFINISH_SHIFTPATH] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[frontier; IN_DIFF] THEN
    MATCH_MP_TAC CLOSURE_INC THEN MATCH_MP_TAC HULL_INC THEN
    REWRITE_TAC[path_image; IN_INTERVAL_1; DROP_VEC; IN_IMAGE] THEN
    ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = path_length(g:real^1->real^2)` THEN
  MP_TAC(ISPEC `g:real^1->real^2` ARC_LENGTH_REPARAMETRIZATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^1->real^2` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 <= L /\
    path_length g' = L /\
    simple_path(g':real^1->real^2) /\
    rectifiable_path(g':real^1->real^2) /\
    pathfinish g' = pathstart g' /\
    pathstart g' IN frontier(convex hull (path_image g')) /\
    (!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1]
           ==> dist(g' x,g' y) <= L * dist(x,y))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PATH_LENGTH_POS_LE; SIMPLE_PATH_IMP_PATH];
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`g':real^1->real^2`,`g:real^1->real^2`)] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `(path_image g:real^2->bool) SUBSET frontier(convex hull path_image g)`
  THENL
   [EXISTS_TAC `g:real^1->real^2` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC lemma3 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a b. (!n. a n IN interval[vec 0,vec 1]) /\
          (!n. b n IN interval[vec 0,vec 1]) /\
          (!n:num. drop(a n) <= drop(b n)) /\
          (!n. g(a n) IN frontier(convex hull (path_image g))) /\
          (!n. g(b n) IN frontier(convex hull (path_image g))) /\
          components
            {t | t IN interval[vec 0,vec 1] /\
                 (g:real^1->real^2) t IN
                 (:real^2) DIFF frontier(convex hull (path_image g))} =
          {interval(a n,b n) | n IN (:num)}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `open_in (subtopology euclidean (interval[vec 0,vec 1]))
              {t | t IN interval[vec 0,vec 1] /\
                   (g:real^1->real^2) t IN
                   (:real^2) DIFF frontier(convex hull (path_image g))}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
      REWRITE_TAC[GSYM closed; FRONTIER_CLOSED] THEN
      MATCH_MP_TAC LIPSCHITZ_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[GSYM dist] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `s =
        {t | t IN interval[vec 0,vec 1] /\
             (g:real^1->real^2) t IN
             (:real^2) DIFF frontier(convex hull (path_image g))}` THEN
    ASM_CASES_TAC `s:real^1->bool = {}` THENL
     [UNDISCH_TAC `s:real^1->bool = {}` THEN EXPAND_TAC "s" THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `{t | t IN k /\ g t IN UNIV DIFF f} = {}
        ==> IMAGE g k SUBSET f`)) THEN
      ASM_REWRITE_TAC[GSYM path_image];
      ALL_TAC] THEN
    SUBGOAL_THEN `COUNTABLE(components(s:real^1->bool))` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC COUNTABLE_COMPONENTS THEN
      MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_SIMP_TAC[CONVEX_IMP_LOCALLY_CONNECTED; CONVEX_INTERVAL];
      ALL_TAC] THEN
    MP_TAC(ISPEC `components(s:real^1->bool)` COUNTABLE_AS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPONENTS_EQ_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:num->real^1->bool`) THEN
    SUBGOAL_THEN `!n:num. ?a b:real^1. q n = interval(a,b)` MP_TAC THENL
     [X_GEN_TAC `n:num` THEN
      MP_TAC(ISPEC `closure((q:num->real^1->bool) n)`
        CONNECTED_COMPACT_INTERVAL_1) THEN
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CLOSURE THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `s = IMAGE q UNIV
            ==> (!x. x IN s ==> connected x) ==> connected(q n)`)) THEN
          REWRITE_TAC[IN_COMPONENTS_CONNECTED];
          REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE] THEN
          MATCH_MP_TAC BOUNDED_SUBSET THEN
          EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN
          MATCH_MP_TAC CLOSURE_MINIMAL THEN
          REWRITE_TAC[CLOSED_INTERVAL]];
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^1` THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^1` THEN
        REWRITE_TAC[GSYM INTERIOR_INTERVAL] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
        TRANS_TAC EQ_TRANS `interior((q:num->real^1->bool) n)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_INTERIOR_CLOSURE THEN
          REWRITE_TAC[CONVEX_CONNECTED_1] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `s = IMAGE q UNIV
            ==> (!x. x IN s ==> connected x) ==> connected(q n)`)) THEN
          REWRITE_TAC[IN_COMPONENTS_CONNECTED];
          ALL_TAC] THEN
        MATCH_MP_TAC INTERIOR_OPEN THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
        EXISTS_TAC `interval(vec 0:real^1,vec 1)` THEN
        REWRITE_TAC[OPEN_INTERVAL] THEN
        MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
        REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `s:real^1->bool` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
            CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
            MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
            EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
            SIMP_TAC[CONVEX_IMP_LOCALLY_CONNECTED; CONVEX_INTERVAL];
            ALL_TAC] THEN
          EXPAND_TAC "s" THEN
          MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
          ASM_SIMP_TAC[GSYM path; RECTIFIABLE_PATH_IMP_PATH] THEN
          REWRITE_TAC[GSYM closed; FRONTIER_CLOSED];
          REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN
          MATCH_MP_TAC(SET_RULE
           `(~(a IN t) /\ ~(b IN t)) /\ t SUBSET s
            ==> t SUBSET s DIFF {a,b}`) THEN
          CONJ_TAC THENL
           [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `s = IMAGE q UNIV ==> ~(a IN UNIONS s) ==> ~(a IN q n)`)) THEN
            REWRITE_TAC[GSYM UNIONS_COMPONENTS] THEN EXPAND_TAC "s" THEN
            RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
            ASM SET_TAC[];
            ALL_TAC]]] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s = IMAGE q UNIV
          ==> UNIONS s SUBSET t
              ==> q n SUBSET t`)) THEN
        REWRITE_TAC[GSYM UNIONS_COMPONENTS] THEN EXPAND_TAC "s" THEN
        REWRITE_TAC[SUBSET_RESTRICT];
      REWRITE_TAC[SKOLEM_THM]] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num->real^1` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real^1` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `!n. drop((a:num->real^1) n) < drop(b n)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INTERVAL_NE_EMPTY_1] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o LAND_CONV) [GSYM th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s = IMAGE q UNIV
        ==> (!c. c IN s ==> ~(c = {})) ==> !n. ~(q n = {})`)) THEN
      REWRITE_TAC[IN_COMPONENTS_NONEMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `!n. interval((a:num->real^1) n,b n) SUBSET s`
    ASSUME_TAC THENL
     [GEN_TAC THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s = IMAGE q UNIV
        ==> (!c. c IN s ==> c SUBSET t) ==> q n SUBSET t`)) THEN
      GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. closure(interval((a:num->real^1) n,b n)) SUBSET interval[vec 0,vec 1]`
    MP_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      REWRITE_TAC[CLOSED_INTERVAL] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[CLOSURE_OPEN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
      DISCH_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(TAUT `(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1;
                    REAL_LT_IMP_LE];
      STRIP_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [CONJ_TAC THEN X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`s:real^1->bool`; `interval((a:num->real^1) n,b n)`]
       IN_COMPONENTS_MAXIMAL) THEN
      (DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
        [ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
         DISCH_THEN(MP_TAC o last o CONJUNCTS)])
      THENL
       [DISCH_THEN(MP_TAC o SPEC
         `(a:num->real^1) n INSERT interval(a n,b n)`);
        DISCH_THEN(MP_TAC o SPEC
         `(b:num->real^1) n INSERT interval(a n,b n)`)] THEN
      REWRITE_TAC[NOT_INSERT_EMPTY; INSERT_SUBSET; IMP_CONJ] THEN
      (ANTS_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
      MATCH_MP_TAC(TAUT
       `q /\ ~s /\ r /\ (~t ==> p) ==> (p ==> q ==> r ==> s) ==> t`) THEN
      REWRITE_TAC[SET_RULE `x INSERT s = s <=> x IN s`; ENDS_IN_INTERVAL] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
      SIMP_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
      EXISTS_TAC `interval((a:num->real^1) n,b n)` THEN
      ASM_SIMP_TAC[CLOSURE_INTERVAL; INTERVAL_EQ_EMPTY_1] THEN
      ASM_REWRITE_TAC[GSYM REAL_NOT_LT; CONNECTED_INTERVAL] THEN
      REWRITE_TAC[INSERT_SUBSET; ENDS_IN_INTERVAL] THEN
      REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED; INTERVAL_NE_EMPTY_1] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN SET_TAC[];
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?h. (!n. simple_path (h n) /\
             rectifiable_path (h n) /\
             pathstart (h n) = pathstart g /\
             pathfinish (h n) = pathfinish g /\
             convex hull path_image (h n) = convex hull path_image g /\
             (!x y.
                x IN interval [vec 0,vec 1] /\ y IN interval [vec 0,vec 1]
                ==> dist (h n x,h n y) <= L * dist (x,y)) /\
             (!x.
                x IN UNIONS {interval (a m,b m) | m < n}
                ==> h n x IN frontier (convex hull path_image g)) /\
             (!x. ~(x IN UNIONS {interval (a m,b m) | m < n})
                  ==> h n x = g x)) /\
        (!n x. ~(x IN interval(a n,b n) /\
                 !m. m < n ==> ~(x IN interval(a m,b m)))
               ==> (h:num->real^1->real^2)(SUC n) x = h n x)`
  MP_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [EXISTS_TAC `g:real^1->real^2` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LT] THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `h:real^1->real^2`] THEN STRIP_TAC THEN
    ASM_CASES_TAC
     `interval(a n,b n) = {} \/
      ?m. m:num < n /\
          interval(a(n):real^1,b(n)) SUBSET interval(a m,b m)`
    THENL
     [SUBGOAL_THEN
       `UNIONS {interval(a m:real^1,b m) | m < SUC n} =
        UNIONS {interval(a m:real^1,b m) | m < n}`
      SUBST1_TAC THENL
       [REWRITE_TAC[LT; UNIONS_GSPEC] THEN ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `h:real^1->real^2` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
      REWRITE_TAC[INTERVAL_NE_EMPTY_1; NOT_EXISTS_THM] THEN
      REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN STRIP_TAC] THEN
    MP_TAC(ISPECL
     [`h:real^1->real^2`; `(a:num->real^1) n`; `(b:num->real^1) n`;
      `L:real`] STEP_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(h:real^1->real^2)(a(n:num)) = g(a n) /\
      (h:real^1->real^2)(b(n:num)) = g(b n)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s = {i n | n IN (:num)} ==> ~(x IN UNIONS s)
        ==> ~(x IN UNIONS {i n | P n})`)) THEN
      REWRITE_TAC[UNIONS_INSERT; UNION_EMPTY; GSYM UNIONS_COMPONENTS] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN interval(a(n:num),b n) ==> (h:real^1->real^2) x = g x`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `(!m. m < n ==> ~(k n SUBSET k m))
        ==> x IN k n /\
            (!s t. s IN {k n | n IN (:num)} /\
                   t IN {k n | n IN (:num)} /\
                   ~(s = t)
                   ==> DISJOINT s t)
            ==> ~(?m. m < n /\ x IN k m)`)) THEN
      ASM_REWRITE_TAC[GSYM pairwise] THEN
      FIRST_X_ASSUM(fun th ->
       GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      REWRITE_TAC[PAIRWISE_INSERT; DISJOINT_EMPTY] THEN
      REWRITE_TAC[PAIRWISE_DISJOINT_COMPONENTS];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `(!x. x IN s ==> h x = g x)
        ==> IMAGE g s INTER k = j
            ==> IMAGE h s INTER k = j`)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s = {k n | n IN (:num)}
        ==> IMAGE g (UNIONS s) INTER f = {}
            ==> IMAGE g (k n) INTER f = {}`)) THEN
      REWRITE_TAC[UNIONS_INSERT; UNION_EMPTY; GSYM UNIONS_COMPONENTS] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC `f:real^1->real^2` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIPSCHITZ_IMP_RECTIFIABLE_PATH THEN
      REWRITE_TAC[GSYM dist] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LT; SET_RULE
     `{f x | x = a \/ P x} = (f a) INSERT {f x | P x}`] THEN
    ASM_REWRITE_TAC[UNIONS_INSERT; FORALL_IN_UNION] THEN
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `IMAGE f c SUBSET t
        ==> i SUBSET c ==> !x. x IN i ==> f x IN t`)) THEN
      REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED];
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^1->real^2) x = h x`
       (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `(!m. m < n ==> ~(k n SUBSET k m))
          ==> (x IN UNIONS {k m | m < n}) /\
              (!s t. s IN {k n | n IN (:num)} /\
                     t IN {k n | n IN (:num)} /\
                     ~(s = t)
                     ==> DISJOINT s t)
              ==> ~(x IN k n)`)) THEN
      ASM_REWRITE_TAC[GSYM pairwise] THEN
      FIRST_X_ASSUM(fun th ->
         GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      REWRITE_TAC[PAIRWISE_INSERT; DISJOINT_EMPTY] THEN
      REWRITE_TAC[PAIRWISE_DISJOINT_COMPONENTS];
      X_GEN_TAC `x:real^1` THEN
      ASM_CASES_TAC `x IN interval((a:num->real^1) n,b n)` THEN
      ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `(!m. m < n ==> ~(k n SUBSET k m))
         ==> x IN k n /\
            (!s t. s IN {k n | n IN (:num)} /\
                       t IN {k n | n IN (:num)} /\
                       ~(s = t)
                       ==> DISJOINT s t)
            ==> ~(!m. m < n ==> ~(x IN k m)) ==> p`)) THEN
       ASM_REWRITE_TAC[GSYM pairwise] THEN
       FIRST_X_ASSUM(fun th ->
           GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
       REWRITE_TAC[PAIRWISE_INSERT; DISJOINT_EMPTY] THEN
       REWRITE_TAC[PAIRWISE_DISJOINT_COMPONENTS]];
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^1->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. ?y. x IN interval[vec 0,vec 1]
            ==> eventually (\n. (f:num->real^1->real^2) n x = y) sequentially`
  MP_TAC THENL
   [X_GEN_TAC `x:real^1` THEN
    ASM_CASES_TAC `(x:real^1) IN interval[vec 0,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC
     `(x:real^1) IN UNIONS {interval (a n,b n) | n IN (:num)}`
    THENL
     [ALL_TAC;
      EXISTS_TAC `(g:real^1->real^2) x` THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
    REWRITE_TAC[EXISTS_IN_GSPEC; IN_UNIV] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:num->real^1->real^2) (n + 1) x` THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `n + 1` THEN
    MATCH_MP_TAC(MESON[LE_EXISTS]
     `(!d:num. P(n + d)) ==> (!m. n <= m ==> P m)`) THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `n:num` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `h:real^1->real^2` THEN DISCH_THEN(LABEL_TAC "*") THEN
  SUBGOAL_THEN
   `!x y. x IN interval[vec 0,vec 1] /\ y IN interval[vec 0,vec 1]
          ==> dist((h:real^1->real^2) x,h y) <= L * dist(x,y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REMOVE_THEN "*"
     (fun th ->
       MP_TAC(SPEC `y:real^1` th) THEN MP_TAC(SPEC `x:real^1` th)) THEN
    ASM_REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIPSCHITZ_IMP_RECTIFIABLE_PATH THEN
    REWRITE_TAC[GSYM dist] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[simple_path; RECTIFIABLE_PATH_IMP_PATH] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN STRIP_TAC THEN
    REMOVE_THEN "*"
     (fun th ->
       MP_TAC(SPEC `y:real^1` th) THEN MP_TAC(SPEC `x:real^1` th)) THEN
    ASM_REWRITE_TAC[IMP_IMP; GSYM EVENTUALLY_AND] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[simple_path]) THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REMOVE_THEN "*"
     (fun th ->
       MP_TAC(SPEC `vec 0:real^1` th) THEN
       MP_TAC(SPEC `vec 1:real^1` th)) THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; IMP_IMP; GSYM EVENTUALLY_AND] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[pathstart; pathfinish];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_LENGTH_LIPSCHITZ THEN
    ASM_REWRITE_TAC[GSYM dist];
    DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [DISCH_THEN(fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC th) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC lemma3 THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [path_image] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^1` THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `?n. x IN interval((a:num->real^1) n,b n)` THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `n:num`) THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N + SUC n`)) THEN
      REWRITE_TAC[LE_ADD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      REMOVE_THEN "*" (MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
      REWRITE_TAC[LE_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN `(f:num->real^1->real^2) n x = g x` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN
        ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `c = {k n | n IN (:num)}
          ==> ~(?n. x IN k n) /\ (~(g(x) IN t) ==> x IN UNIONS c)
              ==> g x IN t`)) THEN
        ASM_REWRITE_TAC[GSYM UNIONS_COMPONENTS] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    GEN_REWRITE_TAC LAND_CONV [path_image] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^1` THEN
    DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `x:real^1`) THEN
    ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `convex hull path_image g =
      convex hull path_image((f:num->real^1->real^2) n)`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[path_image] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  TRANS_TAC SUBSET_TRANS
   `convex hull IMAGE (g:real^1->real^2)
    (interval[vec 0,vec 1] DIFF UNIONS {interval(a n,b n) | n IN (:num)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
    MATCH_MP_TAC CONVEX_HULL_REDUNDANT_SUBSET THEN
    ASM_SIMP_TAC[COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
    REWRITE_TAC[path_image] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM SET_DIFF_FRONTIER] THEN
    MATCH_MP_TAC(SET_RULE
     `p SUBSET c /\ DISJOINT (p DIFF q) f
      ==> p DIFF q SUBSET c DIFF f`) THEN
    REWRITE_TAC[HULL_SUBSET] THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN k /\ x IN j ==> ~(g x IN t))
      ==> DISJOINT (IMAGE g k DIFF IMAGE g (k DIFF j)) t`) THEN
    X_GEN_TAC `x:real^1` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM UNIONS_COMPONENTS; GSYM path_image] THEN ASM SET_TAC[];
    MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[path_image] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN k DIFF j ==> h x = g x)
      ==> IMAGE g (k DIFF j) SUBSET IMAGE h k`) THEN
    X_GEN_TAC `x:real^1` THEN
    SIMP_TAC[UNIONS_GSPEC; IN_DIFF; NOT_EXISTS_THM; IN_ELIM_THM; IN_UNIV] THEN
    STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o SPEC `x:real^1`) THEN
    ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[UNIONS_GSPEC] THEN
    ASM SET_TAC[]]);;
```
### Informal statement
For every function `g` from real numbers to pairs of real numbers (i.e., a path) such that `g` is a rectifiable path, `g` is a simple path, and the endpoint of `g` is equal to the starting point of `g`, there exists a function `h` from real numbers to pairs of real numbers such that `h` is a rectifiable path, `h` is a simple path, the endpoint of `h` is equal to the starting point of `h`, the path length of `h` is less than or equal to the path length of `g`, the convex hull of the image of `h` is equal to the convex hull of the image of `g`, and the image of `h` is equal to the frontier of the convex hull of the image of `g`.

### Informal sketch
The proof demonstrates that any rectifiable, simple, closed path can be transformed into another rectifiable, simple, closed path `h` whose image is the frontier of the convex hull of the original path's image, without increasing the path length.

- The proof proceeds by establishing a subgoal that handles the case where the starting point of the path `g` lies on the frontier of the convex hull of `g`'s image.

- It then uses `CONVEX_HULL_REDUNDANT_SUBSET` to remove redundancy in the convex hull calculation if the path image is already or results in a subset of the convex hull.

- The proof uses `shiftpath` tactic, which shifts the path `g` to ensure that the start point is suitable for further analysis without altering essential properties like arc length, image, simplicity, or the rectifiable nature of the path.

- It introduces an arc-length reparametrization `g'` of `g` using `ARC_LENGTH_REPARAMETRIZATION`.

- The proof uses case distinction on whether the image of `g` is a subset of the frontier of the convex hull of the image of `g`. If true, `g` itself can be the solution.

- It leverages the properties of components of open sets, specifically within the interval [0, 1]. Constructing `s` as the set of `t` where `g t` is in the complement of the frontier of the convex hull of image `g`. Showing components are countable, and each component is an open interval (`interval(a n, b n)`).

- It employs `DEPENDENT_CHOICE` to construct a sequence of paths `h n`.

- It relies on `STEP_LEMMA`, and reasoning about endpoint values, to iteratively adjust the path `h n`, ensuring it gradually approximates the desired properties.

- It uses `eventually sequentially` to show that the sequence `f n x` converges to a limit `h x` for any `x` in the unit interval. Finally we show that `h` has the desired properties.

### Mathematical insight
This theorem is related to the isoperimetric inequality. The convex hull operation "chops off" any non-convex parts of the curve, and replaces them by line segments completing the boundary of the convex hull, this process shortens the perimeter.

### Dependencies
- `rectifiable_path`
- `simple_path`
- `pathfinish`
- `pathstart`
- `path_length`
- `convex hull`
- `path_image`
- `frontier`
- `CONVEX_HULL_REDUNDANT_SUBSET`
- `EMPTY_SUBSET`
- `DIFF_EMPTY`
- `CONVEX_HULL_EMPTY`
- `CONVEX_HULL_EQ_EMPTY`
- `PATH_IMAGE_NONEMPTY`
- `COMPACT_PATH_IMAGE`
- `SIMPLE_PATH_IMP_PATH`
- `SUBSET`
- `NOT_FORALL_THM`
- `NOT_IMP`
- `EXISTS_IN_IMAGE`
- `shiftpath`
- `RECTIFIABLE_PATH_SHIFTPATH`
- `SIMPLE_PATH_SHIFTPATH`
- `PATH_LENGTH_SHIFTPATH`
- `PATH_IMAGE_SHIFTPATH`
- `IN_INTERVAL_1`
- `DROP_VEC`
- `PATHSTART_SHIFTPATH`
- `PATHFINISH_SHIFTPATH`
- `CLOSURE_INC`
- `HULL_INC`
- `IN_DIFF`
- `ARC_LENGTH_REPARAMETRIZATION`
- `PATH_LENGTH_POS_LE`
- `SIMPLE_PATH_IMP_PATH`
- `REAL_LE_REFL`
- `components`
- `LOCALLY_OPEN_SUBSET` DEPENDENT_CHOICE STEP_LEMMA CONNECTED_COMPACT_INTERVAL_1
- `CONVEX_IMP_LOCALLY_CONNECTED`
- `CONVEX_INTERVAL`
- `COUNTABLE_AS_IMAGE`
- `COMPONENTS_EQ_EMPTY`
- `CONNECTED_COMPACT_INTERVAL_1`
- `CONNECTED_CLOSURE`
- `MONO_EXISTS`
- `CONVEX_INTERIOR_CLOSURE`
- `CONVEX_CONNECTED_1`
- `INTERIOR_OPEN`
- `OPEN_IN_OPEN_TRANS`
- `INTERVAL_OPEN_SUBSET_CLOSED`
- `OPEN_IN_TRANS`
- `OPEN_IN_COMPONENTS_LOCALLY_CONNECTED`
- `CONTINUOUS_OPEN_IN_PREIMAGE`
- `LIPSCHITZ_IMP_CONTINUOUS_ON`
- `FRONTIER_CLOSED`
-  REAL_LT_IMP_LE ENDS_IN_INTERVAL EVENTUALLY_AND

### Porting notes (optional)
- The extensive use of tactics like `ASM_MESON_TAC` may indicate significant automation is needed to replicate the reasoning steps in other proof assistants.
- Particular attention should be paid to the definitions related to paths (`rectifiable_path`, `simple_path`, etc.) and how they are represented in the target proof assistant.
- The handling of real analysis concepts, such as `Lipschitz continuity` and `convex hulls`, should be verified for consistency.


---

## ISOPERIMETRIC_CONVEXIFICATION_1

### Name of formal statement
ISOPERIMETRIC_CONVEXIFICATION_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOPERIMETRIC_CONVEXIFICATION_1 = prove
 (`!g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        ~convex(inside(path_image g))
        ==> ?h:real^1->real^2.
                rectifiable_path h /\
                simple_path h /\
                pathfinish h = pathstart h /\
                path_length h <= path_length g /\
                convex hull path_image h = convex hull path_image g /\
                path_image h = frontier (convex hull path_image g) /\
                measure(inside(path_image g)) < measure(inside(path_image h))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^2` ISOPERIMETRIC_CONVEXIFICATION) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `h:real^1->real^2` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DIFF_SUBSET o rand o snd) THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 6)
   [MEASURABLE_INSIDE; COMPACT_PATH_IMAGE; SIMPLE_PATH_IMP_PATH;
    COMPACT_FRONTIER; COMPACT_CONVEX_HULL; INSIDE_FRONTIER_EQ_INTERIOR;
    CONVEX_CONVEX_HULL; BOUNDED_CONVEX_HULL; BOUNDED_PATH_IMAGE;
    SIMPLE_PATH_IMP_PATH; MEASURABLE_MEASURE_POS_LT; MEASURABLE_DIFF;
    MEASURABLE_INTERIOR] THEN
  REWRITE_TAC[INSIDE_SUBSET_INTERIOR_CONVEX_HULL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NEGLIGIBLE_EMPTY_INTERIOR) THEN
  SUBGOAL_THEN
   `~(path_image g INTER interior(convex hull path_image g):real^2->bool = {})`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SET_DIFF_FRONTIER] THEN MATCH_MP_TAC(SET_RULE
     `p SUBSET c /\ ~(p SUBSET f) ==> ~(p INTER (c DIFF f) = {})`) THEN
    REWRITE_TAC[HULL_SUBSET] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `g:real^1->real^2` lemma3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT `~p ==> p ==> F`)) THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [INSIDE_FRONTIER_EQ_INTERIOR; CONVEX_CONVEX_HULL; BOUNDED_CONVEX_HULL;
      BOUNDED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH; CONVEX_INTERIOR];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `g:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  ASM_REWRITE_TAC[FRONTIER_STRADDLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `path_image g:real^2->bool` OPEN_OUTSIDE) THEN
  ASM_SIMP_TAC[CLOSED_PATH_IMAGE; SIMPLE_PATH_IMP_PATH] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (e / &2)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; BALL_MIN_INTER; REAL_HALF] THEN
  MATCH_MP_TAC(SET_RULE
   `DISJOINT s v /\ t SUBSET u ==> s INTER t SUBSET u DIFF v`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `b SUBSET t ==> s INTER t = {} ==> DISJOINT b s`)) THEN
    REWRITE_TAC[INSIDE_INTER_OUTSIDE];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[OPEN_BALL] THEN
    TRANS_TAC SUBSET_TRANS `ball(x:real^2,e)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(x:real^2,y) < e / &2` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN CONV_TAC NORM_ARITH]);;
```

### Informal statement
For any function `g` from real numbers to pairs of real numbers, if `g` represents a rectifiable path, `g` represents a simple path, the endpoint of `g` equals the starting point of `g`, and the inside of the path image of `g` is not a convex set, then there exists a function `h` from real numbers to pairs of real numbers such that `h` represents a rectifiable path, `h` represents a simple path, the endpoint of `h` equals the starting point of `h`, the length of `h` is less than or equal to the length of `g`, the convex hull of the path image of `h` is equal to the convex hull of the path image of `g`, the path image of `h` is equal to the frontier of the convex hull of the path image of `g`, and the measure of the inside of the path image of `g` is less than the measure of the inside of the path image of `h`.

### Informal sketch
The proof demonstrates that given a rectifiable simple closed path `g` whose interior is non-convex, we can find another rectifiable simple closed path `h` whose length is no more than that of `g`, whose convex hull is the same as that of `g`, whose image is the frontier of this convex hull, and whose interior encloses a larger area.
- Assume we have a rectifiable simple closed path `g` such that `~convex(inside(path_image g))`.
- Apply the theorem `ISOPERIMETRIC_CONVEXIFICATION` to get a path `h` with the desired properties except for the measure inequality, i.e. `path_length h <= path_length g` and `convex hull path_image h = convex hull path_image g` and `path_image h = frontier (convex hull path_image g)`.
- Show that `measure(inside(path_image g)) < measure(inside(path_image h))`. This is done by showing that the difference between the `interior` of the `convex hull path_image g` and `inside g` has positive measure.
- Show that `inside(path_image g)` is a subset of the `interior` of the `convex hull path_image g`, thus enabling the use of `MEASURE_DIFF_SUBSET`.
- Establish `~(path_image g INTER interior(convex hull path_image g):real^2->bool = {})`. This is achieved by showing that `(path_image g INTER interior(convex hull path_image g))` is non-empty, which is equivalent to showing that there exists a point `x` in `inside g` and a radius `e` such that the `ball(x,e)` is contained in `inside g`, but there is some point `y` on the frontier of `inside g` such that `dist(x,y) < e/2`. This uses `JORDAN_INSIDE_OUTSIDE` and `OPEN_OUTSIDE`.

### Mathematical insight
This theorem formalizes a step in proving the isoperimetric inequality. It states that if a simple closed curve encloses a non-convex region, we can find another simple closed curve of no larger perimeter that encloses a region with the same convex hull but larger area. This new curve will be the frontier of the convex hull. Repeating this process will eventually lead to a convex region whose area is maximized for a given perimeter, which is a stepping stone towards showing the isoperimetric inequality.

### Dependencies
Theorems:
- `ISOPERIMETRIC_CONVEXIFICATION`
- `MONO_EXISTS`
- `REAL_SUB_LT`
- `MEASURE_DIFF_SUBSET`
- `MEASURABLE_INSIDE`
- `COMPACT_PATH_IMAGE`
- `SIMPLE_PATH_IMP_PATH`
- `COMPACT_FRONTIER`
- `COMPACT_CONVEX_HULL`
- `INSIDE_FRONTIER_EQ_INTERIOR`
- `CONVEX_CONVEX_HULL`
- `BOUNDED_CONVEX_HULL`
- `BOUNDED_PATH_IMAGE`
- `MEASURABLE_MEASURE_POS_LT`
- `MEASURABLE_DIFF`
- `MEASURABLE_INTERIOR`
- `INSIDE_SUBSET_INTERIOR_CONVEX_HULL`
- `NEGLIGIBLE_EMPTY_INTERIOR`
- `lemma3` (likely a supporting lemma within the same file or theory)
- `JORDAN_INSIDE_OUTSIDE`
- `OPEN_OUTSIDE`
- `CLOSED_PATH_IMAGE`
- `OPEN_CONTAINS_BALL`
- `REAL_LT_MIN`
- `BALL_MIN_INTER`
- `INSIDE_INTER_OUTSIDE`
- `INTERIOR_MAXIMAL`
- `OPEN_BALL`

Definitions:
- `rectifiable_path`
- `simple_path`
- `pathfinish`
- `pathstart`
- `convex`
- `inside`
- `path_image`
- `path_length`
- `convex hull`
- `frontier`
- `measure`
- `interior`
- `dist`
- `ball`
- `DISJOINT`
- `OUTSIDE`

### Porting notes (optional)
Porting this theorem requires representing concepts of rectifiable paths, simple paths, convex hulls, measure theory, and Jordan curve theorem in the target proof assistant. The proof relies heavily on properties of measure and integration, so a well-developed measure theory library is crucial. The use of `CONV_TAC` and `ASM_REWRITE_TAC` with specific simplification sets suggests that a similar level of automation might be helpful in the target system. The dependencies on various geometric lemmas (`lemma3`, `OPEN_OUTSIDE`, `JORDAN_INSIDE_OUTSIDE`) indicate that a geometric library might be necessary.


---

## ISOPERIMETRIC_THEOREM

### Name of formal statement
ISOPERIMETRIC_THEOREM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOPERIMETRIC_THEOREM = prove
 (`!L g:real^1->real^2.
        rectifiable_path g /\
        simple_path g /\
        pathfinish g = pathstart g /\
        path_length g = L
        ==> measure(inside(path_image g)) <= L pow 2 / (&4 * pi) /\
            (measure(inside(path_image g)) =  L pow 2 / (&4 * pi)
             ==> ?a r. path_image g = sphere(a,r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
  ASM_CASES_TAC `convex(inside(path_image g):real^2->bool)` THENL
   [ASM_MESON_TAC[ISOPERIMETRIC_THEOREM_CONVEX]; ALL_TAC] THEN
  MP_TAC(SPEC `g:real^1->real^2` ISOPERIMETRIC_CONVEXIFICATION_1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`path_length(h:real^1->real^2)`; `h:real^1->real^2`]
    ISOPERIMETRIC_THEOREM_CONVEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR; CONVEX_CONVEX_HULL;
                 BOUNDED_CONVEX_HULL; BOUNDED_PATH_IMAGE; CONVEX_INTERIOR];
    MATCH_MP_TAC(TAUT
     `(p ==> q /\ ~r) ==> (p /\ s ==> q /\ (r ==> t))`) THEN
    REWRITE_TAC[GSYM REAL_LT_LE] THEN MATCH_MP_TAC(REAL_ARITH
     `g:real < h /\ m <= l ==> h <= m ==> g < l`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; PI_POS;
                 REAL_ARITH `&0 < &4 * x <=> &0 < x`] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`) THEN
    ASM_SIMP_TAC[PATH_LENGTH_POS_LE]]);;
```

### Informal statement
For any function `g` from real numbers to pairs of real numbers (i.e., a path in the plane), if `g` is a rectifiable path, `g` is a simple path, the endpoint of `g` is equal to the starting point of `g`, and the length of `g` is `L`, then the measure of the interior of the image of `g` is less than or equal to `L` squared divided by `4 * pi`. Furthermore, if the measure of the interior of the image of `g` is equal to `L` squared divided by `4 * pi`, then there exists a point `a` and a real number `r` such that the image of `g` is equal to the sphere centered at `a` with radius `r`.

### Informal sketch
The proof proceeds by induction on whether the interior of the path's image is convex:
- Case 1: If the `inside(path_image g)` is convex, the theorem follows from `ISOPERIMETRIC_THEOREM_CONVEX`.
- Case 2: If the `inside(path_image g)` is not convex, the proof constructs (using `ISOPERIMETRIC_CONVEXIFICATION_1`) a convexification `h` of `g` and then applies `ISOPERIMETRIC_THEOREM_CONVEX` to `h`. The assumptions related to the length, start and end points must be discharged via simplification and arithmetic reasoning.
Key steps include showing that the length of the convexified path `h` is no greater than the length of the original path `g`, and appealing to properties relating to the isoperimetric quotient of convex regions.

### Mathematical insight
This theorem is the Isoperimetric Theorem in the plane, which states that for a given perimeter, the circle encloses the maximum area. The theorem relates the length of a closed curve to the area it encloses. The equality case implies that the curve achieving the maximum area for a given perimeter is a circle.

### Dependencies
- `ISOPERIMETRIC_THEOREM_CONVEX`
- `SIMPLE_PATH_IMP_PATH`
- `ISOPERIMETRIC_CONVEXIFICATION_1`
- `INSIDE_FRONTIER_EQ_INTERIOR`
- `CONVEX_CONVEX_HULL`
- `BOUNDED_CONVEX_HULL`
- `BOUNDED_PATH_IMAGE`
- `CONVEX_INTERIOR`
- `REAL_LT_LE`
- `REAL_LE_DIV2_EQ`
- `PI_POS`
- `REAL_LE_SQUARE_ABS`
- `PATH_LENGTH_POS_LE`


---

