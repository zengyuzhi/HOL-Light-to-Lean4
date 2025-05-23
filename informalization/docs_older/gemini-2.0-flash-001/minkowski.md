# minkowski.ml

## Overview

Number of statements: 4

`minkowski.ml` formalizes Minkowski's convex body theorem. The file, part of the `Multivariate` library, leverages measure theory to relate the volume of a convex body to its symmetry and the existence of integer points. It imports `measure.ml` for measure-theoretic foundations.


## LEMMA

### Name of formal statement
LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LEMMA = prove
 (`!f:real^N->bool t s:real^N->bool.
        FINITE { u | u IN f /\ ~(t u = {})} /\
        measurable s /\ &1 < measure s /\
        (!u. u IN f ==> measurable(t u)) /\
        s SUBSET UNIONS (IMAGE t f) /\
        (!u v. u IN f /\ v IN f /\ ~(u = v) ==> DISJOINT (t u) (t v)) /\
        (!u. u IN f ==> (IMAGE (\x. x - u) (t u)) SUBSET interval[vec 0,vec 1])
        ==> ?u v. u IN f /\ v IN f /\ ~(u = v) /\
                  ~(DISJOINT (IMAGE (\x. x - u) (t u))
                             (IMAGE (\x. x - v) (t v)))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ ~c /\ ~d) <=> a /\ b /\ ~c ==> d`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\u:real^N. IMAGE (\x:real^N. x - u) (t u)`;
                 `f:real^N->bool`]
                HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `x - u:real^N = --u + x`] THEN
    ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `vec 1:real^N`] (CONJUNCT1
                HAS_MEASURE_INTERVAL)) THEN
  REWRITE_TAC[CONTENT_UNIT] THEN
  MATCH_MP_TAC(TAUT `(b /\ a ==> F) ==> a ==> ~b`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE
   [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] HAS_MEASURE_SUBSET)) THEN
  ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; REAL_NOT_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `&1 < a ==> a <= b ==> &1 < b`)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS (IMAGE (t:real^N->real^N->bool) f))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_SUBSET THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `UNIONS (IMAGE (t:real^N->real^N->bool) f) =
      UNIONS (IMAGE t {u | u IN f /\ ~(t u = {})})`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[NOT_IN_EMPTY];
      ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_UNIONS THEN
    ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->real^N->bool`; `f:real^N->bool`]
                HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; NOT_IMP] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP MEASURE_UNIQUE) THEN
  REWRITE_TAC[VECTOR_ARITH `x - u:real^N = --u + x`] THEN
  ASM_SIMP_TAC[MEASURE_TRANSLATION; REAL_LE_REFL]);;
```
### Informal statement
For all functions `f` from `real^N` to boolean (representing a set of vectors in `real^N`) and `t` from `real^N` to `real^N` to boolean (representing a set-valued function mapping vectors in `real^N` to sets of vectors in `real^N`), if the set of vectors `u` such that `u` is in `f` and `t u` is non-empty is finite, and `s` is a measurable set with measure greater than 1, and for all `u`, if `u` is in `f` then `t u` is measurable, and `s` is a subset of the union of the images of `t` applied to `f`, and for all `u` and `v`, if `u` is in `f` and `v` is in `f` and `u` is not equal to `v`, then `t u` and `t v` are disjoint, and for all `u`, if `u` is in `f` then the image of `t u` under the translation `x -> x - u` is a subset of the interval from `vec 0` to `vec 1`, then there exist `u` and `v` such that `u` is in `f` and `v` is in `f` and `u` is not equal to `v` and the images of `t u` and `t v` translated by `x -> x - u` and `x -> x - v` respectively, are not disjoint.

### Informal sketch
The proof proceeds by contradiction, assuming that the translated images of `t u` and `t v` are disjoint for all distinct `u` and `v` in `f`.
- Using `HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG`, establish measurability of the translated sets `IMAGE (\x. x - u) (t u)`.
- Use `HAS_MEASURE_INTERVAL` to show the interval `interval[vec 0,vec 1]` has measure 1.
- Show `measure s <= measure(UNIONS (IMAGE t f))`.
- Employ `HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG` to relate the measure of the union of the translated sets to the sum of their individual measures.
- Since the translated sets are assumed disjoint, derive a contradiction by showing that `measure s` ≤ `measure(UNIONS (IMAGE t f))` ≤ 1, while `measure s` > 1. The main steps involve proving that the measure `measure(UNIONS (IMAGE t f))` equals `measure(UNIONS (IMAGE t {u | u IN f /\ ~(t u = {})}))`, using `MEASURE_SUBSET`, `MEASURABLE_UNIONS`.
- Conclude there must exist distinct `u` and `v` in `f` such that the translated images of `t u` and `t v` are not disjoint.

### Mathematical insight
This lemma is a step towards Minkowski's convex body theorem. It states that under certain conditions, if a set `s` with measure greater than 1 is contained in the union of disjoint sets `t u` (translated to be within the unit interval), then two of these translated sets must overlap. The main idea is that if the translated sets were disjoint and within the unit interval, their total measure would be at most 1, contradicting the measure of `s` being greater than 1.

### Dependencies
- `Multivariate/measure.ml`
- `HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG`
- `IMAGE_EQ_EMPTY`
- `NOT_IMP`
- `MEASURABLE_TRANSLATION_EQ`
- `HAS_MEASURE_INTERVAL`
- `CONTENT_UNIT`
- `HAS_MEASURE_SUBSET`
- `UNIONS_SUBSET`
- `FORALL_IN_IMAGE`
- `REAL_NOT_LE`
- `REAL_LE_TRANS`
- `MEASURE_SUBSET`
- `MEASURABLE_UNIONS`
- `FINITE_IMAGE`
- `IN_ELIM_THM`
- `ASM_MESON_TAC`
- `MEASURE_UNIQUE`
- `MEASURE_TRANSLATION`
- `REAL_LE_REFL`


---

## BLICHFELDT

### Name of formal statement
BLICHFELDT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BLICHFELDT = prove
 (`!s:real^N->bool.
        measurable s /\ &1 < measure s
        ==> ?x y. x IN s /\ y IN s /\ ~(x = y) /\
                  !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i - y$i)`,
  SUBGOAL_THEN
   `!s:real^N->bool.
        bounded s /\ measurable s /\ &1 < measure s
        ==> ?x y. x IN s /\ y IN s /\ ~(x = y) /\
                  !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i - y$i)`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `measure(s:real^N->bool) - &1` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] MEASURABLE_INNER_COMPACT)) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{ u:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                   ==> integer(u$i) }`;
                 `\u. {x | (x:real^N) IN s /\
                           !i. 1 <= i /\ i <= dimindex(:N)
                               ==> (u:real^N)$i <= x$i /\ x$i < u$i + &1 }`;
                 `s:real^N->bool`]
                LEMMA) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; IN_INTER] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_ARITH `x - u:real^N = y - v <=> x + (v - u) = y`] THEN
    REWRITE_TAC[UNWIND_THM1] THEN STRIP_TAC THEN
    EXISTS_TAC `x + (v - u):real^N` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x = x + (v - u) <=> v:real^N = u`] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_ARITH `x - (x + v - u):real = u - v`;
                 INTEGER_CLOSED]] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `?N. !x:real^N i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> abs(x$i) < &N`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
      DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
      MP_TAC(SPEC `B:real` (MATCH_MP REAL_ARCH REAL_LT_01)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[REAL_MUL_RID] THEN
      X_GEN_TAC `N:num` THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
      SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_LET_TRANS];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{u:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                      ==> integer (u$i) /\ abs(u$i) <= &N}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CART THEN
      REWRITE_TAC[GSYM REAL_BOUNDS_LE; FINITE_INTSEG];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
    STRIP_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_REVERSE_INTEGERS THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `k:num`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `k:num`]) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MEASURABLE_ALMOST THEN
    EXISTS_TAC `s INTER interval[u:real^N,u + vec 1]` THEN
    ASM_SIMP_TAC[MEASURABLE_INTER_INTERVAL] THEN
    EXISTS_TAC `interval[u:real^N,u + vec 1] DIFF interval(u,u + vec 1)` THEN
    REWRITE_TAC[NEGLIGIBLE_FRONTIER_INTERVAL] THEN
    MATCH_MP_TAC(SET_RULE
     `s' SUBSET i /\ j INTER s' = j INTER s
      ==> (s INTER i) UNION (i DIFF j) = s' UNION (i DIFF j)`) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL; IN_INTER; EXTENSION;
                IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN TRY EQ_TAC THEN
    REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `(lambda i. floor((x:real^N)$i)):real^N` THEN
    ASM_SIMP_TAC[LAMBDA_BETA; FLOOR];
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[CART_EQ; REAL_EQ_INTEGERS] THEN
    REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP; REAL_NOT_LT] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM (MP_TAC o SPEC `k:num`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real^N` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTERVAL] THEN
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VEC_COMPONENT] THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For all measurable sets `s` in a real N-dimensional space such that the measure of `s` is greater than 1, there exist two distinct points `x` and `y` in `s` such that for all indices `i` between 1 and the dimension of the space, the difference between the `i`-th components of `x` and `y` is an integer.

### Informal sketch
The proof proceeds as follows:
- First, the theorem is proven for bounded sets `s`.
 - This involves assuming `s` is bounded, measurable, and its measure is greater than 1, and then proving the existence of `x` and `y` with the stated properties. This is done by:
   - Using `MEASURABLE_INNER_COMPACT` and `REAL_SUB_LT` to show that there exists a compact set `c` such that `c` is a subset of `s` and the measure of `c` is still greater than 1.
   - Using `COMPACT_IMP_BOUNDED` to deduce `c` is bounded.
   - Applying real arithmetic (`ASM_REAL_ARITH_TAC`) and set theory (`ASM SET_TAC[]`) to finish the proof under the assumption of boundedness.
- The proof then proceeds to handle the general case where `s` is not necessarily bounded.
 - This is achieved by using `LEMMA` with `ISPECL` instantiated with a lattice of integer points and a function that maps each integer point to a related subset of `s`. Then it is shown that there exist two distinct elements `u` and `v` in the lattice, and two related points `x` and `y` in the sets related to `u` and `v` such that for each index `i` between 1 and the dimension of the space, `x_i - y_i` is an integer.
    - This part relies on showing that the set of integer points intersected with `s` are disjoint and that at least one of them is not empty (`DISJOINT`, `MEMBER_NOT_EMPTY`).
 - The theorem reduces to showing there exists a bound `N` such that for any point `x` in the original set `s`, the absolute value of each coordinate of `x` is strictly less than `N`. This involves:
   - Showing that if `s` is bounded, then such an `N` exists (handled using `BOUNDED_POS`, `REAL_ARCH`, `COMPONENT_LE_NORM`, `REAL_LE_TRANS`).
   - Using the fact that a finite subset exists (using `FINITE_SUBSET`), we define a finite subset consisting of integer points bounded by N.
   - Showing that the measure of the intersection between `s` and the intervals determined by the lattice is almost equal to the sum of the measures of the intersection between `s` and the open intervals. This step employs `MEASURABLE_ALMOST` and properties of the `interval` function, also using `NEGLIGIBLE_FRONTIER_INTERVAL`.
   - Finally, an averaging/pigeonhole principle argument completes the proof, showing that since the measure of `s` is greater than one, some pair of points `x` and `y` can be found with the desired properties.

### Mathematical insight
Blichfeldt's theorem is a fundamental result in the geometry of numbers. It essentially states that if a set in `R^n` has measure greater than 1, then it must contain two points whose difference is an integer vector. This result is a stepping stone to Minkowski's theorem.

### Dependencies
- `MEASURABLE_INNER_COMPACT`
- `REAL_SUB_LT`
- `COMPACT_IMP_BOUNDED`
- `DISJOINT`
- `MEMBER_NOT_EMPTY`
- `MONO_EXISTS`
- `VECTOR_ARITH`
- `UNWIND_THM1`
- `VECTOR_SUB_COMPONENT`
- `VECTOR_ADD_COMPONENT`
- `REAL_ARITH`
- `INTEGER_CLOSED`
- `BOUNDED_POS`
- `REAL_ARCH`
- `COMPONENT_LE_NORM`
- `REAL_LE_TRANS`
- `REAL_LET_TRANS`
- `FINITE_SUBSET`
- `FINITE_CART`
- `FINITE_INTSEG`
- `REAL_BOUNDS_LE`
- `REAL_LE_REVERSE_INTEGERS`
- `MEASURABLE_ALMOST`
- `NEGLIGIBLE_FRONTIER_INTERVAL`
- `IN_UNIONS`
- `FLOOR`
- `CART_EQ`
- `REAL_EQ_INTEGERS`
- `NOT_FORALL_THM`
- `NOT_IMP`
- `REAL_NOT_LT`


---

## MINKOWSKI

### Name of formal statement
MINKOWSKI

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MINKOWSKI = prove
 (`!s:real^N->bool.
        convex s /\
        (!x. x IN s ==> (--x) IN s) /\
        &2 pow dimindex(:N) < measure s
        ==> ?u. ~(u = vec 0) /\
                (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)) /\
                u IN s`,
  SUBGOAL_THEN
   `!s:real^N->bool.
        convex s /\
        bounded s /\
        (!x. x IN s ==> (--x) IN s) /\
        &2 pow dimindex(:N) < measure s
        ==> ?u. ~(u = vec 0) /\
                (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)) /\
                u IN s`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `&2 pow dimindex(:N)`]
        CHOOSE_LARGE_COMPACT_SUBSET_ALT) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_CONVEX] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o SPEC `vec 0:real^N` o
      MATCH_MP BOUNDED_SUBSET_BALL) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s INTER ball(vec 0:real^N,r)`) THEN
    ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    SIMP_TAC[BOUNDED_INTER; BOUNDED_BALL] THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL; IN_INTER] THEN
    SIMP_TAC[IN_BALL_0; NORM_NEG] THEN
    TRANS_TAC REAL_LTE_TRANS `measure(c:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT; SUBSET_INTER] THEN
    MATCH_MP_TAC MEASURABLE_CONVEX THEN
     SIMP_TAC[BOUNDED_INTER; BOUNDED_BALL] THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. (&1 / &2) % x) s` BLICHFELDT) THEN
  ASM_SIMP_TAC[MEASURABLE_SCALING; MEASURE_SCALING; MEASURABLE_CONVEX;
               BOUNDED_SCALING] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV; REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div; REAL_POW_INV] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_POW2; REAL_MUL_LID] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_ARITH `inv(&2) % x:real^N = inv(&2) % y <=> x = y`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; GSYM REAL_SUB_LDISTRIB] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(&2) % (u - v):real^N` THEN
  ASM_SIMP_TAC[VECTOR_ARITH `inv(&2) % (u - v):real^N = vec 0 <=> u = v`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  REWRITE_TAC[VECTOR_SUB; VECTOR_ADD_LDISTRIB] THEN
  FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
  ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For any set `s` of real vectors in `N` dimensions, if `s` is convex, centrally symmetric (i.e., if `x` is in `s`, then `-x` is in `s`), and its Lebesgue measure is greater than `2` raised to the power of the dimension `N`, then there exists a non-zero vector `u` whose components are all integers, and `u` is in `s`.

### Informal sketch
The proof proceeds as follows:
- First, the theorem is strengthened by adding the condition that the set `s` is bounded. This strengthening is proven first, and then the original theorem follows.
- The proof of the strengthened version uses Blichfeldt's principle.
- It starts by taking a set `s` that satisfies the given conditions: convex, bounded, centrally symmetric, and with sufficiently large measure.
- From `convex s` one derives that `s` is Lebesgue measurable using `LEBESGUE_MEASURABLE_CONVEX`.
- A compact subset `c` of `s` is chosen using `CHOOSE_LARGE_COMPACT_SUBSET_ALT` such that the measure of `c` is still greater than `2` raised to the power of the dimension `N`.
- Since `c` is compact it is bounded using `COMPACT_IMP_BOUNDED`.
- Then `r` is chosen so that the ball of radius `r` around the origin contains `s INTER ball(vec 0:real^N,r)` using `BOUNDED_SUBSET_BALL`.
- Applying Blichfeldt's principle to the scaled set `IMAGE (\x:real^N. (&1 / &2) % x) s`, one obtains that there exist distinct vectors `u` and `v` in `s` such that `(1/2) * (u - v)` is an integer vector.
- By the central symmetry and convexity of `s`, `(1/2) * (u - v)` is in `s`.
- Since `u` and `v` are distinct, `(1/2) * (u - v)` is a non-zero integer vector in `s`.

### Mathematical insight
Minkowski's theorem is a fundamental result in the geometry of numbers. It provides a criterion for the existence of non-zero integer vectors within a convex, centrally symmetric set of sufficiently large volume. The theorem has applications in various areas of number theory, such as proving results about Diophantine approximation and algebraic number theory.

### Dependencies
**Theorems:**
- `BLICHFELDT`
- `COMPACT_IMP_BOUNDED`
- `BOUNDED_SUBSET_BALL`
- `RIGHT_EXISTS_AND_THM`
- `LEFT_IMP_EXISTS_THM`
- `RIGHT_AND_EXISTS_THM`
- `MEASURE_SUBSET`
- `REAL_LTE_TRANS`

**Definitions:**
- `convex`
- `measure`
- `vec`
- `integer`
- `dimindex`
- `ball`
- `IMAGE`

**Other rules:**
- `LEBESGUE_MEASURABLE_CONVEX`
- `MEASURABLE_SCALING`
- `MEASURE_SCALING`
- `MEASURABLE_CONVEX`
- `BOUNDED_SCALING`
- `real_div`
- `REAL_MUL_LID`
- `REAL_ABS_INV`
- `REAL_ABS_NUM`
- `REAL_MUL_SYM`
- `GSYM real_div`
- `REAL_POW_INV`
- `REAL_LT_RDIV_EQ`
- `REAL_LT_POW2`
- `BOUNDED_INTER`
- `BOUNDED_BALL`
- `CONVEX_INTER`
- `CONVEX_BALL`
- `IN_INTER`
- `IN_BALL_0`
- `NORM_NEG`
- `MEASURABLE_COMPACT`
- `SUBSET_INTER`
- `VECTOR_ARITH`
- `VECTOR_MUL_COMPONENT`
- `REAL_SUB_LDISTRIB`
- `VECTOR_SUB`
- `VECTOR_ADD_LDISTRIB`

### Porting notes (optional)
- The proof relies heavily on measure theory and properties of real vectors. Ensure that the target proof assistant has adequate support for these concepts.
- The use of `CHOOSE_LARGE_COMPACT_SUBSET_ALT` indicates a need for a choice principle to select a compact subset with sufficient measure.
- The `VECTOR_ARITH` tactic is used extensively which means one needs to perform Vector arithmetic reasoning.
- Blichfeldt's principle is used, make sure that the target proof assistant has a library that includes this principles.


---

## MINKOWSKI_COMPACT

### Name of formal statement
MINKOWSKI_COMPACT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MINKOWSKI_COMPACT = prove
 (`!s:real^N->bool.
        convex s /\ compact s /\
        (!x. x IN s ==> (--x) IN s) /\
        &2 pow dimindex(:N) <= measure s
        ==> ?u. ~(u = vec 0) /\
                (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)) /\
                u IN s`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[GSYM REAL_NOT_LT; MEASURE_EMPTY; REAL_LT_POW2];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    SUBST1_TAC(VECTOR_ARITH `vec 0:real^N = inv(&2) % a + inv(&2) % --a`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
    ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`s:real^N->bool`;
     `{u | !i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)}
      DELETE (vec 0:real^N)`]
    SEPARATE_COMPACT_CLOSED) THEN
  REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC(TAUT
   `(~e ==> c) /\ a /\ b /\ (d ==> e)
        ==> (a /\ b /\ c ==> d) ==> e`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ASM_REWRITE_TAC[]] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DISCRETE_IMP_CLOSED THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IN_DELETE; IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[CART_EQ; REAL_NOT_LT; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((y - x:real^N)$k)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM; VECTOR_SUB_COMPONENT] THEN
    ASM_MESON_TAC[REAL_EQ_INTEGERS; REAL_NOT_LE];
    ALL_TAC] THEN
  SIMP_TAC[dist] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. (&1 + d / &2 / B) % x) s` MINKOWSKI) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_SCALING; BOUNDED_SCALING; COMPACT_IMP_BOUNDED] THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT; MEASURE_SCALING] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_IMAGE] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_ARITH
       `--(a % x):real^N = a % y <=> a % (x + y) = vec 0`] THEN
      ASM_MESON_TAC[VECTOR_ADD_RINV];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `d <= m ==> m < n ==> d < n`)) THEN
    REWRITE_TAC[REAL_ARITH `m < a * m <=> &0 < m * (a - &1)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MEASURABLE_COMPACT; MEASURABLE_MEASURE_POS_LT] THEN
      REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
      DISCH_THEN(SUBST_ALL_TAC o MATCH_MP MEASURE_UNIQUE) THEN
      ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_POW2];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_LT_1 THEN
    REWRITE_TAC[DIMINDEX_NONZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &1 < abs(&1 + x)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> c /\ b /\ a`] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`u:real^N`; `(&1 + d / &2 / B) % u:real^N`]) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
  REWRITE_TAC[VECTOR_ARITH `u - (&1 + e) % u:real^N = --(e % u)`] THEN
  REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(d / &2 / B) * B` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_ABS_POS] THEN
  ASM_REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC);;
```

### Informal statement
For all sets `s` of real vectors in `N` dimensions, if `s` is convex, compact, symmetric about the origin (i.e., if `x` is in `s`, then `-x` is in `s`), and its measure is greater than or equal to `2` raised to the power of the dimension `N`, then there exists a non-zero vector `u` such that all its components `u$i` are integers, and `u` is an element of `s`.

### Informal sketch
The proof proceeds by contradiction and leverages `Minkowski's theorem`.

- First, the case where `s` is empty is handled directly.
- Next, assuming `s` is non-empty, it's shown that `vec 0` (the zero vector) must belong to `s` using the convexity and symmetry assumptions.
- The proof then considers the set of non-zero vectors with integer components.
- Applying `SEPARATE_COMPACT_CLOSED` it is shown that the set of vectors with integer components is discrete, hence closed.
- A contradiction argument shows that the infimum of distances between points in the set and s must be positive.
- Because `s` is compact, it is also bounded. Let `B` be its bound.
- Now Minkowski's theorem is applied to the image of `s` under a scaling transformation (`IMAGE (\x:real^N. (&1 + d / &2 / B) % x) s`). The scaling is chosen such that if `d <= measure s` then `&2 pow dimindex(:N) <= measure (IMAGE (\x:real^N. (&1 + d / &2 / B) % x) s)`.
- By `Minkowski's theorem`, this scaled set contains a non-zero vector `u` with integer components.
- Finally, it is shown that `u` must also be in `s`, completing the proof.

### Mathematical insight
This theorem is a variant of Minkowski's theorem, which states that a convex body in `n`-dimensional Euclidean space that is symmetric about the origin and has sufficiently large volume must contain a non-zero integer point. This version leverages compactness and symmetry properties of the set `s` to establish the existence of such an integer point.

### Dependencies
- `convex`
- `compact`
- `measure`
- `MEMBER_NOT_EMPTY`
- `convex`
- `SEPARATE_COMPACT_CLOSED`
- `EXTENSION`
- `IN_DELETE`
- `IN_ELIM_THM`
- `IN_INTER`
- `NOT_IN_EMPTY`
- `DISCRETE_IMP_CLOSED`
- `REAL_LT_01`
- `CONTRAPOS_THM`
- `CART_EQ`
- `REAL_NOT_LT`
- `NOT_FORALL_THM`
- `NOT_IMP`
- `REAL_LE_TRANS`
- `COMPONENT_LE_NORM`
- `VECTOR_SUB_COMPONENT`
- `REAL_EQ_INTEGERS`
- `REAL_NOT_LE`
- `dist`
- `COMPACT_IMP_BOUNDED`
- `BOUNDED_POS`
- `LEFT_IMP_EXISTS_THM`
- `MINKOWSKI`
- `CONVEX_SCALING`
- `BOUNDED_SCALING`
- `COMPACT_IMP_BOUNDED`
- `MEASURABLE_COMPACT`
- `MEASURE_SCALING`
- `FORALL_IN_IMAGE`
- `IN_IMAGE`
- `VECTOR_MUL_EQ_0`
- `VECTOR_ARITH`
- `VECTOR_ADD_RINV`
- `REAL_ARITH`
- `MEASURABLE_MEASURE_POS_LT`
- `HAS_MEASURE_0`
- `MEASURE_UNIQUE`
- `REAL_NOT_LT`
- `REAL_LT_POW2`
- `REAL_SUB_LT`
- `REAL_POW_LT_1`
- `DIMINDEX_NONZERO`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `ARITH`
- `DE_MORGAN_THM`
- `MONO_EXISTS`
- `NORM_NEG`
- `NORM_MUL`
- `REAL_NOT_LE`
- `REAL_LET_TRANS`
- `REAL_LE_LMUL`
- `REAL_ABS_POS`
- `REAL_ABS_DIV`
- `REAL_ABS_NUM`
- `REAL_DIV_RMUL`
- `REAL_LT_IMP_NZ`

### Porting notes (optional)
- `Minkowski's theorem` will likely need to be ported beforehand.
- The definition of `measure` might differ in other proof assistants.
- Ensure that the concept of convexity and compactness are properly defined and aligned with the HOL Light definitions.


---

