# minkowski.ml

## Overview

Number of statements: 4

This file formalizes Minkowski's convex body theorem in HOL Light, which establishes that any convex, symmetric body in Euclidean space with volume greater than 2^n must contain a non-zero integer point. Building upon the multivariate measure theory, it develops the necessary concepts of convexity, symmetry, and lattice points, culminating in a formal proof of this fundamental result in geometry of numbers. The formalization likely includes supporting lemmas about convex bodies and their properties.

## LEMMA

### LEMMA

### Type of the formal statement
- theorem

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
This theorem states: For a finite family $f$ of sets in $\mathbb{R}^N$ and a function $t$ that maps elements of $f$ to sets in $\mathbb{R}^N$, if:
1. The set $\{u \in f \mid t(u) \neq \emptyset\}$ is finite
2. $s$ is measurable with measure greater than 1
3. For each $u \in f$, the set $t(u)$ is measurable
4. $s$ is a subset of $\bigcup_{u \in f} t(u)$
5. For all distinct $u, v \in f$, the sets $t(u)$ and $t(v)$ are disjoint
6. For each $u \in f$, the translated set $\{x - u \mid x \in t(u)\}$ is contained in the unit hypercube $[0,1]^N$

Then there exist distinct $u, v \in f$ such that the sets $\{x - u \mid x \in t(u)\}$ and $\{x - v \mid x \in t(v)\}$ are not disjoint.

### Informal proof
The proof proceeds by contradiction:

- Assume that for all distinct $u, v \in f$, the sets $\{x - u \mid x \in t(u)\}$ and $\{x - v \mid x \in t(v)\}$ are disjoint.

- We first note that for each $u \in f$, the set $\{x - u \mid x \in t(u)\}$ is measurable because translation preserves measurability (by `MEASURABLE_TRANSLATION_EQ`).

- Since the sets $\{x - u \mid x \in t(u)\}$ are disjoint for distinct $u \in f$ (by our assumption), we can apply `HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG` to find that $\bigcup_{u \in f} \{x - u \mid x \in t(u)\}$ has measure equal to $\sum_{u \in f} \text{measure}(\{x - u \mid x \in t(u)\})$.

- Each set $\{x - u \mid x \in t(u)\}$ is contained in the unit hypercube $[0,1]^N$ (from the hypotheses).

- The unit hypercube has measure 1, as shown by `HAS_MEASURE_INTERVAL` and `CONTENT_UNIT`.

- By `MEASURE_SUBSET`, since each $\{x - u \mid x \in t(u)\} \subseteq [0,1]^N$, and all these sets are disjoint, their union must have measure less than or equal to 1.

- However, we know that $s \subseteq \bigcup_{u \in f} t(u)$, so:
  * $\text{measure}(s) \leq \text{measure}(\bigcup_{u \in f} t(u))$
  * Using `MEASURE_TRANSLATION`, we get $\text{measure}(t(u)) = \text{measure}(\{x - u \mid x \in t(u)\})$
  * Therefore, $\text{measure}(\bigcup_{u \in f} t(u)) = \text{measure}(\bigcup_{u \in f} \{x - u \mid x \in t(u)\}) \leq 1$

- But we assumed that $\text{measure}(s) > 1$, which creates a contradiction.

- Therefore, our assumption must be false, meaning there exist distinct $u, v \in f$ such that $\{x - u \mid x \in t(u)\}$ and $\{x - v \mid x \in t(v)\}$ are not disjoint.

### Mathematical insight
This lemma is essentially a version of the pigeonhole principle in the context of measure theory. It states that if you have a collection of disjoint measurable sets whose union contains a set of measure greater than 1, and if each set, when translated, fits within the unit hypercube, then at least two of these translated sets must overlap.

This result is used in the proof of Minkowski's convex body theorem, which states that if a symmetric convex body in $\mathbb{R}^n$ has volume greater than $2^n$, then it contains a non-zero integer point. The lemma helps establish that certain translates must overlap, which is a key step in proving the existence of integer points in convex bodies.

### Dependencies
- **Theorems**:
  - `MEASURE_UNIQUE`: If a set $s$ has measure $m$, then $\text{measure}(s) = m$.
  - `HAS_MEASURE_INTERVAL`: Intervals (both open and closed) have measures equal to their content.
  - `HAS_MEASURE_SUBSET`: If $s_1 \subseteq s_2$ and both have measures, then $\text{measure}(s_1) \leq \text{measure}(s_2)$.
  - `MEASURE_SUBSET`: If measurable sets satisfy $s \subseteq t$, then $\text{measure}(s) \leq \text{measure}(t)$.
  - `MEASURABLE_UNIONS`: A finite union of measurable sets is measurable.
  - `HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG`: Measure of a union of disjoint sets equals the sum of measures.
  - `MEASURE_TRANSLATION`: Translations preserve measure: $\text{measure}(s + a) = \text{measure}(s)$.
  - `MEASURABLE_TRANSLATION_EQ`: Translations preserve measurability.
  
- **Definitions**:
  - `measurable`: A set is measurable if it has some measure.
  - `measure`: The measure of a set, defined as the unique value $m$ such that the set has measure $m$.

### Porting notes
When porting this theorem:
1. Ensure your system has a well-developed measure theory with concepts of measurable sets and translation-invariant measures.
2. Pay attention to how translations and finite unions of sets are handled in your target system.
3. The proof uses a contradiction argument combined with measure-theoretic inequalities, which should translate well to most systems.
4. The specific requirement that translated sets fit within the unit hypercube is essential - this constrains the overall measure of their union.

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
Let $s$ be a measurable set in $\mathbb{R}^N$. If $\text{measure}(s) > 1$, then there exist distinct points $x, y \in s$ such that $x_i - y_i$ is an integer for all coordinates $i$ where $1 \leq i \leq N$.

In other words, a measurable set with measure greater than 1 must contain two distinct points whose difference is in the integer lattice $\mathbb{Z}^N$.

### Informal proof
The proof proceeds in two main steps:

1. First, we prove a stronger statement for bounded measurable sets:
   - If $s$ is bounded, measurable, and $\text{measure}(s) > 1$, then the desired property holds.

2. Then, we reduce the general case to the bounded case:
   - Given a measurable set $s$ with $\text{measure}(s) > 1$
   - We use `MEASURABLE_INNER_COMPACT` to find a compact (hence bounded) subset $c \subset s$ with measure sufficiently large
   - Since $c$ is bounded and $\text{measure}(c) > 1$, the first part applies
   - The points found in $c$ work also for $s$ since $c \subset s$

For the bounded case, the proof uses a pigeonhole principle argument:

- We partition $\mathbb{R}^N$ into unit hypercubes centered at integer points
- Each hypercube has the form $\{x \in \mathbb{R}^N : u_i \leq x_i < u_i + 1\}$ for some $u \in \mathbb{Z}^N$
- Due to bounded nature of $s$, only finitely many such hypercubes intersect $s$
- The sum of measures of these intersections equals $\text{measure}(s) > 1$
- By a pigeonhole principle (formalized using the LEMMA about disjoint sets), there must exist distinct integer lattice points $u$ and $v$ where the hypercubes have non-empty intersection with $s$
- This gives us points $x \in s \cap (u \text{ hypercube})$ and $y \in s \cap (v \text{ hypercube})$ with $x - u = y - v$
- Therefore $x - y = u - v$ is an integer vector

The proof uses properties of measurable sets, floor function for constructing the integer grid, and basic set-theoretic arguments.

### Mathematical insight
Blichfeldt's theorem is a fundamental result in the geometry of numbers. It states a basic property about the density of points in high-dimensional spaces: any set with measure greater than 1 must contain lattice-equivalent points (points differing by integer vectors).

This theorem forms the backbone for many important results in number theory, particularly:
- It leads directly to Minkowski's theorem about convex bodies
- It provides insight into how points must be distributed in Euclidean space
- It establishes a fundamental relationship between volume and lattice points

The proof technique is essentially a continuous version of the pigeonhole principle, where the unit hypercubes serve as the "bins" and the measure of the set corresponds to the "objects" being placed into these bins.

### Dependencies
- **Theorems**:
  - `MEASURABLE_ALMOST`: If $s$ is measurable, $t$ is negligible, and $s \cup t = s' \cup t$, then $s'$ is measurable
  - `MEASURABLE_INTER_INTERVAL`: If $s$ is measurable, then $s \cap [a,b]$ is measurable
  - `MEASURABLE_INNER_COMPACT`: For a measurable set $s$ and $\varepsilon > 0$, there exists a compact set $t \subset s$ with $\text{measure}(s) < \text{measure}(t) + \varepsilon$

- **Definitions**:
  - `measurable`: A set is measurable if it has a measure
  - `measure`: The measure of a set

### Porting notes
When porting this theorem:
1. Ensure the target system has an adequate measure theory framework
2. The proof relies heavily on partition arguments and the pigeonhole principle, which may need different formulations in other systems
3. The LEMMA used in the proof (shown as "ISPECL ... LEMMA") appears to be a general result about partitioning sets that may need to be proved separately
4. Care must be taken with the bounded/unbounded distinction, as the proof strategy handles these cases differently

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
For any set $s \subseteq \mathbb{R}^N$ that is:
- convex,
- symmetric about the origin (i.e., $\forall x \in s, -x \in s$), and
- has measure greater than $2^N$,

there exists a nonzero integer lattice point in $s$ (i.e., there exists $u \in s$ such that $u \neq 0$ and all coordinates of $u$ are integers).

### Informal proof
The proof proceeds in two main phases:

- First, we prove that the theorem holds for bounded sets.
- Then, we extend the result to unbounded sets.

For the bounded case:
* We apply Blichfeldt's theorem to the set $s' = \{\frac{1}{2}x : x \in s\}$, which is also convex and measurable.
* Since $s$ has measure greater than $2^N$, the scaled set $s'$ has measure greater than $1$ (by the scaling property of measure).
* Blichfeldt's theorem implies that there exist distinct points $u, v \in s'$ such that $u - v$ has integer coordinates.
* Let $w = \frac{1}{2}(u - v)$. Since $u \neq v$, $w \neq 0$, and $w$ has integer coordinates.
* By convexity and symmetry of $s$, $w \in s$.

For the unbounded case:
* For an unbounded convex set $s$ with measure greater than $2^N$, we can find a large enough compact subset $c \subset s$ with measure still greater than $2^N$.
* We restrict our attention to $s \cap B(0,r)$ where $B(0,r)$ is a ball containing $c$.
* This intersection is bounded, convex, and symmetric, with measure greater than $2^N$.
* We apply the bounded case to find a nonzero integer lattice point in this intersection, which is also in $s$.

### Mathematical insight
This is Minkowski's theorem, a fundamental result in the geometry of numbers. It states that if a convex, symmetric body in $\mathbb{R}^N$ has volume greater than $2^N$, then it must contain a nonzero integer lattice point. The theorem has numerous applications in number theory, including:

1. Proving that certain Diophantine equations have solutions
2. Finding small solutions to linear congruences
3. Establishing bounds for the discriminant of algebraic number fields
4. Proving results about quadratic forms

The theorem is particularly important because it provides a geometric condition (volume > $2^N$) that guarantees the existence of integer points with specific properties.

### Dependencies
- Measure theory:
  - `measure`
  - `MEASURE_SUBSET`
  - `MEASURABLE_SCALING`
  - `MEASURE_SCALING`
  - `MEASURABLE_COMPACT`
  - `MEASURABLE_CONVEX`
  - `LEBESGUE_MEASURABLE_CONVEX`
  - `CHOOSE_LARGE_COMPACT_SUBSET_ALT`
- Convex geometry:
  - Blichfeldt's theorem (implied by the code)

### Porting notes
When porting this theorem:
1. Ensure your system has a well-developed theory of measure for subsets of $\mathbb{R}^N$.
2. The proof relies on Blichfeldt's theorem, which should be ported first.
3. The treatment of bounded vs. unbounded convex sets requires careful handling - make sure your system can handle this distinction.
4. The HOL Light techniques for handling vector components and integer constraints should be translated appropriately to your target system's conventions.

---

## MINKOWSKI_COMPACT

### MINKOWSKI_COMPACT
- MINKOWSKI_COMPACT

### Type of the formal statement
- theorem

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

For any set $s$ in $\mathbb{R}^N$, if:
1. $s$ is convex,
2. $s$ is compact,
3. $s$ is symmetric about the origin (i.e., $\forall x \in s, -x \in s$), and
4. The measure of $s$ is at least $2^N$ (where $N$ is the dimension),

then there exists a non-zero integer lattice point in $s$, i.e., there exists a vector $u$ such that:
- $u \neq 0$,
- All components of $u$ are integers: $\forall i. 1 \leq i \leq N \Rightarrow u_i \in \mathbb{Z}$, and
- $u \in s$.

### Informal proof

The proof proceeds as follows:

* First, we handle the trivial case where $s$ is empty. This case is impossible because $2^N > 0 = \text{measure}(\emptyset)$.

* Next, we establish that $0 \in s$. This follows from convexity and symmetry: if $a \in s$, then $-a \in s$ by symmetry, and $0 = \frac{1}{2}a + \frac{1}{2}(-a) \in s$ by convexity.

* We aim to apply the separation theorem between compact and closed sets. The key is to consider the set $s$ and the set of integer lattice points excluding the origin.

* We show that the set of integer lattice points is discrete (hence closed). We prove that any two distinct integer lattice points have distance at least 1.

* For a contradiction, we assume there is no non-zero integer lattice point in $s$. This means $s$ can be separated from the non-zero integer lattice points. So there exists some distance $d > 0$ between them.

* Since $s$ is compact, it is bounded. Let $B > 0$ be such that $\|x\| \leq B$ for all $x \in s$.

* We then apply the Minkowski theorem to the scaled set $s' = \{(1+\frac{d}{2B})x : x \in s\}$. This set is:
  - Convex (as scaling preserves convexity)
  - Bounded (as scaling preserves boundedness)
  - Symmetric about origin (by construction)
  - Has measure $(1+\frac{d}{2B})^N \cdot \text{measure}(s) > 2^N$

* By Minkowski's theorem, there exists a non-zero integer lattice point $u$ in $s'$.

* This means $u = (1+\frac{d}{2B})x$ for some $x \in s$. 

* We derive a contradiction by showing that the distance between $u$ and $(1+\frac{d}{2B})u$ is less than $d$, which contradicts our assumption about the minimum distance.

* Therefore, there must exist a non-zero integer lattice point in $s$.

### Mathematical insight

This theorem is a variant of Minkowski's theorem from the geometry of numbers, specifically tailored for compact sets. It connects metric properties (measure) with algebraic properties (integer lattice points).

The key insight is that if a convex, symmetric set is "large enough" (as measured by its volume/measure), then it must contain a non-zero lattice point. The threshold for "large enough" is explicitly given as $2^N$, where $N$ is the dimension.

This result has applications in number theory, particularly in the study of lattice points in convex bodies. It's fundamentally related to Minkowski's first theorem, which is a cornerstone in the geometry of numbers.

### Dependencies

- **Theorems**:
  - `MEASURE_UNIQUE`: If a set has measure $m$, then its measure equals $m$.
  - `HAS_MEASURE_0`: A set has measure 0 if and only if it is negligible.
  - `MEASURE_EMPTY`: The measure of the empty set is 0.
  - `MEASURABLE_MEASURE_POS_LT`: For measurable sets, measure is positive iff set is not negligible.
  - `MEASURE_SCALING`: For measurable sets, measure of scaled set is scaled by |c|^N.
  - `MEASURABLE_COMPACT`: All compact sets are measurable.

- **Definitions**:
  - `measure`: The measure of a set.

### Porting notes

When porting this theorem:
1. Ensure your system has a measure theory that properly handles sets in $\mathbb{R}^N$.
2. The notion of "compact" should be standard (closed and bounded in Euclidean space).
3. The theorem uses a separation theorem for compact and closed sets, which should be available in most proof assistants.
4. The proof makes use of several arithmetic and vector manipulations that should be relatively straightforward in any system with good real number support.

---

