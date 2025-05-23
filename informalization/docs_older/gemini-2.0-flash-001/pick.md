# pick.ml

## Overview

Number of statements: 45

The file `pick.ml` formalizes Pick's theorem, a result relating the area of a simple polygon with integer vertex coordinates to the number of integer points in its interior and on its boundary. It relies on prior formalizations of polytopes, measure theory, and topology in multivariate analysis. The file is intended to provide a formal statement and proof of this geometric theorem within HOL Light.


## COLLINEAR_IMP_NEGLIGIBLE

### Name of formal statement
COLLINEAR_IMP_NEGLIGIBLE

### Type of the formal statement
theorem

### Formal Content
```hol
let COLLINEAR_IMP_NEGLIGIBLE = prove
 (`!s:real^2->bool. collinear s ==> negligible s`,
  REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
  MESON_TAC[NEGLIGIBLE_AFFINE_HULL_2; NEGLIGIBLE_SUBSET]);;
```

### Informal statement
For all sets `s` of points in the real plane, if `s` is collinear, then `s` is negligible.

### Mathematical insight
This theorem states that a collinear set of points in the real plane has measure zero. A negligible set is defined to be a set that has outer measure zero. The intuition is that since a collinear set lies on a line, its area is zero, hence it is negligible.

### Informal sketch
The proof proceeds as follows:
- Rewrite the goal `collinear s ==> negligible s` using the theorem `COLLINEAR_AFFINE_HULL` to replace `collinear s` with `negligible (affine_hull s)`. Thus the goal becomes `negligible (affine_hull s) ==> negligible s`.
- Apply `MESON_TAC` with `NEGLIGIBLE_AFFINE_HULL_2` (which states that the affine hull of any set is negligible) and `NEGLIGIBLE_SUBSET` (which states that if a set `s'` is a subset of a negligible set, then `s'` is also negligible). Using `NEGLIGIBLE_AFFINE_HULL_2`, the goal `negligible (affine_hull s) ==> negligible s` is proven by showing that `s` is a subset of `affine_hull s`.

### Dependencies
- `COLLINEAR_AFFINE_HULL`
- `NEGLIGIBLE_AFFINE_HULL_2`
- `NEGLIGIBLE_SUBSET`


---

## CONVEX_HULL_3_0

### Name of formal statement
CONVEX_HULL_3_0

### Type of the formal statement
theorem

### Formal Content
```hol
let CONVEX_HULL_3_0 = prove
 (`!a b:real^N.
        convex hull {vec 0,a,b} =
        {x % a + y % b | &0 <= x /\ &0 <= y /\ x + y <= &1}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {a,b,c}`] THEN
  REWRITE_TAC[CONVEX_HULL_3; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real` THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_ARITH_TAC; EXISTS_TAC `&1 - x - y` THEN ASM_ARITH_TAC]);;
```

### Informal statement
For any vectors `a` and `b` in `real^N`, the convex hull of the set containing the zero vector `vec 0`, `a`, and `b` is equal to the set of all vectors of the form `x % a + y % b` where `x` and `y` are real numbers such that `0 <= x`, `0 <= y`, and `x + y <= 1`. Here `%` denotes scalar multiplication and `real^N` is the N-dimensional real vector space.

### Mathematical insight
This theorem provides a concrete characterization of the convex hull of a set containing the origin and two other vectors in a real vector space. It states that any point in this convex hull can be expressed as a linear combination of the two vectors, where the coefficients are non-negative and sum to at most 1. This characterization is useful for geometric reasoning and for proving properties about convex sets.

### Informal sketch
The proof proceeds as follows:

- Start by generalizing the goal using `REPEAT GEN_TAC`.
- Rewrite the set `{vec 0, a, b}` to `{a, b, vec 0}` using the theorem `SET_RULE '{c,a,b} = {a,b,c}'`.
- Rewrite the goal using the definition of the convex hull of three elements `CONVEX_HULL_3`, the theorem `EXTENSION` for set equality, and `IN_ELIM_THM` to eliminate set membership.
- Introduce dummy variables `x` and `y` using `X_GEN_TAC` and `AP_TERM_TAC` and rewrite with `FUN_EQ_THM`, effectively introducing `x` and `y` as parameters for constructing elements of the set {`x % a + y % b` | `&0 <= x /\ &0 <= y /\ x + y <= &1`}.
- Simplify using `VECTOR_MUL_RZERO` and `VECTOR_ADD_RID`.
- Apply `EQ_TAC` to split the goal into two subgoals (left-to-right and right-to-left implications).
- Apply `STRIP_TAC` to move the assumption of the implication to the assumption list and the conclusion to the conclusion.
- Apply `ASM_REWRITE_TAC[]` to simplify the goal using the assumptions.
- Solve the remaining goals using `ASM_ARITH_TAC` and `EXISTS_TAC '&1 - x - y'` followed by `ASM_ARITH_TAC`.

### Dependencies
- `CONVEX_HULL_3`
- `EXTENSION`
- `IN_ELIM_THM`
- `VECTOR_MUL_RZERO`
- `VECTOR_ADD_RID`
- `SET_RULE '{c,a,b} = {a,b,c}'`
- `FUN_EQ_THM`

### Porting notes (optional)
- The proof relies on arithmetic reasoning, so the target proof assistant should have good support for linear arithmetic over the reals.
- The definition of `CONVEX_HULL_3` and theorems related to set theory and vector spaces like `{c,a,b} = {a,b,c}` should be ported beforehand.


---

## INTERIOR_CONVEX_HULL_3_0

### Name of formal statement
INTERIOR_CONVEX_HULL_3_0

### Type of the formal statement
theorem

### Formal Content
```hol
let INTERIOR_CONVEX_HULL_3_0 = prove
 (`!a b:real^2.
        ~(collinear {vec 0,a,b})
        ==> interior(convex hull {vec 0,a,b}) =
              {x % a + y % b | &0 < x /\ &0 < y /\ x + y < &1}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {a,b,c}`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3] THEN
  REWRITE_TAC[TAUT `a /\ x = &1 /\ b <=> x = &1 /\ a /\ b`] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH `x + y + z = &1 <=> &1 - x - y = z`; UNWIND_THM1] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
For any two vectors `a` and `b` in the real plane `real^2`, if the set containing the zero vector, `a`, and `b` are not collinear, then the interior of the convex hull of the set containing the zero vector `vec 0`, `a`, and `b` is equal to the set of all vectors of the form `x % a + y % b`, where `x` and `y` are real numbers such that `0 < x`, `0 < y`, and `x + y < 1`.

### Mathematical insight
This theorem characterizes the interior of a convex hull formed by the zero vector and two non-collinear vectors. It essentially states that the interior consists of all positive linear combinations of the two vectors `a` and `b`, where the coefficients sum to less than 1. This constructs a (non-closed) triangle without its edges or vertices.

### Informal sketch
The proof proceeds as follows:
- Start by generalizing the goal with the `REPEAT GEN_TAC`.
- Rewrite the set `{vec 0, a, b}` using the set rule `{c, a, b} = {a, b, c}`.
- Strip the universal quantifiers and implication.
- Simplify using `INTERIOR_CONVEX_HULL_3`.
- Tautologically rewrite using `a /\ x = &1 /\ b <=> x = &1 /\ a /\ b`.
- Apply arithmetic simplifications with `VECTOR_MUL_RZERO` and `VECTOR_ADD_RID`.
- Rewrite with a real arithmetic rule `x + y + z = &1 <=> &1 - x - y = z` and unwind a theorem with `UNWIND_THM1`.
- Rewrite using `EXTENSION` and `IN_ELIM_THM`.
- Apply tactics to rewrite, and generalize with `GEN_TAC`, then apply and abstract.
- Apply an equality tactic, strip, rewrite with the assumption list and use `ASM_REAL_ARITH_TAC`.

### Dependencies
- `INTERIOR_CONVEX_HULL_3`
- `SET_RULE`
- `VECTOR_MUL_RZERO`
- `VECTOR_ADD_RID`
- `REAL_ARITH`
- `EXTENSION`
- `IN_ELIM_THM`
- `TAUT`
- `UNWIND_THM1`

### Porting notes (optional)
The main challenge in porting this theorem lies in the handling of real arithmetic and vector operations. Ensure that the target proof assistant has comparable libraries for real numbers and vector spaces. The tactic `ASM_REAL_ARITH_TAC` may need to be replaced by equivalent automation for real arithmetic reasoning in the other proof assistant. Also ensure the corresponding definition of collinearity, convex hull, and interior have been properly defined.


---

## MEASURE_CONVEX_HULL_2_TRIVIAL

### Name of formal statement
MEASURE_CONVEX_HULL_2_TRIVIAL

### Type of the formal statement
theorem

### Formal Content
```hol
let MEASURE_CONVEX_HULL_2_TRIVIAL = prove
 (`(!a:real^2. measure(convex hull {a}) = &0) /\
   (!a b:real^2. measure(convex hull {a,b}) = &0)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_EQ_0 THEN
  MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; CONVEX_HULL_SING] THEN
  REWRITE_TAC[COLLINEAR_SING; COLLINEAR_SEGMENT]);;
```

### Informal statement
The theorem states that:
1. For any point `a` in the real plane, the measure of the convex hull of the set containing only `a` is 0.
2. For any two points `a` and `b` in the real plane, the measure of the convex hull of the set containing `a` and `b` is 0.

### Mathematical insight
This theorem expresses the intuitive fact that points and line segments in the plane have zero Lebesgue measure. The convex hull of a single point is the point itself, and the convex hull of two points is the line segment connecting them. Since both are one-dimensional objects embedded in the two-dimensional plane, they have zero area.

### Informal sketch
The proof proceeds as follows:
- First, strip the goal. This splits the goal into two subgoals, one for each universally quantified statement.
- The first subgoal, `measure(convex hull {a}) = &0`, is handled using `MEASURE_EQ_0`. An auxiliary theorem `MEASURE_EQ_0` is used, which essentially states that the measure of a set is 0 if and only if the set is negligible.
- The second subgoal, `measure(convex hull {a,b}) = &0`, is handled similarly: first apply `MEASURE_EQ_0`, then `COLLINEAR_IMP_NEGLIGIBLE`. `COLLINEAR_IMP_NEGLIGIBLE` says that if any two distinct points are collinear, they have negligible measure. The remaining proof steps are:
  - Rewrite `convex hull {a}` to `{a}` using `CONVEX_HULL_SING`.
  - Rewrite `convex hull {a,b}` to `SEGMENT(a,b)` using `GSYM SEGMENT_CONVEX_HULL`.
  - Finally, use `COLLINEAR_SING` and `COLLINEAR_SEGMENT` to show that `{a}` and `SEGMENT(a,b)` are collinear, thus measurable

### Dependencies
- Theorems:
  - `MEASURE_EQ_0`
  - `COLLINEAR_IMP_NEGLIGIBLE`
  - `COLLINEAR_SING`
  - `COLLINEAR_SEGMENT`

- Definitions/Theorems used as rewrite rules:
  - `GSYM SEGMENT_CONVEX_HULL`
  - `CONVEX_HULL_SING`


---

## NEGLIGIBLE_SEGMENT_2

### Name of formal statement
NEGLIGIBLE_SEGMENT_2

### Type of the formal statement
theorem

### Formal Content
```hol
let NEGLIGIBLE_SEGMENT_2 = prove
 (`!a b:real^2. negligible(segment[a,b])`,
  SIMP_TAC[COLLINEAR_IMP_NEGLIGIBLE; COLLINEAR_SEGMENT]);;
```

### Informal statement
For all points `a` and `b` in the real plane, the line segment connecting `a` and `b` is negligible.

### Mathematical insight
This theorem states that any line segment in the real plane has negligible area. This is a fundamental property used in measure theory, where sets of measure zero are "negligible" for integration. A line segment, being a one-dimensional object embedded in two dimensions, has zero area.

### Informal sketch
The proof uses simplification tactics with the following steps:
- The goal is `negligible(segment[a,b])` for arbitrary `a` and `b`.
- Apply `COLLINEAR_SEGMENT`, which states that `collinear[a,b; a,b]` for any `a` and `b`. This reduces the goal to `negligible(segment[a,b])` given `collinear[a,b; a,b]`.
- Apply `COLLINEAR_IMP_NEGLIGIBLE`, which states that if vectors `a`,`b` are collinear, then the line segment `segment[a,b]` is negligible. This discharges the condition `collinear[a,b; a,b]` and proves the goal.

### Dependencies
- Theorems: `COLLINEAR_IMP_NEGLIGIBLE`, `COLLINEAR_SEGMENT`


---

## TRIANGLE_DECOMPOSITION

### Name of formal statement
TRIANGLE_DECOMPOSITION

### Type of the formal statement
theorem

### Formal Content
```hol
let TRIANGLE_DECOMPOSITION = prove
 (`!a b c d:real^2.
        d IN convex hull {a,b,c}
        ==> (convex hull {a,b,c} =
             convex hull {d,b,c} UNION
             convex hull {d,a,c} UNION
             convex hull {d,a,b})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{a:real^2,b,c}`; `d:real^2`; `x:real^2`]
     IN_CONVEX_HULL_EXCHANGE) THEN
    ASM_REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN
    REPEAT(MATCH_MP_TAC MONO_OR THEN CONJ_TAC) THEN
    SPEC_TAC(`x:real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    SIMP_TAC[SUBSET_HULL; CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[HULL_INC; IN_INSERT]]);;
```

### Informal statement
For all points `a`, `b`, `c`, and `d` in the real plane, if `d` is in the convex hull of `{a, b, c}`, then the convex hull of `{a, b, c}` is equal to the union of the convex hulls of `{d, b, c}`, `{d, a, c}`, and `{d, a, b}`.

### Mathematical insight
This theorem states that if a point `d` lies within a triangle defined by vertices `a`, `b`, and `c`, then the triangle can be decomposed into three smaller triangles with `d` as a common vertex.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal.
- Apply the antisymmetry property of subsets (`SUBSET_ANTISYM`). This requires proving that `convex hull {a,b,c}` is a subset of `convex hull {d,b,c} UNION convex hull {d,a,c} UNION convex hull {d,a,b}` and vice-versa.
- Rewrite using `UNION_SUBSET`.
- Split the goal into two subgoals (corresponding to the two subset inclusions).
    - For the first subgoal ( `convex hull {a,b,c}` is a subset of `convex hull {d,b,c} UNION convex hull {d,a,c} UNION convex hull {d,a,b}` ):
        - Rewrite `SUBSET` to introduce the `IN` predicate meaning membership.
        - Introduce a variable `x:real^2` representing an arbitrary point.
        - Discharge the assumption.
        - Instantiate the theorem `IN_CONVEX_HULL_EXCHANGE` with `{a,b,c}`, `d`, and `x`. `IN_CONVEX_HULL_EXCHANGE` likely relates membership in the convex hull of a set to conditions involving existing members and another point.
        - Simplify with `EXISTS_IN_INSERT`, `NOT_IN_EMPTY`, and `IN_UNION`.
        - Repeatedly apply `MONO_OR` followed by `CONJ_TAC`.
        - Specialize `x:real^2` twice and simplify with `GSYM SUBSET`.
        - Apply `HULL_MONO` followed by `SET_TAC[]`.
    - For the second subgoal ( `convex hull {d,b,c} UNION convex hull {d,a,c} UNION convex hull {d,a,b}` is a subset of `convex hull {a,b,c}` ):
        - Simplify using `SUBSET_HULL` and `CONVEX_CONVEX_HULL`.
        - Rewrite with `INSERT_SUBSET` and `EMPTY_SUBSET`.
        - Simplify using `HULL_INC` and `IN_INSERT`.

### Dependencies
**Theorems:**
- `SUBSET_ANTISYM`
- `UNION_SUBSET`
- `EXISTS_IN_INSERT`
- `NOT_IN_EMPTY`
- `IN_UNION`
- `MONO_OR`
- `GSYM SUBSET`
- `HULL_MONO`
- `SUBSET_HULL`
- `CONVEX_CONVEX_HULL`
- `INSERT_SUBSET`
- `EMPTY_SUBSET`
- `HULL_INC`
- `IN_INSERT`

**Definitions:**
- `IN`
- `convex hull`

**Tactics:**
- `REPEAT STRIP_TAC`
- `MATCH_MP_TAC`
- `REWRITE_TAC`
- `CONJ_TAC`
- `X_GEN_TAC`
- `DISCH_TAC`
- `MP_TAC`
- `ISPECL`
- `ASM_REWRITE_TAC`
- `SPEC_TAC`
- `SET_TAC`
- `SIMP_TAC`
- `ASM_SIMP_TAC`

### Porting notes
- The theorem relies heavily on properties of convex hulls and set theory. Ensure that equivalent theorems are available or proven in the target proof assistant.
- The tactic `SET_TAC` likely performs set-theoretic reasoning. This may need to be replicated using appropriate automation in other systems.
- `IN_CONVEX_HULL_EXCHANGE` likely defines when some point `x` is inside the `convex hull {a, b, c}`; this definition may need to be ported into the target system.


---

## TRIANGLE_ADDITIVE_DECOMPOSITION

### Name of formal statement
TRIANGLE_ADDITIVE_DECOMPOSITION

### Type of the formal statement
theorem

### Formal Content
```hol
let TRIANGLE_ADDITIVE_DECOMPOSITION = prove
 (`!f:(real^2->bool)->real a b c d.
        (!s t. compact s /\ compact t
               ==> f(s UNION t) = f(s) + f(t) - f(s INTER t)) /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        ~affine_dependent {a,b,c} /\ d IN convex hull {a,b,c}
        ==> f(convex hull {a,b,c}) =
            (f(convex hull {a,b,d}) +
             f(convex hull {a,c,d}) +
             f(convex hull {b,c,d})) -
            (f(convex hull {a,d}) +
             f(convex hull {b,d}) +
             f(convex hull {c,d})) +
            f(convex hull {d})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP TRIANGLE_DECOMPOSITION) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [COMPACT_UNION; COMPACT_INTER; COMPACT_CONVEX_HULL;
               FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY;
               UNION_OVER_INTER] THEN
  MP_TAC(ISPECL [`{a:real^2,b,c}`; `d:real^2`]
        CONVEX_HULL_EXCHANGE_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY;
           SET_RULE `s SUBSET u /\ t SUBSET u ==> (s INTER t) SUBSET u`] THEN
  ASM_REWRITE_TAC[INSERT_INTER; IN_INSERT; NOT_IN_EMPTY; INTER_EMPTY] THEN
  DISCH_TAC THEN REWRITE_TAC[INSERT_AC] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any function `f` from sets of points in the real plane to real numbers, and any points `a`, `b`, `c`, and `d` in the real plane, if:

1.  `f` is additive on compact sets, meaning that for any compact sets `s` and `t`, `f(s UNION t) = f(s) + f(t) - f(s INTER t)`, and
2.  `a`, `b`, and `c` are distinct points and not affine dependent (i.e., not collinear), and
3.  `d` lies within the convex hull of `{a, b, c}`,

then the value of `f` on the convex hull of `{a, b, c}` can be expressed as:

`f(convex hull {a, b, c}) = (f(convex hull {a, b, d}) + f(convex hull {a, c, d}) + f(convex hull {b, c, d})) - (f(convex hull {a, d}) + f(convex hull {b, d}) + f(convex hull {c, d})) + f(convex hull {d})`

### Mathematical insight
This theorem provides a decomposition formula for the value of a function `f` over a triangle (the convex hull of three non-collinear points) in terms of its values on smaller triangles and line segments obtained by introducing a fourth point `d` inside the original triangle. It expresses how the function's value on the entire triangle can be calculated from its values on smaller components formed by connecting an interior point to the vertices. The additivity property of `f` is crucial for this decomposition.

### Informal sketch
The proof proceeds by induction on a pre-existing theorem called `TRIANGLE_DECOMPOSITION`.

- The theorem starts by stripping the premises, introducing the function `f` and the points `a`, `b`, `c`, and `d` into the assumptions.
- Application of a substitution based on the `TRIANGLE_DECOMPOSITION` theorem, which decomposes the original triangle.
- Simplification using `COMPACT_UNION`, `COMPACT_INTER`, `COMPACT_CONVEX_HULL`, `FINITE_IMP_COMPACT`, `FINITE_INSERT`, `FINITE_EMPTY`, and `UNION_OVER_INTER` to eliminate set operations with convex hulls. This step exploits the assumed compactness and also simplifies expressions involving unions and intersections.
- Application of `CONVEX_HULL_EXCHANGE_INTER` after specializing to `{a:real^2,b,c}` and `d:real^2`.
- Rewriting with assumptions.
- Simplification with `INSERT_SUBSET`, `EMPTY_SUBSET`, `IN_INSERT`, `NOT_IN_EMPTY`, and a subset rule, presumably handling set-theoretic manipulation.
- Rewriting with `INSERT_INTER`, `IN_INSERT`, `NOT_IN_EMPTY`, `INTER_EMPTY`.
- Discharging and rewriting with `INSERT_AC` to canonicalise the order of elements in the sets.
- Finally, use real arithmetic to conclude.

### Dependencies

**Theorems:**
- `TRIANGLE_DECOMPOSITION`

**Definitions:**
- `convex hull`
- `affine_dependent`
- `compact`

**Lemmas/Rules:**
- `COMPACT_UNION`
- `COMPACT_INTER`
- `COMPACT_CONVEX_HULL`
- `FINITE_IMP_COMPACT`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `UNION_OVER_INTER`
- `CONVEX_HULL_EXCHANGE_INTER`
- `INSERT_SUBSET`
- `EMPTY_SUBSET`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `INSERT_INTER`
- `INTER_EMPTY`
- `INSERT_AC`


---

## integral_vector

### Name of formal statement
integral_vector

### Type of the formal statement
new_definition

### Formal Content
```hol
let integral_vector = define
 `integral_vector(x:real^N) <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i)`;;
```

### Informal statement
The vector `x` of type `real^N` is an integral vector, written `integral_vector(x)`, if and only if for all indices `i`, if `i` is greater than or equal to 1 and `i` is less than or equal to the dimension index of the type `:N`, then the `i`-th element of `x` is an integer.

### Mathematical insight
The definition introduces the concept of an "integral vector." An integral vector is a vector whose components are all integers. The definition quantifies over all possible index values `i` to assert that each component `x$i` should satisfy the integer predicate. The dimension of the vector space `N` is obtained using `dimindex(:N)`.

### Informal sketch
To define `integral_vector`, the following steps are taken:

- Express the condition for a vector `x` to be an integral vector. This condition is that every component of `x` must be an integer.
- Formalize this condition. For each index `i` between 1 and the dimension `dimindex(:N)`, the `i`-th component `x$i` must satisfy the predicate `integer`.
- Use `define` tactical to introduce the definition `integral_vector(x) <=> !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i)`.

### Dependencies
- `integer`
- `dimindex`


---

## INTEGRAL_VECTOR_VEC

### Name of formal statement
INTEGRAL_VECTOR_VEC

### Type of the formal statement
theorem

### Formal Content
```hol
let INTEGRAL_VECTOR_VEC = prove
 (`!n. integral_vector(vec n)`,
  REWRITE_TAC[integral_vector; VEC_COMPONENT; INTEGER_CLOSED]);;
```

### Informal statement
For all natural numbers `n`, the vector `vec n` is an integral vector.

### Mathematical insight
This theorem states that given a natural number `n`, the function `vec` applied to `n` produces an integral vector. The function `vec` presumably constructs a vector, and the predicate `integral_vector` checks if all components of a given vector are integers.

### Informal sketch
The proof proceeds by rewriting the goal using the definitions of `integral_vector` and `VEC_COMPONENT`, and the theorem `INTEGER_CLOSED`.

- The initial goal is `!n. integral_vector(vec n)`.
- We rewrite `integral_vector` to expand its definition.
- We rewrite using `VEC_COMPONENT` to access the components of `vec n`.
- The goal is then proven utilizing `INTEGER_CLOSED`.

### Dependencies
- Definitions: `integral_vector`, `VEC_COMPONENT`
- Theorems: `INTEGER_CLOSED`


---

## INTEGRAL_VECTOR_STDBASIS

### Name of formal statement
INTEGRAL_VECTOR_STDBASIS

### Type of the formal statement
theorem

### Formal Content
```hol
let INTEGRAL_VECTOR_STDBASIS = prove
 (`!i. integral_vector(basis i:real^N)`,
  REWRITE_TAC[integral_vector] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED]);;
```

### Informal statement
For all `i`, the vector `basis i` in `real^N` is an integral vector.

### Mathematical insight
This theorem states that the standard basis vectors in `real^N` are integral vectors.  An integral vector is defined as a vector whose components are all integers. The standard basis vectors have a `1` in the `i`-th position and `0` elsewhere. Since `1` and `0` are integers, the standard basis vectors are integral vectors. This is a fundamental property often used in linear algebra and vector space theory.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `!i. integral_vector(basis i:real^N)`.
- Expand the definition of `integral_vector` using `REWRITE_TAC[integral_vector]`. This replaces `integral_vector v` with `!n. integral(v$n)`.
- Apply `REPEAT STRIP_TAC` to remove the quantifier `!i` and `!n`, and thus stripping implications and universally quantified variables by introducing the assumptions into the assumption list.
- Simplify using assumption `ASM_SIMP_TAC[BASIS_COMPONENT]`. The term `basis i $ n` becomes `Kronecker delta i n` for all `i` and `n`.
- Perform `COND_CASES_TAC` to consider the cases of `i = n` and `~(i = n)`.
- In both cases, simplify using `REWRITE_TAC[INTEGER_CLOSED]`. Since the Kronecker delta is either 0 or 1, both integers, the goal is proven.

### Dependencies
- `integral_vector`
- `BASIS_COMPONENT`
- `INTEGER_CLOSED`


---

## INTEGRAL_VECTOR_ADD

### Name of formal statement
INTEGRAL_VECTOR_ADD

### Type of the formal statement
theorem

### Formal Content
```hol
let INTEGRAL_VECTOR_ADD = prove
 (`!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x + y)`,
  SIMP_TAC[integral_vector; VECTOR_ADD_COMPONENT; INTEGER_CLOSED]);;
```

### Informal statement
For all vectors `x` and `y` of real numbers indexed by the type `N`, if `x` is an integral vector and `y` is an integral vector, then the vector sum of `x` and `y` is also an integral vector.

### Mathematical insight
This theorem states that the set of integral vectors is closed under vector addition. An "integral vector" is a vector where all components are integers.  This is a fundamental property needed when reasoning about integral vectors.

### Informal sketch
The proof proceeds by:
- Using `SIMP_TAC` to apply the definitions of `integral_vector` and `VECTOR_ADD_COMPONENT`, and the property `INTEGER_CLOSED`.
- The definition of `integral_vector x` unfolds to `!i. x$i IN Int`, asserting that every component indexed by `i` of vector `x` is an integer.
- `VECTOR_ADD_COMPONENT` states that `(x + y)$i = x$i + y$i`. This allows rewriting the condition that `(x+y)` is an integral vector to show that each component `(x+y)$i` is integral, which can be rewritten to `x$i + y$i IN Int`.
- `INTEGER_CLOSED` states that `!x y. x IN Int /\ y IN Int ==> x + y IN Int`.
- The `SIMP_TAC` tactic chains these facts together to prove the theorem.

### Dependencies
- `integral_vector`
- `VECTOR_ADD_COMPONENT`
- `INTEGER_CLOSED`


---

## INTEGRAL_VECTOR_SUB

### Name of formal statement
INTEGRAL_VECTOR_SUB

### Type of the formal statement
theorem

### Formal Content
```
let INTEGRAL_VECTOR_SUB = prove
 (`!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x - y)`,
  SIMP_TAC[integral_vector; VECTOR_SUB_COMPONENT; INTEGER_CLOSED]);;
```

### Informal statement
For all vectors `x` and `y` of type `real^N`, if `x` is an integral vector and `y` is an integral vector, then the vector `x - y` is an integral vector.

### Mathematical insight
This theorem states that the set of integral vectors (vectors where all components are integers) is closed under subtraction. This is a fundamental property when reasoning about vector spaces and linear algebra over integers. The integral vectors form a subgroup of the vector space of real vectors.

### Informal sketch
The proof proceeds by simplifying the goal using the following facts:

- The definition of `integral_vector`: `integral_vector v` holds if and only if all components of `v` are integers.
- The definition of `VECTOR_SUB_COMPONENT`: `(x - y)$i = x$i - y$i` for any index `i`.
- `INTEGER_CLOSED`: The integers are closed under subtraction; that is, if `x` and `y` are integers, then `x - y` is an integer.

The goal `integral_vector(x - y)` is thus reduced to showing that `x$i - y$i` is an integer for all indices `i`, given that `x$i` and `y$i` are integers for all indices `i`. This follows directly from `INTEGER_CLOSED`.

### Dependencies
- Definitions: `integral_vector`, `VECTOR_SUB_COMPONENT`
- Theorems: `INTEGER_CLOSED`


---

## INTEGRAL_VECTOR_ADD_LCANCEL

### Name of formal statement
INTEGRAL_VECTOR_ADD_LCANCEL

### Type of the formal statement
theorem

### Formal Content
```hol
let INTEGRAL_VECTOR_ADD_LCANCEL = prove
 (`!x y:real^N.
        integral_vector x ==> (integral_vector(x + y) <=> integral_vector y)`,
  MESON_TAC[INTEGRAL_VECTOR_ADD; INTEGRAL_VECTOR_SUB;
            VECTOR_ARITH `(x + y) - x:real^N = y`]);;
```

### Informal statement
For all vectors `x` and `y` in `real^N`, if `x` is an integral vector, then `x + y` is an integral vector if and only if `y` is an integral vector.

### Mathematical insight
This theorem states that adding an integral vector to another vector preserves the property of being an integral vector if and only if the original "other" vector already possessed that property. In other words, whether the sum `x + y` is an integral vector depends entirely on `y` when `x` is already known to be an integral vector.

### Informal sketch
The proof is automated using `MESON_TAC`, which combines several key facts:

- `INTEGRAL_VECTOR_ADD`: if `x` and `y` are integral vectors, then `x + y` is an integral vector.
- `INTEGRAL_VECTOR_SUB`: if `x` and `y` are integral vectors, then `x - y` is an integral vector.
- `VECTOR_ARITH \`(x + y) - x:real^N = y\``: This is a basic vector arithmetic fact showing that `(x + y) - x` simplifies to `y`.
*   The `MESON_TAC` likely uses these to decompose the equivalence.
    *   (=>) If `integral_vector (x + y)` and `integral_vector x`, then by `INTEGRAL_VECTOR_SUB` we have `integral_vector ((x+y) - x)`. The arithmetic fact then gives `integral_vector y`.
    *   (<=) If `integral_vector y` and `integral_vector x`, then by `INTEGRAL_VECTOR_ADD` we have `integral_vector (x + y)`.

### Dependencies
- `INTEGRAL_VECTOR_ADD`
- `INTEGRAL_VECTOR_SUB`
- Vector arithmetic fact: `VECTOR_ARITH \`(x + y) - x:real^N = y\``

### Porting notes (optional)
The main challenge in porting this theorem lies in ensuring that the definitions of `integral_vector`, vector addition, subtraction, and the vector arithmetic simplification rule are correctly defined and that the automated tactic (analogous to `MESON_TAC`) can effectively combine these facts to prove the result. You might need to provide the proof steps manually if automation is insufficient.


---

## FINITE_BOUNDED_INTEGER_POINTS

### Name of formal statement
FINITE_BOUNDED_INTEGER_POINTS

### Type of the formal statement
theorem

### Formal Content
```
let FINITE_BOUNDED_INTEGER_POINTS = prove
 (`!s:real^N->bool. bounded s ==> FINITE {x | x IN s /\ integral_vector x}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL; integral_vector] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                       ==> integer(x$i) /\
                           (a:real^N)$i <= x$i /\ x$i <= (b:real^N)$i}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_INTSEG];
    ASM SET_TAC[]]);;
```

### Informal statement
For any set `s` of real N-dimensional vectors, if `s` is bounded, then the set of integer vectors within `s` is finite. An N-dimensional vector is an integer vector if all of its components are integers.

### Mathematical insight
This theorem states that a bounded set within a real vector space can contain only a finite number of points whose coordinates are all integers. This is a fundamental result in real analysis and has applications in various areas, including number theory and optimization. The core idea is to use the fact that a bounded set is contained in a closed interval, and then exploit the finiteness of integers within given real bounds.

### Informal sketch
The proof proceeds as follows:
- Assume `s` is a bounded set.
- Use `BOUNDED_SUBSET_CLOSED_INTERVAL` to show that there exist vectors `a` and `b` such that `s` is a subset of the interval defined by `a` and `b` (i.e., `{x | !i. a$i <= x$i /\ x$i <= b$i}`).
- Expand the definition of `integral_vector` and `IN` for intervals.
- Use `FINITE_SUBSET`, so we need to show the set of integer vectors included in interval `a` and `b` is finite.
- Provide an explicit finite set, the Cartesian product of integer segments defined by a and b : `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i) /\ (a:real^N)$i <= x$i /\ x$i <= (b:real^N)$i}`
- Prove the set of integer vectors in interval(`a`,`b`) is a subset of that explicit finite set. This is proved by assumption contradiction.
- Prove the explicit finite set is finite. By the theorem `FINITE_CART` and rewrite with `FINITE_INTSEG`, which states integer segments are finite.

### Dependencies

**Theorems:**
- `BOUNDED_SUBSET_CLOSED_INTERVAL`
- `LEFT_IMP_EXISTS_THM`
- `FINITE_SUBSET`
- `FINITE_CART`
- `FINITE_INTSEG`

**Definitions:**
- `SUBSET`
- `IN_INTERVAL`
- `integral_vector`

### Porting notes (optional)
- The theorem `BOUNDED_SUBSET_CLOSED_INTERVAL` essentially encapsulates the Heine–Borel property. If porting to a system without a readily available form of Heine-Borel, it needs to be established separately somehow.
- The finiteness of integer segments (`FINITE_INTSEG`) and Cartesian products (`FINITE_CART`) are standard set theory results and should be straightforward to prove or find in libraries.
- The most challenging aspect may be automated manipulation of vector components (e.g., `x$i`). Ensure that the target proof assistant has adequate support for indexed data structures and quantification over indices. Some may require explicit casts between `real` and `integer` types.


---

## FINITE_TRIANGLE_INTEGER_POINTS

### Name of formal statement
FINITE_TRIANGLE_INTEGER_POINTS

### Type of the formal statement
theorem

### Formal Content
```hol
let FINITE_TRIANGLE_INTEGER_POINTS = prove
 (`!a b c:real^N. FINITE {x | x IN convex hull {a,b,c} /\ integral_vector x}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_BOUNDED_INTEGER_POINTS THEN
  SIMP_TAC[FINITE_IMP_BOUNDED_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY]);;
```

### Informal statement
For any vectors `a`, `b`, and `c` in real N-dimensional space, the set of all points `x` that lie within the convex hull of `a`, `b`, and `c`, and are also integral vectors, is finite.

### Mathematical insight
This theorem formalizes the intuitive idea that a triangle in N-dimensional space can only contain a finite number of integer points (points with integer coordinates). The convex hull of the vertices `a`, `b`, and `c` defines the triangle, and since the triangle is bounded, it intersects only finitely many points on the integer grid.

### Informal sketch
The proof proceeds as follows:
- By repeatedly applying `GEN_TAC`, we universally quantify over `a`, `b`, and `c`.
- We then apply `MATCH_MP_TAC` with the theorem `FINITE_BOUNDED_INTEGER_POINTS`. This theorem states that any bounded set in N-dimensional real space contains finitely many integer points. Therefore, it suffices to show that the set `{x | x IN convex hull {a,b,c} /\ integral_vector x}` is bounded.
- We use simplification with the theorems `FINITE_IMP_BOUNDED_CONVEX_HULL`, `FINITE_INSERT`, and `FINITE_EMPTY`. `FINITE_IMP_BOUNDED_CONVEX_HULL` states that if a finite set is bounded, its convex hull is also bounded.  `FINITE_INSERT` and `FINITE_EMPTY` are used to show that `{a,b,c}` is a finite set. Thus, the convex hull of `{a,b,c}` is bounded, and because `x` is in that convex hull as well as `integral_vector x`, the set  `{x | x IN convex hull {a,b,c} /\ integral_vector x}` is a subset of the set of integer vectors contained in a bounded region, which is finite.

### Dependencies
- `FINITE_BOUNDED_INTEGER_POINTS`
- `FINITE_IMP_BOUNDED_CONVEX_HULL`
- `FINITE_INSERT`
- `FINITE_EMPTY`


---

## LINEAR_INTEGRAL_VECTOR

### Name of formal statement
LINEAR_INTEGRAL_VECTOR

### Type of the formal statement
theorem

### Formal Content
```
let LINEAR_INTEGRAL_VECTOR = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x. integral_vector x ==> integral_vector(f x)) <=>
             (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N)
                    ==> integer(matrix f$i$j)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  ABBREV_TAC `M = matrix(f:real^N->real^N)` THEN
  SIMP_TAC[integral_vector; matrix_vector_mul; LAMBDA_BETA] THEN
  EQ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis j:real^N`) THEN
    REWRITE_TAC[GSYM integral_vector; INTEGRAL_VECTOR_STDBASIS] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; COND_RAND; COND_RATOR] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG; REAL_MUL_RID];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC INTEGER_SUM THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; IN_NUMSEG]]);;
```

### Informal statement
For any linear transformation `f` from `real^N` to `real^N`, the following holds: `f` maps integer vectors to integer vectors if and only if all the entries of the matrix representation of `f` are integers. More precisely, for all `f:real^N -> real^N`, if `f` is a linear transformation, then (for all `x`, if `x` is an integer vector, then `f x` is an integer vector) if and only if (for all `i` and `j` such that `1 <= i <= dimindex(:N)` and `1 <= j <= dimindex(:N)`, it holds that the `(i, j)`-th entry of the matrix representing `f` is an integer).

### Mathematical insight
This theorem connects the concept of linear transformations preserving integer vectors with the integer nature of the matrix representation of these transformations. It establishes that a linear map `f` sends integer vectors to integer vectors if and only if the matrix representing the linear map has integer entries. This provides a fundamental link between linear algebra and number theory in the context of `real^N`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is linear.
- Prove the equivalence in two directions:
    - Assume that `f` maps integer vectors to integer vectors. Show that the entries of the matrix representing `f` are integers:
        - Introduce indices `i` and `j`.
        - Specialize the antecedent to the basis vector `basis j`.  Since `basis j` is an integer vector, `f (basis j)` is an integer vector.
        - Express `f (basis j)` as a linear combination of the basis vectors using the matrix representation of `f`.
        - Extract the `i`-th component of `f (basis j)` using `BASIS_COMPONENT`, which gives the `(i, j)`-th entry of the matrix representing `f`.
        - Conclude that the `(i, j)`-th entry of the matrix is an integer.
    - Assume that all entries of the matrix representing `f` are integers. Show that `f` maps integer vectors to integer vectors:
        - Let `x` be an integer vector.
        - Introduce an index `i`.
        - Show that the `i`-th component of `f x` is an integer, and therefore `f x` is an integer vector.  The `i`-th component is a sum of products of matrix entries (integers) and vector components (integers). Apply `INTEGER_SUM` and `INTEGER_CLOSED` to conclude.

### Dependencies
- Definitions: `linear`, `integral_vector`
- Theorems: `MATRIX_WORKS`, `matrix_vector_mul`, `INTEGRAL_VECTOR_STDBASIS`, `BASIS_COMPONENT`, `SUM_DELTA`, `INTEGER_SUM`, `INTEGER_CLOSED`, `REAL_MUL_RZERO`, `IN_NUMSEG`, `REAL_MUL_RID`

### Porting notes (optional)
- The definitions like `linear`, `integral_vector`, and the properties of matrices and vector operations need to be available or defined.
- The theorem `MATRIX_WORKS` is crucial as it links linear transformations with their matrix representations.
- The standard basis vectors `basis` and their properties are also essential.
- In other systems, the handling of indexed sums like `SUM_DELTA` and the integer properties like `INTEGER_SUM` and `INTEGER_CLOSED` might require specific tactics or libraries.


---

## INTEGRAL_BASIS_UNIMODULAR

### Name of formal statement
INTEGRAL_BASIS_UNIMODULAR

### Type of the formal statement
theorem

### Formal Content
```hol
let INTEGRAL_BASIS_UNIMODULAR = prove
 (`!f:real^N->real^N.
        linear f /\ IMAGE f integral_vector = integral_vector
        ==> abs(det(matrix f)) = &1`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN REWRITE_TAC[IN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> integer(matrix(f:real^N->real^N)$i$j)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GSYM LINEAR_INTEGRAL_VECTOR]; ALL_TAC] THEN
  SUBGOAL_THEN
    `?g:real^N->real^N. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]; ALL_TAC] THEN
    SUBGOAL_THEN `!y. y:real^N IN span(IMAGE f (:real^N))` MP_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[SPAN_LINEAR_IMAGE; SPAN_UNIV] THEN SET_TAC[]] THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    ASM_MESON_TAC[INTEGRAL_VECTOR_STDBASIS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> integer(matrix(g:real^N->real^N)$i$j)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LINEAR_INTEGRAL_VECTOR] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(matrix(f:real^N->real^N)) * det(matrix(g:real^N->real^N)) =
    det(matrix(I:real^N->real^N))`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM DET_MUL; GSYM MATRIX_COMPOSE] THEN
    REPEAT AP_TERM_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `abs:real->real`) THEN
  REWRITE_TAC[MATRIX_I; DET_I; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[INTEGER_DET; INTEGER_ABS_MUL_EQ_1]);;
```

### Informal statement
For any linear transformation `f` from `real^N` to `real^N`, if the image of the set of integral vectors under `f` is equal to the set of integral vectors, then the absolute value of the determinant of the matrix representation of `f` is equal to 1.

### Mathematical insight
The theorem states that if a linear transformation `f` maps the set of integral vectors bijectively onto itself, then its determinant must be either 1 or -1. This means that `f` preserves the "volume" of integer lattices. This is a characterization of unimodular transformations when acting on integral vectors.

### Informal sketch
- Start with the assumption that `f` is a linear transformation and that `IMAGE f integral_vector = integral_vector`.
- Show that the matrix entries of `f` are integers. That is, prove `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) ==> integer(matrix(f:real^N->real^N)$i$j)`. This utilizes the premise `IMAGE f integral_vector = integral_vector` along with `LINEAR_INTEGRAL_VECTOR`.
- Show that `f` is bijective, i.e., there exists a linear map `g` that is the inverse of `f`, that is, `?g:real^N->real^N. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)`. This uses `LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE` given `f` is linear as an initial step. Also, use `LINEAR_SURJECTIVE_IMP_INJECTIVE`.
  - Show the range of f spans the whole space `real^N`. In other words, prove `!y. y:real^N IN span(IMAGE f (:real^N))`. This utilizes the fact that by the premise, the image of `f` includes all the standard basis vectors, and `span` of a set containing a basis is the whole space using `INTEGRAL_VECTOR_STDBASIS`.
- Show that the matrix entries of the inverse function `g` are integers. That is, prove `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) ==> integer(matrix(g:real^N->real^N)$i$j)`. This uses the surjectivity premise similarly to the proof for f. This also uses `LINEAR_INTEGRAL_VECTOR`.
- Prove that `det(matrix(f:real^N->real^N)) * det(matrix(g:real^N->real^N)) = det(matrix(I:real^N->real^N))`. Apply `DET_MUL` and `MATRIX_COMPOSE`.
- Apply the absolute value function to both sides and simplify. Then, using the fact that the determinant of the identity matrix is 1, and the determinants of the matrices of `f` and `g` are integers (since their matrix entries are integers), we conclude that `abs(det(matrix f))` must be equal to 1. Uses `INTEGER_DET` and `INTEGER_ABS_MUL_EQ_1`.

### Dependencies

#### Theorems
- `SUBSET_ANTISYM_EQ`
- `FUN_EQ_THM`
- `o_THM`
- `I_THM`
- `INTEGER_DET`
- `INTEGER_ABS_MUL_EQ_1`
- `LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE`
- `LINEAR_SURJECTIVE_IMP_INJECTIVE`

#### Definitions
- `SUBSET`
- `FORALL_IN_IMAGE`
- `IN_IMAGE`
- `IN`
- `LINEAR_INTEGRAL_VECTOR`
- `SPAN_LINEAR_IMAGE`
- `SPAN_UNIV`
- `BASIS_EXPANSION`
- `SPAN_VSUM`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `SPAN_MUL`
- `SPAN_SUPERSET`
- `INTEGRAL_VECTOR_STDBASIS`
- `DET_MUL`
- `MATRIX_COMPOSE`
- `MATRIX_I`
- `DET_I`
- `REAL_ABS_NUM`

### Porting notes
- The theorem relies heavily on properties of linear transformations and determinants in finite-dimensional real vector spaces. These properties are generally available in other proof assistants, but the names and exact formulations might differ.
- Mechanizing the notion of "integral vector" might require defining a suitable type class for the underlying numerical elements to represent integer properties, or defining ad-hoc predicates.
- The tactic `ASM_MESON_TAC` is used for automated reasoning. The porter might have to rely on different automated tactics or provide manual proofs depending on the capabilities of the target proof assistant.


---

## PICK_ELEMENTARY_TRIANGLE_0

### Name of formal statement
PICK_ELEMENTARY_TRIANGLE_0

### Type of the formal statement
theorem

### Formal Content
```hol
let PICK_ELEMENTARY_TRIANGLE_0 = prove
 (`!a b:real^2.
        {x | x IN convex hull {vec 0,a,b} /\ integral_vector x} = {vec 0,a,b}
        ==> measure(convex hull {vec 0,a,b}) =
               if collinear {vec 0,a,b} then &0 else &1 / &2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; COLLINEAR_IMP_NEGLIGIBLE;
               COLLINEAR_CONVEX_HULL_COLLINEAR] THEN
  POP_ASSUM MP_TAC THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC])
   [`a:real^2 = vec 0`; `b:real^2 = vec 0`; `a:real^2 = b`] THEN
  DISCH_TAC THEN SUBGOAL_THEN `independent {a:real^2,b}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{vec 0:real^2, a, b}` THEN
    REWRITE_TAC[independent; CONTRAPOS_THM] THEN
    REWRITE_TAC[dependent; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {c,b,a}`]; ALL_TAC] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `a IN s ==> s SUBSET t ==> a IN t`)) THEN
    MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `span{a,b} = (:real^2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `{a:real^2,b}`] CARD_EQ_DIM) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; SUBSET; EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HAS_SIZE; FINITE_INSERT; FINITE_EMPTY] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; DIM_UNIV; DIMINDEX_2; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_INSERT;
              FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^2. transp(vector[a;b]:real^2^2) ** x`
        INTEGRAL_BASIS_UNIMODULAR) THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[DET_2; MEASURE_TRIANGLE; VECTOR_2; DET_TRANSP; VEC_COMPONENT] THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN] THEN
    SIMP_TAC[LINEAR_INTEGRAL_VECTOR; MATRIX_VECTOR_MUL_LINEAR; LAMBDA_BETA;
             MATRIX_OF_MATRIX_VECTOR_MUL; transp; DIMINDEX_2; ARITH] THEN
    MAP_EVERY UNDISCH_TAC
     [`integral_vector(a:real^2)`; `integral_vector(b:real^2)`] THEN
    REWRITE_TAC[integral_vector; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IMP_IMP; FORALL_2; DIMINDEX_2; VECTOR_2] THEN
    REWRITE_TAC[CONJ_ACI];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN REWRITE_TAC[IN] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_VECTOR_2] THEN
  REWRITE_TAC[MATRIX_VECTOR_COLUMN; TRANSP_TRANSP] THEN
  REWRITE_TAC[DIMINDEX_2; VSUM_2; VECTOR_2; integral_vector; FORALL_2] THEN
  SUBGOAL_THEN `(x:real^2) IN span{a,b}` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[SPAN_2; IN_UNIV; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `frac u % a + frac v % b:real^2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(&1 - frac u) % a + (&1 - frac v) % b:real^2`) THEN
  MATCH_MP_TAC(TAUT
   `b' /\ (b' ==> b) /\ (a \/ a') /\ (c \/ c' ==> x)
    ==> (a /\ b ==> c) ==> (a' /\ b' ==> c') ==> x`) THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `integral_vector(floor u % a + floor v % b:real^2)`
    MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`integral_vector(a:real^2)`; `integral_vector(b:real^2)`] THEN
      SIMP_TAC[integral_vector; DIMINDEX_2; FORALL_2;
               VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[FLOOR; INTEGER_CLOSED];
      UNDISCH_TAC `integral_vector(x:real^2)` THEN REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_VECTOR_SUB) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH
       `(x % a + y % b) - (u % a + v % b) = (x - u) % a + (y - v) % b`] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_ARITH `u - x:real = y <=> u = x + y`] THEN
      REWRITE_TAC[GSYM FLOOR_FRAC]];
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + (&1 - v) % b = (a + b) - (u % a + v % b)`] THEN
    ASM_SIMP_TAC[INTEGRAL_VECTOR_ADD; INTEGRAL_VECTOR_SUB];
    REWRITE_TAC[CONVEX_HULL_3_0; IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `&0 <= frac u /\ &0 <= frac v /\ frac u + frac v <= &1 \/
      &0 <= &1 - frac u /\ &0 <= &1 - frac v /\
      (&1 - frac u) + (&1 - frac v) <= &1`
    MP_TAC THENL
     [MP_TAC(SPEC `u:real` FLOOR_FRAC) THEN
      MP_TAC(SPEC `v:real` FLOOR_FRAC) THEN REAL_ARITH_TAC;
      MESON_TAC[]];
    REWRITE_TAC
     [VECTOR_ARITH `x % a + y % b = a <=> (x - &1) % a + y % b = vec 0`;
      VECTOR_ARITH `x % a + y % b = b <=> x % a + (y - &1) % b = vec 0`] THEN
    ASM_SIMP_TAC[INDEPENDENT_2; GSYM REAL_FRAC_EQ_0] THEN
    MP_TAC(SPEC `u:real` FLOOR_FRAC) THEN
    MP_TAC(SPEC `v:real` FLOOR_FRAC) THEN REAL_ARITH_TAC]);;
```

### Informal statement
For any vectors `a` and `b` in `real^2`, if the set of integral vectors in the convex hull of `{vec 0, a, b}` is equal to `{vec 0, a, b}`, then the measure (area) of the convex hull of `{vec 0, a, b}` is 0 if `{vec 0, a, b}` are collinear, and 1/2 otherwise.

### Mathematical insight
This theorem establishes Pick's theorem for elementary triangles. Pick's theorem generally relates the area of a polygon whose vertices are integral coordinates, to the number of integral points that lie in the interior of the polygon and the number of integral points that lie on its boundary. In this specific case, the polygon considered is a triangle with vertices `vec 0`, `a`, and `b`, and the hypothesis guarantees that there are no integral points other than `vec 0`, `a` and `b` in the convex hull. Then conclusion is that the area of the triangle is 1/2 if its vertices are not collinear and 0 if they are.

### Informal sketch
The proof proceeds by case distinction and linear algebra.

- The cases where `a`, `b` or both equal `vec 0`, or `a`=`b` are handled first.
- We assume that `a` and `b` are independent, and `~collinear{vec 0:real^2, a, b}`. Then we show that the span of `{a,b}` is `real^2`.
- Then we utilize the theorem `INTEGRAL_BASIS_UNIMODULAR`: `integral_vector(transp(vector[a; b]:real^2^2) ** x)`
- Finally the two inclusions are proved to show the equality. `SUBSET_ANTISYM`
- The integral vector is dealt and the assumptions are simplified.
- With real and floor operations, the final assumptions are simplified using `REAL_ARITH_TAC` and `MESON_TAC`.

### Dependencies
#### Theorems
- `MEASURE_EQ_0`
- `COLLINEAR_IMP_NEGLIGIBLE`
- `COLLINEAR_CONVEX_HULL_COLLINEAR`
- `CONTRAPOS_THM`
- `SUBSET_ANTISYM`
- `INTEGRAL_BASIS_UNIMODULAR`

#### Definitions
- `collinear`
- `convex hull`
- `integral_vector`
- `measure`
- `independent`
- `dependent`
- `span`
- `VEC`
- `transp`
- `vector`

#### Other rules
- `INSERT_AC`
- `COLLINEAR_2`
- `independent`
- `dependent`
- `EXISTS_IN_INSERT`
- `NOT_IN_EMPTY`
- `COLLINEAR_3_AFFINE_HULL`
- `AFFINE_HULL_EQ_SPAN`
- `HULL_INC`
- `IN_INSERT`
- `HAS_SIZE`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `CARD_CLAUSES`
- `NOT_IN_EMPTY`
- `DIM_UNIV`
- `DIMINDEX_2`
- `ARITH`
- `SUBSET_ANTISYM_EQ`
- `SUBSET`
- `FORALL_IN_INSERT`
- `FORALL_IN_GSPEC`
- `IN_ELIM_THM`
- `NOT_IN_EMPTY`
- `IN_INSERT`
- `MATRIX_OF_MATRIX_VECTOR_MUL`
- `MATRIX_VECTOR_MUL_LINEAR`
- `DET_2`
- `MEASURE_TRIANGLE`
- `VECTOR_2`
- `DET_TRANSP`
- `VEC_COMPONENT`
- `SUBSET`
- `FORALL_IN_IMAGE`
- `LINEAR_INTEGRAL_VECTOR`
- `LAMBDA_BETA`
- `transp`
- `EXISTS_VECTOR_2`
- `MATRIX_VECTOR_COLUMN`
- `TRANSP_TRANSP`
- `VSUM_2`
- `SPAN_2`
- `IN_UNIV`
- `MONO_EXISTS`
- `TAUT`
- `integral_vector`
- `VECTOR_ADD_COMPONENT`
- `VECTOR_MUL_COMPONENT`
- `FLOOR`
- `INTEGER_CLOSED`
- `INTEGRAL_VECTOR_SUB`
- `VECTOR_ARITH`
- `FLOOR_FRAC`
- `CONVEX_HULL_3_0`
- `INDEPENDENT_2`
- `REAL_FRAC_EQ_0`

### Porting notes (optional)
- The proof uses HOL Light specific tactics such as `ASM_SIMP_TAC`, `ASM_CASES_TAC`, `MESON_TAC`. So some expertise will be required to port this proof into other proof assistants.
- The core mathematical ideas (case distinctions, linear algebra manipulations, properties of convex hulls, integral vectors) should be standard and portable.
- `INTEGRAL_BASIS_UNIMODULAR` might be tricky to port depending on the library support for unimodular transformations.


---

## PICK_ELEMENTARY_TRIANGLE

### Name of formal statement
PICK_ELEMENTARY_TRIANGLE

### Type of the formal statement
theorem

### Formal Content
```hol
let PICK_ELEMENTARY_TRIANGLE = prove
 (`!a b c:real^2.
        {x | x IN convex hull {a,b,c} /\ integral_vector x} = {a,b,c}
        ==> measure(convex hull {a,b,c}) =
               if collinear {a,b,c} then &0 else &1 / &2`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `s = t ==> (!x. x IN s <=> (!x. x IN t) /\ s = t`)) THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC `a:real^2`) THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
  GEOM_ORIGIN_TAC `a:real^2`THEN
  SIMP_TAC[INTEGRAL_VECTOR_ADD_LCANCEL; VECTOR_ADD_RID] THEN
  REWRITE_TAC[PICK_ELEMENTARY_TRIANGLE_0]);;
```

### Informal statement
For all points `a`, `b`, and `c` in the real plane, if the set of integral (integer-coordinate) vectors within the convex hull of `{a, b, c}` is exactly the set `{a, b, c}`, then the measure (area) of the convex hull of `{a, b, c}` is 0 if `a`, `b`, and `c` are collinear, and 1/2 if they are not.

### Mathematical insight
This theorem characterizes elementary integer triangles, that is, triangles in the real plane whose vertices have integer coordinates, and which contain no other integer points in their convex hull (boundary or interior). The theorem establishes that such a triangle has area 1/2. If the vertices are collinear, then the "triangle" has area 0. The condition `{x | x IN convex hull {a,b,c} /\ integral_vector x} = {a,b,c}` means that a, b, c are the only integer vertices in the triangle formed by a, b, c.

### Informal sketch
The proof proceeds as follows:

- Generalize over the variables `a`, `b`, and `c`.
- Discharge the assumption `{x | x IN convex hull {a,b,c} /\ integral_vector x} = {a,b,c}`.  Apply the rule `s = t ==> (!x. x IN s <=> x IN t) /\ s = t`.
- Rewrite using `IMP_CONJ` to separate the implication into two goals. The interesting goal has hypothesis `{x | x IN convex hull {a,b,c} /\ integral_vector x} = {a,b,c}`.
- Specialize `a` to `a:real^2`. Rewrite the in expressions using `IN_INSERT` and `IN_ELIM_THM`.
- Apply a geometric origin transformation using `GEOM_ORIGIN_TAC` centered at point `a`. This allows translation invariance to be employed by placing the variables with respect to the origin.
- Simplify using `INTEGRAL_VECTOR_ADD_LCANCEL` and `VECTOR_ADD_RID` regarding integral vectors and vector addition.
- Rewrite using the theorem `PICK_ELEMENTARY_TRIANGLE_0`.

### Dependencies
- `SET_RULE`
- `IMP_CONJ`
- `IN_INSERT`
- `IN_ELIM_THM`
- `INTEGRAL_VECTOR_ADD_LCANCEL`
- `VECTOR_ADD_RID`
- `PICK_ELEMENTARY_TRIANGLE_0`

### Porting notes
- The theorem relies on geometrical transformations (`GEOM_ORIGIN_TAC`). These transformations will need to be ported into other proof assistants using their respective geometric libraries or tactics.
- `PICK_ELEMENTARY_TRIANGLE_0` seems like a critical dependency. The translation will either require a proof of this theorem or the porting of this theorem.


---

## PICK_TRIANGLE_FLAT

### Name of formal statement
PICK_TRIANGLE_FLAT

### Type of the formal statement
theorem

### Formal Content
```hol
let PICK_TRIANGLE_FLAT = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c /\
        c IN segment[a,b]
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `convex hull {a:real^2,b,c} = segment[a,b]` SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC CONVEX_HULLS_EQ THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[ENDS_IN_SEGMENT; HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(segment[a:real^2,b]) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC MEASURE_EQ_0 THEN
    MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
    REWRITE_TAC[COLLINEAR_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `&0 = c - (a + b + c) / &2 + &1 / &2 <=> a + b = c + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  SUBGOAL_THEN
   `segment[a:real^2,b] = segment[b,c] UNION segment[a,c]`
  SUBST1_TAC THENL [ASM_MESON_TAC[SEGMENT_SYM; UNION_SEGMENT]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
    `{x | x IN (s UNION t) /\ P x} =
     {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
  SIMP_TAC[CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN
  MATCH_MP_TAC(ARITH_RULE
   `z:num <= x /\ z = 1 ==> x + y = (x + y) - z + 1`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN SET_TAC[];
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
                          {x | x IN (s INTER t) /\ P x}`] THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment[a,c] = {c}`
    SUBST1_TAC THENL [ASM_MESON_TAC[INTER_SEGMENT; SEGMENT_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `{x:real^2 | x IN {c} /\ integral_vector x} = {c}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; ARITH; NOT_IN_EMPTY]]);;
```

### Informal statement
For any points `a`, `b`, `c` in the real plane `real^2`, if `a`, `b`, and `c` have integer coordinates (i.e., `integral_vector a`, `integral_vector b`, and `integral_vector c`) and `c` lies on the line segment between `a` and `b` (i.e., `c IN segment[a,b]`), then the area (`measure`) of the convex hull of `{a,b,c}` is equal to the number of integer points in the convex hull of `{a,b,c}`, minus one-half times the sum of the number of integer points in the convex hulls of `{b,c}`, `{a,c}`, and `{a,b}`, plus one-half.

### Mathematical insight
This theorem states that Pick's theorem, which relates the area of a polygon to the number of integer points inside and on its boundary, holds in a degenerate case when the "triangle" defined by the points `a`, `b`, and `c` is flat (i.e., the points are collinear).  In this case, the area of the "triangle" is zero. The formula is a variant of Pick's theorem relating area, interior integer points, and boundary integer points.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and implication.
- Rewrite `segment[a,b]` as `convex hull {a,b}` using the GSYM version of `SEGMENT_CONVEX_HULL`.
- Show that `convex hull {a,b,c} = segment[a,b]` by demonstrating that the convex hull of three points, one of which lies on the segment joining the other two, is just the segment. This involves rewriting using `SEGMENT_CONVEX_HULL`, using `CONVEX_HULLS_EQ` and simplifications using `INSERT_SUBSET`, `EMPTY_SUBSET`, `ENDS_IN_SEGMENT`, `HULL_INC` and `IN_INSERT`.
- Show that the area of the segment is zero by using `MEASURE_EQ_0`, `COLLINEAR_IMP_NEGLIGIBLE`, and `COLLINEAR_SEGMENT`.
- Simplify the equation using real arithmetic (`REAL_ARITH`, `REAL_OF_NUM_ADD`, `REAL_OF_NUM_EQ`) to `a + b = c + &1`.
- Show that `segment[a,b] = segment[b,c] UNION segment[a,c]` using `SEGMENT_SYM` and `UNION_SEGMENT` with an `ASM_MESON_TAC`.
- Rewrite the set comprehension involving the union using `SET_RULE`.
- Simplify, using facts about the cardinality of a union of sets (`CARD_UNION_GEN`), the finiteness of integer points in a bounded region (`FINITE_BOUNDED_INTEGER_POINTS`) , and the fact that a segment is bounded (`BOUNDED_SEGMENT`).
- Simplify the cardinality expression and use the cardinality of a subset (`CARD_SUBSET`).
- Show that `segment[b,c] INTER segment[a,c] = {c}` using `INTER_SEGMENT` and `SEGMENT_SYM`.
- Show that `{x:real^2 | x IN {c} /\ integral_vector x} = {c}` using `ASM SET_TAC`.
- Simplify using `CARD_CLAUSES`, `FINITE_EMPTY`, `ARITH` and `NOT_IN_EMPTY`.

### Dependencies
- `SEGMENT_CONVEX_HULL`
- `CONVEX_HULLS_EQ`
- `INSERT_SUBSET`
- `EMPTY_SUBSET`
- `ENDS_IN_SEGMENT`
- `HULL_INC`
- `IN_INSERT`
- `MEASURE_EQ_0`
- `COLLINEAR_IMP_NEGLIGIBLE`
- `COLLINEAR_SEGMENT`
- `REAL_ARITH`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_EQ`
- `SEGMENT_SYM`
- `UNION_SEGMENT`
- `SET_RULE`
- `CARD_UNION_GEN`
- `FINITE_BOUNDED_INTEGER_POINTS`
- `BOUNDED_SEGMENT`
- `CARD_SUBSET`
- `INTER_SEGMENT`
- `CARD_CLAUSES`
- `FINITE_EMPTY`
- `ARITH`
- `NOT_IN_EMPTY`


---

## PICK_TRIANGLE_ALT

### Name of formal statement
PICK_TRIANGLE_ALT

### Type of the formal statement
theorem

### Formal Content
```hol
let PICK_TRIANGLE_ALT = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2`,
  let tac a bc =
    MATCH_MP_TAC CARD_PSUBSET THEN
    REWRITE_TAC[FINITE_TRIANGLE_INTEGER_POINTS] THEN
    REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}`) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; HULL_INC];
      DISCH_TAC] THEN
    SUBGOAL_THEN(subst[bc,`bc:real^2->bool`]
        `convex hull {a:real^2,b,c} = convex hull bc`)
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONVEX_HULLS_EQ THEN
      ASM_SIMP_TAC[HULL_INC; IN_INSERT; INSERT_SUBSET; EMPTY_SUBSET] THEN
      SUBGOAL_THEN(subst [a,`x:real^2`] `x IN convex hull {a:real^2,b,c}`)
      MP_TAC THENL
       [SIMP_TAC[HULL_INC; IN_INSERT]; ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{a:real^2,b,c}`; a]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] in
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `CARD {x:real^2 | x IN convex hull {a,b,c} /\
                                  integral_vector x}` THEN
  ASM_CASES_TAC `collinear{a:real^2,b,c}` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_BETWEEN_CASES]) THEN
    REWRITE_TAC[BETWEEN_IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `a:real^2`] PICK_TRIANGLE_FLAT);
      MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `b:real^2`] PICK_TRIANGLE_FLAT);
      MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`]
       PICK_TRIANGLE_FLAT)] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
     REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
     REWRITE_TAC[INSERT_AC; REAL_ADD_AC]);
    ALL_TAC] THEN
  UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
  MAP_EVERY
   (fun t -> ASM_CASES_TAC t THENL
     [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC])
   [`a:real^2 = b`; `a:real^2 = c`; `b:real^2 = c`] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `{x:real^2 | x IN convex hull {a, b, c} /\ integral_vector x} =
    {a,b,c}`
  THENL
   [ASM_SIMP_TAC[PICK_ELEMENTARY_TRIANGLE] THEN
    SUBGOAL_THEN
     `{x | x IN convex hull {b,c} /\ integral_vector x} = {b,c} /\
      {x | x IN convex hull {a,c} /\ integral_vector x} = {a,c} /\
      {x | x IN convex hull {a,b} /\ integral_vector x} = {a:real^2,b}`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [REPEAT CONJ_TAC THEN
      (FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `{x | x IN cs /\ P x} = s
         ==> t SUBSET s /\ t SUBSET ct /\ ct SUBSET cs /\
                (s DIFF t) INTER ct = {}
             ==> {x | x IN ct /\ P x} = t`)) THEN
       REPEAT CONJ_TAC THENL
        [SET_TAC[];
         MATCH_ACCEPT_TAC HULL_SUBSET;
         MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
         ASM_REWRITE_TAC[INSERT_DIFF; IN_INSERT; NOT_IN_EMPTY; EMPTY_DIFF] THEN
         MATCH_MP_TAC(SET_RULE `~(x IN s) ==> {x} INTER s = {}`) THEN
         REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; GSYM BETWEEN_IN_SEGMENT] THEN
         DISCH_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
         UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[INSERT_AC]]);
       SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
       ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV];
     ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real^2. d IN convex hull {a, b, c} /\ integral_vector d /\
               ~(d = a) /\ ~(d = b) /\ ~(d = c)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `~(s = t) ==> t SUBSET s ==> ?d. d IN s /\ ~(d IN t)`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_INSERT; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM; GSYM CONJ_ASSOC] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [COLLINEAR_3_EQ_AFFINE_DEPENDENT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`measure:(real^2->bool)->real`;
    `a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
   TRIANGLE_ADDITIVE_DECOMPOSITION) THEN
  SIMP_TAC[MEASURE_UNION; MEASURABLE_COMPACT] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MEASURE_CONVEX_HULL_2_TRIVIAL; REAL_ADD_RID; REAL_SUB_RZERO] THEN
  MP_TAC(ISPECL
   [`\s. &(CARD {x:real^2 | x IN s /\ integral_vector x})`;
    `a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
   TRIANGLE_ADDITIVE_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | x IN (s UNION t) /\ P x} =
                          {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`;
                SET_RULE `{x | x IN (s INTER t) /\ P x} =
                          {x | x IN s /\ P x} INTER {x | x IN t /\ P x}`] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `x:real = y + z - w <=> x + w = y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE
     `x:num = (y + z) - w /\ w <= z ==> x + w = y + z`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_UNION_GEN;
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[INTER_SUBSET]] THEN
    ASM_SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS; COMPACT_IMP_BOUNDED];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `d:real^2`] th) THEN
   MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `d:real^2`] th) THEN
   MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `d:real^2`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [tac `a:real^2` `{b:real^2,c,d}`; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [tac `b:real^2` `{a:real^2,c,d}`; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [tac `c:real^2` `{a:real^2,b,d}`; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `{x:real^2 | x IN convex hull {d} /\ integral_vector x} = {d}`
  SUBST1_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_SING] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
  REWRITE_TAC[INSERT_AC] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any three points `a`, `b`, and `c` in the real plane, if `a`, `b`, and `c` are integral vectors, then the measure of the convex hull of the set `{a, b, c}` is equal to: the number of integral vectors within the convex hull of `{a, b, c}`, minus one-half of the sum of the number of integral vectors within the convex hulls of `{b, c}`, `{a, c}`, and `{a, b}`, plus one-half.

### Mathematical insight
This is a version of Pick's Theorem for triangles specifically. Pick's Theorem generally relates the area of a polygon whose vertices are integral coordinates to the number of integral points inside the polygon and on its boundary. This version provides a formula relating the area of triangle formed by three integral points `a`, `b`, `c` in terms of the number of integral points in the triangle's interior and on its edges.

### Informal sketch
The proof proceeds by well-founded induction on the number of integral points in the convex hull of `{a, b, c}`. The proof proceeds by cases.

- **Base Case (Collinear Points):** If the points `a`, `b`, and `c` are collinear:
  - Use the fact that collinearity implies one point is between the other two (cases are handled by `COLLINEAR_BETWEEN_CASES`).
  - Apply `PICK_TRIANGLE_FLAT` three times, permuting `a`, `b`, `c` appropriately.
  - Simplify the resulting expression using set identities and arithmetic.
- **Inductive Step (Non-Collinear Points):** If the points are not collinear:
  - Exclude trivial cases where two or more points are equal (cases generated for `a = b`, `a = c`, `b = c`).
  - Consider the case when the convex hull contains only the vertices `{a, b, c}`:
     - Apply the theorem `PICK_ELEMENTARY_TRIANGLE`.
     - Show that the number of integral points on the edges is exactly two per edge (e.g., `{x | x IN convex hull {b,c} /\ integral_vector x} = {b,c}`) using set reasoning, hull inclusion, and the fact that the points are not collinear.
     - Use arithmetic.
  - Inductive case: assume there exists an additional integral point `d` inside the triangle different from `a`, `b`, and `c`.
     - Use `TRIANGLE_ADDITIVE_DECOMPOSITION` to decompose the triangle `abc` into triangles `abd`, `acd`, and `bcd`.
     - Relate the area and the number of integer points of the large triangle(`abc`) to the sum of the areas and number of the integer points of the three small triangles(`abd`, `acd`, `bcd`).
     - Apply the inductive hypothesis to each of the three smaller triangles.
     - Simplify to show that Pick's theorem holds for the original triangle `abc`.

### Dependencies

**Theorems:**
- `CARD_PSUBSET`
- `FINITE_TRIANGLE_INTEGER_POINTS`
- `PICK_TRIANGLE_FLAT`
- `COLLINEAR_BETWEEN_CASES`
- `EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT`
- `EXTREME_POINT_OF_CONVEX_HULL`
- `PICK_ELEMENTARY_TRIANGLE`
- `SEGMENT_CONVEX_HULL`
- `BETWEEN_IN_SEGMENT`
- `BETWEEN_IMP_COLLINEAR`
- `COLLINEAR_3_EQ_AFFINE_DEPENDENT`
- `TRIANGLE_ADDITIVE_DECOMPOSITION`
- `MEASURE_UNION`
- `MEASURABLE_COMPACT`
- `MEASURE_CONVEX_HULL_2_TRIVIAL`
- `FINITE_BOUNDED_INTEGER_POINTS`
- `COMPACT_IMP_BOUNDED`

**Definitions:**
- `integral_vector`
- `measure`
- `convex hull`
- `collinear`

**Rules:**
- `CARD_CLAUSES`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `FINITE_RULES`
- `NOT_IN_EMPTY`
- `INSERT_AC`
- `HULL_INC`
- `IN_INSERT`
- `INSERT_SUBSET`
- `EMPTY_SUBSET`
- `HULL_MINIMAL`
- `CONVEX_CONVEX_HULL`
- `PSUBSET`

**Tactics:**
- `WF_INDUCT_TAC`
- `ASM_CASES_TAC`
- `REAL_ARITH_TAC`
- `ASM_SIMP_TAC`

### Porting notes (optional)
- The proof relies heavily on tactics, especially `ASM_CASES_TAC` for case splitting. Other proof assistants may require more manual case splitting.
- The use of `REAL_ARITH_TAC` suggests that a powerful real number decision procedure is useful for this proof.
- The induction is on the cardinality of integer points within the convex hull. Ensure that the target proof assistant has support for reasoning about cardinalities and convex hulls.


---

## PICK_TRIANGLE

### Name of formal statement
PICK_TRIANGLE

### Type of the formal statement
theorem

### Formal Content
```hol
let PICK_TRIANGLE = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
                if collinear {a,b,c} then &0
                else &(CARD {x | x IN interior(convex hull {a,b,c}) /\
                                 integral_vector x}) +
                     &(CARD {x | x IN frontier(convex hull {a,b,c}) /\
                                 integral_vector x}) / &2 - &1`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; COLLINEAR_IMP_NEGLIGIBLE;
               COLLINEAR_CONVEX_HULL_COLLINEAR] THEN
  ASM_SIMP_TAC[PICK_TRIANGLE_ALT] THEN
  REWRITE_TAC[INTERIOR_OF_TRIANGLE; FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN (s DIFF t) /\ P x} =
    {x | x IN s /\ P x} DIFF {x | x IN t /\ P x}`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i + c = s /\ ccc = c + &3
    ==> s - ccc / &2 + &1 / &2 = i + c / &2 - &1`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE `y:num <= x /\ x - y = z ==> z + y = x`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET; MATCH_MP_TAC(GSYM CARD_DIFF)] THEN
    ASM_SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS;
      FINITE_IMP_BOUNDED_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}`) THEN
    REWRITE_TAC[UNION_SUBSET; SEGMENT_CONVEX_HULL] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    REWRITE_TAC[SET_RULE
     `{x | x IN (s UNION t) /\ P x} =
      {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
    SIMP_TAC[CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS;
      FINITE_INTER; FINITE_UNION; BOUNDED_SEGMENT; UNION_OVER_INTER] THEN
    REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
      {x | x IN (s INTER t) /\ P x}`] THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment [c,a] = {c} /\
      segment[a,b] INTER segment [b,c] = {b} /\
      segment[a,b] INTER segment [c,a] = {a}`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[INTER_SEGMENT; SEGMENT_SYM; INSERT_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[SET_RULE `P a ==> {x | x IN {a} /\ P x} = {a}`] THEN
    ASM_CASES_TAC `b:real^2 = a` THENL
     [ASM_MESON_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[SET_RULE `~(a = b) ==> {b} INTER {a} = {}`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; SUB_0] THEN
    MATCH_MP_TAC(ARITH_RULE
     `c:num <= ca /\ a <= ab /\ b <= bc /\
      bc' + ac' + ab' + a + b + c = ab + bc + ca + 3
      ==> bc' + ac' + ab' = (ab + (bc + ca) - c) - (b + a) + 3`) THEN
    ASM_SIMP_TAC[CARD_SUBSET; SING_SUBSET; IN_ELIM_THM; ENDS_IN_SEGMENT;
                 FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN
    SIMP_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; FINITE_INSERT;
             FINITE_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; INSERT_AC] THEN ARITH_TAC]);;
```

### Informal statement
For any three points `a`, `b`, and `c` in the real plane `real^2` such that `a`, `b`, and `c` are integral vectors, the measure (area) of the convex hull of the set `{a, b, c}` is equal to: if `a`, `b`, and `c` are collinear, then 0; otherwise, the number of integral vectors in the interior of the convex hull of `{a, b, c}` plus one-half of the number of integral vectors on the frontier (boundary) of the convex hull of `{a, b, c}`, minus 1.

### Mathematical insight
This theorem is a specific instantiation of Pick's theorem, which relates the area of a simple polygon with integer vertex coordinates to the number of integer points in its interior and on its boundary. This version applies to triangles. The area is expressed in terms of the number of integer points inside and on the boundary of the triangle.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumptions using `REPEAT STRIP_TAC`.
- Perform case splitting based on whether points are collinear (`COND_CASES_TAC`).
- If collinear, simplify using `MEASURE_EQ_0`, `COLLINEAR_IMP_NEGLIGIBLE`, and `COLLINEAR_CONVEX_HULL_COLLINEAR` which states that area should be zero.
- If not collinear, apply an alternate form of Pick's theorem using `PICK_TRIANGLE_ALT`.
- Rewrite `interior` and `frontier` of the triangle using `INTERIOR_OF_TRIANGLE` and `FRONTIER_OF_TRIANGLE` respectively.
- Rewrite set difference using the set rule `{x | x IN (s DIFF t) /\ P x} = {x | x IN s /\ P x} DIFF {x | x IN t /\ P x}`.
- Apply real arithmetic reasoning with `REAL_ARITH` to transform the equation. The goal is to transform the expressions into the form of Pick's theorem.
- Split the goal using `CONJ_TAC`.
- Perform arithmetic rewriting using `REAL_OF_NUM_ADD` and `REAL_OF_NUM_EQ`.
- Apply an arithmetic rule using `ARITH_RULE`.
- Split the goal again using `CONJ_TAC`.
- Apply cardinality rules using `CARD_SUBSET` and `CARD_DIFF`.
- Simplify using `FINITE_BOUNDED_INTEGER_POINTS`, `FINITE_IMP_BOUNDED_CONVEX_HULL`, `FINITE_INSERT` and `FINITE_EMPTY` to establish finiteness.
- Apply a set rule using `s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}`.
- Rewrite using `UNION_SUBSET` and `SEGMENT_CONVEX_HULL`.
- Repeatedly apply `CONJ_TAC`, apply `HULL_MONO`, and use `SET_TAC`.
- Rewrite set comprehension over a union using the rule `{x | x IN (s UNION t) /\ P x} = {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`.
- Simplify using `CARD_UNION_GEN`, `FINITE_BOUNDED_INTEGER_POINTS`, `FINITE_INTER`, `FINITE_UNION`, `BOUNDED_SEGMENT`, and `UNION_OVER_INTER`.
- Rewrite set comprehension over intersection using the rule `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} = {x | x IN (s INTER t) /\ P x}`.
- Set up a subgoal: `segment[b:real^2,c] INTER segment [c,a] = {c} /\ segment[a,b] INTER segment [b,c] = {b} /\ segment[a,b] INTER segment [c,a] = {a}`.
  - Repeatedly apply `CONJUNCTS_THEN` and `SUBST1_TAC` to prove each conjunct of the subgoal.
  - Solve the subgoal with `INTER_SEGMENT`, `SEGMENT_SYM`, and `INSERT_AC` using `ASM_MESON_TAC`.
- Simplify using `SET_RULE` P a ==> `{x | x IN {a} /\ P x} = {a}`.
- Case split on `b = a` using `ASM_CASES_TAC`.
  - If `b = a`, use `COLLINEAR_2` and `INSERT_AC` to derive collinearity and conclude the proof.
- Simplify using `~(a = b) ==> {b} INTER {a} = {}`.
- Rewrite using `REAL_OF_NUM_ADD` and `REAL_OF_NUM_EQ`.
- Rewrite using `NOT_IN_EMPTY`, `EMPTY_GSPEC`, `CARD_CLAUSES`, and `SUB_0`.
- Apply an arithmetic rule and use `ASM_SIMP_TAC` with simplification theorems related to sets, cardinality, vectors like `CARD_SUBSET`, `SING_SUBSET`, `IN_ELIM_THM`, `ENDS_IN_SEGMENT`, `FINITE_BOUNDED_INTEGER_POINTS`, `BOUNDED_SEGMENT`.
- Simplify with `SIMP_TAC` and theorems like `NOT_IN_EMPTY`, `EMPTY_GSPEC`, `CARD_CLAUSES`, `FINITE_INSERT`, `FINITE_EMPTY`.
- Convert the expression to numeric form using `CONV_TAC NUM_REDUCE_CONV`.
- Rewrite using a set rule `{x | x IN s /\ P x} = s INTER P`.
- Rewrite using `SEGMENT_CONVEX_HULL` and `INSERT_AC`.
- Solve the remaining goal using `ARITH_TAC`.

### Dependencies

**Theorems**:
- `MEASURE_EQ_0`
- `COLLINEAR_IMP_NEGLIGIBLE`
- `COLLINEAR_CONVEX_HULL_COLLINEAR`
- `PICK_TRIANGLE_ALT`
- `INTERIOR_OF_TRIANGLE`
- `FRONTIER_OF_TRIANGLE`
- `CARD_SUBSET`
- `CARD_DIFF`
- `FINITE_BOUNDED_INTEGER_POINTS`
- `FINITE_IMP_BOUNDED_CONVEX_HULL`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `UNION_SUBSET`
- `SEGMENT_CONVEX_HULL`
- `HULL_MONO`
- `CARD_UNION_GEN`
- `FINITE_INTER`
- `FINITE_UNION`
- `BOUNDED_SEGMENT`
- `UNION_OVER_INTER`
- `INTER_SEGMENT`
- `SEGMENT_SYM`
- `INSERT_AC`
- `COLLINEAR_2`
- `NOT_IN_EMPTY`
- `EMPTY_GSPEC`
- `CARD_CLAUSES`
- `SUB_0`
- `IN_ELIM_THM`
- `ENDS_IN_SEGMENT`

**Rules**:
- `SET_RULE`
- `REAL_ARITH`
- `ARITH_RULE`


---

## PARITY_LEMMA

### Name of formal statement
PARITY_LEMMA

### Type of the formal statement
theorem

### Formal Content
```hol
let PARITY_LEMMA = prove
 (`!a b c d p x:real^2.
        simple_path(p ++ linepath(a,b)) /\
        pathstart p = b /\ pathfinish p = a /\
        segment(a,b) INTER segment(c,d) = {x} /\
        segment[c,d] INTER path_image p = {}
        ==> (c IN inside(path_image(p ++ linepath(a,b))) <=>
             d IN outside(path_image(p ++ linepath(a,b))))`,
  let lemma = prove
   (`!a b x y:real^N.
          collinear{y,a,b} /\ between x (a,b) /\
          dist(y,x) < dist(x,b) /\ dist(y,x) < dist(x,a)
          ==> y IN segment(a,b)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COLLINEAR_DIST_IN_OPEN_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[between; DIST_SYM] THEN
    NORM_ARITH_TAC)
  and symlemma = prove
   (`(!n. P(--n) <=> P (n)) /\ (!n. &0 < n dot x ==> P n)
     ==> !n:real^N. ~(n dot x = &0) ==> P n`,
    STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `~(x = &0) <=> &0 < x \/ &0 < --x`] THEN
    REWRITE_TAC[GSYM DOT_LNEG] THEN ASM_MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^1->real^2`; `linepath(a:real^2,b)`]
        SIMPLE_PATH_JOIN_LOOP_EQ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(a:real^2) INSERT b INSERT c INSERT d INSERT path_image p`;
                 `x:real^2`]
        DISTANCE_ATTAINS_INF) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT b INSERT c INSERT d INSERT s =
                             {a,b,c,d} UNION s`] THEN
  ASM_SIMP_TAC[CLOSED_UNION; FINITE_IMP_CLOSED; CLOSED_PATH_IMAGE;
               FINITE_INSERT; FINITE_EMPTY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cp:real^2` MP_TAC) THEN
  DISJ_CASES_TAC(NORM_ARITH `cp = x \/ &0 < dist(x:real^2,cp)`) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(TAUT `~a ==> a /\ b ==> c`) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE `a = {x} ==> x IN a`)) THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
                IN_INTER; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `p INTER s SUBSET u ==> x IN (s DIFF u) ==> ~(x IN p)`)) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; PATH_IMAGE_LINEPATH];
    ALL_TAC] THEN
  ABBREV_TAC `e = dist(x:real^2,cp)` THEN FIRST_X_ASSUM(K ALL_TAC o SYM) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARC_LINEPATH_EQ]) THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
        FINITE_INTER_COLLINEAR_OPEN_SEGMENTS) THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `d:real^2`; `c:real^2`]
        FINITE_INTER_COLLINEAR_OPEN_SEGMENTS) THEN
  SUBST1_TAC(MESON[SEGMENT_SYM] `segment(d:real^2,c) = segment(c,d)`) THEN
  ASM_REWRITE_TAC[FINITE_SING; NOT_INSERT_EMPTY] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(a IN segment[c:real^2,d]) /\ ~(b IN segment[c,d])`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE;
                  IN_INTER; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^2 = a) /\ ~(c = b) /\ ~(d = a) /\ ~(d = b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `x IN segment(a:real^2,b) /\ x IN segment(c,d)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_OPEN_SEGMENT_ALT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{c,d} INTER path_image(p ++ linepath(a:real^2,b)) = {}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_LINEPATH; PATHSTART_LINEPATH] THEN
    REWRITE_TAC[SET_RULE
     `{c,d} INTER (s UNION t) = {} <=>
      (~(c IN s) /\ ~(d IN s)) /\ ~(c IN t) /\ ~(d IN t)`] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ENDS_IN_SEGMENT; IN_INTER; NOT_IN_EMPTY];
      REWRITE_TAC[PATH_IMAGE_LINEPATH; GSYM BETWEEN_IN_SEGMENT] THEN
      CONJ_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `b - x:real^2` ORTHOGONAL_TO_VECTOR_EXISTS) THEN
  REWRITE_TAC[DIMINDEX_2; LE_REFL; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN segment(a,b) /\ x IN segment(c,d)` MP_TAC THENL
   [ASM SET_TAC[];
    SIMP_TAC[IN_OPEN_SEGMENT_ALT; GSYM BETWEEN_IN_SEGMENT] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^2, b, c, d}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COLLINEAR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n dot (d - x:real^2) = &0)` MP_TAC THENL
   [REWRITE_TAC[GSYM orthogonal] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:real^2`; `d - x:real^2`; `b - x:real^2`]
      ORTHOGONAL_TO_ORTHOGONAL_2D) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_SYM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM COLLINEAR_3] THEN DISCH_TAC THEN
    UNDISCH_TAC `~collinear{a:real^2, b, c, d}` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b,c,d} = {b,d,a,c}`] THEN
    ASM_SIMP_TAC[COLLINEAR_4_3] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `{b:real^2,x,a,d}` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[COLLINEAR_4_3]; SET_TAC[]] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {c,b,a}`] THEN
      ASM_SIMP_TAC[BETWEEN_IMP_COLLINEAR];
      MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `{d:real^2,x,b,c}` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[COLLINEAR_4_3]; SET_TAC[]] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {c,b,a}`] THEN
      ASM_SIMP_TAC[BETWEEN_IMP_COLLINEAR]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
                       MP_TAC th) THEN
  SPEC_TAC(`n:real^2`,`n:real^2`) THEN
  MATCH_MP_TAC symlemma THEN CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_RNEG; VECTOR_NEG_EQ_0]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n dot (c - x:real^2) < &0` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < n dot (d - x:real^2)` THEN
    SUBGOAL_THEN `(x:real^2) IN segment(c,d)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
      `d - ((&1 - u) % c + u % d):real^N = (&1 - u) % (d - c) /\
       c - ((&1 - u) % c + u % d) = --u % (d - c)`] THEN
    REWRITE_TAC[DOT_RMUL; REAL_MUL_LNEG; REAL_ARITH `--x < &0 <=> &0 < x`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_SUB_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(x:real^2,e)
        ==> y IN segment(a,b) \/
            &0 < n dot (y - x) \/
            n dot (y - x) < &0`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~c /\ ~b ==> a) ==> a \/ b \/ c`) THEN
    REWRITE_TAC[REAL_ARITH `~(x < &0) /\ ~(&0 < x) <=> x = &0`] THEN
    REWRITE_TAC[GSYM orthogonal] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:real^2`; `y - x:real^2`; `b - x:real^2`]
      ORTHOGONAL_TO_ORTHOGONAL_2D) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_SYM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM COLLINEAR_3] THEN DISCH_TAC THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[REAL_LTE_TRANS; DIST_SYM]] THEN
    ONCE_REWRITE_TAC[SET_RULE `{y,a,b} = {a,b,y}`] THEN
    MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `collinear{y:real^2, x, b}` THEN
    MP_TAC(MATCH_MP BETWEEN_IMP_COLLINEAR (ASSUME
     `between (x:real^2) (a,b)`)) THEN
    SIMP_TAC[INSERT_AC];
    ALL_TAC] THEN
  MP_TAC(SPEC `p ++ linepath(a:real^2,b)` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(connected_component((:real^2) DIFF path_image(p ++ linepath (a,b))) c d)`
  MP_TAC THENL
   [DISCH_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `path_image(p ++ linepath(a:real^2,b))` o
      MATCH_MP (SET_RULE
     `~(x IN s <=> y IN t)
      ==> !p. s UNION t = (:real^2) DIFF p /\ {x,y} INTER p = {}
              ==> x IN s /\ y IN s \/ x IN t /\ y IN t`)) THEN
    ASM_REWRITE_TAC[connected_component] THEN
    ASM_REWRITE_TAC[SET_RULE `t SUBSET UNIV DIFF s <=> t INTER s = {}`] THEN
    ASM_MESON_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP]] THEN
  MP_TAC(SPEC `p ++ linepath(a:real^2,b)` JORDAN_DISCONNECTED) THEN
  ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  SUBGOAL_THEN
   `!u v. u IN inside(path_image(p ++ linepath(a,b))) /\
          v IN outside(path_image(p ++ linepath(a,b)))
          ==> connected_component
              ((:real^2) DIFF path_image (p ++ linepath (a,b))) u v`
  ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SYM(ASSUME `inside (path_image (p ++ linepath (a,b))) UNION
                  outside (path_image (p ++ linepath (a,b))) =
                  (:real^2) DIFF path_image (p ++ linepath (a,b))`)] THEN
    REWRITE_TAC[IN_UNION; CONNECTED_IFF_CONNECTED_COMPONENT] THEN
    STRIP_TAC THENL
     [REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `inside(path_image(p ++ linepath(a:real^2,b)))`;
      ASM_MESON_TAC[];
      ASM_MESON_TAC[CONNECTED_COMPONENT_SYM];
      REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `outside(path_image(p ++ linepath(a:real^2,b)))`] THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[OUTSIDE_NO_OVERLAP; INSIDE_NO_OVERLAP]] THEN
  SUBGOAL_THEN `(x:real^2) IN path_image(p ++ linepath(a,b))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
    REWRITE_TAC[IN_UNION; PATH_IMAGE_LINEPATH] THEN DISJ2_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[open_segment]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `frontier(inside(path_image(p ++ linepath(a:real^2,b)))) =
    path_image(p ++ linepath(a,b))` THEN
  REWRITE_TAC[EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[frontier] THEN
  REWRITE_TAC[IN_DIFF; CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `w:real^2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `inside(path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    ALL_TAC] THEN
  UNDISCH_TAC
   `frontier(outside(path_image(p ++ linepath(a:real^2,b)))) =
    path_image(p ++ linepath(a,b))` THEN
  REWRITE_TAC[EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[frontier] THEN
  REWRITE_TAC[IN_DIFF; CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `z:real^2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `outside(path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[OUTSIDE_NO_OVERLAP]] THEN
  SUBGOAL_THEN
   `!y. dist(y,x) < e /\ ~(y IN path_image(p ++ linepath (a,b)))
        ==> connected_component
             ((:real^2) DIFF path_image(p ++ linepath(a,b))) c y`
  ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `c:real^2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC CONNECTED_COMPONENT_SYM; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP; IN_INTER;
                  NOT_IN_EMPTY]] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[c,d] INTER path_image(p ++ linepath(a,b)) = {x:real^2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `{c,d} INTER p = {} /\ (segment[c,d] DIFF {c,d}) INTER p = {x}
      ==> segment[c,d] INTER p = {x}`) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATH_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `cd INTER p = {} /\ l INTER (cd DIFF {c,d}) = {x}
      ==> (cd DIFF {c,d}) INTER (p UNION l) = {x}`) THEN
    ASM_REWRITE_TAC[GSYM open_segment; PATH_IMAGE_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `~(a IN segment[c,d]) /\ ~(b IN segment[c,d]) /\
      segment(a,b) INTER segment(c,d) = {x} /\
      segment(a,b) = segment[a,b] DIFF {a,b} /\
      segment(c,d) = segment[c,d] DIFF {c,d}
      ==> segment[a,b] INTER segment(c,d) = {x}`) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[open_segment];
    ALL_TAC] THEN
  UNDISCH_THEN
    `!y. y IN ball(x:real^2,e)
          ==> y IN segment(a,b) \/ &0 < n dot (y - x) \/ n dot (y - x) < &0`
    (MP_TAC o SPEC `y:real^2`) THEN
  REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    UNDISCH_TAC `~(y IN path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
    SIMP_TAC[CONTRAPOS_THM; open_segment; IN_DIFF; IN_UNION;
             PATH_IMAGE_LINEPATH];
    DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `x + min (&1 / &2) (e / &2 / norm(d - x)) % (d - x):real^2` THEN
    REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
     [EXISTS_TAC `segment[x:real^2,d] DELETE x` THEN
      SIMP_TAC[CONVEX_SEMIOPEN_SEGMENT; CONVEX_CONNECTED] THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `cd INTER p = {x}
          ==> xd SUBSET cd
              ==> (xd DELETE x) SUBSET (UNIV DIFF p)`)) THEN
        REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
        UNDISCH_TAC `segment (a,b) INTER segment (c,d) = {x:real^2}` THEN
        REWRITE_TAC[open_segment] THEN SET_TAC[];
        REWRITE_TAC[IN_SEGMENT; VECTOR_ARITH
         `x + a % (y - x):real^N = (&1 - a) % x + a % y`] THEN
        EXISTS_TAC `min (&1 / &2) (e / &2 / norm(d - x:real^2))` THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        REWRITE_TAC[REAL_LE_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; NORM_POS_LE; REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ;
                        VECTOR_ARITH `x + a:real^N = x <=> a = vec 0`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min (&1 / &2) x = &0)`) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]];
      EXISTS_TAC `ball(x,e) INTER {w:real^2 | &0 < n dot (w - x)}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_BALL; DOT_RSUB; REAL_SUB_LT] THEN
        REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_GT];
        ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
        MATCH_MP_TAC(SET_RULE
         `p SUBSET (UNIV DIFF b) /\ l INTER w = {}
          ==> (b INTER w) SUBSET (UNIV DIFF (p UNION l))`) THEN
        ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL; REAL_NOT_LT] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. t INTER u = {} /\ s SUBSET t ==> s INTER u = {}`) THEN
        EXISTS_TAC `affine hull {x:real^2,b}` THEN CONJ_TAC THENL
         [REWRITE_TAC[AFFINE_HULL_2; FORALL_IN_GSPEC; SET_RULE
           `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          SIMP_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
          REWRITE_TAC[DOT_RMUL; VECTOR_ARITH
           `((&1 - v) % x + v % b) - x:real^N = v % (b - x)`] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[orthogonal]) THEN
          ONCE_REWRITE_TAC[DOT_SYM] THEN
          ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
          REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
          SIMP_TAC[SUBSET_HULL; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          SIMP_TAC[HULL_INC; IN_INSERT] THEN
          ASM_SIMP_TAC[GSYM COLLINEAR_3_AFFINE_HULL] THEN
          ONCE_REWRITE_TAC[SET_RULE `{x,b,a} = {a,x,b}`] THEN
          MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM; dist] THEN
        REWRITE_TAC[NORM_ARITH `norm(x - (x + a):real^N) = norm a`] THEN
        REWRITE_TAC[VECTOR_ARITH `(x + a) - x:real^N = a`] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT;
                       VECTOR_SUB_EQ] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ x < e ==> abs(min (&1 / &2) x) < e`) THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[DOT_RMUL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_REWRITE_TAC[REAL_LT_MIN] THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_01]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]];
    DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `x + min (&1 / &2) (e / &2 / norm(c - x)) % (c - x):real^2` THEN
    REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
     [EXISTS_TAC `segment[x:real^2,c] DELETE x` THEN
      SIMP_TAC[CONVEX_SEMIOPEN_SEGMENT; CONVEX_CONNECTED] THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `cd INTER p = {x}
          ==> xd SUBSET cd
              ==> (xd DELETE x) SUBSET (UNIV DIFF p)`)) THEN
        REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
        UNDISCH_TAC `segment (a,b) INTER segment (c,d) = {x:real^2}` THEN
        REWRITE_TAC[open_segment] THEN SET_TAC[];
        REWRITE_TAC[IN_SEGMENT; VECTOR_ARITH
         `x + a % (y - x):real^N = (&1 - a) % x + a % y`] THEN
        EXISTS_TAC `min (&1 / &2) (e / &2 / norm(c - x:real^2))` THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        REWRITE_TAC[REAL_LE_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; NORM_POS_LE; REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ;
                        VECTOR_ARITH `x + a:real^N = x <=> a = vec 0`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min (&1 / &2) x = &0)`) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]];
      EXISTS_TAC `ball(x,e) INTER {w:real^2 | n dot (w - x) < &0}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_BALL; DOT_RSUB; REAL_ARITH `a - b < &0 <=> a < b`;
                    CONVEX_HALFSPACE_LT];
        ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
        MATCH_MP_TAC(SET_RULE
         `p SUBSET (UNIV DIFF b) /\ l INTER w = {}
          ==> (b INTER w) SUBSET (UNIV DIFF (p UNION l))`) THEN
        ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL; REAL_NOT_LT] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. t INTER u = {} /\ s SUBSET t ==> s INTER u = {}`) THEN
        EXISTS_TAC `affine hull {x:real^2,b}` THEN CONJ_TAC THENL
         [REWRITE_TAC[AFFINE_HULL_2; FORALL_IN_GSPEC; SET_RULE
           `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          SIMP_TAC[REAL_ARITH `

---

## polygonal_path

### Name of formal statement
polygonal_path

### Type of the formal statement
new_definition

### Formal Content
```
let polygonal_path = define
 `polygonal_path[] = linepath(vec 0,vec 0) /\
  polygonal_path[a] = linepath(a,a) /\
  polygonal_path [a;b] = linepath(a,b) /\
  polygonal_path (CONS a (CONS b (CONS c l))) =
       linepath(a,b) ++ polygonal_path(CONS b (CONS c l))`;;
```

### Informal statement
The polygonal path of a list of vectors is defined recursively as follows:
- The polygonal path of the empty list `[]` is the line path from the zero vector `vec 0` to the zero vector `vec 0`.
- The polygonal path of a singleton vector list `[a]` is the line path from vector `a` to itself.
- The polygonal path of a list of two vectors `[a; b]` is the line path from vector `a` to vector `b`.
- The polygonal path of a list with at least three elements `CONS a (CONS b (CONS c l))` is the concatenation of the line path from `a` to `b` with the polygonal path of the list `CONS b (CONS c l)`.

### Mathematical insight
The definition specifies how to construct a path from a list of points/vectors. The path is constructed by connecting consecutive points in the list with line segments. The initial cases handle the empty list, a single-element list, and a two-element list, defining the base cases for the recursion. The recursive case decomposes the list into its first two elements and the remaining list, constructs a line segment from the first to the second element, and concatenates it with the polygonal path of the remaining list.

### Informal sketch
The definition is given by primitive recursion over lists.
- Base case 1: `polygonal_path[] = linepath(vec 0,vec 0)` defines the path for an empty list as a path from the origin to itself.
- Base case 2: `polygonal_path[a] = linepath(a,a)` defines the path a singleton lists as the path from the single point to itself.
- Base case 3: `polygonal_path [a;b] = linepath(a,b)` defines the path a list with two elements.
- Recursive step: `polygonal_path (CONS a (CONS b (CONS c l))) = linepath(a,b) ++ polygonal_path(CONS b (CONS c l))` decomposes the list and constructs the final path by combining the `linepath` from `a` to `b` with the `polygonal_path` on the tail of the list.

### Dependencies
- `linepath`
- `vec`
- `++`
- `CONS`

### Porting notes (optional)
The concatenation operator `++` on paths needs to be defined and available. The definition of `linepath` is assumed to be previously defined. The handling of lists (empty list, singleton list, two-element list, and cons operation) will need to be adapted to the list structure of the target proof assistant.


---

## POLYGONAL_PATH_CONS_CONS

### Name of formal statement
POLYGONAL_PATH_CONS_CONS

### Type of the formal statement
theorem

### Formal Content
```hol
let POLYGONAL_PATH_CONS_CONS = prove
 (`!a b p. ~(p = [])
           ==> polygonal_path(CONS a (CONS b p)) =
               linepath(a,b) ++ polygonal_path(CONS b p)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[polygonal_path]);;
```

### Informal statement
For all points `a` and `b`, and for all non-empty lists of points `p`, the polygonal path of the list `a :: b :: p` is equal to the line segment from `a` to `b` concatenated with the polygonal path of the list `b :: p`.

### Mathematical insight
This theorem provides a reduction rule for computing the polygonal path of a list of points. It states that we can decompose a polygonal path into its first line segment and the remaining polygonal path. This is a key property for reasoning about polygonal paths inductively or recursively.

### Informal sketch
The proof proceeds by induction on the list `p`.

- Base case: `p = []`. The goal becomes `polygonal_path(CONS a (CONS b [])) = linepath(a,b) ++ polygonal_path(CONS b [])`. This follows directly from the definition of `polygonal_path`.
- Inductive step: Assume `polygonal_path(CONS a (CONS b p)) = linepath(a,b) ++ polygonal_path(CONS b p)`.
  We want to prove `polygonal_path(CONS a (CONS b (CONS h p))) = linepath(a,b) ++ polygonal_path(CONS b (CONS h p))`. Applying the definition of `polygonal_path`, the left-hand side becomes `linepath(a,b) ++ polygonal_path(CONS b (CONS h p))`. The right-hand side is already `linepath(a,b) ++ polygonal_path(CONS b (CONS h p))`. Thus, the two sides are equal.

The proof uses `LIST_INDUCT_TAC` to perform the induction on the list `p`. The `REWRITE_TAC[polygonal_path]` step applies the definition of `polygonal_path`.

### Dependencies
- `polygonal_path`
- `linepath`

### Porting notes (optional)
The inductive proof using `LIST_INDUCT_TAC` should be straightforward to translate into other proof assistants. The key is to ensure that the definition of `polygonal_path` is defined appropriately for list processing. Depending on how concatenation is handled, there may need to be some work done to ensure that `++` is adequately defined.


---

## POLYGONAL_PATH_TRANSLATION

### Name of formal statement
POLYGONAL_PATH_TRANSLATION

### Type of the formal statement
theorem

### Formal Content
```hol
let POLYGONAL_PATH_TRANSLATION = prove
 (`!a b p. polygonal_path (MAP (\x. a + x) (CONS b p)) =
         (\x. a + x) o (polygonal_path (CONS b p))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[MAP; polygonal_path; LINEPATH_TRANSLATION] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC list_INDUCT THEN
  ASM_SIMP_TAC[MAP; polygonal_path; LINEPATH_TRANSLATION] THEN
  REWRITE_TAC[JOINPATHS_TRANSLATION]);;
```

### Informal statement
For all vectors `a` and `b`, and for all lists of vectors `p`, the polygonal path of the list obtained by translating each element of `CONS b p` by `a` is equal to the composition of the translation function by `a` with the polygonal path of `CONS b p`. In other words, translating a polygonal path is the same as taking the polygonal path of the translated vertices.
### Mathematical insight
This theorem states that translation commutes with the construction of a polygonal path. Translating the vertices of the polygonal path and then constructing the path is the same as constructing the path first and then translating the entire path. This is a geometrically intuitive property.

### Informal sketch
The proof proceeds by induction.

- First, generalize `a`, `b`, and `p`. This is done by `GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM]`.
- Then, perform induction using `list_INDUCT` on the list `p`.
- In the base case (where `p` is the empty list), rewrite using the definitions of `MAP`, `polygonal_path`, and `LINEPATH_TRANSLATION`.
- Then, generalize `a`, `b`, and `p` again using `ONCE_REWRITE_TAC[SWAP_FORALL_THM]` and perform induction using `list_INDUCT` on the list `p`.
- In the inductive step, simplify using the definitions of `MAP`, `polygonal_path`, and `LINEPATH_TRANSLATION` in the assumption.
- Finally, rewrite using `JOINPATHS_TRANSLATION`.

### Dependencies

- **Theorems:** `SWAP_FORALL_THM`
- **Definitions:** `MAP`, `polygonal_path`, `LINEPATH_TRANSLATION`, `JOINPATHS_TRANSLATION`


---

## POLYGONAL_PATH_LINEAR_IMAGE

### Name of formal statement
POLYGONAL_PATH_LINEAR_IMAGE

### Type of the formal statement
theorem

### Formal Content
```hol
let POLYGONAL_PATH_LINEAR_IMAGE = prove
 (`!f p. linear f ==> polygonal_path (MAP f p) = f o polygonal_path p`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; MAP] THEN CONJ_TAC THENL
   [REWRITE_TAC[LINEPATH_REFL; o_DEF; FUN_EQ_THM] THEN ASM_MESON_TAC[LINEAR_0];
    ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[polygonal_path; MAP] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[LINEPATH_LINEAR_IMAGE];
    ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[polygonal_path; MAP] THEN
  ASM_SIMP_TAC[GSYM JOINPATHS_LINEAR_IMAGE; GSYM LINEPATH_LINEAR_IMAGE]);;
```

### Informal statement
For any linear function `f` and any list of points `p`, the polygonal path through the image of `p` under `f` is equal to `f` composed with the polygonal path through `p`.

### Mathematical insight
This theorem states that linear transformations preserve polygonal paths. Applying a linear transformation to a polygonal path is the same as applying the transformation to each point defining the path and then constructing the polygonal path through those transformed points. This is a crucial result for working with geometric objects and linear algebra.

### Informal sketch
The proof proceeds by induction on the list of points `p`.

- **Base case:** The list `p` is empty. The theorem reduces to showing that `polygonal_path (MAP f []) = f o polygonal_path []`. This is proved by rewriting using the definitions of `polygonal_path` and `MAP`, then using the lemma `LINEAR_0` which states that for a linear function `f`, `f 0 = 0`.
- **Inductive step:** Assume the theorem holds for a list `l`. We need to show it holds for `h::l`. The induction hypothesis is `linear f ==> polygonal_path (MAP f l) = f o polygonal_path l`.
    - The goal becomes `polygonal_path (MAP f (h::l)) = f o polygonal_path (h::l)`.
    - Expand the definitions of `polygonal_path` and `MAP`. The goal then contains `JOINPATHS` and `LINEPATH`.
    - Use `LINEPATH_LINEAR_IMAGE` and `JOINPATHS_LINEAR_IMAGE` lemmas.
    - Simplify using the inductive hypothesis and properties of composition, to complete the proof.

### Dependencies

- Definitions: `polygonal_path`, `MAP`, `LINEPATH`, `JOINPATHS`, `o_DEF`
- Theorems: `RIGHT_FORALL_IMP_THM`, `FUN_EQ_THM`, `SWAP_FORALL_THM`, `LINEPATH_LINEAR_IMAGE`, `JOINPATHS_LINEAR_IMAGE`
- Lemmas: `LINEAR_0`, `LINEPATH_REFL`

### Porting notes (optional)
- The list induction is standard and should be available in most proof assistants.
- The key lemmas here are `LINEPATH_LINEAR_IMAGE` and `JOINPATHS_LINEAR_IMAGE`. These will need to be proven first in the target proof assistant, and may require equivalent definitions of `LINEPATH` and `JOINPATHS`.
- The `linear` predicate and its properties (`LINEAR_0`) must be defined in the target system.


---

## PATHSTART_POLYGONAL_PATH

### Name of formal statement
PATHSTART_POLYGONAL_PATH

### Type of the formal statement
theorem

### Formal Content
```
let PATHSTART_POLYGONAL_PATH = prove
 (`!p. pathstart(polygonal_path p) = if p = [] then vec 0 else HD p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; NOT_CONS_NIL; HD] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; HD; PATHSTART_JOIN]);;
```

### Informal statement
For all lists of points `p`, the starting point of the polygonal path formed by connecting the points in `p` is equal to the zero vector if `p` is empty, and to the first element of `p` otherwise.

### Mathematical insight
This theorem gives a simple characterization of the starting point of a polygonal path. It states that the starting point is the first point in the defining point sequence unless the sequence is empty, in which case it's the origin. This is a fundamental property needed when reasoning about polygonal paths.

### Informal sketch
The proof proceeds by induction on the list `p` twice.

- The first induction is applied directly to the theorem statement.
- The case `p = []` is handled by rewriting `polygonal_path []` to `linepath(REVERSAL [])` and then using `PATHSTART_LINEPATH` to simplify `pathstart (linepath(REVERSAL []))` to `vec 0`.
- Then we proceed to the inductive step for `CONS h t`.
- The second induction is applied again to the list `t`.
- In the base case where `t = []`, rewrite. Specifically, the right hand side of the equality `pathstart (polygonal_path(CONS h []))` is `HD (CONS h [])` which simplifies to `h`, which is equal to `pathstart(polygonal_path(CONS h []))` using `PATHSTART_LINEPATH` once `polygonal_path` is rewritten.
- In the inductive step for the cases when `t = CONS h1 tl`, rewrite using `polygonal_path`, `PATHSTART_LINEPATH`, `HD`, `PATHSTART_JOIN` to derive the final result.

### Dependencies
- Definitions: `polygonal_path`, `PATHSTART_LINEPATH`
- Theorems: `NOT_CONS_NIL`, `HD`, `PATHSTART_JOIN`
- Tactics: `list_INDUCT`

### Porting notes (optional)
The main challenges when porting this theorem likely involve adapting the induction tactic (`list_INDUCT`) and ensuring the rewrites proceed in the correct order. The success of the proof relies on the correct unfolding of the definition of `polygonal_path` and the subsequent application of other theorems related to path starting points. The rewriting steps using `REWRITE_TAC` might need adjusting depending on the capabilities and automation of the target proof assistant.


---

## PATHFINISH_POLYGONAL_PATH

### Name of formal statement
PATHFINISH_POLYGONAL_PATH

### Type of the formal statement
theorem

### Formal Content
```hol
let PATHFINISH_POLYGONAL_PATH = prove
 (`!p. pathfinish(polygonal_path p) = if p = [] then vec 0 else LAST p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH; NOT_CONS_NIL; LAST] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH; PATHFINISH_JOIN]);;
```

### Informal statement
For all lists of vectors `p`, the `pathfinish` of the `polygonal_path` constructed from `p` is equal to `vec 0` if `p` is the empty list, and `LAST p` otherwise. Here, `LAST p` denotes the last element of the list `p`.

### Mathematical insight
This theorem relates the path finishing point of a polygonal path, which is constructed by joining a list of vectors, to the list of its constituent vectors. Specifically, it states that the final point of the path is simply the last vector segment in the list if the list is nonempty; otherwise, it is at the origin. This result is fundamental for reasoning about the geometry of polygonal paths.

### Informal sketch
The proof proceeds by induction on the list `p`.

- Base case (empty list): We need to show that `pathfinish(polygonal_path []) = vec 0`.
  The proof uses rewriting with `polygonal_path` and `PATHFINISH_LINEPATH` in this base case.

- Inductive step: Assuming the result holds for `p`, we need to show it holds for `CONS h p`.
    - The goal is `pathfinish(polygonal_path (CONS h p)) = LAST (CONS h p)`.
    - The proof uses rewriting with `polygonal_path`, `PATHFINISH_LINEPATH`, `NOT_CONS_NIL`, and `LAST`.
    - The proof uses also PATHFINISH_JOIN to combine the result from induction hypothesis with the vector `h`.

### Dependencies
- `polygonal_path`
- `PATHFINISH_LINEPATH`
- `NOT_CONS_NIL`
- `LAST`
- `PATHFINISH_JOIN`


---

## VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH

### Name of formal statement
VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH

### Type of the formal statement
theorem

### Formal Content
```
let VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH = prove
 (`!p:(real^N)list. set_of_list p SUBSET path_image (polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[set_of_list; EMPTY_SUBSET] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[set_of_list; polygonal_path; PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[SEGMENT_REFL; INSERT_AC; SUBSET_REFL] THEN
   GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[set_of_list; polygonal_path] THEN CONJ_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_LINEPATH; INSERT_SUBSET; ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[EMPTY_SUBSET];
    REPEAT GEN_TAC THEN REPLICATE_TAC 3 DISCH_TAC THEN
    ONCE_REWRITE_TAC[INSERT_SUBSET] THEN
    SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
        HD; NOT_CONS_NIL; IN_UNION; ENDS_IN_SEGMENT; PATH_IMAGE_LINEPATH] THEN
    ASM SET_TAC[]]);;
```

### Informal statement
For any list `p` of points in `real^N`, the set of points in `p` is a subset of the path image of the polygonal path defined by `p`. In other words, all the vertices contained in the list p lie on the polygonal path constructed using the list.

### Mathematical insight
This theorem states that the vertices defining a polygonal path are contained within the path itself. This is a fundamental property that connects the discrete representation of the path (the list of vertices) with its continuous representation (the polygonal path).

### Informal sketch
The proof proceeds by induction on the list `p` of points.

- Base case 1: The empty list. We show that the set of the empty list (`set_of_list []`) is a subset of (`SUBSET`) the path image of the polygonal path of the empty list (`polygonal_path []`). This follows directly since the set of the empty list is the empty set (`set_of_list`), and the empty set is a subset of any set (`EMPTY_SUBSET`).

- Base case 2: A list with one element `[x]`. We show that the set of the list `[x]` is a subset of the path image of the polygonal path of `[x]`. The polygonal path of `[x]` is just a line path corresponding to a single point, which is the degenerate segment `SEGMENT x x`. The path image of this degenerate segment contains `x` (`PATH_IMAGE_LINEPATH`), and the set of `[x]` contains only `x` (`set_of_list`).

- Inductive step: Assume the theorem holds for list `p`.  We must show that it holds for `x::p`. The polygonal path of `x::p` is the join (`PATH_IMAGE_JOIN`) of the segment from `x` to the head of `p` (if `p` is non-empty) with the polygonal path of `p`. The set of `x::p` is the insert of `x` into the set of `p` (`INSERT_SUBSET` and `set_of_list`). By the inductive hypothesis, the set of `p` is a subset of the path image of `polygonal_path p`. We also know that `x` is in `path_image (segment x (HD p))` due to `ENDS_IN_SEGMENT`. Finally, using theorems about the path image of `PATH_IMAGE_JOIN` and sets, we can show the desired result.

### Dependencies

**Theorems/Definitions:**
- `set_of_list`
- `EMPTY_SUBSET`
- `polygonal_path`
- `PATH_IMAGE_LINEPATH`
- `SEGMENT_REFL`
- `INSERT_AC`
- `SUBSET_REFL`
- `PATH_IMAGE_JOIN`
- `PATHFINISH_LINEPATH`
- `PATHSTART_POLYGONAL_PATH`
- `HD`
- `NOT_CONS_NIL`
- `IN_UNION`
- `ENDS_IN_SEGMENT`
- `INSERT_SUBSET`

### Porting notes (optional)
- Inductions on lists are common in HOL Light, and should be straightforward to translate to other proof assistants, given their respective list induction tactics.
- The set theory reasoning is quite basic and should be easily expressible in other proof assistants. Ensure that set membership, subset relations and set operations are defined appropriately.
- Be aware of how the `real^N` type is handled. In other proof assistants, this will likely require a vector space library over the reals.


---

## ARC_POLYGONAL_PATH_IMP_DISTINCT

### Name of formal statement
ARC_POLYGONAL_PATH_IMP_DISTINCT

### Type of the formal statement
theorem

### Formal Content
```
let ARC_POLYGONAL_PATH_IMP_DISTINCT = prove
 (`!p:(real^N)list. arc(polygonal_path p) ==> PAIRWISE (\x y. ~(x = y)) p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN
  X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN
  X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[PAIRWISE; ALL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 DISCH_TAC THEN
  SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           HD; NOT_CONS_NIL; ARC_LINEPATH_EQ] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[PAIRWISE] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[ALL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_SING; ENDS_IN_SEGMENT; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
    (REWRITE_RULE[SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH))) THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM; DE_MORGAN_THM; GSYM ALL_MEM] THEN
  MESON_TAC[]);;
```

### Informal statement
For any list `p` of points in `real^N`, if the polygonal path `polygonal_path p` is an arc, then the points in `p` are pairwise distinct.

### Mathematical insight
This theorem states that if a polygonal path is an arc (i.e., it is injective), then all the vertices that define the path must be distinct. This makes sense because if two vertices coincided, the path would backtrack or stay in the same place between these vertices and thus not be an arc. The converse need not ne true: a path with distict vertices can still intersect with itself.

### Informal sketch
The proof proceeds by induction on the list `p`.

- **Base Case (Nil List):** The polygonal path of an empty list is an arc, and the pairwise distinct condition is vacuously true.
- **Base Case (Single element list):** The polygonal path of a single element list is an arc, and the pairwise distinct condition is vacuously true (since there are no two elements).
- **Inductive Step:** Assume the theorem holds for a list `p`. We want to show it holds for `c::p`. Decompose the assumption `arc(polygonal_path (c::p))` into `arc(join(linepath c a, polygonal_path p))`. Simplify using `ARC_JOIN_EQ`, `PATHFINISH_LINEPATH`, `PATHSTART_POLYGONAL_PATH`, `HD`, `NOT_CONS_NIL`, and `ARC_LINEPATH_EQ`. Then `STRIP_TAC`, rewrite using `PAIRWISE`, and simplify.
  - Then, show that the points in `c :: p` are pairwise distinct, *i.e.*, that `c` is distinct from all points in `p` which can be expressed by `!(x::(real^N)). MEM x p ==> ~(c = x)` and that the points in `p` are pairwise distinct.
  - The proof proceeds using assumptions about the path images and vertices of `linepath` and `polygonal_path`, particularly the fact that if `x` is in the intersection of `path_image (linepath c a)` and `path_image (polygonal_path p)` for distinct `a` and `c`, then it must be that `a = c`
  - Use `MESON_TAC` to discharge the goal.

### Dependencies
- `polygonal_path`
- `ARC_LINEPATH_EQ`
- `ARC_JOIN_EQ`
- `PATHFINISH_LINEPATH`
- `PATHSTART_POLYGONAL_PATH`
- `HD`
- `NOT_CONS_NIL`
- `PAIRWISE`
- `ALL`
- `SUBSET`
- `IN_INTER`
- `IN_SING`
- `ENDS_IN_SEGMENT`
- `PATH_IMAGE_LINEPATH`
- `VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH`
- `IN_SET_OF_LIST`
- `MEM`
- `DE_MORGAN_THM`
- `ALL_MEM`
- `CONTRAPOS_THM`

### Porting notes (optional)
The proof relies heavily on rewriting and simplification tactics, particularly `ASM_REWRITE_TAC` and `MESON_TAC`. A similar level of automation may be needed in other proof assistants to replicate this proof efficiently. The use of higher-order functions such as `PAIRWISE` might require special attention in proof assistants with limited support for higher-order logic. The definition and handling of polygonal paths and arcs are crucial and needs to be addressed first when porting.


---

## PATH_POLYGONAL_PATH

### Name of formal statement
PATH_POLYGONAL_PATH

### Type of the formal statement
theorem

### Formal Content
```hol
let PATH_POLYGONAL_PATH = prove
 (`!p:(real^N)list. path(polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  SIMP_TAC[PATH_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           NOT_CONS_NIL; HD; PATH_LINEPATH]);;
```

### Informal statement
For all `p`, a list of points in `real^N`, the `polygonal_path` constructed from `p` is a `path`.

### Mathematical insight
This theorem states that a `polygonal_path`, which is a path obtained by joining line segments between consecutive points in a list, is indeed a `path` according to the formal definition of a path. This ensures that our construction of polygonal paths adheres to the general properties expected of paths (e.g., continuity).

### Informal sketch
The proof proceeds by induction on the list `p` of points.

- Base case 1: `p` is the empty list `[]`.
    - By definition, `polygonal_path []` is a `linepath []`.
    - `linepath []` corresponds to a constant path, which is a path.

- Base case 2: `p` is a singleton list `[a]`.
    - By definition, `polygonal_path [a]` is `linepath [a]`.
    - A `linepath` from a single point is a path.

- Inductive step: Assume `path (polygonal_path p)` and show `path (polygonal_path (a::b::p))`.
    - By definition, `polygonal_path (a::b::p)` is `PATH_JOIN (linepath [a, b]) (polygonal_path (b::p))`.
    - `PATH_JOIN` combines two paths. We need to show both parts are paths.
        - `linepath [a, b]` is a path by `PATH_LINEPATH`.
        - `polygonal_path (b::p)` is a path by the inductive hypothesis as the tail of the list `p` is a path.
        - Therefore, the join is a path according to `PATH_JOIN`.
    - Simplifications using `PATHFINISH_LINEPATH`, `PATHSTART_POLYGONAL_PATH`, `NOT_CONS_NIL`, `HD`, and `PATH_LINEPATH` are performed to finalize the proof.

### Dependencies
- `polygonal_path`
- `PATH_LINEPATH`
- `PATH_JOIN`
- `PATHFINISH_LINEPATH`
- `PATHSTART_POLYGONAL_PATH`
- `NOT_CONS_NIL`
- `HD`
- `list_INDUCT`


---

## PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL

### Name of formal statement
PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL

### Type of the formal statement
theorem

### Formal Content
```hol
let PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL = prove
 (`!p. ~(p = [])
       ==> path_image(polygonal_path p) SUBSET convex hull (set_of_list p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN CONJ_TAC THENL
   [REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; set_of_list] THEN
    REWRITE_TAC[SEGMENT_REFL; CONVEX_HULL_SING] THEN SET_TAC[];
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path] THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; set_of_list] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL; SUBSET_REFL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL; set_of_list] THEN
      SIMP_TAC[HULL_MONO; INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[set_of_list] THEN
      SET_TAC[]]]);;
```

### Informal statement
For any non-empty list `p` of points, the path image of the polygonal path defined by `p` is a subset of the convex hull of the set of points in `p`.

### Mathematical insight
This theorem states that the polygonal path generated by a list of points lies entirely within the convex hull defined by those same points. This is an intuitive geometric result; the convex hull is the smallest convex set containing the points, and the polygonal path connecting them must be contained within it.

### Informal sketch
The proof proceeds by induction on lists.

- Base case 1: A list of length 1.
  - If the list `p` contains only one element i.e., `[a]`, then the `polygonal_path [a]` is just the point `a` itself.
  - The `path_image` is therefore just `{a}`.
  - The `convex hull` of `set_of_list [a]` is `convex hull {a}` which is `{a}`.
  - Thus, `{a} SUBSET {a}` which follows by reflexivity of subset.

- Base case 2: A list of length 2.
  - If the list `p` contains two elements, i.e. `[a;b]`, then the `polygonal_path [a;b]` is the `segment a b`.
  - `path_image(segment a b) SUBSET convex hull {a,b}` which is true by `SEGMENT_CONVEX_HULL`.

- Inductive step: Assume the theorem holds for list `l`. We want to prove it for `a::b::l`.
  - `path_image (polygonal_path (a::b::l)) SUBSET convex hull (set_of_list (a::b::l))`
  - `polygonal_path (a::b::l)` is `join (segment a b) (polygonal_path (b::l))`.
  - `path_image (join (segment a b) (polygonal_path (b::l))) SUBSET convex hull (set_of_list (a::b::l))`
  - By `SUBSET_PATH_IMAGE_JOIN`, we need to show:
    `convex hull (path_image (segment a b) UNION path_image (polygonal_path (b::l))) SUBSET convex hull (set_of_list (a::b::l))`
  - `path_image (segment a b) SUBSET convex hull (set_of_list (a::b::l))` and `path_image (polygonal_path (b::l)) SUBSET convex hull (set_of_list (a::b::l))`
  - The first part follows because `path_image (segment a b) SUBSET convex hull {a,b} SUBSET convex hull (set_of_list (a::b::l))` with `SEGMENT_CONVEX_HULL` and monotonicity of `convex hull`.
  - The second part follows by the inductive hypothesis `path_image (polygonal_path (b::l)) SUBSET convex hull (set_of_list (b::l))` and monotonicity of the `convex hull` to show `convex hull (set_of_list (b::l)) SUBSET convex hull (set_of_list (a::b::l))`.

### Dependencies

- Definitions:
  - `polygonal_path`
  - `PATH_IMAGE_LINEPATH`
  - `set_of_list`
  - `SEGMENT_REFL`
  - `CONVEX_HULL_SING`

- Theorems:
  - `NOT_CONS_NIL`
  - `SEGMENT_CONVEX_HULL`
  - `SUBSET_REFL`
  - `SUBSET_PATH_IMAGE_JOIN`
  - `HULL_MONO`
  - `INSERT_SUBSET`
  - `EMPTY_SUBSET`
  - `IN_INSERT`
  - `SUBSET_TRANS`
  - `IMP_CONJ`

- Tactics:
  - `list_INDUCT`
  - `MATCH_MP_TAC`
  - `REWRITE_TAC`
  - `GEN_TAC`
  - `CONJ_TAC`
  - `SET_TAC`
  - `STRIP_TAC`
  - `SIMP_TAC`
  - `FIRST_X_ASSUM`
  - `MATCH_MP`
  - `REWRITE_RULE`

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification, which might need adaptation based on the capabilities of the target proof assistant.
- The inductive tactics `list_INDUCT` should be straightforward to translate.
- The subset reasoning and convex hull manipulations may require specific libraries or theorems to be imported and proven in the target system.


---

## PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS

### Name of formal statement
PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS

### Type of the formal statement
theorem

### Formal Content
```hol
let PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS = prove
 (`!p x:real^N.
        arc(polygonal_path p) /\ 3 <= LENGTH p /\
        x IN path_image(polygonal_path p)
        ==> ?a b. MEM a p /\ MEM b p /\ x IN segment[a,b] /\
                  segment[a,b] SUBSET path_image(polygonal_path p) /\
                  ~(pathstart(polygonal_path p) IN segment[a,b] /\
                    pathfinish(polygonal_path p) IN segment[a,b])`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `c:real^N` THEN X_GEN_TAC `p:(real^N)list` THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[polygonal_path] THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           ARC_JOIN_EQ; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH; ARC_LINEPATH] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNION] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[MEM; SUBSET_UNION; ENDS_IN_SEGMENT] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
    REWRITE_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL] THEN
    DISCH_TAC THEN REWRITE_TAC[ARC_LINEPATH_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!p b. (s INTER p) SUBSET {b} /\
      x IN p /\ b IN s /\ ~(x = b)
      ==> ~(x IN s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`path_image(polygonal_path (CONS (b:real^N) (CONS c p)))`;
      `b:real^N`] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; PATHFINISH_IN_PATH_IMAGE];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `3 <= SUC(SUC p) <=> ~(p = 0)`] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_CASES_TAC `p:(real^N)list = []` THENL
     [ASM_REWRITE_TAC[LENGTH; polygonal_path] THEN
      REWRITE_TAC[PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      UNDISCH_TAC
       `x IN path_image(polygonal_path (CONS (b:real^N) (CONS c p)))` THEN
      ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH] THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`b:real^N`; `c:real^N`] THEN
      ASM_REWRITE_TAC[MEM; SUBSET_UNION; ENDS_IN_SEGMENT] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH] THEN
      REWRITE_TAC[ARC_LINEPATH_EQ] THEN
      MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN SET_TAC[];
      ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^N` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N` THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[MEM];
        ASM_MESON_TAC[MEM];
        ASM_REWRITE_TAC[];
        ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `(sab INTER p) SUBSET {b}
          ==> !sde a. sde SUBSET p /\
              ~(b IN sde) /\ d IN sde /\ a IN sde /\ a IN sab
              ==> F`) o el 2 o CONJUNCTS) THEN
        MAP_EVERY EXISTS_TAC [`segment[d:real^N,e]`; `a:real^N`] THEN
        ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]]]]);;
```

### Informal statement
For any polygonal path `p` in `real^N` and any point `x` in `real^N`, if `p` is an arc, the length of `p` is greater than or equal to 3, and `x` is in the path image of `p`, then there exist points `a` and `b` in `p` such that `x` is in the segment from `a` to `b`, the segment from `a` to `b` is a subset of the path image of `p`, and it is not the case that both the starting point of `p` and the finishing point of `p` are in the segment from `a` to `b`.

### Mathematical insight
This theorem states that if a point `x` lies on a polygonal path `p` (which is an arc and has at least 3 points), then `x` must lie on a segment `[a,b]` whose endpoints `a` and `b` are vertices of the path. Moreover, the segment `[a,b]` must be entirely contained within the path (intuitively follows the path) and it should not contain both `pathstart(p)` and `pathfinish(p)`. The last conjunct is important to rule out trivial segments of length 0. This is fundamental when working with properties of polygonal paths and their approximations.

### Informal sketch
The proof proceeds by induction on lists.

- Base case: The list has length 0, 1 or 2, which contradicts `3 <= LENGTH p`.
- Inductive step:
    - The outer induction is over the list of points defining the path.

    - The theorem is of the form `!p x. P(p, x) ==> ?a b. Q(p, x, a, b)`.

    - Assume `arc(polygonal_path(CONS a (CONS b p))) /\ 3 <= LENGTH(CONS a (CONS b p)) /\ x IN path_image(polygonal_path(CONS a (CONS b p)))`.

    - Split the `path_image` using `PATH_IMAGE_JOIN` to consider segments `[a, b]` and the remaining path `polygonal_path (CONS b p)`.

    - If `x` is located on `segment[a,b]`, pick `a` and `b` directly.

    - Otherwise, the point `x` belongs to `path_image(polygonal_path(CONS b p))`, so the inductive hypothesis can be applied to `CONS b p` to find `a` and `b`.
    - If `x` is in a segment in the tail, then the induction hypothesis gives us the segment endpoints `a` and `b`, and the required properties follow.

    - The proof handles the case by case analysis required by the `path_image` and `segment` definitions with specific rules.

### Dependencies
- `LENGTH`
- `ARITH`
- `polygonal_path`
- `PATHSTART_JOIN`
- `PATHFINISH_JOIN`
- `PATH_IMAGE_JOIN`
- `PATHFINISH_LINEPATH`
- `PATHSTART_POLYGONAL_PATH`
- `ARC_JOIN_EQ`
- `NOT_CONS_NIL`
- `HD`
- `PATHSTART_LINEPATH`
- `PATH_IMAGE_LINEPATH`
- `ARC_LINEPATH`
- `IN_UNION`
- `MEM`
- `SUBSET_UNION`
- `ENDS_IN_SEGMENT`
- `ARC_DISTINCT_ENDS`
- `ARC_LINEPATH_EQ`
- `PATHFINISH_IN_PATH_IMAGE`
- `LENGTH_EQ_NIL`
- `MONO_EXISTS`

### Porting notes (optional)
- The proof relies heavily on list induction and rewriting using definitions related to polygonal paths and segments. Pay attention to the definitions of `path_image`, `polygonal_path`, and `segment` when porting.
- HOL Light's `SIMP_TAC` plays a crucial role in simplifying expressions involving lists and sets. Ensure that your target proof assistant can handle similar simplifications automatically or provide manual simplification rules.
- The `MESON_TAC` calls at the end suggest the use of a first-order automated theorem prover to discharge some of the simpler goals. You may need to adapt or replace this step depending on the automation capabilities of your target proof assistant.


---

## SET_OF_LIST_POLYGONAL_PATH_ROTATE

### Name of formal statement
SET_OF_LIST_POLYGONAL_PATH_ROTATE

### Type of the formal statement
theorem

### Formal Content
```hol
let SET_OF_LIST_POLYGONAL_PATH_ROTATE = prove
 (`!p. ~(p = []) ==> set_of_list(CONS (LAST p) (BUTLAST p)) = set_of_list p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN SET_TAC[]);;
```

### Informal statement
For any list `p`, if `p` is not empty, then the set of elements in `CONS (LAST p) (BUTLAST p)` is equal to the set of elements in `p`.  Here, `LAST p` is the last element of `p`, `BUTLAST p` is the list `p` without its last element, and `CONS x l` adds the element `x` at the head of the list `l`.

### Mathematical insight
The theorem states that rotating a non-empty list does not change the set of elements in the list.  Rotating a list means moving the last element of the list to the front. `CONS (LAST p) (BUTLAST p)` represents the rotation of the list `p`. The theorem is important for reasoning about geometric objects defined from lists of vertices.

### Informal sketch
The proof proceeds by:
- Stripping the goal. This introduces `p` as an assumption and reduces the goal to showing `set_of_list(CONS (LAST p) (BUTLAST p)) = set_of_list p` under the assumption `~(p = [])`.
- Rewriting using `APPEND_BUTLAST_LAST` to rewrite `p` as `APPEND (BUTLAST p) [LAST p]` within the context of `set_of_list`.
- Rewriting using `SET_OF_LIST_APPEND` and `set_of_list` to obtain the desired result.
- Applying `SET_TAC[]` to close the goal.

### Dependencies
- `SET_OF_LIST_APPEND`
- `set_of_list`
- `APPEND_BUTLAST_LAST`


---

## PROPERTIES_POLYGONAL_PATH_SNOC

### Name of formal statement
PROPERTIES_POLYGONAL_PATH_SNOC

### Type of the formal statement
theorem

### Formal Content
```hol
let PROPERTIES_POLYGONAL_PATH_SNOC = prove
 (`!p d:real^N.
        2 <= LENGTH p
        ==> path_image(polygonal_path(APPEND p [d])) =
            path_image(polygonal_path p ++ linepath(LAST p,d)) /\
            (arc(polygonal_path(APPEND p [d])) <=>
             arc(polygonal_path p ++ linepath(LAST p,d))) /\
            (simple_path(polygonal_path(APPEND p [d])) <=>
             simple_path(polygonal_path p ++ linepath(LAST p,d)))`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; ARITH] THEN X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[APPEND; polygonal_path; LAST; NOT_CONS_NIL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `d:real^N` THEN DISCH_TAC THEN REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[LAST] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  ONCE_REWRITE_TAC[polygonal_path] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[APPEND; LENGTH; ARITH_RULE `2 <= SUC(SUC n)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SIMP_TAC[GSYM ARC_ASSOC; GSYM SIMPLE_PATH_ASSOC; PATHSTART_JOIN;
           PATHFINISH_JOIN; PATHSTART_POLYGONAL_PATH;
           PATHFINISH_POLYGONAL_PATH;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
           PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD] THEN
    REWRITE_TAC[UNION_ACI];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = d` THENL
   [MATCH_MP_TAC(TAUT
     `(~p /\ ~p') /\ (q <=> q') ==> (p <=> p') /\ (q <=> q')`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARC_SIMPLE_PATH; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      ASM_REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; NOT_CONS_NIL; LAST;
                      APPEND_EQ_NIL; LAST_APPEND];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_JOIN_LOOP_EQ o
     lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; PATHSTART_LINEPATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_JOIN_LOOP_EQ o
     rhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
                  PATHFINISH_POLYGONAL_PATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
    MATCH_MP_TAC(TAUT
     `((q <=> p) /\ (q' <=> p')) /\ (p <=> p')
      ==> (p <=> p') /\ (q <=> q')`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_PATH_EQ_ARC THEN
      REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
                  PATHFINISH_POLYGONAL_PATH] THEN
      ASM_REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) ARC_JOIN_EQ o lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) ARC_JOIN_EQ o rhs o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH; PATHSTART_JOIN;
               NOT_CONS_NIL; HD];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]]);;
```

### Informal statement
For all `p:real^N list` and `d:real^N`, if the length of `p` is greater than or equal to 2, then:
1. The image of the polygonal path constructed from the list `p` appended with the point `d` is equal to the image of the joined path of the polygonal path of `p` and the line path from the last point of `p` to `d`.
2. The polygonal path constructed from the list `p` appended with `d` is an arc if and only if the joined path of the polygonal path of `p` and the line path from the last point of `p` to `d` is an arc.
3. The polygonal path constructed from the list `p` appended with `d` is a simple path if and only if the joined path of the polygonal path of `p` and the line path from the last point of `p` to `d` is a simple path.

### Mathematical insight
This theorem relates the properties of a polygonal path extended by a single point to the properties of the original polygonal path joined with a line segment. In particular, extending a polygonal path by appending one point `d` is equivalent to joining the original polygonal path with the line segment from `LAST p` to `d`. This is useful for inductive proofs about polygonal paths. The properties considered here are the path image, whether the path is an arc, and whether the path is simple.

### Informal sketch
The theorem is proved by induction on lists.

- Base case 1: The list `p` is empty. This case is trivial because `LENGTH p >= 2` is false, so the implication holds vacuously.
- Base case 2: The list `p` has one element. Again, this case is trivial since `LENGTH p >= 2` is false.
- Inductive step: Assume the theorem holds for `p`. We want to prove it for `CONS h p`.
  - Assume `2 <= LENGTH (CONS h p)`. This implies `1 <= LENGTH p`.
  - Let `d` be a point in `real^N`.
  - The goal is to show that `path_image(polygonal_path(APPEND (CONS h p) [d])) = path_image(polygonal_path (CONS h p) ++ linepath(LAST (CONS h p), d))` and `arc(polygonal_path(APPEND (CONS h p) [d])) <=> arc(polygonal_path (CONS h p) ++ linepath(LAST (CONS h p), d))` and `simple_path(polygonal_path(APPEND (CONS h p) [d])) <=> simple_path(polygonal_path (CONS h p) ++ linepath(LAST (CONS h p), d))`.
  - Rewrite `APPEND` and `LAST` to simplify the expressions.
  - Apply the inductive hypothesis.
  - Simplify using properties such as `ARC_ASSOC`, `SIMPLE_PATH_ASSOC`, `PATHSTART_JOIN`, `PATHFINISH_JOIN`, `PATHSTART_POLYGONAL_PATH`, `PATHFINISH_POLYGONAL_PATH`, `PATHSTART_LINEPATH`, `PATHFINISH_LINEPATH`.
  - Consider the case when `hd = d`.
    - Use tautologies to simplify the equivalence relations between `arc` and `simple_path`.
    - Use `SIMPLE_PATH_JOIN_LOOP_EQ` to deal with simple paths.
    - Use `ARC_JOIN_EQ` to deal with arcs.
  - Consider the case when `hd != d`. The theorem becomes easier.

### Dependencies

**Definitions:**
- `LENGTH`
- `APPEND`
- `polygonal_path`
- `LAST`
- `linepath`
- `path_image`
- `arc`
- `simple_path`
- `PATHSTART_JOIN`
- `PATHFINISH_JOIN`
- `PATHSTART_POLYGONAL_PATH`
- `PATHFINISH_POLYGONAL_PATH`
- `PATHSTART_LINEPATH`
- `PATHFINISH_LINEPATH`
- `UNION_ACI`

**Theorems:**
- `ARC_ASSOC`
- `SIMPLE_PATH_ASSOC`
- `NOT_CONS_NIL`
- `HD`
- `PATH_IMAGE_JOIN`
- `ARC_SIMPLE_PATH`
- `APPEND_EQ_NIL`
- `LAST_APPEND`
- `SIMPLE_PATH_JOIN_LOOP_EQ`
- `ARC_JOIN_EQ`
- `SIMPLE_PATH_EQ_ARC`

**Tactics:**
- `list_INDUCT`

### Porting notes (optional)
- The proof relies heavily on rewriting with various path lemmas, so ensure that the corresponding path lemmas are available or proved in the target proof assistant.
- The use of `MATCH_MP_TAC` with tautologies to simplify the proof may require translating the tautologies into equivalent forms in the target proof assistant or using similar tactics.
- Pay close attention to how the definitions of `polygonal_path`, `linepath`, `arc`, and `simple_path` are encoded, as these will be key to translating the theorem and its proof.


---

## PATH_IMAGE_POLYGONAL_PATH_ROTATE

### Name of formal statement
PATH_IMAGE_POLYGONAL_PATH_ROTATE

### Type of the formal statement
theorem

### Formal Content
```hol
let PATH_IMAGE_POLYGONAL_PATH_ROTATE = prove
 (`!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> path_image(polygonal_path(APPEND (TL p) [HD(TL p)])) =
            path_image(polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[HD; TL] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAST; APPEND; NOT_CONS_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL] THEN ONCE_REWRITE_TAC[GSYM LAST] THEN
  DISCH_TAC THEN
  SIMP_TAC[PROPERTIES_POLYGONAL_PATH_SNOC; LENGTH;
           ARITH_RULE `2 <= SUC(SUC n)`] THEN
  ONCE_REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [polygonal_path] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST]) THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
           PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
           LAST; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[UNION_ACI]);;
```

### Informal statement
For any list of points `p` in `real^N` such that the length of `p` is greater than or equal to 2 and the last point of `p` is equal to the first point of `p`, the path image of the polygonal path constructed from rotating the list `p`, which appends the head of the tail of `p` to the tail of `p`, is equal to the path image of the polygonal path constructed from `p`.

### Mathematical insight
This theorem states that if we have a closed polygonal path (i.e., the last point is the same as the first), then the path image of the polygonal path remains unchanged if we shift the points in the path by one position. This essentially asserts the path image is invariant under cyclic permutations of the points that define the polygonal path, provided it's closed.

### Informal sketch
The proof proceeds by induction on the list `p`.

- Base case 1 (list of length 0): Trivial as assumption `2 <= LENGTH p` fails.
- Base case 2 (list of length 1): Trivial as assumption `2 <= LENGTH p` fails.
- Base case 3 (list of length 2): We assume `2 <= LENGTH p /\ LAST p = HD p` and show the theorem holds. Here `p` is of the form `[a;b]`.  The goal simplifies.
- Inductive step: We assume the theorem holds for a list `p` of length `n` and we want to show it holds for list `c::p` (of length `n+1`).
 - We assume `2 <= LENGTH (c::p) /\ LAST (c::p) = HD (c::p)`. 
 - The goal is `path_image(polygonal_path(APPEND (TL (c::p)) [HD(TL (c::p))])) = path_image(polygonal_path (c::p))`.
 - The proof involves rewriting `LAST`, `APPEND`, `NOT_CONS_NIL` etc.
 - We then use `PROPERTIES_POLYGONAL_PATH_SNOC`, `LENGTH`, the arithmetic fact `2 <= SUC(SUC n)`.
 - Using the induction hypothesis and properties of `polygonal_path`, `path_image`, `PATHSTART_LINEPATH`, `PATHFINISH_LINEPATH`, `PATHSTART_POLYGONAL_PATH`, `PATHFINISH_POLYGONAL_PATH` we can show that the equality holds.

### Dependencies

**Theorems:**
- `LENGTH`
- `ARITH`
- `HD`
- `TL`
- `LAST`
- `APPEND`
- `NOT_CONS_NIL`
- `PATH_IMAGE_JOIN`
- `PATHSTART_LINEPATH`
- `PATHFINISH_LINEPATH`
- `PATHSTART_POLYGONAL_PATH`
- `PATHFINISH_POLYGONAL_PATH`
- `UNION_ACI`
- `PROPERTIES_POLYGONAL_PATH_SNOC`

**Definitions:**
- `path_image`
- `polygonal_path`

### Porting notes
- The proof relies heavily on rewriting with definitions and simplification rules related to list operations (`HD`, `TL`, `LAST`, `APPEND`). These may need to be adapted based on the list library available in the target proof assistant.
- The properties about `polygonal_path` would have to be translated possibly by defining the same notion of polygonal paths and proving that these properties hold for the new definition and its components such as, `path_image`, start point, and end point.


---

## SIMPLE_PATH_POLYGONAL_PATH_ROTATE

### Name of formal statement
SIMPLE_PATH_POLYGONAL_PATH_ROTATE

### Type of the formal statement
theorem

### Formal Content
```hol
let SIMPLE_PATH_POLYGONAL_PATH_ROTATE = prove
 (`!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> (simple_path(polygonal_path(APPEND (TL p) [HD(TL p)])) =
             simple_path(polygonal_path p))`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[HD; TL] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAST; APPEND; NOT_CONS_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL] THEN ONCE_REWRITE_TAC[GSYM LAST] THEN
  DISCH_TAC THEN
  SIMP_TAC[PROPERTIES_POLYGONAL_PATH_SNOC; LENGTH;
           ARITH_RULE `2 <= SUC(SUC n)`] THEN
  ONCE_REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [polygonal_path] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST]) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
               PATHFINISH_LINEPATH; LAST; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[INSERT_AC; INTER_ACI; CONJ_ACI]);;
```

### Informal statement
For any list `p` of points in `real^N` (N-dimensional real space) satisfying the conditions that the length of `p` is greater than or equal to 2 and the last element of `p` is equal to the first element of `p`, the simplicity of the polygonal path formed by rotating the list `p` is equivalent to the simplicity of the polygonal path formed by the original list `p`. The rotation consists of taking the tail of `p` and appending the head of the tail to it, to obtain `APPEND (TL p) [HD(TL p)]`.

### Mathematical insight
This theorem states that cyclically rotating a closed polygonal path does not affect whether it is a simple path (i.e., non-self-intersecting). The condition `LAST p = HD p` ensures that the polygonal path is closed, forming a loop. Rotating the path merely changes the starting point of the loop, but not its overall shape or whether it intersects itself. This is important because the starting point is arbitrary as long as the path is closed.

### Informal sketch
The proof proceeds by induction on lists.

- Base Case 1: Lists of zero length are handled.
- Base Case 2: Lists of one element are handled.
- Base Case 3: Lists of two element are handled by simplifications of `LAST`, `APPEND` and `NOT_CONS_NIL`.
- Inductive Step: Assume the theorem holds for a list `p`. We want to prove that it also holds for `c::p`, where `c` is a point in `real^N`. The goal now is `simple_path(polygonal_path(APPEND (TL (c::p)) [HD(TL (c::p))])) = simple_path(polygonal_path (c::p))`.
  - Assume that `2 <= LENGTH (c::p)` and `LAST (c::p) = HD (c::p)`.
  - Simplify the goal using `PROPERTIES_POLYGONAL_PATH_SNOC`, `LENGTH`, and other lemmas about lists.
  - Use the inductive hypothesis: `simple_path(polygonal_path(APPEND (TL p) [HD(TL p)])) = simple_path(polygonal_path p)`.
  - Use several simplification rules like `SIMPLE_PATH_JOIN_LOOP_EQ`, `PATHSTART_LINEPATH`, `PATHFINISH_LINEPATH`, `PATHSTART_POLYGONAL_PATH`, `PATHFINISH_POLYGONAL_PATH` along with list operations on `LAST`, `HD` and `TL` to simplify the expression.
  - Finally, rewrite using `INSERT_AC`, `INTER_ACI`, and `CONJ_ACI` for additional simplification.

### Dependencies
- List operations: `LENGTH`, `LAST`, `HD`, `TL`, `APPEND`, `NOT_CONS_NIL`
- Polygonal path: `polygonal_path`, `PROPERTIES_POLYGONAL_PATH_SNOC`, `PATHSTART_POLYGONAL_PATH`, `PATHFINISH_POLYGONAL_PATH`,
- Simple path: `simple_path`, `SIMPLE_PATH_JOIN_LOOP_EQ`
- Line path: `PATHSTART_LINEPATH`, `PATHFINISH_LINEPATH`
- Set operations: `INSERT_AC`, `INTER_ACI`, `CONJ_ACI`
- Arithmetic: `ARITH`, `ARITH_RULE 2 <= SUC(SUC n)`

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification with respect to list operations and path definitions. Ensure that the target proof assistant's list library and path constructions are adequately developed.
- The use of tactics like `ASM_SIMP_TAC` and `GEN_REWRITE_TAC` implies substantial simplification by the simplifier. Replicating this level of automation might require significant effort.
- Special care needs to be taken when porting the `polygonal_path` definition which links sequence of point into path defined in HOL Light. One may use piecewise line path alternative to represent such object in other proof assistant.


---

## ROTATE_LIST_TO_FRONT_1

### Name of formal statement
ROTATE_LIST_TO_FRONT_1

### Type of the formal statement
theorem

### Formal Content
```hol
let ROTATE_LIST_TO_FRONT_1 = prove
 (`!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. EL 1 l' = a /\ P l'`,
  let lemma0 = prove
     (`!P. (!i. P i /\ 0 < i ==> P(i - 1)) /\ (?k. 0 < k /\ P k)
             ==> P 1`,
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `!i:num. i < k ==> P(k - i)` MP_TAC THENL
       [INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN DISCH_TAC THEN
        REWRITE_TAC[ARITH_RULE `k - SUC i = k - i - 1`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC;
        DISCH_THEN(MP_TAC o SPEC `k - 1`) THEN
        ASM_SIMP_TAC[ARITH_RULE `0 < k ==> k - 1 < k /\ k - (k - 1) = 1`]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?i l'. 0 < i /\ i < LENGTH l' /\ P l' /\ EL i l' = (a:A)`
  MP_TAC THENL
   [SUBGOAL_THEN `~(l:A list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH; ARITH_RULE `~(3 <= 0)`]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MEM_EXISTS_EL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC (ARITH_RULE `i = 0 \/ 0 < i`)
    THENL
     [EXISTS_TAC `LENGTH(l:A list) - 2` THEN
      EXISTS_TAC `(APPEND (TL l) [HD(TL l):A])` THEN
      ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TL; EL_APPEND] THEN
      REWRITE_TAC[LT_REFL; LENGTH; SUB_REFL; EL; HD] THEN
      SUBGOAL_THEN `3 <= LENGTH(l:A list)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[ARITH_RULE `3 <= n ==> n - 2 < n - 1`] THEN
      ASM_SIMP_TAC[EL_TL; ARITH_RULE `3 <= n ==> n - 2 + 1 = n - 1`] THEN
      ASM_MESON_TAC[LAST_EL];
      MAP_EVERY EXISTS_TAC [`i:num`; `l:A list`] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT] lemma0)) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:A list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `APPEND (TL m) [HD(TL m):A]` THEN
    SUBGOAL_THEN `~(m:A list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH; ARITH_RULE `~(3 <= 0)`]; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TL; EL_APPEND] THEN
    ASM_REWRITE_TAC[LENGTH] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    ASM_SIMP_TAC[EL_TL; ARITH_RULE `0 < k ==> k - 1 + 1 = k`]]);;
```

### Informal statement
For any predicate `P` on lists of type `A`, list `l` of type `A` and element `a` of type `A`, if the following conditions hold:
1. For any list `l`, if `P(l)` holds, then `l` has length at least 3 and the last element of `l` equals the first element of `l`.
2. For any list `l`, if `P(l)` holds, then `P(APPEND (TL l) [HD(TL l)])` also holds, where `APPEND (TL l) [HD(TL l)]` is the list obtained by rotating `l` once.
3. `P(l)` holds and `a` is a member of `l`,

then there exists a list `l'` such that the first element of `l'` is `a` and `P(l')` holds.

### Mathematical insight
The theorem states that if a list satisfies a certain property `P`, and that property is preserved by rotations, and an element `a` is a member of the list, then one can rotate the list such that `a` becomes the first element, while preserving the property `P`. The condition on `P` means that we are dealing with rotating a list with length at least 3 and first element equals to the last.
`lemma0` establishes a general result of number theory which can be rephrased as: For any predicate `P` on natural numbers, if decreasing index `i` preserves `P` provided `P i` and `i` is greater than `0`, and there is an natural number `k` greater than `0` such that `P k`, then `P 1`

### Informal sketch
The proof proceeds by induction and case distinction to find a suitable rotation.

- First, prove `lemma0`:
  - State the goal `!i:num. i < k ==> P(k - i)`.
  - Perform induction.
    - Base case: `i = 0`.  Simplify using `SUB_0` and arithmetic.
    - Inductive step: Simplify using arithmetic rules, apply the inductive hypothesis, and use arithmetic.
  - Apply the derived lemma to establish the main result.

- Main proof:
  - Assume the premises.
  - Introduce an existential subgoal: `?i l'. 0 < i /\ i < LENGTH l' /\ P l' /\ EL i l' = (a:A)`. This claims that there exists an index `i` and some rotations `l'` such that element at `i` of list `l'` equals `a`.
  - Argue that `l` is non-empty.
  - Use `MEM_EXISTS_EL` to show that `a` must occur at some index `i` in `l`.
  - Do a case split on whether `i = 0` or `0 < i`.
    - Case `i = 0`:  Construct `l'` as the rotation of `l` by `LENGTH(l) - 2` positions. Show `EL 1 l' = a` and `P l'`.
    - Case `0 < i`: Use `lemma0`.
      - Instantiate existential variable `m` with the list `m`.
      - Construct the rotation `APPEND (TL m) [HD(TL m)]`.
      - Use cases to show `~(m:A list = [])`.
      - Simplify terms using `LENGTH_APPEND`, `LENGTH_TL`, and related rules.
      - Apply `COND_CASES_TAC` to handle conditional expressions.

### Dependencies
- `LENGTH`
- `ARITH_RULE`
- `MEM_EXISTS_EL`
- `LENGTH_APPEND`
- `LENGTH_TL`
- `EL_APPEND`
- `LT_REFL`
- `SUB_REFL`
- `EL`
- `HD`
- `EL_TL`
- `LAST_EL`
- `RIGHT_EXISTS_AND_THM`
- `IMP_CONJ_ALT`

### Porting notes (optional)
- HOL Light's automation (e.g., `ASM_MESON_TAC`, `ASM_SIMP_TAC`) handles many simplification and logical reasoning steps. When porting, be prepared to make these steps explicit.
- The reliance on arithmetic rules (e.g., `ARITH_RULE \`3 <= n ==> n - 2 < n - 1\` `) suggests that a strong arithmetic tactic or decision procedure will be beneficial in other proof assistants.
- The use of `MESON_TAC[]` indicates some first-order reasoning.


---

## ROTATE_LIST_TO_FRONT_0

### Name of formal statement
ROTATE_LIST_TO_FRONT_0

### Type of the formal statement
theorem

### Formal Content
```hol
let ROTATE_LIST_TO_FRONT_0 = prove
 (`!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. HD l' = a /\ P l'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:A list->bool`; `l:A list`; `a:A`]
    ROTATE_LIST_TO_FRONT_1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `l':A list` THEN
  STRIP_TAC THEN EXISTS_TAC `APPEND (TL l') [HD(TL l'):A]` THEN
  ASM_SIMP_TAC[] THEN UNDISCH_TAC `EL 1 l' = (a:A)` THEN
  SUBGOAL_THEN `3 <= LENGTH(l':A list)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`l':A list`,`p:A list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  REWRITE_TAC[APPEND; HD; TL; num_CONV `1`; EL]);;
```

### Informal statement
For any predicate `P` on lists of type `A`, if:
1. For any list `l`, if `P(l)` holds, and `l` is non-empty, then the length of `l` is greater than or equal to 3 and the last element of `l` is equal to its first element, and
2. For any list `l`, if `P(l)` holds, then `P(APPEND (TL l) [HD(TL l)])` also holds (i.e., `P` is inductive with respect to rotation),
then if `P(l)` holds for some list `l` and `a` is a member of `l`, there exists a list `l'` such that the head of `l'` is `a` and `P(l')` holds.

### Mathematical insight
This theorem essentially states that if a predicate `P` on lists is preserved when the list is rotated to the front, and `P` holds for some list `l` containing an element `a`, then we can find another list `l'` that also satisfies predicate `P` and starts with the element `a`. It builds on `ROTATE_LIST_TO_FRONT_1` and adds conditions on `P`, namely a size bound and a condition relating the head and tail of the lists. This is a generalization about lists that maintains a property under rotation, given that it starts with an element present in an initial list.

### Informal sketch
The primary step involves using `ROTATE_LIST_TO_FRONT_1`, an existing theorem which asserts the existence of `l'` such that `EL 1 l' = a`. The goal is to show `HD l' = a` under additional conditions.

- Apply `ROTATE_LIST_TO_FRONT_1` to obtain `EL 1 l' = a`.
- Introduce an existential quantifier for `l'` and rewrite the goal to showing there exits `l'` satisfying the given criteria. Pick `APPEND (TL l') [HD(TL l')]` as a witness.
- Prove the existence of `l'` by providing `APPEND (TL l') [HD(TL l')]` as a witness and simplifying.
- Show that `3 <= LENGTH(l')` using the assumption that `P(l')` is true.
- Apply `list_INDUCT` and rewrite using `LENGTH`, `APPEND`, `HD`, `TL`, `num_CONV '1'`, and `EL`.

### Dependencies
#### Theorems
- `ROTATE_LIST_TO_FRONT_1`
- `LEFT_IMP_EXISTS_THM`

#### Definitions
- `LENGTH`
- `APPEND`
- `HD`
- `TL`
- `EL`

#### Inductive definitions
- `list_INDUCT`

#### Conversion
- `num_CONV`

#### Tactics
- `REPEAT STRIP_TAC`
- `MP_TAC`
- `ISPECL`
- `ASM_REWRITE_TAC`
- `X_GEN_TAC`
- `STRIP_TAC`
- `EXISTS_TAC`
- `ASM_SIMP_TAC`
- `UNDISCH_TAC`
- `SUBGOAL_THEN`
- `ASM_MESON_TAC`
- `ALL_TAC`
- `SPEC_TAC`
- `MATCH_MP_TAC`
- `REWRITE_TAC`
- `GEN_TAC`

### Porting notes (optional)
- The theorem relies on `ROTATE_LIST_TO_FRONT_1`, so that theorem should be ported first.
- The proof relies heavily on rewriting and simplification. Ensure that the target proof assistant has similar capabilities for rewriting and simplification.
- The `list_INDUCT` is an important piece. This can likely be easily ported via the standard library's inductive list definition in other proof assistants.


---

## DISTINGUISHING_ROTATION_EXISTS_PAIR

### Name of formal statement
DISTINGUISHING_ROTATION_EXISTS_PAIR

### Type of the formal statement
theorem

### Formal Content
```hol
let DISTINGUISHING_ROTATION_EXISTS_PAIR = prove
 (`!x y. ~(x = y)
         ==> FINITE {t | &0 <= t /\ t < &2 * pi /\
                         (rotate2d t x)$2 = (rotate2d t y)$2}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  ONCE_REWRITE_TAC[GSYM ROTATE2D_SUB] THEN
  REWRITE_TAC[GSYM IM_DEF; GSYM real; GSYM ARG_EQ_0_PI] THEN
  REWRITE_TAC[FINITE_UNION; SET_RULE
   `{x | p x /\ q x /\ (r x \/ s x)} =
    {x | p x /\ q x /\ r x} UNION {x | p x /\ q x /\ s x}`] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC(MESON[FINITE_SING; FINITE_SUBSET]
       `(?a. s SUBSET {a}) ==> FINITE s`) THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. x IN s /\ y IN s ==> x = y) ==> ?a. s SUBSET {a}`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ARG_ROTATE2D_UNIQUE_2PI THEN EXISTS_TAC `x - y:complex` THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0]);;
```

### Informal statement
For all `x` and `y`, if `x` is not equal to `y`, then the set of `t` such that `0 <= t < 2*pi` and the imaginary part of  `rotate2d t x` equals the imaginary part of `rotate2d t y` is finite.

### Mathematical insight
The theorem states that given two distinct points in the complex plane, there are only finitely many rotations (between 0 and 2π) around the origin such that the y-coordinates (imaginary parts) of the rotated points are equal. This is because the difference between the arguments of the two points only coincides finitely many times with any given rotation within the specified interval.

### Informal sketch
The proof proceeds as follows:
- Assume `x` and `y` are distinct.
- Rewrite `(rotate2d t x)$2 = (rotate2d t y)$2` to `Im(rotate2d t x) = Im(rotate2d t y)`.
- Apply `ROTATE2D_SUB` and rewrite `Im(t * x) = Im(t * y)` as `Im(t * (x - y)) = 0`.
- Rewrite using the definition of imaginary part, `real` and `ARG_EQ_0_PI` to derive `arg(x - y) + t = 0 + k * pi` for some integer `k`.
- Split into cases where `k` is even or odd
- Use `FINITE_UNION` to express the set as union of two sets
- Use `FINITE_SING` and `FINITE_SUBSET` and `(!x y. x IN s /\ y IN s ==> x = y) ==> ?a. s SUBSET {a}` to establish that the set is finite if each element of the considered set is unique.
- Apply `IN_ELIM_THM` and strip assumptions.
- Apply `ARG_ROTATE2D_UNIQUE_2PI` to show that the number of solutions is finite.
- Instantiate the existence with `x-y:complex`
- Apply `COMPLEX_SUB_0` to complete the proof.

### Dependencies
**Theorems:**
- `REAL_SUB_0`
- `VECTOR_SUB_COMPONENT`
- `ROTATE2D_SUB`
- `IM_DEF`
- `real`
- `ARG_EQ_0_PI`
- `FINITE_UNION`
- `FINITE_SING`
- `FINITE_SUBSET`
- `IN_ELIM_THM`
- `ARG_ROTATE2D_UNIQUE_2PI`
- `COMPLEX_SUB_0`
**Tactics:**
- `REPEAT STRIP_TAC`
- `ONCE_REWRITE_TAC`
- `GSYM`
- `REWRITE_TAC`
- `SET_RULE`
- `CONJ_TAC`
- `MATCH_MP_TAC`
- `MESON`
- `EXISTS_TAC`
- `ASM_REWRITE_TAC`


---

## DISTINGUISHING_ROTATION_EXISTS

### Name of formal statement
DISTINGUISHING_ROTATION_EXISTS

### Type of the formal statement
theorem

### Formal Content
```hol
let DISTINGUISHING_ROTATION_EXISTS = prove
 (`!s. FINITE s ==> ?t. pairwise (\x y. ~(x$2 = y$2)) (IMAGE (rotate2d t) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `INFINITE ({t | &0 <= t /\ t < &2 * pi} DIFF
              UNIONS (IMAGE (\(x,y). {t | &0 <= t /\ t < &2 * pi /\
                                          (rotate2d t x)$2 = (rotate2d t y)$2})
                            ({(x,y) | x IN s /\ y IN s /\ ~(x = y)})))`
  MP_TAC THENL
   [MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
    REWRITE_TAC[INFINITE; FINITE_REAL_INTERVAL; REAL_NOT_LE] THEN
    CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{(x:real^2,y:real^2) | x IN s /\ y IN s}` THEN
      ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[DISTINGUISHING_ROTATION_EXISTS_PAIR]];
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[FINITE_EMPTY; INFINITE]
     `INFINITE s ==> ~(s = {})`)) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[UNIONS_IMAGE; EXISTS_IN_GSPEC] THEN
    REWRITE_TAC[pairwise; IN_ELIM_THM] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[ROTATE2D_EQ] THEN MESON_TAC[]]);;
```

### Informal statement
For any finite set `s` of points in the real plane, there exists a real number `t` such that the set obtained by rotating `s` by `t` radians is pairwise separate in the second coordinate (i.e., no two distinct points in the rotated set have the same y-coordinate).

### Mathematical insight
This theorem states that given any finite set of points in the plane, we can find a rotation such that no two points in the rotated set have the same y-coordinate. This is useful when trying to project higher-dimensional data onto a line in a way that preserves information. The key idea is that there are only finitely many "bad" rotations where two distinct points coincide in their y-coordinate. Since the set of possible rotations is infinite, we can always find a "good" rotation.

### Informal sketch
The proof proceeds by showing that the set of angles `t` in the interval `[0, 2*pi)` for which a rotation by `t` causes two distinct points in `s` to have the same y-coordinate is finite. Thus the complement in `[0, 2*pi)` of the union of all these sets corresponding to pairs of distinct points in `s` is infinite.

- Start by stripping off the universal quantifier and implication.
- Introduce a subgoal to show that the set of rotation angles that cause the y-coordinates of the rotations of some pair of distinct points in s to coincide, excluding `t` outside the interval `[0, 2*pi)`, is infinite: `INFINITE ({t | &0 <= t /\ t < &2 * pi} DIFF UNIONS (IMAGE (\(x,y). {t | &0 <= t /\ t < &2 * pi /\ (rotate2d t x)$2 = (rotate2d t y)$2}) ({(x,y) | x IN s /\ y IN s /\ ~(x = y)})))`
- Apply `INFINITE_DIFF_FINITE`, which states that if `A` is infinite and `B` is finite, then `A DIFF B` is infinite. Rewrite `INFINITE`, `FINITE_REAL_INTERVAL`, and `REAL_NOT_LE` to show `{t | &0 <= t /\ t < &2 * pi}` is infinite. Then establish that `UNIONS (IMAGE (\(x,y). {t | &0 <= t /\ t < &2 * pi /\ (rotate2d t x)$2 = (rotate2d t y)$2}) ({(x,y) | x IN s /\ y IN s /\ ~(x = y)}))` is finite.
 - To show that last term being finite, rewrite using `FINITE_UNIONS`, which reduces our task to showing that `IMAGE (\(x,y). {t | &0 <= t /\ t < &2 * pi /\ (rotate2d t x)$2 = (rotate2d t y)$2}) ({(x,y) | x IN s /\ y IN s /\ ~(x = y)})` is finite.
   - Rewrite this using `FINITE_IMAGE` and `FINITE_SUBSET` to reduce the task to showing `{(x,y) | x IN s /\ y IN s}` is finite.
   - The last step is handled using `FINITE_PRODUCT_DEPENDENT` and set operations.
   - Then use `DISTINGUISHING_ROTATION_EXISTS_PAIR` to demonstrate the necessary property within the set.
- From there, show that if s is finite and not empty, there exists a `t` in `[0, 2*pi)` such that, for all pairs of distinct points x and y in s, the y-coordinates of `rotate2d t x` and `rotate2d t y` differ.
  - This step uses `MONO_EXISTS` to introduce the quantifier `t` inside the set expression and `pairwise`, `IMP_CONJ`, `RIGHT_FORALL_IMP_THM`, and `FORALL_IN_IMAGE` to clarify the structure before finishing with an application of `MESON_TAC`.
  - Rewrite with `GSYM MEMBER_NOT_EMPTY`, `IN_DIFF`, `IN_ELIM_THM`,  `UNIONS_IMAGE; EXISTS_IN_GSPEC`, `pairwise; IN_ELIM_THM`, `IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE`, finally `ROTATE2D_EQ`.

### Dependencies

**Theorems/Definitions:**
- `FINITE`
- `INFINITE`
- `pairwise`
- `rotate2d`
- `IMAGE`
- `UNIONS`
- `INFINITE_DIFF_FINITE`
- `FINITE_REAL_INTERVAL`
- `REAL_NOT_LE`
- `PI_POS`
- `FINITE_UNIONS`
- `FINITE_IMAGE`
- `FINITE_SUBSET`
- `FINITE_PRODUCT_DEPENDENT`
- `FORALL_IN_IMAGE`
- `FORALL_IN_GSPEC`
- `DISTINGUISHING_ROTATION_EXISTS_PAIR`
- `FINITE_EMPTY`
- `GSYM MEMBER_NOT_EMPTY`
- `IN_DIFF`
- `IN_ELIM_THM`
- `MONO_EXISTS`
- `EXISTS_IN_GSPEC`
- `IMP_CONJ`
- `RIGHT_FORALL_IMP_THM`
- `ROTATE2D_EQ`

### Porting notes (optional)
- The proof relies heavily on set theory reasoning. The porter should be aware of the corresponding set theory libraries and tactics of the target proof assistant.
- The use of `MESON_TAC` suggests reliance on a first-order logic automated prover. The porter may need to manually decompose the proof or replace it with another automated tactic if `MESON_TAC` is not available or performs poorly.
- The definition of `rotate2d` and the properties used in rewrite steps are important and should be ported accurately.


---

## DISTINGUISHING_ROTATION_EXISTS_POLYGON

### Name of formal statement
DISTINGUISHING_ROTATION_EXISTS_POLYGON

### Type of the formal statement
theorem

### Formal Content
```hol
let DISTINGUISHING_ROTATION_EXISTS_POLYGON = prove
 (`!p:(real^2)list.
        ?f q. (?g. orthogonal_transformation g /\ f = MAP g) /\
              (!x y. MEM x q /\ MEM y q /\ ~(x = y) ==> ~(x$2 = y$2)) /\
              f q = p`,
  GEN_TAC THEN MP_TAC(ISPEC
   `set_of_list(p:(real^2)list)` DISTINGUISHING_ROTATION_EXISTS) THEN
  REWRITE_TAC[FINITE_SET_OF_LIST; pairwise] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_SET_OF_LIST; ROTATE2D_EQ] THEN
  REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `MAP (rotate2d(--t))` THEN
  EXISTS_TAC `MAP (rotate2d t) p` THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF; GSYM ROTATE2D_ADD] THEN
  REWRITE_TAC[REAL_ADD_LINV; ROTATE2D_ZERO; MAP_ID] THEN
  CONJ_TAC THENL [MESON_TAC[ORTHOGONAL_TRANSFORMATION_ROTATE2D]; ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST; SET_OF_LIST_MAP] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST; ROTATE2D_EQ] THEN ASM_MESON_TAC[]);;
```

### Informal statement
For every list `p` of points in the real plane, there exist a list of points `q` and a function `f` such that:
1.  `f` is the result of mapping an orthogonal transformation `g` over `q` (i.e., `f = MAP g`),
2.  For all distinct points `x` and `y` in `q`, their y-coordinates are distinct, and
3.  `f q = p`.

### Mathematical insight
This theorem states that any list of points in the plane can be obtained by applying a rotation to a list of points which have distinct y-coordinates. This is useful because certain algorithms or proofs might be easier to perform on point sets in such *general position*, and this theorem allows us to extend those results to arbitrary point sets.

### Informal sketch
The proof proceeds as follows:
- Start with `DISTINGUISHING_ROTATION_EXISTS` after specializing to `set_of_list(p)`. The theorem implies that every finite set can be rotated to have unique y-coordinates.
- Rewrite using lemmas related to finite sets and pairwise distinct elements.
- Assume `t` is any real number, and then choose `t` such that the rotation of `set_of_list(p)` by `-t` has distinct y coordinates.
- Instantiate the existentially quantified `f` with `MAP (rotate2d (--t))` and `q` with `MAP (rotate2d t) p`.
- Show `f q = p` using properties of function composition (`o`), `rotate2d`, and `MAP`. `MAP (rotate2d(-t)) (MAP(rotate2d(t)) p)` simplifies to `p`. 
- Show that `f` can be written as orthogonal transformation `g`, namely `rotate2d(--t)`, using `ORTHOGONAL_TRANSFORMATION_ROTATE2D`.
- Show that any two distinct elements in `q` have distinct y-coordinates, by first showing `q` is equivalent to `set_of_list q`, then simplifying the membership predicate using `ROTATE2D_EQ`

### Dependencies
#### Theorems
- `DISTINGUISHING_ROTATION_EXISTS`
- `RIGHT_FORALL_IMP_THM`
- `ORTHOGONAL_TRANSFORMATION_ROTATE2D`
- `RIGHT_IMP_FORALL_THM`

#### Definitions
- `orthogonal_transformation`
- `MAP`
- `MEM`
- `rotate2d`
- `o_DEF`
- `FINITE_SET_OF_LIST`
- `pairwise`
- `IN_SET_OF_LIST`
- `ROTATE2D_EQ`
- `GSYM CONJ_ASSOC`
- `GSYM MAP_o`
- `GSYM ROTATE2D_ADD`
- `REAL_ADD_LINV`
- `ROTATE2D_ZERO`
- `MAP_ID`
- `SET_OF_LIST_MAP`

### Porting notes
- The proof makes heavy use of rewriting and assumption simplification.
- The `MESON_TAC` calls indicate that classical reasoning (specifically, first-order logic with equality) is actively used.
- The management of sets (using `set_of_list`) would need to be adapted based on how sets are represented and reasoned about in the target proof assistant.
- The porting needs to ensure that the definition of `orthogonal_transformation` and `rotate2d` are consistent with the original HOL Light definition.


---

## POLYGON_CHOP_IN_TWO

### Name of formal statement
POLYGON_CHOP_IN_TWO

### Type of the formal statement
theorem

### Formal Content
```hol
let POLYGON_CHOP_IN_TWO = prove
 (`!p:(real^2)list.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p
        ==> ?a b. ~(a = b) /\ MEM a p /\ MEM b p /\
                  segment(a,b) SUBSET inside(path_image(polygonal_path p))`,
  let wlog_lemma = MESON[]
   `(!x. ?f:A->A y. transform f /\ nice y /\ f y = x)
    ==> !P. (!f x. transform f ==> (P(f x) <=> P x)) /\
            (!x. nice x ==> P x)
            ==> !x. P x` in
  let between_lemma = prove
   (`!a c u v m:real^N.
          collinear {a,c,u,v,m} /\ m IN segment[u,v] /\ m IN segment(a,c)
          ==> u IN segment(a,c) \/ v IN segment(a,c) \/
              segment[a,c] SUBSET segment[u,v]`,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET; LEFT_IMP_EXISTS_THM; EMPTY_SUBSET] THEN
    MAP_EVERY X_GEN_TAC [`origin:real^N`; `dir:real^N`] THEN
    GEOM_ORIGIN_TAC `origin:real^N` THEN
    REWRITE_TAC[AFFINE_HULL_2; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `dir:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; SEGMENT_REFL; SUBSET_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_SEGMENT] THEN
    ASM_SIMP_TAC[SEGMENT_SCALAR_MULTIPLE; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
    REAL_ARITH_TAC) in
  MATCH_MP_TAC(MATCH_MP wlog_lemma DISTINGUISHING_ROTATION_EXISTS_POLYGON) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MESON[] `(!x y. (?z. P z /\ x = f z) ==> Q x y) <=>
                         (!z y. P z ==> Q (f z) y)`] THEN
    REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
    GEOM_TRANSFORM_TAC [];
    ALL_TAC] THEN
  X_GEN_TAC `q:(real^2)list` THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?b:real^2. MEM b q /\ !d. MEM d q ==> b$2 <= d$2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\x:real^2. x$2) (set_of_list q)`
        INF_FINITE) THEN
    SIMP_TAC[FINITE_SET_OF_LIST; FINITE_IMAGE] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; SET_OF_LIST_EQ_EMPTY] THEN
    UNDISCH_TAC `5 <= LENGTH(q:(real^2)list)` THEN
    ASM_CASES_TAC `q:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE; LEFT_AND_EXISTS_THM; IN_SET_OF_LIST] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p:(real^2)list.
        EL 1 p = b /\ LAST p = HD p /\
        LENGTH p = LENGTH q /\ set_of_list p = set_of_list q /\
        path_image(polygonal_path p) = path_image(polygonal_path q) /\
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p)`
  MP_TAC THENL
   [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_1 THEN EXISTS_TAC `q:(real^2)list` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(q:(real^2)list)) =
       pathstart(polygonal_path q)`;
      `5 <= LENGTH(q:(real^2)list)`] THEN
    ASM_CASES_TAC `q:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(q:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `a IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_THEN `pathfinish(polygonal_path(q:(real^2)list)) =
                pathstart(polygonal_path q)` (K ALL_TAC) THEN
  UNDISCH_THEN `simple_path(polygonal_path(q:(real^2)list))` (K ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(real^2)list` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [EXTENSION] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> REWRITE_TAC[GSYM th] THEN
              RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `MEM (b:real^2) r` (K ALL_TAC) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^2` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b':real^2` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `c:real^2` THEN X_GEN_TAC `p:(real^2)list` THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  REWRITE_TAC[num_CONV `1`; EL; HD; TL] THEN
  ASM_CASES_TAC `b':real^2 = b` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `5 <= SUC(SUC(SUC n)) <=> ~(n = 0) /\ 2 <= n`] THEN
  ASM_CASES_TAC `p:(real^2)list = []` THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS; LAST; NOT_CONS_NIL] THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real^2`) THEN
  REWRITE_TAC[MESON[MEM] `MEM b (CONS a (CONS b l))`] THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`linepath(a:real^2,b)`;
    `polygonal_path(CONS (b:real^2) (CONS c p))`]
   SIMPLE_PATH_JOIN_IMP) THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
  REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
  REWRITE_TAC[ARC_LINEPATH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN MP_TAC th)
                MP_TAC) THEN
  SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[ARC_LINEPATH_EQ; GSYM CONJ_ASSOC; PATH_IMAGE_LINEPATH] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           HD; NOT_CONS_NIL] THEN
  REWRITE_TAC[SET_RULE `s INTER (t UNION u) SUBSET v <=>
                        s INTER t SUBSET v /\ s INTER u SUBSET v`] THEN
  ASM_CASES_TAC `a:real^2 = c` THENL
   [DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_SYM; INTER_ACI] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ_ALT]
        FINITE_SUBSET)) THEN
    REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `CONS (b:real^2) (CONS c p)`
    ARC_POLYGONAL_PATH_IMP_DISTINCT) THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
  REWRITE_TAC[PAIRWISE; ALL] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REWRITE_TAC[MESON[] `(!x. P x ==> ~(a = x)) <=> ~(P a)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^2)$2 < (a:real^2)$2 /\
                (b:real^2)$2 < (c:real^2)$2 /\
                (!v. MEM v p ==> (b:real^2)$2 < (v:real^2)$2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^2,b,c}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_BETWEEN_CASES; BETWEEN_IN_SEGMENT] THEN
    SUBGOAL_THEN `FINITE(segment[a:real^2,b] INTER segment[b,c])` MP_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{a:real^2,b}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `segment[a:real^2,b] INTER segment[b,c] = segment[a,b]`
       (fun th -> ASM_REWRITE_TAC[FINITE_SEGMENT; th]) THEN
      REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`] THEN
      ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT];
      DISCH_TAC THEN UNDISCH_TAC `b IN segment[c:real^2,a]` THEN
      ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT] THEN
      ASM_REWRITE_TAC[IN_SEGMENT; NOT_IN_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$2`) THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&1 - u) * b < (&1 - u) * c /\ u * b < u * a
        ==> ~(b = (&1 - u) * c + u * a)`) THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_SUB_LT];
      SUBGOAL_THEN `segment[a:real^2,b] INTER segment[b,c] = segment[b,c]`
       (fun th -> ASM_REWRITE_TAC[FINITE_SEGMENT; th]) THEN
      REWRITE_TAC[SET_RULE `s INTER t = t <=> t SUBSET s`] THEN
      ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
         e <= (a:real^2)$2 - (b:real^2)$2 /\
         e <= (c:real^2)$2 - (b:real^2)$2 /\
         !v. MEM v p ==> e <= (v:real^2)$2 - (b:real^2)$2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\v. (v:real^2)$2 - (b:real^2)$2)
                        (set_of_list(CONS a (CONS b (CONS c p)))
                          DELETE b)`
                INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_SET_OF_LIST; FINITE_IMAGE; FINITE_DELETE] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[set_of_list; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[IN_DELETE; IN_INSERT];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
    ASM_REWRITE_TAC[set_of_list; FORALL_IN_INSERT; IMP_CONJ; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^2` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_SET_OF_LIST] THEN
    DISCH_TAC THEN EXISTS_TAC `(d:real^2)$2 - (b:real^2)$2` THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; IN_SET_OF_LIST]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a':real^2 = (&1 - e / (a$2 - b$2)) % b + e / (a$2 - b$2) % a`;
    `c':real^2 = (&1 - e / (c$2 - b$2)) % b + e / (c$2 - b$2) % c`] THEN
  SUBGOAL_THEN
   `a' IN segment[b:real^2,a] /\ c' IN segment[b,c]`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + u % b = (&1 - v) % a + v % b <=>
      (u - v) % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_SUB_0] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ p /\ q`] THEN
    REWRITE_TAC[UNWIND_THM1] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV; REAL_SUB_LE;
                 REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':real^2 = b) /\ ~(c':real^2 = b)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + u % b = a <=> u % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a':real^2,b,c'}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[VECTOR_ARITH `((&1 - u) % b + u % a) - b = u % (a - b)`] THEN
    REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL; DOT_LMUL; DOT_RMUL] THEN
    MATCH_MP_TAC(REAL_FIELD
     `~(a = &0) /\ ~(c = &0)
      ==> (a * c * x) pow 2 = (a * a * y) * (c * c * z)
          ==> x pow 2 = y * z`) THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':real^2 = c')` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear{a':real^2,b,c'}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent{a':real^2,b,c'}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3]; ALL_TAC] THEN
  MP_TAC(ISPEC `{a':real^2,b,c'}` INTERIOR_CONVEX_HULL_EQ_EMPTY) THEN
  REWRITE_TAC[DIMINDEX_2; HAS_SIZE; ARITH; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex hull {a,b,c} INTER {x:real^2 | x$2 - b$2 <= e} =
                convex hull {a',b,c'}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
      REWRITE_TAC[CONVEX_HULL_3_ALT] THEN
      REWRITE_TAC[SUBSET; IN_INTER; FORALL_IN_GSPEC; IMP_CONJ] THEN
      REWRITE_TAC[IN_ELIM_THM; VECTOR_ARITH
       `a + x:real^N = a + y <=> x = y`] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN
      REPLICATE_TAC 3 DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
      REWRITE_TAC[VECTOR_ARITH
       `((&1 - u) % b + u % a) - b:real^N = u % (a - b)`] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[REAL_ADD_SUB; VECTOR_SUB_COMPONENT] THEN STRIP_TAC THEN
      EXISTS_TAC `(s * ((a:real^2)$2 - (b:real^2)$2)) / e` THEN
      EXISTS_TAC `(t * ((c:real^2)$2 - (b:real^2)$2)) / e` THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_SUB_LT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_ARITH `a / e + b / e:real = (a + b) / e`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC(REAL_FIELD
       `y < x /\ &0 < e ==> s = (s * (x - y)) / e * e / (x - y)`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[HULL_INC; IN_INSERT; REAL_SUB_REFL; REAL_LT_IMP_LE] THEN
      SIMP_TAC[REAL_LE_SUB_RADD; CONVEX_INTER; CONVEX_HALFSPACE_COMPONENT_LE;
               CONVEX_CONVEX_HULL] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `a' IN segment[b:real^2,a]` THEN
        SPEC_TAC(`a':real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        EXPAND_TAC "a'";
        UNDISCH_TAC `c' IN segment[b:real^2,c]` THEN
        SPEC_TAC(`c':real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        EXPAND_TAC "c'"] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[REAL_ARITH
       `(&1 - u) * b + u * a <= e + b <=> (a - b) * u <= e`] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_SUB_LT] THEN
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior(convex hull {a,b,c}) INTER {x:real^2 | x$2 - b$2 < e} =
    interior(convex hull {a',b,c'})`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_SUB_RADD; GSYM INTERIOR_HALFSPACE_COMPONENT_LE] THEN
    ASM_REWRITE_TAC[GSYM INTERIOR_INTER; GSYM REAL_LE_SUB_RADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real^2. d IN interior(convex hull {a',b,c'}) /\ ~(d$1 = b$1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(interior(convex hull {a':real^2,b,c'}) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^2)$1 = (b:real^2)$1` THENL
     [ALL_TAC; EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o SPEC `x + k / &2 % basis 1:real^2`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x,x + e) = norm e`] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; ARITH] THEN
      UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    EXISTS_TAC `x + k / &2 % basis 1:real^2` THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_GE_1; ARITH; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> ~(b + k / &2 = b)`] THEN
    REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `k / &2` THEN
    ASM_REWRITE_TAC[REAL_HALF; SUBSET] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_BALL] THEN MATCH_MP_TAC(NORM_ARITH
     `!a. dist(x + a,y) < k / &2 /\ norm(a) = k / &2 ==> dist(x,y) < k`) THEN
    EXISTS_TAC `k / &2 % basis 1:real^2` THEN ASM_REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `path_image(polygonal_path(CONS a (CONS b (CONS c p))))
     SUBSET {x:real^2 | x$2 >= b$2}`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC
     `convex hull(set_of_list(CONS (a:real^2) (CONS b (CONS c p))))` THEN
    SIMP_TAC[PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL; NOT_CONS_NIL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE] THEN
    REWRITE_TAC[set_of_list; INSERT_SUBSET; IN_ELIM_THM; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[SUBSET; IN_SET_OF_LIST; real_ge; IN_ELIM_THM; REAL_LT_IMP_LE;
                 REAL_LE_REFL];
    GEN_REWRITE_TAC LAND_CONV [SUBSET]
```
---

## PICK

### Name of formal statement
PICK

### Type of the formal statement
theorem

### Formal Content
```
let PICK = prove
 (`!p:(real^2)list.
        (!x. MEM x p ==> integral_vector x) /\
        simple_path (polygonal_path p) /\
        pathfinish (polygonal_path p) = pathstart (polygonal_path p)
        ==> measure(inside(path_image(polygonal_path p))) =
                &(CARD {x | x IN inside(path_image(polygonal_path p)) /\
                            integral_vector x}) +
                &(CARD {x | x IN path_image(polygonal_path p) /\
                            integral_vector x}) / &2 - &1`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN DISJ_CASES_TAC
  (ARITH_RULE `LENGTH(p:(real^2)list) <= 4 \/ 5 <= LENGTH p`) THENL
   [UNDISCH_TAC `LENGTH(p:(real^2)list) <= 4` THEN
    POP_ASSUM(K ALL_TAC) THEN SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
    X_GEN_TAC `a:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
    X_GEN_TAC `b:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ;
                  PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `c:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REPLICATE_TAC 4 (DISCH_THEN(K ALL_TAC)) THEN
      REWRITE_TAC[polygonal_path] THEN
      REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH] THEN
      ASM_CASES_TAC `c:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                   PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[ARC_LINEPATH_EQ] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
      SUBST1_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
      REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
      ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    X_GEN_TAC `d:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REPLICATE_TAC 5 (DISCH_THEN(K ALL_TAC));
      REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC(SUC(SUC(SUC(SUC n)))) <= 4)`]] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; set_of_list] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_CASES_TAC `d:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATH_IMAGE_JOIN; PATHSTART_LINEPATH;
      ARC_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN REWRITE_TAC[INSIDE_OF_TRIANGLE] THEN
    REWRITE_TAC[GSYM FRONTIER_OF_TRIANGLE] THEN
    SIMP_TAC[MEASURE_INTERIOR; NEGLIGIBLE_CONVEX_FRONTIER;
             CONVEX_CONVEX_HULL; FINITE_IMP_BOUNDED_CONVEX_HULL;
             FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_SIMP_TAC[PICK_TRIANGLE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARC_LINEPATH_EQ] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[UNION_OVER_INTER] THEN
    REWRITE_TAC[UNION_SUBSET] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment [c,a] = segment[b,c] \/
      segment[b,c] INTER segment [c,a] = segment[c,a] \/
      segment[a,b] INTER segment [b,c] = segment[b,c]`
    (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`;
                  SET_RULE `s INTER t = t <=> t SUBSET s`] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_BETWEEN_CASES]) THEN
      REWRITE_TAC[SUBSET_SEGMENT; BETWEEN_IN_SEGMENT; ENDS_IN_SEGMENT] THEN
      REWRITE_TAC[SEGMENT_SYM; DISJ_ACI];
      UNDISCH_TAC `segment [b,c] SUBSET {c:real^2}`;
      UNDISCH_TAC `segment [c,a] SUBSET {c:real^2}`;
      UNDISCH_TAC `segment [b,c] SUBSET {a:real^2, b}`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `p:(real^2)list` POLYGON_CHOP_IN_TWO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`;`b:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?p':(real^2)list.
        HD p' = a /\
        LENGTH p' = LENGTH p /\
        path_image(polygonal_path p') = path_image(polygonal_path p) /\
        set_of_list p' = set_of_list p /\
        simple_path(polygonal_path p') /\
        pathfinish(polygonal_path p') = pathstart(polygonal_path p')`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_0 THEN
    EXISTS_TAC `p:(real^2)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 3 <= p`] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(p:(real^2)list)) =
       pathstart(polygonal_path p)`;
      `5 <= LENGTH(p:(real^2)list)`] THEN
    ASM_CASES_TAC `p:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(p:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `a IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. MEM x p <=> MEM x p'`
   (fun th -> REWRITE_TAC[th] THEN
              RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
  MAP_EVERY (C UNDISCH_THEN (SUBST_ALL_TAC o SYM))
   [`set_of_list(p':(real^2)list) = set_of_list p`;
    `path_image(polygonal_path(p':(real^2)list)) =
     path_image (polygonal_path p)`;
    `LENGTH(p':(real^2)list) = LENGTH(p:(real^2)list)`] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`simple_path(polygonal_path(p:(real^2)list))`;
    `pathfinish(polygonal_path(p:(real^2)list)) =
     pathstart(polygonal_path p)`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`p':(real^2)list`,`p:(real^2)list`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?q r. 2 <= LENGTH q /\ 2 <= LENGTH r /\
          LENGTH q + LENGTH r = LENGTH p + 1 /\
          set_of_list q UNION set_of_list r = set_of_list p /\
          pathstart(polygonal_path q) = pathstart(polygonal_path p) /\
          pathfinish(polygonal_path q) = (b:real^2) /\
          pathstart(polygonal_path r) = b /\
          pathfinish(polygonal_path r) = pathfinish(polygonal_path p) /\
          simple_path(polygonal_path q ++ polygonal_path r) /\
          path_image(polygonal_path q ++ polygonal_path r) =
          path_image(polygonal_path p)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `simple_path(polygonal_path p) /\
      2 <= LENGTH p /\ MEM (b:real^2) p /\
      ~(pathstart(polygonal_path p) = b) /\
      ~(pathfinish(polygonal_path p) = b)`
    MP_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 2 <= p`] THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; CONJ_ASSOC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM];
      POP_ASSUM_LIST(K ALL_TAC)] THEN
    WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `x:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  MEM] THEN
      MESON_TAC[];
      REWRITE_TAC[LENGTH; ARITH]] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `l:(real^2)list`] THEN
    REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN DISCH_TAC THEN
    REWRITE_TAC[polygonal_path] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `a:real^2 = b` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `x:real^2 = b` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl) THEN STRIP_TAC THEN
      EXISTS_TAC `[a:real^2;b]` THEN
      EXISTS_TAC `CONS (b:real^2) (CONS y l)` THEN
      ASM_REWRITE_TAC[polygonal_path; LENGTH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REPEAT(CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[set_of_list] THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (x:real^2) (CONS y l)`) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC n`] THEN ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= SUC(SUC n)`] THEN
      ONCE_REWRITE_TAC[MEM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SIMPLE_PATH_JOIN_IMP)) THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      SIMP_TAC[PATHFINISH_LINEPATH; ARC_IMP_SIMPLE_PATH];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:(real^2)list`; `r:(real^2)list`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`CONS (a:real^2) q`; `r:(real^2)list`] THEN
    ASM_REWRITE_TAC[LENGTH; NOT_CONS_NIL; HD] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[set_of_list; SET_RULE
       `(a INSERT s) UNION t = a INSERT (s UNION t)`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `pathfinish(polygonal_path q) = (b:real^2)` THEN
      REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; LAST; NOT_CONS_NIL] THEN
      UNDISCH_TAC `2 <= LENGTH(q:(real^2)list)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `polygonal_path(CONS (a:real^2) q) =
      linepath(a,x) ++ polygonal_path q`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`pathstart(polygonal_path q) =
         pathstart(polygonal_path (CONS (x:real^2) (CONS y l)))`;
        `2 <= LENGTH(q:(real^2)list)`] THEN
      SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
      GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
      SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pathstart(polygonal_path(CONS x (CONS y l))) = (x:real^2)`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]; ALL_TAC] THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) SIMPLE_PATH_ASSOC o snd) THEN
      ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `simple_path(linepath(a:real^2,x) ++
                               polygonal_path (CONS x (CONS y l)))` THEN
      ASM_CASES_TAC `pathfinish(polygonal_path r) = (a:real^2)` THENL
       [SUBGOAL_THEN
         `pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHFINISH_LINEPATH;
                     PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH] THEN
        STRIP_TAC THEN MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        ASM_MESON_TAC[ARC_LINEPATH_EQ];
        SUBGOAL_THEN
         `~(pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a)`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_EQ_ARC; PATHSTART_JOIN; PATHSTART_LINEPATH;
                     PATHFINISH_JOIN] THEN
        ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN] THEN
        REWRITE_TAC[ARC_LINEPATH_EQ] THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `arc(polygonal_path q ++ polygonal_path r:real^1->real^2)`
        MP_TAC THENL
         [ALL_TAC;
          ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN]] THEN
        MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
        REWRITE_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL]];
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD;
               PATHSTART_POLYGONAL_PATH] THEN
      UNDISCH_THEN
       `path_image(polygonal_path q ++ polygonal_path r) =
        path_image(polygonal_path(CONS (x:real^2) (CONS y l)))`
       (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart(polygonal_path p) = (a:real^2)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `5 <= LENGTH(p:(real^2)list)` THEN
    REWRITE_TAC[PATHSTART_POLYGONAL_PATH] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
    ALL_TAC] THEN
  UNDISCH_THEN `pathfinish (polygonal_path p) = (a:real^2)` SUBST_ALL_TAC THEN
  UNDISCH_THEN `path_image(polygonal_path q ++ polygonal_path r):real^2->bool =
                path_image(polygonal_path p)` (SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `(!x:real^2. MEM x q ==> integral_vector x) /\
    (!x:real^2. MEM x r ==> integral_vector x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST; IN_UNION] THEN
    UNDISCH_THEN
     `(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p`
     (SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  ABBREV_TAC `n = LENGTH(p:(real^2)list)` THEN
  SUBGOAL_THEN `integral_vector(a:real^2) /\ integral_vector(b:real^2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`!x:real^2. MEM x p ==> integral_vector x`;
    `MEM (a:real^2) p`;
    `MEM (b:real^2) p`;
    `HD p = (a:real^2)`;
    `(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p`;
    `simple_path(polygonal_path p :real^1->real^2)`] THEN
  SUBGOAL_THEN `3 <= LENGTH(q:(real^2)list)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a0:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a1:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; ARITH_RULE `3 <= SUC(SUC(SUC n))`] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `a0:real^2 = a` SUBST_ALL_TAC THEN
    UNDISCH_THEN `a1:real^2 = b` SUBST_ALL_TAC THEN
    UNDISCH_TAC `segment(a:real^2,b) SUBSET
                 inside(path_image(linepath(a,b) ++ polygonal_path r))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s' UNION t) INTER (s' UNION t) = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(s' UNION t))`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    ASM_REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_EQ_EMPTY];
    UNDISCH_THEN `2 <= LENGTH(q:(real^2)list)` (K ALL_TAC)] THEN
  SUBGOAL_THEN `3 <= LENGTH(r:(real^2)list)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a0:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a1:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; ARITH_RULE `3 <= SUC(SUC(SUC n))`] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `a0:real^2 = b` SUBST_ALL_TAC THEN
    UNDISCH_THEN `a1:real^2 = a` SUBST_ALL_TAC THEN
    UNDISCH_TAC `segment(a:real^2,b) SUBSET
                 inside(path_image(polygonal_path q ++ linepath(b,a)))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(t UNION s') INTER (t UNION s') = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(t UNION s'))`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    ASM_REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_EQ_EMPTY];
    UNDISCH_THEN `2 <= LENGTH(r:(real^2)list)` (K ALL_TAC)] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(ISPEC `CONS (a:real^2) r` th) THEN
    MP_TAC(ISPEC `CONS (b:real^2) q` th)) THEN
  REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (b:real^2) q) = linepath(b,a) ++ polygonal_path q`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
    SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[PATHSTART_LINEPATH]] THEN
    UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {b,a}`)) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s UNION t) INTER (s UNION t) = {}
      ==> s INTER inside(s UNION t) = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    STRIP_TAC] THEN
  REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (a:real^2) r) = linepath(a,b) ++ polygonal_path r`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
    MATCH_MP_TAC list_IN
```
---

