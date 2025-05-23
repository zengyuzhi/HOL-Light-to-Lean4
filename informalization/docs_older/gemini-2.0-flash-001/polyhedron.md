# polyhedron.ml

## Overview

Number of statements: 58

`polyhedron.ml` formalizes Jim Lawrence's proof of Euler's relation for polyhedra. It builds upon the `polytope.ml` development of polytopes and uses results from `binomial.ml`, `inclusion_exclusion.ml`, and `combinations.ml`. The file culminates in a formal proof of Euler's relation.


## hyperplane_side

### Name of formal statement
hyperplane_side

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let hyperplane_side = new_definition
 `hyperplane_side (a,b) (x:real^N) = real_sgn (a dot x - b)`;;
```

### Informal statement
The function `hyperplane_side` applied to a hyperplane defined by a normal vector `a` and a scalar `b`, and a point `x` in `real^N`, is defined as the real sign of the result of subtracting `b` from the dot product of `a` and `x`.

### Informal sketch
The definition of `hyperplane_side (a, b) x` computes which side of the hyperplane defined by `a` and `b` the point `x` lies on. The hyperplane is given by the equation `a · x = b`, where `a` is the normal vector to the hyperplane. The function calculates `a · x - b` and then takes the sign of the result using `real_sgn`. The `real_sgn` function returns -1 if the input is negative, 0 if the input is zero, and 1 if the input is positive. Thus, the `hyperplane_side` function returns -1 if `x` is on the negative side of the hyperplane, 0 if `x` lies on the hyperplane, and 1 if `x` is on the positive side of the hyperplane.

### Mathematical insight
This definition provides a way to classify points in relation to a hyperplane. It is a fundamental concept in linear algebra and geometry, used to determine on which side of a dividing hyperplane a given point lies. This is crucial in applications like linear programming, computational geometry, and machine learning (e.g., support vector machines).

### Dependencies
- Definition: `real_sgn`
- Definition: `dot`

### Porting notes (optional)
- The `real^N` type in HOL Light will need to mapped to an appropriate vector space type in other provers such as `real ^ nat` in Isabelle/HOL.
- The dot product denoted by `dot` will likely have a different syntax in other proof assistants.
- The `real_sgn` function may be named differently, such as `signum` or `sgn`.


---

## hyperplane_equiv

### Name of formal statement
hyperplane_equiv

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let hyperplane_equiv = new_definition
 `hyperplane_equiv A x y <=>
        !h. h IN A ==> hyperplane_side h x = hyperplane_side h y`;;
```
### Informal statement
For any hyperplane arrangement `A` and any points `x` and `y`, `hyperplane_equiv A x y` holds if and only if for all hyperplanes `h` in `A`, the side of `h` on which `x` lies is equal to the side of `h` on which `y` lies.

### Informal sketch
- The definition introduces an equivalence relation on points with respect to a hyperplane arrangement. Two points are defined to be equivalent if they lie on the same side of every hyperplane in the arrangement.
- There is no proof sketch to provide, since this is a definition. It simply states a condition for two points to be equivalent based on the hyperplanes in the arrangement.

### Mathematical insight
The definition captures the notion of points being "in the same cell" of the space partitioned by the hyperplane arrangement. Two points are equivalent if they cannot be separated by any hyperplane in the arrangement. The equivalence classes correspond to the regions created by the arrangement.

### Dependencies
- `hyperplane_side`
- `IN`


---

## HYPERPLANE_EQUIV_REFL

### Name of formal statement
HYPERPLANE_EQUIV_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_REFL = prove
 (`!A x. hyperplane_equiv A x x`,
  REWRITE_TAC[hyperplane_equiv]);;
```

### Informal statement
For any set `A` of real numbers and any real number `x`, `x` is equivalent to itself with respect to `A` in the sense of the `hyperplane_equiv` relation.

### Informal sketch
The theorem states that the `hyperplane_equiv` relation is reflexive. The proof is a direct application of the definition of `hyperplane_equiv` using `REWRITE_TAC`.

### Mathematical insight
This theorem establishes a fundamental property of the `hyperplane_equiv` relation; namely, that it is reflexive. This property is expected of any equivalence relation.

### Dependencies
- Definition: `hyperplane_equiv`


---

## HYPERPLANE_EQUIV_SYM

### Name of formal statement
HYPERPLANE_EQUIV_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_SYM = prove
 (`!A x y. hyperplane_equiv A x y <=> hyperplane_equiv A y x`,
  REWRITE_TAC[hyperplane_equiv; EQ_SYM_EQ]);;
```
### Informal statement
For all sets `A` and for all `x` and `y`, `hyperplane_equiv A x y` if and only if `hyperplane_equiv A y x`.

### Informal sketch
- The proof relies on rewriting with the definition of `hyperplane_equiv` and the symmetry of equality (`EQ_SYM_EQ`).
- The goal is to prove the equivalence `hyperplane_equiv A x y <=> hyperplane_equiv A y x`.
- The definition of `hyperplane_equiv` is unfolded.
- The symmetry of equality is applied.

### Mathematical insight
This theorem states that the `hyperplane_equiv` relation is symmetric. In other words, if `x` is hyperplane equivalent to `y` with respect to `A`, then `y` is hyperplane equivalent to `x` with respect to `A`. This is an expected property of an equivalence relation.

### Dependencies
- Definitions: `hyperplane_equiv`
- Theorems: `EQ_SYM_EQ`


---

## HYPERPLANE_EQUIV_TRANS

### Name of formal statement
HYPERPLANE_EQUIV_TRANS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_TRANS = prove
 (`!A x y z.
        hyperplane_equiv A x y /\ hyperplane_equiv A y z
        ==> hyperplane_equiv A x z`,
  REWRITE_TAC[hyperplane_equiv] THEN MESON_TAC[]);;
```
### Informal statement
For all `A`, `x`, `y`, and `z`, if `x` is hyperplane-equivalent to `y` with respect to `A`, and `y` is hyperplane-equivalent to `z` with respect to `A`, then `x` is hyperplane-equivalent to `z` with respect to `A`.

### Informal sketch
The proof relies on the transitivity of equality.
- The proof starts by rewriting with the definition of `hyperplane_equiv`.
- The rest of the proof is handled by the MESON tactic.

### Mathematical insight
This theorem establishes the transitivity property of the `hyperplane_equiv` relation. Two points are hyperplane-equivalent if they lie on the same side of the hyperplane. Transitivity is a natural property to expect of such a relation since if `x` and `y` are on the same side of the hyperplane and `y` and `z` are on the same side, then it follows that `x` and `z` must also be on the same side.

### Dependencies
*Definitions:*
- `hyperplane_equiv`


---

## HYPERPLANE_EQUIV_UNION

### Name of formal statement
HYPERPLANE_EQUIV_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_UNION = prove
 (`!A B x y. hyperplane_equiv (A UNION B) x y <=>
                hyperplane_equiv A x y /\ hyperplane_equiv B x y`,
  REWRITE_TAC[hyperplane_equiv; IN_UNION] THEN MESON_TAC[]);;
```
### Informal statement
For all sets `A` and `B` of real vector spaces, and for all real vectors `x` and `y`, `x` and `y` are equivalent with respect to the union of hyperplanes `A UNION B` if and only if `x` and `y` are equivalent with respect to `A` and `x` and `y` are equivalent with respect to `B`.

### Informal sketch
The proof proceeds by:
- Rewriting using the definition of `hyperplane_equiv` and `IN_UNION` which expands `IN (A UNION B)` to `IN A \/ IN B`.
- Applying MESON to discharge the remaining logical equivalences.

### Mathematical insight
This theorem states that equivalence with respect to the union of two sets of hyperplanes is equivalent to equivalence with respect to each of the individual sets. This reflects the fact that the union of sets of hyperplanes separates points if and only if each individual set separates them.

### Dependencies
- Definitions:
  - `hyperplane_equiv`
  - `IN_UNION`


---

## hyperplane_cell

### Name of formal statement
hyperplane_cell

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let hyperplane_cell = new_definition
 `hyperplane_cell A c <=> ?x. c = hyperplane_equiv A x`;;
```
### Informal statement
A set `c` is a `hyperplane_cell` with respect to a hyperplane arrangement `A` if and only if there exists an `x` such that `c` is equivalent to the set obtained by applying `hyperplane_equiv` to `A` and `x`.

### Informal sketch
The definition introduces the concept of a `hyperplane_cell` as a set that is equivalent to one produced by the `hyperplane_equiv` function for some point.
- The definition constructs a relation `hyperplane_cell A c` that holds if a set `c` can be reached from a hyperplane arrangement `A` using `hyperplane_equiv`.

### Mathematical insight
This definition captures the geometric notion of a cell in a hyperplane arrangement (a partition of space induced by a finite collection of hyperplanes). The function `hyperplane_equiv` determines the cell to which a point belongs, and `hyperplane_cell` defines the property of being such a cell. This is a fundamental concept used when building the theory on hyperplane arrangements.

### Dependencies
- Definition: `hyperplane_equiv`

### Porting notes (optional)
When porting to other proof assistants:
- Ensure the function `hyperplane_equiv` is correctly translated, as this definition directly relies on it.
- The definition uses an existential quantifier, so ensure the target proof assistant handles existential quantifiers appropriately and supports reasoning about sets.


---

## HYPERPLANE_CELL

### Name of formal statement
HYPERPLANE_CELL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL = prove
 (`hyperplane_cell A c <=> ?x. c = {y | hyperplane_equiv A x y}`,
  REWRITE_TAC[EXTENSION; hyperplane_cell; IN_ELIM_THM; IN] THEN
  MESON_TAC[]);;
```
### Informal statement
The predicate `hyperplane_cell A c` holds if and only if there exists some `x` such that `c` is equal to the set of all `y` such that `hyperplane_equiv A x y`.

### Informal sketch
The proof uses the following steps:
- Expand the definition of `hyperplane_cell`.
- Apply rewriting rules based on `EXTENSION`, `hyperplane_cell`, `IN_ELIM_THM`, and `IN`.
- Apply MESON to complete the proof.

### Mathematical insight
This theorem defines when a set `c` is a `hyperplane_cell` in terms of the existence of some `x` such that `c` is the set of points equivalent to `x` under the `hyperplane_equiv` relation.

### Dependencies
- Definitions: `hyperplane_cell`
- Theorems: `EXTENSION`, `IN_ELIM_THM`, `IN`


---

## NOT_HYPERPLANE_CELL_EMPTY

### Name of formal statement
NOT_HYPERPLANE_CELL_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_HYPERPLANE_CELL_EMPTY = prove
 (`!A. ~(hyperplane_cell A {})`,
  REWRITE_TAC[hyperplane_cell; EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[HYPERPLANE_EQUIV_REFL; IN]);;
```

### Informal statement
For all sets `A`, it is not the case that the `hyperplane_cell` of `A` is equal to the empty set.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the goal using the definition of `hyperplane_cell`, `EXTENSION`, and the theorem `NOT_IN_EMPTY`. This simplifies the goal.
- Then, use the `MESON_TAC` tactic with the theorems `HYPERPLANE_EQUIV_REFL` and `IN` to discharge the simplified goal. The theorem `HYPERPLANE_EQUIV_REFL` establishes reflexivity of hyperplane equivalence, while `IN` is a basic membership lemma.

### Mathematical insight
This theorem states that the `hyperplane_cell` of any set `A` is non-empty. This is a fundamental property related to hyperplanes and cells, indicating that a hyperplane cell always contains at least one point, and therefore can't be the empty set.

### Dependencies
- Definitions: `hyperplane_cell`, `EXTENSION`
- Theorems: `NOT_IN_EMPTY`, `HYPERPLANE_EQUIV_REFL`, `IN`


---

## NONEMPTY_HYPERPLANE_CELL

### Name of formal statement
NONEMPTY_HYPERPLANE_CELL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NONEMPTY_HYPERPLANE_CELL = prove
 (`!A c. hyperplane_cell A c ==> ~(c = {})`,
  MESON_TAC[NOT_HYPERPLANE_CELL_EMPTY]);;
```

### Informal statement
For all `A` and `c`, if `c` is a hyperplane cell of `A`, then `c` is not empty.

### Informal sketch
The theorem states that any hyperplane cell is nonempty.

- The proof is by MESON, using the theorem `NOT_HYPERPLANE_CELL_EMPTY`. This suggests that `NOT_HYPERPLANE_CELL_EMPTY` is likely an equivalent formulation, or a component sufficiently strong to prove the result.

### Mathematical insight
Hyperplane cells are fundamental geometric objects in the definition of arrangements of hyperplanes. This theorem asserts a basic but important property: that the construction indeed produces meaningful objects (i.e., not the empty set).

### Dependencies
- `NOT_HYPERPLANE_CELL_EMPTY`


---

## UNIONS_HYPERPLANE_CELLS

### Name of formal statement
UNIONS_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNIONS_HYPERPLANE_CELLS = prove
 (`!A. UNIONS {c | hyperplane_cell A c} = (:real^N)`,
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV; IN_ELIM_THM] THEN
  REWRITE_TAC[hyperplane_cell] THEN MESON_TAC[HYPERPLANE_EQUIV_REFL; IN]);;
```
### Informal statement
For all sets of hyperplanes `A`, the union of all `hyperplane_cell` induced by `A` equals the entire space `:real^N`.

### Informal sketch
The proof proceeds by showing that every point in `:real^N` is a member of the union of all `hyperplane_cell`s induced by `A`.
- First, the theorem is rewritten using `EXTENSION`, `IN_UNIONS`, `IN_UNIV`, and `IN_ELIM_THM` to reduce the goal to proving that for any `x :real^N`, `x` is in the union of all `hyperplane_cell`s induced by `A`.  This is equivalent to proving that there exists a `c` such that `hyperplane_cell A c` and `x IN c`.
- Next, the definition of `hyperplane_cell` is expanded via rewriting.
- Finally, `MESON_TAC` is used with `HYPERPLANE_EQUIV_REFL` and `IN`. `HYPERPLANE_EQUIV_REFL` handles the case where two hyperplanes, `h1` and `h2` are equivalent, proving `!x. x IN h1 <=> x IN h2`.

### Mathematical insight
This theorem establishes that the `hyperplane_cell`s associated with a set of hyperplanes form a partition (or tiling) of the entire space `:real^N`. Every point in the space belongs to at least one `hyperplane_cell`.

### Dependencies
- `EXTENSION`
- `IN_UNIONS`
- `IN_UNIV`
- `IN_ELIM_THM`
- `hyperplane_cell`
- `HYPERPLANE_EQUIV_REFL`
- `IN`


---

## DISJOINT_HYPERPLANE_CELLS

### Name of formal statement
DISJOINT_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISJOINT_HYPERPLANE_CELLS = prove
 (`!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2 /\ ~(c1 = c2)
             ==> DISJOINT c1 c2`,
  REWRITE_TAC[hyperplane_cell] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_REWRITE_TAC[IN_DISJOINT; IN; EXTENSION] THEN
  ASM_MESON_TAC[HYPERPLANE_EQUIV_TRANS; HYPERPLANE_EQUIV_SYM]);;
```
### Informal statement
For all sets `A`, `c1`, and `c2`, if `c1` is a `hyperplane_cell` with respect to `A` and `c2` is a `hyperplane_cell` with respect to `A` and `c1` is not equal to `c2`, then `c1` and `c2` are disjoint.

### Informal sketch
The proof proceeds by assuming the hypotheses and then demonstrating that the conclusion, `DISJOINT c1 c2`, holds.

- First, rewrite using the definition of `hyperplane_cell`.
- Then, repeatedly strip the quantifiers and implications using `STRIP_TAC`.
- Next, apply `FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))` to use the negated conclusion to further refine the proof state, which is used to destruct the `DISJOINT` goal.
- Perform automatic rewriting using assumptions and the theorems `IN_DISJOINT`, `IN`, and `EXTENSION`.
- Finally, use `ASM_MESON_TAC` with `HYPERPLANE_EQUIV_TRANS` and `HYPERPLANE_EQUIV_SYM` to complete the proof.

### Mathematical insight
This theorem formalizes the basic geometric intuition that two distinct hyperplane cells generated from the same set of hyperplanes must be disjoint. This result is important for reasoning about the structure and properties of hyperplane arrangements and cell decompositions.

### Dependencies
- Definitions: `hyperplane_cell`
- Theorems: `IN_DISJOINT`, `IN`, `EXTENSION`, `HYPERPLANE_EQUIV_TRANS`, `HYPERPLANE_EQUIV_SYM`


---

## DISJOINT_HYPERPLANE_CELLS_EQ

### Name of formal statement
DISJOINT_HYPERPLANE_CELLS_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISJOINT_HYPERPLANE_CELLS_EQ = prove
 (`!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2
             ==> (DISJOINT c1 c2 <=> ~(c1 = c2))`,
  MESON_TAC[NONEMPTY_HYPERPLANE_CELL; DISJOINT_HYPERPLANE_CELLS;
            SET_RULE `DISJOINT s s <=> s = {}`]);;
```
### Informal statement
For all sets `A`, `c1`, and `c2`, if `c1` is a hyperplane cell with respect to `A` and `c2` is a hyperplane cell with respect to `A`, then `c1` and `c2` are disjoint if and only if `c1` and `c2` are not equal.

### Informal sketch
The proof demonstrates the equivalence between disjointness and inequality for hyperplane cells.
- Assume that `c1` and `c2` are hyperplane cells with respect to `A`.
- The proof uses the theorem `DISJOINT_HYPERPLANE_CELLS`, which likely states that if two hyperplane cells are disjoint, then they are not equal.
- It also utilizes `NONEMPTY_HYPERPLANE_CELL`, which asserts that hyperplane cells are non-empty.
- The set rule `DISJOINT s s <=> s = {}` is used to define disjointness.
- The strategy involves showing that if `c1` and `c2` are not equal, then they are disjoint, and vice versa, given that they are both hyperplane cells with respect to the same `A`. The given MESON_TAC hints at the general automated proof search strategy.

### Mathematical insight
This theorem formalizes the intuition that distinct hyperplane cells (cells formed by partitioning space with hyperplanes) are disjoint. Hyperplane cells are fundamental geometric objects, and their disjointness is a key property used, for example, in spatial reasoning and geometric algorithms.

### Dependencies
- Theorems: `NONEMPTY_HYPERPLANE_CELL`, `DISJOINT_HYPERPLANE_CELLS`
- Rules: `SET_RULE DISJOINT s s <=> s = {}`


---

## HYPERPLANE_CELL_EMPTY

### Name of formal statement
HYPERPLANE_CELL_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_EMPTY = prove
 (`hyperplane_cell {} c <=> c = (:real^N)`,
  REWRITE_TAC[HYPERPLANE_CELL; NOT_IN_EMPTY; hyperplane_equiv] THEN
  SET_TAC[]);;
```
### Informal statement
For any `c` of type `:real^N`, the hyperplane cell of the empty set `{}` at `c` is equivalent to `c` being equal to the zero vector `(:real^N)`.

### Informal sketch
The proof proceeds as follows:
- Rewrite using `HYPERPLANE_CELL`, `NOT_IN_EMPTY`, and `hyperplane_equiv`.
- Apply `SET_TAC` to complete the proof.

### Mathematical insight
The theorem states that the hyperplane cell generated by the empty set is precisely the point where all the inequalities defining the cell become trivial. This is a base case for inductive arguments involving hyperplane arrangements and their cells. The definitions of `HYPERPLANE_CELL`, `NOT_IN_EMPTY` and `hyperplane_equiv` must be already defined.

### Dependencies
- Definitions: `HYPERPLANE_CELL`
- Theorems: `NOT_IN_EMPTY`, `hyperplane_equiv`


---

## HYPERPLANE_CELL_SING_CASES

### Name of formal statement
HYPERPLANE_CELL_SING_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_SING_CASES = prove
 (`!a b c:real^N->bool.
        hyperplane_cell {(a,b)} c
        ==>  c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}`,
  REWRITE_TAC[HYPERPLANE_CELL; hyperplane_equiv] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; IN_SING; hyperplane_side] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC
   (SPEC `(a:real^N) dot y - b` REAL_SGN_CASES) THEN
  ASM_REWRITE_TAC[REAL_SGN_EQ] THEN
  SIMP_TAC[REAL_SUB_0; REAL_SUB_LT; real_gt;
           REAL_ARITH `x - y < &0 <=> x < y`]);;
```

### Informal statement
For all `a`, `b` (functions from `real^N` to boolean) and `c` (a function from `real^N` to boolean), if `c` is a `hyperplane_cell` defined by `(a, b)`, then `c` is equal to the set of all `x` such that `a dot x = b`, or `c` is equal to the set of all `x` such that `a dot x < b`, or `c` is equal to the set of all `x` such that `a dot x > b`.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting the statement using the definition of `HYPERPLANE_CELL` and `hyperplane_equiv`.
- Then, rewrite using `FORALL_UNWIND_THM2`, `IN_SING`, and `hyperplane_side`.
- Perform generic introductions using `REPEAT GEN_TAC`.
- Eliminate the existential quantifier using `X_CHOOSE_THEN` introducing a witness named `y`.
- Rewrite using the symmetry of equality using `EQ_SYM_EQ`.
- Perform case splitting based on the possible values of `real_sgn (a dot y - b)` using `REAL_SGN_CASES`.
- Rewrite using `REAL_SGN_EQ`.
- Simplify using arithmetic relations such as `REAL_SUB_0`, `REAL_SUB_LT`, `real_gt`, and `x - y < &0 <=> x < y`.

### Mathematical insight
This theorem states that a `hyperplane_cell` can only be one of three forms: the hyperplane itself, the open half-space on one side of the hyperplane, or the open half-space on the other side of the hyperplane. This is an important property for reasoning about geometric arrangements and spatial relationships.

### Dependencies
- Definitions:
  - `HYPERPLANE_CELL`
  - `hyperplane_equiv`
  - `hyperplane_side`
  - `IN_SING`
- Theorems:
  - `FORALL_UNWIND_THM2`
  - `REAL_SGN_CASES`
  - `REAL_SGN_EQ`
  - `REAL_SUB_0`
  - `REAL_SUB_LT`
  - `real_gt`
  - `EQ_SYM_EQ`
- Other:
  - `REAL_ARITH x - y < &0 <=> x < y`


---

## HYPERPLANE_CELL_SING

### Name of formal statement
HYPERPLANE_CELL_SING

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_SING = prove
 (`!a b c.
        hyperplane_cell {(a,b)} c <=>
        if a = vec 0 then c = (:real^N)
        else c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[hyperplane_cell; hyperplane_equiv; EXTENSION; IN_UNIV] THEN
    REWRITE_TAC[IN] THEN REWRITE_TAC[hyperplane_equiv] THEN
    ASM_SIMP_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[hyperplane_side; DOT_LZERO];
    EQ_TAC THEN REWRITE_TAC[HYPERPLANE_CELL_SING_CASES] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[hyperplane_cell; EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[IN] THEN REWRITE_TAC[hyperplane_equiv] THEN
    ASM_SIMP_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[hyperplane_side] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a dot x = b <=> a dot x - b = &0`;
                     REAL_ARITH `a > b <=> a - b > &0`;
                     REAL_ARITH `a < b <=> a - b < &0`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SGN_EQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
    MATCH_MP_TAC(MESON[]
     `(?x. f x = a) ==> (?x. !y. f y = a <=> f x = f y)`) THEN
    REWRITE_TAC[REAL_SGN_EQ] THENL
     [EXISTS_TAC `b / (a dot a) % a:real^N`;
      EXISTS_TAC `(b - &1) / (a dot a) % a:real^N`;
      EXISTS_TAC `(b + &1) / (a dot a) % a:real^N`] THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN REAL_ARITH_TAC]);;
```
### Informal statement
For all `a`, `b` (vectors in `real^N`) and `c` (sets of vectors in `real^N`), `c` is a `hyperplane_cell` for the hyperplane defined by `(a, b)` if and only if:

either `a` is the zero vector, in which case `c` must be the entire space `real^N`,
or `a` is not the zero vector, in which case `c` must be either the set of all `x` such that `a` dot `x` equals `b`, or the set of all `x` such that `a` dot `x` is less than `b`, or the set of all `x` such that `a` dot `x` is greater than `b`.

### Informal sketch
The proof proceeds by:
- First, perform case analysis on the condition `a = vec 0`.
- If `a = vec 0`, several rewrites are used:
  - Rewrite using definitions of `hyperplane_cell`, `hyperplane_equiv`, `EXTENSION`, `IN_UNIV`, `IN`, `hyperplane_equiv`.
  - Simplify using `IN_SING` and `FORALL_UNWIND_THM2`.
  - Rewrite using `hyperplane_side` and `DOT_LZERO`.
- If `a != vec 0`, the proof shows that `hyperplane_cell {(a,b)} c` means that `c` corresponds to one of the three half-spaces defined by the hyperplane `a dot x = b`.
  - Rewrite using definitions of `hyperplane_cell`, `EXTENSION`, and `IN_ELIM_THM`.
  - Rewrite using `IN`, `hyperplane_equiv`.
  - Simplify using `IN_SING` and `FORALL_UNWIND_THM2`.
  - Rewrite using `hyperplane_side`.
  - Transform `<, >, =` relations with `a dot x` and `b` to relations with `a dot x - b` and `0`.
  - Use `REAL_SGN_EQ` to change comparisons to checks involving the sign function and then perform rewrites.
  - Finally, exhibit specific points for each case: `b / (a dot a) % a:real^N`, `(b - &1) / (a dot a) % a:real^N`, and `(b + &1) / (a dot a) % a:real^N`.
  - Simplify with `DOT_RMUL`, `REAL_DIV_RMUL`, and `DOT_EQ_0`, and call `REAL_ARITH_TAC` to finish.

### Mathematical insight
This theorem provides a characterization of hyperplane cells. In cases where `a` is not the zero vector, a `hyperplane_cell` must be one of the three natural sets defined by a hyperplane: the hyperplane itself, the half-space on one side of the hyperplane, or the half-space on the other side. If `a` is the zero vector then the hyperplane is not well defined (it's everything) so `c` must be everything for it to be a valid `hyperplane_cell`.

### Dependencies
- Definitions: `hyperplane_cell`, `hyperplane_equiv`
- Theorems: `EXTENSION`, `IN_UNIV`, `IN`, `IN_SING`, `FORALL_UNWIND_THM2`, `hyperplane_side`, `DOT_LZERO`, `IN_ELIM_THM`, `DOT_RMUL`, `REAL_DIV_RMUL`, `DOT_EQ_0`
- Axioms: `REAL_ARITH`, `REAL_SGN_EQ`, `REAL_SUB_0`


---

## HYPERPLANE_CELL_UNION

### Name of formal statement
HYPERPLANE_CELL_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_UNION = prove
 (`!A B c:real^N->bool.
        hyperplane_cell (A UNION B) c <=>
        ~(c = {}) /\
        ?c1 c2. hyperplane_cell A c1 /\
                hyperplane_cell B c2 /\
                c = c1 INTER c2`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c:real^N->bool = {}` THENL
   [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[HYPERPLANE_CELL; HYPERPLANE_EQUIV_UNION] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  REWRITE_TAC[MESON[]
   `(?c1 c2. (?x. c1 = f x) /\ (?y. c2 = g y) /\ P c1 c2) <=>
    (?x y. P (f x) (g y))`] THEN
  EQ_TAC THENL [MESON_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[HYPERPLANE_EQUIV_TRANS; HYPERPLANE_EQUIV_SYM]);;
```

### Informal statement
For all sets `A` and `B` of hyperplanes in `N`-dimensional real space, and for all sets of points `c` in `N`-dimensional real space, the set `c` is a `hyperplane_cell` of the union of `A` and `B` if and only if the following conditions hold: `c` is not empty, and there exist sets `c1` and `c2` such that `c1` is a `hyperplane_cell` of `A`, `c2` is a `hyperplane_cell` of `B`, and `c` is the intersection of `c1` and `c2`.

### Informal sketch
The proof proceeds by:
- Splitting the biconditional into two implications and proving each separately.
- Showing that if `c` is the empty set and `hyperplane_cell (A UNION B) c` holds, then this implies a contradiction.
- Expanding the definition of `hyperplane_cell` using `HYPERPLANE_CELL` and then rewriting using `HYPERPLANE_EQUIV_UNION`.
- Using set theory to manipulate intersections `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`.
- Manipulating existential quantifiers `(?c1 c2. (?x. c1 = f x) /\ (?y. c2 = g y) /\ P c1 c2) <=> (?x y. P (f x) (g y))`.
- For the reverse implication, use `LEFT_IMP_EXISTS_THM`.
- The fact that `MEMBER_NOT_EMPTY` along with `MONO_EXISTS` and `EXTENSION; IN_INTER; IN_ELIM_THM` are used.
- Finally, the proof uses the transitivity and symmetry of `HYPERPLANE_EQUIV` with `HYPERPLANE_EQUIV_TRANS; HYPERPLANE_EQUIV_SYM`.

### Mathematical insight
The theorem states that the `hyperplane_cell` of the union of two sets of hyperplanes is the intersection of the `hyperplane_cells` of each individual set of hyperplanes, provided that these `hyperplane_cells` are non-empty. This is a natural and expected result because adding more hyperplanes refines the cellular decomposition, leading to finer cells which arise from the intersection of the cells defined by the original hyperplane arrangements.

### Dependencies
- Definitions:
  - `HYPERPLANE_CELL`
- Theorems:
  - `NONEMPTY_HYPERPLANE_CELL`
  - `HYPERPLANE_EQUIV_UNION`
  - `SET_RULE` (`{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`)
  - `HYPERPLANE_EQUIV_TRANS`
  - `HYPERPLANE_EQUIV_SYM`
  - `LEFT_IMP_EXISTS_THM`
  - `MEMBER_NOT_EMPTY`
  - `EXTENSION`
  - `IN_INTER`
  - `IN_ELIM_THM`
  - `MONO_EXISTS`
---

---

## FINITE_HYPERPLANE_CELLS

### Name of formal statement
FINITE_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_HYPERPLANE_CELLS = prove
 (`!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c}`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[HYPERPLANE_CELL_EMPTY; SING_GSPEC; FINITE_SING] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`; `A:(real^N#real)->bool`] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{ c1 INTER c2:real^N->bool |
                c1 IN {c | hyperplane_cell A c} /\
                c2 IN {c | hyperplane_cell {(a,b)} c}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `{{x:real^N | a dot x = b},{x | a dot x < b},{x | a dot x > b}}` THEN
    REWRITE_TAC[SUBSET; IN_SING; HYPERPLANE_CELL_SING_CASES; IN_ELIM_THM;
                IN_INSERT; NOT_IN_EMPTY; FINITE_INSERT; FINITE_EMPTY];
    REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN MESON_TAC[INTER_COMM]]);;
```

### Informal statement
For all sets `A` of pairs of real vectors in `N` dimensions and real numbers, if `A` is finite, then the set of hyperplane cells generated by `A` is finite.

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `A`.

- **Base Case:** If `A` is empty, then the set of hyperplane cells generated by `A` is finite because the only hyperplane cell is the entire space `real^N->bool`, and a singleton set `{real^N->bool}` is finite.
- **Inductive Step:** Assume that for all sets `A'` such that `FINITE A'`, it holds that `FINITE {c | hyperplane_cell A' c}`.  We now show that if `A` is finite, then `FINITE {c | hyperplane_cell A c}`.  Let `A` be a finite set. We can represent `A` as the insertion of an element `(a,b)` into a set `s`, as shown in HOL Light with `a INSERT s = {a} UNION s`. The `hyperplane_cell` of `A` is therefore equal to the union of intersection of the form `{ c1 INTER c2 | c1 IN {c | hyperplane_cell A c} /\ c2 IN {c | hyperplane_cell {(a,b)} c}}` by the theorem `HYPERPLANE_CELL_UNION`. It suffices to prove that this set is finite, which follows by showing that `{c | hyperplane_cell A c}` and `{c | hyperplane_cell {(a,b)} c}` are finite, and then appealing to `FINITE_PRODUCT_DEPENDENT` and `FINITE_SUBSET`. The finiteness of `{c | hyperplane_cell A c}` is given by the inductive hypothesis.  The finiteness of `{c | hyperplane_cell {(a,b)} c}` arises because, in the 1-hyperplane case, a hyperplane splits the space into at most 3 regions:  `{{x:real^N | a dot x = b},{x | a dot x < b},{x | a dot x > b}}`. These three regions are finite, using theorems `HYPERPLANE_CELL_SING_CASES`, `FINITE_INSERT` and `FINITE_EMPTY`. Finally, `MESON_TAC` is used to finish the proof with `INTER_COMM`.

### Mathematical insight
This theorem states that if you have a finite number of hyperplanes in N-dimensional space, then the number of regions (hyperplane cells) they define is also finite. This is a foundational result in areas like computational geometry and linear programming, where hyperplanes are used to define constraints and feasible regions.

### Dependencies

**Definitions:**
- `hyperplane_cell`

**Theorems:**
- `FINITE_INDUCT_STRONG`
- `HYPERPLANE_CELL_EMPTY`
- `SING_GSPEC`
- `FINITE_SING`
- `FORALL_PAIR_THM`
- `SET_RULE a INSERT s = {a} UNION s`
- `HYPERPLANE_CELL_UNION`
- `FINITE_SUBSET`
- `FINITE_PRODUCT_DEPENDENT`
- `SUBSET`
- `IN_SING`
- `HYPERPLANE_CELL_SING_CASES`
- `IN_ELIM_THM`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `INTER_COMM`


---

## FINITE_RESTRICT_HYPERPLANE_CELLS

### Name of formal statement
FINITE_RESTRICT_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_RESTRICT_HYPERPLANE_CELLS = prove
 (`!P A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c /\ P c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cell A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLS] THEN SET_TAC[]);;
```
### Informal statement
For any set A of real vectors and any predicate P on functions from real vectors to booleans, if A is a finite set, then the set of functions `c` from real vectors to booleans such that `c` is a hyperplane cell with respect to A and `P c` holds, is a finite set.

### Informal sketch
The proof proceeds by showing that the set `{c:real^N->bool | hyperplane_cell A c /\ P c}` is a subset of `{c:real^N->bool | hyperplane_cell A c}`, i.e.the set of all hyperplane cells induced by `A`. Since `A` is finite and `FINITE_HYPERPLANE_CELLS` states that the set of hyperplane cells induced by a finite set is finite, we can use `FINITE_SUBSET` to prove that `{c:real^N->bool | hyperplane_cell A c /\ P c}` is also finite.

- First, strip the quantifiers and assume `FINITE A`.

- Apply `MATCH_MP_TAC FINITE_SUBSET`. This suggests that we need to show that `{c:real^N->bool | hyperplane_cell A c /\ P c}` is a subset of a finite set.

- Prove that `{c:real^N->bool | hyperplane_cell A c /\ P c}` is a subset of `{c:real^N->bool | hyperplane_cell A c}` by using `EXISTS_TAC` and `SET_TAC[]`. 

- Use `ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLS]` to show finiteness.

### Mathematical insight
The statement expresses that restricting the set of hyperplane cells induced by a finite set `A` with an arbitrary predicate `P` still results in a finite set. Since the set of hyperplane cells induced by a finite set is finite, any subset of it must also be finite.

### Dependencies
- `FINITE_SUBSET`
- `FINITE_HYPERPLANE_CELLS`


---

## FINITE_SET_OF_HYPERPLANE_CELLS

### Name of formal statement
FINITE_SET_OF_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_SET_OF_HYPERPLANE_CELLS = prove
 (`!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> FINITE C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cell A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLS] THEN ASM SET_TAC[]);;
```
### Informal statement
For any set `A` and any set `C` of functions from `real^N` to boolean values, if `A` is finite and every element `c` of `C` is a hyperplane cell with respect to `A`, then `C` is finite.

### Informal sketch
The proof proceeds as follows:
- Assume `A` is finite and every element `c` in `C` is a `hyperplane_cell A c`.
- Apply `FINITE_SUBSET`: To prove `FINITE C`, it suffices to show that `C` is a subset of some finite set.
- Instantiate this finite superset as `{c:real^N->bool | hyperplane_cell A c}`: The set of all functions mapping from `real^N` to boolean values that are hyperplane cells with respect to `A`.
- Simplify using `FINITE_HYPERPLANE_CELLS`: The set of all hyperplane cells with respect to a finite set `A` is finite.
- Apply basic set reasoning (`SET_TAC`) and assumption to finish the proof, since the hypothesis implies that the set `C` is a subset of a finite set.

### Mathematical insight
This theorem shows that if we have a finite set `A` and construct a set `C` of hyperplane cells all defined with respect to `A`, then the set `C` must also be finite. This is important because it establishes a finiteness property for hyperplane cells, which are fundamental building blocks for partitioning space.

### Dependencies
- Theorems:
  - `FINITE_SUBSET`
  - `FINITE_HYPERPLANE_CELLS`


---

## PAIRWISE_DISJOINT_HYPERPLANE_CELLS

### Name of formal statement
PAIRWISE_DISJOINT_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRWISE_DISJOINT_HYPERPLANE_CELLS = prove
 (`!A C. (!c. c IN C ==> hyperplane_cell A c)
         ==> pairwise DISJOINT C`,
  REWRITE_TAC[pairwise] THEN MESON_TAC[DISJOINT_HYPERPLANE_CELLS]);;
```
### Informal statement
For all `A` and `C`, if every element `c` of `C` is a hyperplane cell with respect to `A`, then the elements of `C` are pairwise disjoint.

### Informal sketch
The proof proceeds as follows:
- It starts by rewriting with the definition of `pairwise`.
- Then it uses `MESON_TAC` along with the theorem `DISJOINT_HYPERPLANE_CELLS` to discharge the goal.

### Mathematical insight
This theorem establishes a condition under which a set of hyperplane cells are guaranteed to be pairwise disjoint. Specifically, if every set in `C` is constructed as `hyperplane_cell` on `A`, then no two sets in `C` can intersect with each other. This is a fundamental result when dealing with collections of hyperplane cells, namely the cells induced by a hyperplane arrangement, and contributes to understanding their structural properties.

### Dependencies
- Definitions: `pairwise`
- Theorems: `DISJOINT_HYPERPLANE_CELLS`


---

## HYPERPLANE_CELL_INTER_OPEN_AFFINE

### Name of formal statement
HYPERPLANE_CELL_INTER_OPEN_AFFINE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_INTER_OPEN_AFFINE = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> ?s t. open s /\ affine t /\ c = s INTER t`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[HYPERPLANE_CELL_EMPTY] THEN REPEAT STRIP_TAC THEN
    REPEAT(EXISTS_TAC `(:real^N)`) THEN
    ASM_REWRITE_TAC[AFFINE_UNIV; OPEN_UNIV; INTER_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`; `A:real^N#real->bool`] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN X_GEN_TAC `c':real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real^N->bool`; `c:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[HYPERPLANE_CELL_SING] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_UNIV];
    MAP_EVERY EXISTS_TAC
     [`s:real^N->bool`; `{x:real^N | a dot x = b} INTER t`] THEN
    ASM_REWRITE_TAC[INTER_ACI] THEN MATCH_MP_TAC AFFINE_INTER THEN
    ASM_REWRITE_TAC[AFFINE_HYPERPLANE];
    MAP_EVERY EXISTS_TAC
     [`{x:real^N | a dot x < b} INTER s`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_ACI] THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_LT];
    MAP_EVERY EXISTS_TAC
     [`{x:real^N | a dot x > b} INTER s`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_ACI] THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_GT]]);;
```
### Informal statement
For any `A` from `real^N` to `bool` and any `c` from `real^N` to `bool`, if `A` is finite and `c` is a hyperplane cell with respect to `A`, then there exist sets `s` and `t` such that `s` is open, `t` is affine, and `c` is the intersection of `s` and `t`.

### Informal sketch
The proof proceeds by strong induction on the finiteness of `A`.
- Base case: If `A` is empty (i.e., `FINITE A` and `hyperplane_cell A c`), then `c` must be the entire space `UNIV`. The space `UNIV` is both open and affine. We pick `s` and `t` to be `UNIV` in this case and use `AFFINE_UNIV` and `OPEN_UNIV` to show that the intersection the claim holds.
- Inductive step: Assume the theorem holds for all sets `A'` smaller than `A`. Let `A` be a finite set and `c` be a hyperplane cell with respect to `A`. This implies that for any element in `A`, we can write A as the union of the element `a` and the rest of the set. By definition, `c` can be written as the union of the hyperplane cells `c1` w.r.t `A \ {a}`. By the inductive hypothesis, there exists some `s` and `t` such that `c1` is the interesection of `s` and `t`, with `s`  being open and `t` is affine. Now we must deal with the element `a`.
  - If the set is an equality, take the intersection of the original intersection with the hyperplane `a dot x = b`, where the new section is affine using `AFFINE_HYPERPLANE` and the property `AFFINE_INTER`. 
  - If the set is an < inequality, take the intersection of the original intersection with the halfspace `a dot x < b` where the new section is open using `OPEN_HALFSPACE_LT` and the property `OPEN_INTER`.
  - If the set is an > inequality, take the intersection of the original intersection with the halfspace `a dot x > b` where the new section is open using `OPEN_HALFSPACE_GT` and the property `OPEN_INTER`.

### Mathematical insight
This theorem decomposes a hyperplane cell, which is defined based on intersections of half-spaces and hyperplanes determined by a finite set of affine functions, into the intersection of an open set and an affine set. This decomposition might be useful in separating properties related to "openness" and "affinity".

### Dependencies
- Definitions:
  - `FINITE`
  - `hyperplane_cell`
  - `open`
  - `affine`
  - `INTER`

- Theorems:
  - `IMP_CONJ`
  - `RIGHT_FORALL_IMP_THM`
  - `FINITE_INDUCT_STRONG`
  - `HYPERPLANE_CELL_EMPTY`
  - `AFFINE_UNIV`
  - `OPEN_UNIV`
  - `INTER_UNIV`
  - `FORALL_PAIR_THM`
  - `SET_RULE `a INSERT s = {a} UNION s``
  - `HYPERPLANE_CELL_UNION`
  - `LEFT_IMP_EXISTS_THM`
  - `HYPERPLANE_CELL_SING`
  - `INTER_ACI`
  - `AFFINE_INTER`
  - `AFFINE_HYPERPLANE`
  - `OPEN_INTER`
  - `OPEN_HALFSPACE_LT`
  - `OPEN_HALFSPACE_GT`


---

## HYPERPLANE_CELL_RELATIVELY_OPEN

### Name of formal statement
HYPERPLANE_CELL_RELATIVELY_OPEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_RELATIVELY_OPEN = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> open_in (subtopology euclidean (affine hull c)) c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HYPERPLANE_CELL_INTER_OPEN_AFFINE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[OPEN_IN_EMPTY] THEN
  SUBGOAL_THEN `affine hull (s INTER t:real^N->bool) = t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `affine hull t:real^N->bool` THEN
    ASM_REWRITE_TAC[AFFINE_HULL_EQ] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[INTER_COMM]
      AFFINE_HULL_CONVEX_INTER_OPEN) THEN
    ASM_SIMP_TAC[AFFINE_IMP_CONVEX];
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_INTER]]);;
```

### Informal statement
For any set `A` of real vectors in `N` dimensions, and any cell `c` also in `N` dimensions, if `A` is finite and `c` is a hyperplane cell induced by `A`, then `c` is open in the subspace topology on the affine hull of `c` (where the ambient topology is the Euclidean topology).

### Informal sketch
The proof proceeds as follows:
- Assume `FINITE A` and `hyperplane_cell A c`.
- Apply `HYPERPLANE_CELL_INTER_OPEN_AFFINE` which states that if `s` and `t` are disjoint sets, where `s` is a relatively open set in the affine hull of `t`, and `t` is the affine hull of `c`, then `c` is relatively open in the affine hull of `c`.
- Rewrite using `LEFT_IMP_EXISTS_THM` to transform the goal into a form suitable for further manipulation.
- Introduce two sets `s` and `t` using `EXISTS_TAC`, which correspond to the relative open set and the affine hull of `c`, respectively.
- Assume that the antecedent of the implication provided by `HYPERPLANE_CELL_INTER_OPEN_AFFINE` is satisfied, i.e. `s INTER t` is `{}`.
- Perform case splitting on `s INTER t:real^N->bool = {}`.
- If `s INTER t` is empty, use the fact that the empty set is open in any topology ( `OPEN_IN_EMPTY` ).
- If `s INTER t` is not empty, show that `affine hull (s INTER t:real^N->bool)` is equal to `t`.
- Show that `affine hull t` is equal to `t` using `AFFINE_HULL_EQ`.
- Apply `ONCE_REWRITE_RULE[INTER_COMM]
      AFFINE_HULL_CONVEX_INTER_OPEN` and `ASM_SIMP_TAC[AFFINE_IMP_CONVEX]` to prove that the intersection of the affine hull of `s` and `t` equals `t`.
- Use `ONCE_REWRITE_TAC[INTER_COMM]` and `ASM_SIMP_TAC[OPEN_IN_OPEN_INTER]` to prove that `c` is an intersection of relatively open sets.

### Mathematical insight
The theorem formalizes the geometric intuition that a hyperplane cell, being an intersection of open half-spaces within the affine hull it spans, is itself an relatively open set in that same affine hull. The theorem depends on establishing that hyperplane cells can be represented as intersections of relatively open sets and utilizes properties of affine hulls.

### Dependencies
- `HYPERPLANE_CELL_INTER_OPEN_AFFINE`
- `LEFT_IMP_EXISTS_THM`
- `OPEN_IN_EMPTY`
- `AFFINE_HULL_EQ`
- `AFFINE_HULL_CONVEX_INTER_OPEN`
- `AFFINE_IMP_CONVEX`
- `OPEN_IN_OPEN_INTER`
- `INTER_COMM`


---

## HYPERPLANE_CELL_RELATIVE_INTERIOR

### Name of formal statement
HYPERPLANE_CELL_RELATIVE_INTERIOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_RELATIVE_INTERIOR = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> relative_interior c = c`,
  MESON_TAC[RELATIVE_INTERIOR_OPEN_IN; HYPERPLANE_CELL_RELATIVELY_OPEN]);;
```
### Informal statement
For any set `A` of real vectors of dimension `N` and any hyperplane cell `c`, if `A` is finite and `c` is a hyperplane cell with respect to `A`, then the relative interior of `c` is equal to `c` itself.

### Informal sketch
The proof proceeds by showing that if `A` is a finite set of real vectors and `c` is a `hyperplane_cell` with respect to `A`, then the `relative_interior` of `c` is equal to `c`.

- The proof uses `MESON_TAC` with the theorems `RELATIVE_INTERIOR_OPEN_IN` and `HYPERPLANE_CELL_RELATIVELY_OPEN`.
- This suggests that the proof likely relies on the facts that the `relative_interior` is open in the subspace it is defined on, and that `hyperplane_cell`'s are also relatively open in some corresponding affine space. Combining these likely gives equality.

### Mathematical insight
The theorem expresses the idea that hyperplane cells are "open" with respect to the affine space they lie in. In particular, it states that the relative interior of a hyperplane cell (which is the largest open set contained in the cell, relative to the cell's affine hull) is equal to the cell itself. This is a crucial property for working with hyperplane arrangements and related geometric structures. It essentially says that the `hyperplane_cell` `c` contains no boundary in its relative space and thus the relative interior will coincide with it.

### Dependencies
- Theorems:
    - `RELATIVE_INTERIOR_OPEN_IN`
    - `HYPERPLANE_CELL_RELATIVELY_OPEN`


---

## HYPERPLANE_CELL_CONVEX

### Name of formal statement
HYPERPLANE_CELL_CONVEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_CONVEX = prove
 (`!A c:real^N->bool. hyperplane_cell A c ==> convex c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HYPERPLANE_CELL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` SUBST1_TAC) THEN
  REWRITE_TAC[hyperplane_equiv] THEN
  ONCE_REWRITE_TAC[SET_RULE `f x = f y <=> y IN {y | f x = f y}`] THEN
  REWRITE_TAC[GSYM INTERS_IMAGE] THEN MATCH_MP_TAC CONVEX_INTERS THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC[hyperplane_side] THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC
   (SPEC `(a:real^N) dot c - b` REAL_SGN_CASES) THEN
  ASM_REWRITE_TAC[REAL_SGN_EQ] THEN
  SIMP_TAC[REAL_SUB_0; REAL_ARITH `a - b > &0 <=> a > b`;
           REAL_ARITH `a - b < &0 <=> a < b`] THEN
  REWRITE_TAC[CONVEX_HALFSPACE_LT; CONVEX_HALFSPACE_GT;
              CONVEX_HYPERPLANE]);;
```
### Informal statement
For any function `A` from `real^N` to boolean and any set `c` of type `real^N`, if `c` is a hyperplane cell with respect to `A`, then `c` is convex.

### Informal sketch
The proof proceeds as follows:
- Assume that `c` is a `hyperplane_cell` with respect to `A`.
- Unfold the definition of `hyperplane_cell`: `c` is the intersection of sets of the form `{x | A x = bx}`, where `bx` is a boolean value depending on `x`.
- Use the equivalence `f x = f y <=> y IN {y | f x = f y}`.
- Rewrite using the symmetry of `INTERS_IMAGE`.
- Apply the theorem `CONVEX_INTERS`, which states that the intersection of convex sets is convex.
- Rewrite using the theorem `FORALL_IN_IMAGE`.
- Rewrite using the theorem `FORALL_PAIR_THM`.
- Introduce arbitrary `a` and `b` of type `real^N`.
- Apply `DISCH_TAC`.
- Simplify using symmetry.
- Rewrite using the definition of `hyperplane_side`.
- Perform case analysis on the sign of `(a:real^N) dot c - b` using `REAL_SGN_CASES`.
- Simplify based on the sign analysis (`REAL_SGN_EQ`, `REAL_SUB_0`, and arithmetic facts).
- Rewrite using the definitions of `CONVEX_HALFSPACE_LT`, `CONVEX_HALFSPACE_GT`, and `CONVEX_HYPERPLANE`. This reduces each case to known facts about convexity of half-spaces and hyperplanes.

### Mathematical insight
This theorem states that a cell defined by hyperplanes in `real^N` is a convex set. This underscores the fundamental connection between linear algebra (hyperplanes) and convexity. The proof hinges on the fact that half-spaces and hyperplanes are convex, and that the intersection of convex sets is also convex.

### Dependencies
- Definitions: `HYPERPLANE_CELL`
- Theorems: `hyperplane_equiv`, `CONVEX_INTERS`, `FORALL_IN_IMAGE`, `FORALL_PAIR_THM`
- Theorems: `REAL_SGN_CASES`, `REAL_SGN_EQ`, `REAL_SUB_0`, `CONVEX_HALFSPACE_LT`, `CONVEX_HALFSPACE_GT`, `CONVEX_HYPERPLANE`
- Rules: `SET_RULE`

### Porting notes (optional)
- The case splitting on real signs (`REAL_SGN_CASES`) may require careful adaptation depending on the target proof assistant's reals library.
- The extensive rewriting relies on the simplifier; ensure that equivalent simplification rules are available.


---

## HYPERPLANE_CELL_INTERS

### Name of formal statement
HYPERPLANE_CELL_INTERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_INTERS = prove
 (`!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c) /\
         ~(C = {}) /\ ~(INTERS C = {})
         ==> hyperplane_cell A (INTERS C)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HYPERPLANE_CELL; GSYM MEMBER_NOT_EMPTY] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[IN_INTERS] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `c:real^N->bool`);
    X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN SIMP_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[HYPERPLANE_EQUIV_SYM; HYPERPLANE_EQUIV_TRANS]);;
```

### Informal statement
For all `A` and `C`, if every `c` in `C` is a hyperplane cell with respect to `A`, `C` is non-empty, and the intersection of all sets in `C` is non-empty, then the intersection of all sets in `C` is a hyperplane cell with respect to `A`.

### Informal sketch
The proof proceeds by assuming the antecedent and proving the consequent:
- Assume that every `c` in `C` is a `hyperplane_cell A c`, `C` is not empty, and `INTERS C` is not empty.
- Show that `INTERS C` is a `hyperplane_cell A (INTERS C)`.
- Use the definition of `hyperplane_cell`. To prove `hyperplane_cell A (INTERS C)` we must show that there exists a function `z` such that for any x, x is in `INTERS C` if and only if `A x = z x`.
- Since `INTERS C` is non-empty, we can choose `z` such that `z IN INTERS C`. 
- Then, prove that for all `x`, `x IN INTERS C` is equivalent to `A x = A z`.
- The left-to-right direction follows directly from the fact that each `c IN C` is a `hyperplane_cell A c`. That is, `x IN INTERS C` means `x IN c` for all `c IN C`. Then, since `z IN c` for all `c IN C`, this means `A x = A z` for all `c IN C`.
- The right-to-left direction uses a similar argument to prove that if `A x = A z`, then `x IN c` for all `c IN C` and `z IN c` for all `c IN C`. Thus, `x IN INTERS C`.
- The lemmas `HYPERPLANE_EQUIV_SYM` and `HYPERPLANE_EQUIV_TRANS` are used to deduce that `A x = A z` and `z IN c` then `x IN c` for all `c IN C`.

### Mathematical insight
This theorem states that the intersection of a non-empty collection of hyperplane cells (all defined with respect to the same function `A`) is also a hyperplane cell, provided that the intersection is non-empty itself. This result is important for understanding how hyperplane cells behave under set-theoretic operations and is canonical in set theory.

### Dependencies
- Definition: `HYPERPLANE_CELL`
- Theorem: `MEMBER_NOT_EMPTY`
- Theorem: `EXTENSION`
- Theorem: `IN_ELIM_THM`
- Theorem: `HYPERPLANE_EQUIV_SYM`
- Theorem: `HYPERPLANE_EQUIV_TRANS`

### Porting notes (optional)
- The proof relies on higher-order logic features to quantify over sets of functions (`c:real^N->bool`).
- The `ASM_MESON_TAC` performs automated reasoning using the provided lemmas which may require different automation schemes in other proof assistants.


---

## HYPERPLANE_CELL_INTER

### Name of formal statement
HYPERPLANE_CELL_INTER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_INTER = prove
 (`!A s t:real^N->bool.
        hyperplane_cell A s /\ hyperplane_cell A t /\ ~(s INTER t = {})
        ==> hyperplane_cell A (s INTER t)`,
  REWRITE_TAC[GSYM INTERS_2] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HYPERPLANE_CELL_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; NOT_INSERT_EMPTY]);;
```

### Informal statement
For any `A`, `s`, and `t` mapping from `real^N` to boolean values, if `s` is a `hyperplane_cell` with respect to `A` and `t` is a `hyperplane_cell` with respect to `A` and the intersection of `s` and `t` is not empty, then the intersection of `s` and `t` is also a `hyperplane_cell` with respect to `A`.

### Informal sketch

The proof proceeds as follows:
- Rewrite using `GSYM INTERS_2` to change `s INTER t` to `t INTER s`.
- Repeatedly strip the top-level implications and universal quantifiers using `STRIP_TAC`.
- Apply the theorem `HYPERPLANE_CELL_INTERS` using `MATCH_MP_TAC`. This theorem likely states that the intersection of a set of hyperplane cells is a hyperplane cell.
- Rewrite using the assumptions `FORALL_IN_INSERT`, `NOT_IN_EMPTY`, and `NOT_INSERT_EMPTY` using `ASM_REWRITE_TAC`. These rewrites likely simplify assumptions about elements within sets, leveraging properties of `insert` and `empty` sets.

### Mathematical insight
The theorem demonstrates a fundamental closure property of `hyperplane_cell`s. Specifically, it shows that the intersection of two `hyperplane_cell`s (with respect to the same set A of hyperplanes) is also a `hyperplane_cell`, provided that the intersection is non-empty. This result contributes to understanding the geometric structure formed by arrangements of hyperplanes.

### Dependencies
- Theorems: `HYPERPLANE_CELL_INTERS`
- Definitions: `hyperplane_cell`
- Theorems related to sets: `INTERS_2`, `FORALL_IN_INSERT`, `NOT_IN_EMPTY`, `NOT_INSERT_EMPTY`


---

## hyperplane_cellcomplex

### Name of formal statement
hyperplane_cellcomplex

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let hyperplane_cellcomplex = new_definition
 `hyperplane_cellcomplex A s <=>
        ?t. (!c. c IN t ==> hyperplane_cell A c) /\
            s = UNIONS t`;;
```
### Informal statement
The set `s` is a `hyperplane_cellcomplex` of set `A` if and only if there exists a set `t` such that every element `c` in `t` is a `hyperplane_cell` of `A`, and `s` is the union of all elements in `t`.

### Informal sketch
*   The definition introduces the concept of a `hyperplane_cellcomplex`.
*   It states that a set `s` is a `hyperplane_cellcomplex` constructed from a set `A` if `s` can be represented as the union of a set `t` where each element `c` within `t` is a `hyperplane_cell` with respect to `A`.

### Mathematical insight
This definition captures the intuitive notion of a cell complex being built from hyperplane cells. It essentially says that a cell complex is the union of hyperplane cells. The existential quantifier over `t` allows for different ways to decompose a cell complex into hyperplane cells.

### Dependencies
*   Definitions: `hyperplane_cell`, `UNIONS`


---

## HYPERPLANE_CELLCOMPLEX_EMPTY

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_EMPTY = prove
 (`!A:real^N#real->bool. hyperplane_cellcomplex A {}`,
  GEN_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  EXISTS_TAC `{}:(real^N->bool)->bool` THEN
  REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0]);;
```

### Informal statement
For every function `A` from `real^N` to `real->bool`, the `hyperplane_cellcomplex` of `A` applied to the empty set is true.

### Informal sketch

*   The proof starts by using `GEN_TAC` to assume an arbitrary function `A:real^N#real->bool`.
*   It then rewrites the goal using the definition of `hyperplane_cellcomplex`.
*   Next, it introduces an existential quantifier with the empty set `{}:(real^N->bool)->bool` as the witness.
*   Finally, it rewrites using the theorems `NOT_IN_EMPTY` and `UNIONS_0` to simplify the goal and complete the proof.

### Mathematical insight
The theorem states that the `hyperplane_cellcomplex` property holds for the empty set of hyperplanes. This essentially means that the empty set satisfies the condition defined by `hyperplane_cellcomplex`, which is crucial when building up more complex cell complexes iteratively. It's a base case that allows inductive arguments to proceed.

### Dependencies
*Definitions:* `hyperplane_cellcomplex`
*Theorems:* `NOT_IN_EMPTY`, `UNIONS_0`


---

## HYPERPLANE_CELL_CELLCOMPLEX

### Name of formal statement
HYPERPLANE_CELL_CELLCOMPLEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_CELLCOMPLEX = prove
 (`!A c:real^N->bool. hyperplane_cell A c ==> hyperplane_cellcomplex A c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  EXISTS_TAC `{c:real^N->bool}` THEN
  ASM_SIMP_TAC[IN_SING; UNIONS_1]);;
```

### Informal statement
For all `A` from real N-dimensional space to Boolean and all `c` from real N-dimensional space to Boolean, if `c` is a `hyperplane_cell` of `A`, then `c` is a `hyperplane_cellcomplex` of `A`.

### Informal sketch
The proof proceeds by showing that if `c` is a `hyperplane_cell` of `A`, then `c` is a `hyperplane_cellcomplex` of `A`.
- Expand the definition of `hyperplane_cellcomplex`.
- Introduce an existential variable, `c`, which represents a cell in the `hyperplane_cellcomplex`.
- Simplify using assumptions, especially `IN_SING` which describes singletons and `UNIONS_1` which is a property about unions of sets.

### Mathematical insight
This theorem demonstrates that any `hyperplane_cell` residing within a specified arrangement `A` inherently qualifies as a `hyperplane_cellcomplex` within the same arrangement. The `hyperplane_cellcomplex` is constructed as a set of sets, and each `hyperplane_cell` is one of those sets.

### Dependencies
- Definitions: `hyperplane_cellcomplex`
- Theorems: `IN_SING`, `UNIONS_1`


---

## HYPERPLANE_CELLCOMPLEX_UNIONS

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_UNIONS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_UNIONS = prove
 (`!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (UNIONS C)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(real^N->bool)->(real^N->bool)->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `UNIONS (IMAGE (f:(real^N->bool)->(real^N->bool)->bool) C)` THEN
  REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[UNIONS_IMAGE]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  ASM SET_TAC[]);;
```

### Informal statement
For all sets `A` and `C`, if every `s` in `C` satisfies that `hyperplane_cellcomplex A s`, then `hyperplane_cellcomplex A (UNIONS C)`.

### Informal sketch
The proof proceeds by assuming that every set `s` in `C` satisfies `hyperplane_cellcomplex A s` and proving that `hyperplane_cellcomplex A (UNIONS C)`.
- The definition of `hyperplane_cellcomplex` is unfolded.
- Skolemization introduces a function `f` for the witnesses.
- Introduce the witness to the `EXISTS` by applying the function `f` to the set `C`.
- Expand `FORALL_IN_UNIONS`, `IMP_CONJ`, `RIGHT_FORALL_IMP_THM` and `FORALL_IN_IMAGE`.
- Split the goals into two subgoals.
- The first subgoal is solved by assumption and MESON. The second subgoal uses `UNIONS_IMAGE`.
- Simplify using `EXTENSION`, `IN_UNIONS` and `IN_ELIM_THM`.

### Mathematical insight
This theorem states that if a collection of sets all satisfy the `hyperplane_cellcomplex` property with respect to a set `A`, then the union of that collection also satisfies the `hyperplane_cellcomplex` property with respect to `A`. This is a crucial property for reasoning about cell complexes, ensuring that operations like taking unions preserve the cell complex structure.

### Dependencies
- Definitions: `hyperplane_cellcomplex`
- Theorems:`RIGHT_IMP_EXISTS_THM`, `SKOLEM_THM`, `LEFT_IMP_EXISTS_THM`, `FORALL_IN_UNIONS`, `IMP_CONJ`, `RIGHT_FORALL_IMP_THM`, `FORALL_IN_IMAGE`, `UNIONS_IMAGE`, `EXTENSION`, `IN_UNIONS`, `IN_ELIM_THM`


---

## HYPERPLANE_CELLCOMPLEX_UNION

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_UNION = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;
```

### Informal statement
For all sets of hyperplanes `A`, and for all sets `s` and `t`, if `s` is a `hyperplane_cellcomplex` with respect to `A` and `t` is a `hyperplane_cellcomplex` with respect to `A`, then the union of `s` and `t` (i.e. `s UNION t`) is a `hyperplane_cellcomplex` with respect to `A`.

### Informal sketch
The proof proceeds as follows:
- Assume that `s` and `t` are `hyperplane_cellcomplex`es with respect to `A`.
- Rewrite `s UNION t` to `UNIONS {s, t}`. This uses the theorem `GSYM UNIONS_2`.
- Apply the theorem `HYPERPLANE_CELLCOMPLEX_UNIONS` to discharge the goal.
- Discharge the remaining assumptions using simplification with the list of theorems `FORALL_IN_INSERT` and `NOT_IN_EMPTY`.

### Mathematical insight
This theorem shows that the property of being a `hyperplane_cellcomplex` is closed under the union operation. This is a fundamental property useful when constructing more complex cell complexes from simpler ones.

### Dependencies
- Theorems: `HYPERPLANE_CELLCOMPLEX_UNIONS`, `GSYM UNIONS_2`, `FORALL_IN_INSERT`, `NOT_IN_EMPTY`.


---

## HYPERPLANE_CELLCOMPLEX_UNIV

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_UNIV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_UNIV = prove
 (`!A. hyperplane_cellcomplex A (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_HYPERPLANE_CELLS] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  REWRITE_TAC[IN_ELIM_THM; HYPERPLANE_CELL_CELLCOMPLEX]);;
```
### Informal statement
For any set of hyperplanes `A` in `real^N`, `hyperplane_cellcomplex A` is a cell complex in `real^N`. In other words, every set of hyperplanes in `real^N` induces a cell complex structure on the entire space `real^N`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal.
- Rewrite using `GSYM UNIONS_HYPERPLANE_CELLS` to replace `(:real^N)` with `UNIONS(hyperplane_cells A)`.
- Apply `HYPERPLANE_CELLCOMPLEX_UNIONS` by matching, which reduces the goal to showing that `UNIONS(hyperplane_cells A)` is a cell complex given that `hyperplane_cells A` can be used to form a cell complex.
- Rewrite using `IN_ELIM_THM` and `HYPERPLANE_CELL_CELLCOMPLEX` to demonstrate that `hyperplane_cells A` can be used to form a cell complex.

### Mathematical insight
The theorem `HYPERPLANE_CELLCOMPLEX_UNIV` establishes that any arrangement of hyperplanes in `real^N` naturally induces a cell complex structure on the entire space. This is a fundamental result in geometric and topological combinatorics, providing a way to decompose `real^N` into cells defined by hyperplane intersections. It is crucial for reasoning about the structure and properties of hyperplane arrangements.

### Dependencies
- Definitions:
  - `hyperplane_cellcomplex`
  - `UNIONS`
  - `hyperplane_cells`
- Theorems:
  - `HYPERPLANE_CELLCOMPLEX_UNIONS`
  - `IN_ELIM_THM`
  - `HYPERPLANE_CELL_CELLCOMPLEX`


---

## HYPERPLANE_CELLCOMPLEX_INTERS

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_INTERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_INTERS = prove
 (`!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (INTERS C)`,
  let lemma = prove
   (`UNIONS s = UNIONS {t | t IN s /\ ~(t = {})}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[NOT_IN_EMPTY]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `C:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; HYPERPLANE_CELLCOMPLEX_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [hyperplane_cellcomplex] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(real^N->bool)->(real^N->bool)->bool` THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `C = {UNIONS((f:(real^N->bool)->(real^N->bool)->bool) s) | s IN C}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTERS_OVER_UNIONS] THEN ONCE_REWRITE_TAC[lemma] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
  MATCH_MP_TAC HYPERPLANE_CELL_INTERS THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]);;
```

### Informal statement
For all sets `A` of hyperplanes in `real^N` and all sets of sets of points `C` in `real^N`, if every set `s` in `C` is a hyperplane cell complex with respect to `A`, then the intersection of all sets in `C` is also a hyperplane cell complex with respect to `A`.

### Informal sketch
The proof proceeds as follows:
- First, a lemma is proved stating that `UNIONS s = UNIONS {t | t IN s /\ ~(t = {})}`. This is done by rewriting with definitions of `UNIONS_GSPEC`, `EXTENSION`, `IN_UNIONS`, `IN_ELIM_THM`, and `NOT_IN_EMPTY`.
- The main proof starts by considering the cases where `C` is empty or non-empty.
    - If `C` is empty, then `INTERS C` is the universe, and the result follows from `HYPERPLANE_CELLCOMPLEX_UNIV`.
    - If `C` is non-empty, the goal is to show `hyperplane_cellcomplex A (INTERS C)`.
- The sets `C` and `f` are generalized, where `f` is a function that maps a set to another set.
- The goal is transformed to prove `C = {UNIONS (f s) | s IN C}` to be able to rewrite the goal using `INTERS_OVER_UNIONS`.
- The theorem `HYPERPLANE_CELLCOMPLEX_UNIONS` is used to reduce the goal to showing that for all `s` in `C`, `hyperplane_cellcomplex A (UNIONS (f s))` holds, given that each `f s` consists of cells.
- The proof then uses `HYPERPLANE_CELL_CELLCOMPLEX` and `HYPERPLANE_CELL_INTERS`, along with some set manipulations, to complete the demonstration.

### Mathematical insight
This theorem is a fundamental result in hyperplane arrangements, showing that the intersection of hyperplane cell complexes is also a hyperplane cell complex. This property is crucial for constructing and analyzing more complex structures within hyperplane arrangements.

### Dependencies
- `UNIONS_GSPEC`
- `EXTENSION`
- `IN_UNIONS`
- `IN_ELIM_THM`
- `NOT_IN_EMPTY`
- `INTERS_0`
- `HYPERPLANE_CELLCOMPLEX_UNIV`
- `RIGHT_IMP_EXISTS_THM`
- `SKOLEM_THM`
- `LEFT_IMP_EXISTS_THM`
- `INTERS_OVER_UNIONS`
- `HYPERPLANE_CELLCOMPLEX_UNIONS`
- `FORALL_IN_GSPEC`
- `IMP_CONJ`
- `HYPERPLANE_CELL_CELLCOMPLEX`
- `HYPERPLANE_CELL_INTERS`

### Porting notes (optional)
The proof relies heavily on rewriting and equational reasoning. Systems like Isabelle and Coq might require more explicit handling of set theory and quantifiers. The tactic `ASM_CASES_TAC` could be replaced with case distinctions or inductive hypotheses within other proof assistants.


---

## HYPERPLANE_CELLCOMPLEX_INTER

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_INTER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_INTER = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;
```
### Informal statement
For all sets of hyperplanes `A`, and for all sets `s` and `t` of relatively open sets, if `s` is a hyperplane cell complex with respect to `A` and `t` is a hyperplane cell complex with respect to `A`, then the intersection of `s` and `t` is a hyperplane cell complex with respect to `A`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and the implication.
- Rewrite the goal using `GSYM INTERS_2` to express the intersection of `s` and `t` as an intersection over the union of `s` and `t`. This step uses the set theory fact that `s INTER t = INTERS (s UNION t)`. This transforms the goal into proving that `hyperplane_cellcomplex A (INTERS (s UNION t))`.
- Apply the theorem `HYPERPLANE_CELLCOMPLEX_INTERS`, which states that the intersection of an arbitrary set of hyperplane cell complexes is a hyperplane cell complex. This reduces the goal to showing that `s UNION t` consists only of hyperplane cell complexes with respect to `A`, i.e., for all `x` in `s UNION t`, `hyperplane_cellcomplex A x` holds.
- Use assumption rewriting to simplify goals regarding membership in the form `FORALL_IN_INSERT` and `NOT_IN_EMPTY`.

### Mathematical insight
The theorem asserts that the intersection of two hyperplane cell complexes is also a hyperplane cell complex. This is a fundamental property for reasoning about the topological structure induced by hyperplane arrangements. It ensures that basic set-theoretic operations preserve the cell complex structure.

### Dependencies
- `HYPERPLANE_CELLCOMPLEX_INTERS`
- `INTERS_2`
- `FORALL_IN_INSERT`
- `NOT_IN_EMPTY`


---

## HYPERPLANE_CELLCOMPLEX_COMPL

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_COMPL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_COMPL = prove
 (`!A s. hyperplane_cellcomplex A s
         ==> hyperplane_cellcomplex A ((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [hyperplane_cellcomplex] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `C:(real^N->bool)->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[UNIONS_INTERS; COMPL_COMPL] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(:real^N) DIFF c = UNIONS {c' | hyperplane_cell A c' /\ ~(c' = c)}`
  SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ISPEC `A:real^N#real->bool` UNIONS_HYPERPLANE_CELLS)) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `c':real^N->bool` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`A:real^N#real->bool`; `c:real^N->bool`; `c':real^N->bool`]
        DISJOINT_HYPERPLANE_CELLS_EQ) THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
    ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX; IN_ELIM_THM]]);;
```

### Informal statement
For all `A` and `s`, if `s` is a hyperplane cell complex with respect to `A`, then the complement of `s` (i.e., `(:real^N) DIFF s`) is also a hyperplane cell complex with respect to `A`.

### Informal sketch
The proof proceeds as follows:
- Assume `hyperplane_cellcomplex A s`.
- Show that there exists some `C` such that `hyperplane_cellcomplex A C` holds and `C = ((:real^N) DIFF s)`.
- We rewrite the goal to show that there exists a C such that the set of cells of A, which are subsets of (:real^N) DIFF s, is the same of set of all elements of `C`.
- Replace `(:real^N) DIFF c` with `UNIONS {c' | hyperplane_cell A c' /\ ~(c' = c)}`.
- To prove `(:real^N) DIFF c = UNIONS {c' | hyperplane_cell A c' /\ ~(c' = c)}`
 - Use the fact that `!A. (:real^N) = UNIONS (hyperplane_cells A)`
 - Show that the two sets must be extensionally equal.
  - Show that if x is in `UNIONS {c' | hyperplane_cell A c' /\ ~(c' = c)}` then x is in `(:real^N) DIFF c` using `DISJOINT_HYPERPLANE_CELLS_EQ`.
  - Show that if x is in `(:real^N) DIFF c` then x is in  `UNIONS {c' | hyperplane_cell A c' /\ ~(c' = c)}` using `HYPERPLANE_CELLCOMPLEX_UNIONS`.
- Use `HYPERPLANE_CELLCOMPLEX_UNIONS` saying that if all unions of hyperplane cells form a hyperplane cell complex, then so will the complement.

### Mathematical insight
This theorem states that if you have a hyperplane cell complex, then taking the complement of that region will still be a hyperplane cell complex. This is an important closure property in the theory of hyperplane arrangements.

### Dependencies
- `hyperplane_cellcomplex`
- `LEFT_IMP_EXISTS_THM`
- `UNIONS_INTERS`
- `COMPL_COMPL`
- `HYPERPLANE_CELLCOMPLEX_INTERS`
- `FORALL_IN_GSPEC`
- `UNIONS_HYPERPLANE_CELLS`
- `EXTENSION`
- `IN_DIFF`
- `UNIONS_GSPEC`
- `IN_ELIM_THM`
- `LEFT_AND_EXISTS_THM`
- `FUN_EQ_THM`
- `DISJOINT_HYPERPLANE_CELLS_EQ`
- `HYPERPLANE_CELLCOMPLEX_UNIONS`
- `HYPERPLANE_CELL_CELLCOMPLEX`

### Porting notes (optional)
The main challenge would be to ensure that the definitions and theorems about sets, unions, intersections, and complements are consistent with the target proof assistant. The handling of `GSPEC` might also need careful translation.


---

## HYPERPLANE_CELLCOMPLEX_DIFF

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_DIFF = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s DIFF t)`,
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  SIMP_TAC[HYPERPLANE_CELLCOMPLEX_COMPL; HYPERPLANE_CELLCOMPLEX_INTER]);;
```
### Informal statement
For any set `A` and sets `s` and `t`, if `s` and `t` are hyperplane cell complexes associated with `A`, then `s DIFF t` is also a hyperplane cell complex associated with `A`.

### Informal sketch
The proof proceeds as follows:
- Rewrite `s DIFF t` as `s INTER (UNIV DIFF t)`.
- Apply simplification using the theorems `HYPERPLANE_CELLCOMPLEX_COMPL` and `HYPERPLANE_CELLCOMPLEX_INTER`. Specifically:
    - `HYPERPLANE_CELLCOMPLEX_COMPL` establishes that the complement of a hyperplane cell complex is also a hyperplane cell complex.
    - `HYPERPLANE_CELLCOMPLEX_INTER` establishes that the intersection of two hyperplane cell complexes is also a hyperplane cell complex.

### Mathematical insight
The theorem demonstrates that the class of hyperplane cell complexes is closed under the set difference operation. This is a useful property when manipulating and reasoning about spatial subdivisions defined by hyperplanes. It ensures that removing one hyperplane cell complex from another still results in a valid hyperplane cell complex.

### Dependencies
- `HYPERPLANE_CELLCOMPLEX_COMPL`
- `HYPERPLANE_CELLCOMPLEX_INTER`
- `SET_RULE`


---

## HYPERPLANE_CELLCOMPLEX_MONO

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_MONO = prove
 (`!A B s:real^N->bool.
        hyperplane_cellcomplex A s /\ A SUBSET B
        ==> hyperplane_cellcomplex B s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hyperplane_cellcomplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `B:(real^N#real)->bool = A UNION (B DIFF A)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[hyperplane_cellcomplex; HYPERPLANE_CELL_UNION] THEN
  EXISTS_TAC `{c' INTER c:real^N->bool |c'| hyperplane_cell (B DIFF A) c' /\
                                            ~(c' INTER c = {})}` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`c:real^N->bool`; `c':real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_COMM];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL [DISCH_TAC; MESON_TAC[]] THEN
    MP_TAC(ISPEC `B DIFF A:(real^N#real)->bool` UNIONS_HYPERPLANE_CELLS) THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN ASM SET_TAC[]]);;
```

### Informal statement
For all sets `A` and `B` of subsets of `real^N`, and for all sets `s` of `real^N`, if `A` forms a hyperplane cell complex with respect to `s`, and `A` is a subset of `B`, then `B` also forms a hyperplane cell complex with respect to `s`.

### Informal sketch
The proof proceeds as follows:
- Assume `hyperplane_cellcomplex A s` and `A SUBSET B`.
- We want to prove `hyperplane_cellcomplex B s`.
- The definition of `hyperplane_cellcomplex` is expanded.
- We consider each cell `c` in `A`.
- We want to prove that the intersection of any two distinct cells in `B` is contained in the union of a finite set of hyperplanes `s`.
- Decompose `B` into `A UNION (B DIFF A)`.
- The `hyperplane_cellcomplex` property for cells in `A` is already known.
- Focus on cells `c'` in `B DIFF A`.
- Use `HYPERPLANE_CELLCOMPLEX_UNIONS` to show that the union of hyperplane cells forms a hyperplane cell complex.
- Show that for any `c'` in `B DIFF A`, the intersection `c' INTER c` can be expressed as the union of sets of the form `c'' INTER c`, where `c''` is a hyperplane cell in `B DIFF A`.
- Use the fact that `B DIFF A` is a subset of hyperplane cells.

### Mathematical insight
This theorem states that if a set `A` of regions forms a hyperplane cell complex, then any superset `B` of `A` also forms a hyperplane cell complex. In other words, adding more regions to a hyperplane cell complex preserves the structure.

### Dependencies
- `hyperplane_cellcomplex` (definition)
- `HYPERPLANE_CELLCOMPLEX_UNIONS` (theorem)
- `HYPERPLANE_CELL_UNION` (theorem)
- `FORALL_IN_GSPEC` (Definition)
- `EXTENSION` (Definition)
- `UNIONS_GSPEC` (Definition)
- `IN_ELIM_THM` (Theorem)
- `IN_INTER` (Theorem)
- `UNIONS_HYPERPLANE_CELLS` (Theorem)
- `IN_UNIONS` (Definition)
- `IN_UNIV` (Definition)


---

## FINITE_HYPERPLANE_CELLCOMPLEXES

### Name of formal statement
FINITE_HYPERPLANE_CELLCOMPLEXES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_HYPERPLANE_CELLCOMPLEXES = prove
 (`!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `IMAGE UNIONS {t | t SUBSET {c:real^N->bool | hyperplane_cell A c}}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET; FINITE_HYPERPLANE_CELLS] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; hyperplane_cellcomplex] THEN
  MESON_TAC[]);;
```
### Informal statement
For all sets `A`, if `A` is finite, then the set of all `c` such that `c` is a function from `real^N` to `bool` and `c` is a hyperplane cell complex of `A` is finite.

### Informal sketch
We aim to prove that if `A` is finite, then the set of `hyperplane_cellcomplex A c` is also finite.
- Starting with the assumption `FINITE A`, we use `FINITE_SUBSET` and existential introduction to rewrite our goal to showing that the image of the union of sets containing subsets `t` of the set of `hyperplane_cell A c` is finite.
- We simplify using theorems `FINITE_IMAGE`, `FINITE_POWERSET`, and `FINITE_HYPERPLANE_CELLS`.
- We rewrite the goal to a more explicit form using `SUBSET`, `IN_IMAGE`, `IN_ELIM_THM`, and `hyperplane_cellcomplex`.
- Finally, `MESON_TAC` completes the proof by discharging the remaining assumptions.

### Mathematical insight
This theorem states that if we start with a finite set of hyperplanes `A`, then the set of cell complexes induced by those hyperplanes is also finite. This result is important because it allows us to reason about the complexity of arrangements of hyperplanes. The finiteness of the cell complexes derived from finitely many hyperplanes contributes to the tractability of algorithms that operate on such hyperplane arrangements.

### Dependencies
- Theorems:
   - `FINITE_IMAGE`
   - `FINITE_POWERSET`
   - `FINITE_SUBSET`
   - `IN_ELIM_THM`
- Definitions:
   - `FINITE`
   - `SUBSET`
   - `IN_IMAGE`
   - `hyperplane_cell`
   - `hyperplane_cellcomplex`


---

## FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES

### Name of formal statement
FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES = prove
 (`!P A. FINITE A
         ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c /\ P c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cellcomplex A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLCOMPLEXES] THEN SET_TAC[]);;
```

### Informal statement
For all predicates `P` over functions from `real^N` to booleans, and for all sets `A` of hyperplanes, if `A` is finite, then the set of functions `c` from `real^N` to booleans such that `c` is a hyperplane cell complex with respect to `A` and `P(c)` holds is also finite.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and implication.
- Applying `FINITE_SUBSET`, reducing the goal to showing that the set `{c:real^N->bool | hyperplane_cellcomplex A c /\ P c}` is a subset of a finite set.
- Showing that `{c:real^N->bool | hyperplane_cellcomplex A c}` exists, which allows us to use the theorem `FINITE_HYPERPLANE_CELLCOMPLEXES`.
- Using `FINITE_HYPERPLANE_CELLCOMPLEXES` to show that the set of all `hyperplane_cellcomplex`es associated with the finite set `A` is finite, and then applying `SET_TAC[]` for basic set-theoretic reasoning.

### Mathematical insight
This theorem states that if we have a finite set of hyperplanes `A`, then any subset of the `hyperplane_cellcomplex`es formed from `A` defined by some predicate `P` is also finite. This is a direct consequence of the fact that the set of *all* `hyperplane_cellcomplex`es for a finite set of hyperplanes is finite.

### Dependencies
- `FINITE_SUBSET`
- `FINITE_HYPERPLANE_CELLCOMPLEXES`
- `hyperplane_cellcomplex`
- `FINITE`


---

## FINITE_SET_OF_HYPERPLANE_CELLS

### Name of formal statement
FINITE_SET_OF_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_SET_OF_HYPERPLANE_CELLS = prove
 (`!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c)
         ==> FINITE C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cellcomplex A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLCOMPLEXES] THEN ASM SET_TAC[]);;
```
### Informal statement
For all sets `A` of hyperplanes in `real^N` and all sets `C` of regions in `real^N`, if `A` is finite and every region `c` in `C` is a hyperplane cell complex induced by `A`, then `C` is finite.

### Informal sketch
The proof proceeds as follows:
- Assume that `A` is a finite set and that every element `c` of the set `C` is a `hyperplane_cellcomplex A c`.
- Apply `FINITE_SUBSET`, which states that a subset of a finite set is finite, reducing the goal to proving that `{c:real^N->bool | hyperplane_cellcomplex A c}` is finite, which means constructing a finite superset of `C`.
- Show that there exists a set containing all `c` such that `hyperplane_cellcomplex A c`.
- Apply `FINITE_HYPERPLANE_CELLCOMPLEXES` to show that the set of all `hyperplane_cellcomplex A c` is finite.
- Use `ASM SET_TAC[]` to simplify the goal using the assumptions and the finiteness of the superset.

### Mathematical insight
This theorem establishes that the set of all hyperplane cell complexes induced by a finite collection of hyperplanes is itself finite. This is a crucial result for reasoning about geometric structures arising from hyperplane arrangements, where finiteness properties are essential for algorithm termination and complexity analysis.

### Dependencies
- Theorems: `FINITE_SUBSET`, `FINITE_HYPERPLANE_CELLCOMPLEXES`
- Definitions: `hyperplane_cellcomplex`, `FINITE`


---

## CELL_SUBSET_CELLCOMPLEX

### Name of formal statement
CELL_SUBSET_CELLCOMPLEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CELL_SUBSET_CELLCOMPLEX = prove
 (`!A s c:real^N->bool.
        hyperplane_cell A c /\ hyperplane_cellcomplex A s
        ==> (c SUBSET s <=> ~(DISJOINT c s))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hyperplane_cellcomplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN EQ_TAC THENL
   [ASM_CASES_TAC `c:real^N->bool = {}` THENL
     [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ASM SET_TAC[]];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `c':real^N->bool`] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`A:(real^N#real)->bool`; `c:real^N->bool`;
      `c':real^N->bool`] DISJOINT_HYPERPLANE_CELLS_EQ) THEN
    ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `c':real^N->bool = c` THENL
     [DISCH_THEN(K ALL_TAC); ASM SET_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE `c IN C ==> c SUBSET UNIONS C`) THEN
    ASM_MESON_TAC[]]);;
```

### Informal statement
For any `A` and `s` both functions from `real^N` to boolean values (representing sets of points in N-dimensional space), and for any function `c` from `real^N` to boolean values (representing a set of points in N-dimensional space), if `c` is a hyperplane cell with respect to `A` and `s` is a hyperplane cell complex with respect to `A`, then `c` is a subset of `s` if and only if `c` and `s` are not disjoint.

### Informal sketch
The proof proceeds by showing that the statement `c SUBSET s <=> ~(DISJOINT c s)` holds for a hyperplane cell `c` and hyperplane cell complex `s`.
- First, rewrite using the definition of `hyperplane_cellcomplex` to express `s` as a union of hyperplane cells `C`.
- Introduce a case split: Assume `c` is empty. Then `c` is a subset of `s` vacuously, and `c` is disjoint from `s` if and only if `s` is empty, which is addressed using `NONEMPTY_HYPERPLANE_CELL`.
- In the case that `c` is nonempty, rewrite `DISJOINT` in terms of intersections, and use the fact that a hyperplane cell is nonempty, along with `UNIONS_GSPEC` to reduce `c SUBSET UNIONS C <=> ~(DISJOINT c (UNIONS C))` to `!x. x IN c ==> (?c'. c' IN C /\ x IN c')`.
- Apply `DISJOINT_HYPERPLANE_CELLS_EQ` which states disjointness of hyperplane cells is equivalent to equality, given that one is a subset of the other.
- Perform a sub-case split: `c' = c`. Complete the proof.
- Apply `SET_RULE `c IN C ==> c SUBSET UNIONS C`` to complete the proof with `ASM_MESON_TAC[]`

### Mathematical insight
This theorem establishes a fundamental relationship between a hyperplane cell and a hyperplane cell complex. It states that a hyperplane cell is contained within a hyperplane cell complex if and only if they are not disjoint. This is an intuitive result, as the cell complex is constructed as a union of cells. The theorem highlights the relationship between set membership and disjointness, crucial for reasoning about spatial decomposition in N-dimensional space.

### Dependencies
- `hyperplane_cell`
- `hyperplane_cellcomplex`
- `DISJOINT`
- `INTER_UNIONS`
- `MEMBER_NOT_EMPTY`
- `UNIONS_GSPEC`
- `IN_ELIM_THM`
- `LEFT_IMP_EXISTS_THM`
- `IN_INTER`
- `DISJOINT_HYPERPLANE_CELLS_EQ`
- `NONEMPTY_HYPERPLANE_CELL`

### Porting notes (optional)
- The proof relies heavily on rewriting definitions and using MESON for automated reasoning. The definitions of `hyperplane_cell` and `hyperplane_cellcomplex` need to be carefully ported. The properties related to set theory such as `DISJOINT`, `INTER_UNIONS`, `UNIONS_GSPEC`, `IN_INTER` will need to be present.
- The `DISJOINT_HYPERPLANE_CELLS_EQ` lemma will need to be proven in the target proof assistant, likely requiring a similar argument based on the definitions of hyperplane cells.


---

## euler_characteristic

### Name of formal statement
euler_characteristic

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let euler_characteristic = new_definition
 `euler_characteristic A (s:real^N->bool) =
        sum {c | hyperplane_cell A c /\ c SUBSET s}
            (\c. (-- &1) pow (num_of_int(aff_dim c)))`;;
```

### Informal statement
The Euler characteristic of a set `A` (where `A` defines an arrangement of hyperplanes) with respect to a subset `s` of `real^N` is defined as the sum, over all hyperplane cells `c` such that `c` is a subset of `s`, of `(-- &1)` raised to the power of the number of integers representing the affine dimension of `c`.

### Informal sketch
The definition introduces the concept of the Euler characteristic for hyperplane arrangements.

- The definition calculates a sum.
- This sum has terms indexed by hyperplane cells `c`. The condition `hyperplane_cell A c /\ c SUBSET s` filters the summation to only consider hyperplane cells `c` within the arrangement `A` that are also subsets of a given set `s`.
- Each term in the sum is `(-- &1) pow (num_of_int(aff_dim c))`. This calculates (-1) to the power of the affine dimension of the cell `c`. The affine dimension `aff_dim c` is an element of type `:num`, which has to be converted into integer and then into real. The term `(-- &1)` represent the real number -1.

### Mathematical insight
The Euler characteristic is a topological invariant. This definition provides a way to compute the Euler characteristic for arrangements of hyperplanes, which are geometric configurations of hyperplanes in a real space. The key idea is to sum alternating signs (depending on dimension) for cells lying within a specified subset `s`.

### Dependencies
Arrangement theory (hyperplane_cell, aff_dim)
Real analysis (sum, pow)
Set theory (SUBSET)
Integer theory (num_of_int)


---

## EULER_CHARACTERISTIC_EMPTY

### Name of formal statement
EULER_CHARACTERISTIC_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_EMPTY = prove
 (`euler_characteristic A {} = &0`,
  REWRITE_TAC[euler_characteristic; SUBSET_EMPTY] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN
  MATCH_MP_TAC(MESON[] `~(?x. x IN s) ==> (!x. x IN s ==> P x)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[NONEMPTY_HYPERPLANE_CELL]);;
```
### Informal statement
The Euler characteristic of the empty set `A {}` is equal to the real number 0.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using the definition of `euler_characteristic` and the subset relation of the empty set `SUBSET_EMPTY`.
- Then, use the theorem that the sum over an empty set is 0. `SUM_EQ_0`.
- Instantiate a higher-order theorem that if there is no `x` such that `x` is in `s`, then for all `x`, if `x` is in `s`, then `P x` holds, where `s` is a set and `P` a predicate.
- Apply `IN_ELIM_THM` to eliminate the empty `IN` relation.
- Finally, complete the proof using the theorem `NONEMPTY_HYPERPLANE_CELL`.

### Mathematical insight
This theorem establishes a base case for the Euler characteristic, showing that the empty set contributes zero to any calculation of the Euler characteristic of a more complex space. The Euler characteristic is a topological invariant, and this result is consistent with that understanding. A space containing no cells has an Euler characteristic of 0.

### Dependencies
- Definitions: `euler_characteristic`
- Theorems: `SUBSET_EMPTY`, `SUM_EQ_0`, `IN_ELIM_THM`, `NONEMPTY_HYPERPLANE_CELL`


---

## EULER_CHARACTERISTIC_CELL_UNIONS

### Name of formal statement
EULER_CHARACTERISTIC_CELL_UNIONS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELL_UNIONS = prove
 (`!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. (-- &1) pow (num_of_int(aff_dim c)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[euler_characteristic] THEN
  MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
  EQ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `~(c:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ALL_TAC] THEN
  REWRITE_TAC[MEMBER_NOT_EMPTY; SUBSET; IN_UNIONS] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(DISJOINT (c:real^N->bool) c')` MP_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[DISJOINT_HYPERPLANE_CELLS_EQ]]);;
```

### Informal statement
For any set `A` of real vectors of dimension `N` and any set `C` of sets of real vectors of dimension `N`, if every set `c` in `C` is a hyperplane cell with respect to `A`, then the Euler characteristic of `A` applied to the union of all sets in `C` is equal to the sum over all sets `c` in `C` of `(-1)` raised to the power of the affine dimension of `c`.

### Informal sketch
The proof proceeds by induction on the set `C` of hyperplane cells.
- The base case uses the definition of `euler_characteristic`.
- The inductive step starts by rewriting the Euler characteristic of the union using the definition `euler_characteristic`. Then it uses the fact that `s = t ==> sum s f = sum t f`.
- The proof requires showing that the set `c` is nonempty. This uses the theorem `NONEMPTY_HYPERPLANE_CELL`.
- The proof requires showing that some `x` exists such that `x` is in the union of `C`.
- We need to pick an arbitrary `c'` from `C`
- The proof establishes the disjointness of `c` and `c'`, and that they are each hyperplane cells, so that `DISJOINT_HYPERPLANE_CELLS_EQ` can be applied.

### Mathematical insight
This theorem relates the Euler characteristic of a union of hyperplane cells to the sum of (-1) raised to the power of their affine dimensions. This provides a way to compute the Euler characteristic of a complex geometric object by decomposing it into simpler cell structures. The formula connects a topological invariant (Euler characteristic) to a geometric property (affine dimension).

### Dependencies
- `euler_characteristic`
- `EXTENSION`
- `IN_ELIM_THM`
- `NONEMPTY_HYPERPLANE_CELL`
- `MEMBER_NOT_EMPTY`
- `SUBSET`
- `IN_UNIONS`
- `GSYM MEMBER_NOT_EMPTY`
- `LEFT_IMP_EXISTS_THM`
- `DISJOINT_HYPERPLANE_CELLS_EQ`


---

## EULER_CHARACTERISTIC_CELL

### Name of formal statement
EULER_CHARACTERISTIC_CELL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELL = prove
 (`!A c. hyperplane_cell A c
         ==> euler_characteristic A c =  (-- &1) pow (num_of_int(aff_dim c))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM UNIONS_1] THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELL_UNIONS; IN_SING; SUM_SING]);;
```

### Informal statement
For any set `A` and any hyperplane cell `c`, `c` being a `hyperplane_cell` of `A` is equivalent to the Euler characteristic of `A` and `c` being equal to `(-1)` raised to the power of the number of elements in the integer representation of the affine dimension of `c`.

### Informal sketch
The proof proceeds by:
- Stripping the goal.
- Rewriting with `GSYM UNIONS_1` after applying `LAND_CONV` and `RAND_CONV` to its right-hand side.
- Applying an assumption-based simplification tactic using `EULER_CHARACTERISTIC_CELL_UNIONS`, `IN_SING`, and `SUM_SING`.

### Mathematical insight
This theorem provides a formula for computing the Euler characteristic of a hyperplane cell.  The Euler characteristic is a topological invariant, and this result connects it to the affine dimension of the cell. For instance, if `c` is a 0-dimensional cell (a point), its affine dimension is 0, and the Euler characteristic is `(-1)^0 = 1`. If `c` is a 1-dimensional cell (an interval), its affine dimension is 1, and the Euler characteristic is `(-1)^1 = -1`.

### Dependencies
- Definitions: `hyperplane_cell`, `euler_characteristic`, `aff_dim`
- Theorems: `EULER_CHARACTERISTIC_CELL_UNIONS`, `IN_SING`, `SUM_SING`, `UNIONS_1`


---

## EULER_CHARACTERISTIC_CELLCOMPLEX_UNION

### Name of formal statement
EULER_CHARACTERISTIC_CELLCOMPLEX_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELLCOMPLEX_UNION = prove
 (`!A s t:real^N->bool.
        FINITE A /\
        hyperplane_cellcomplex A s /\
        hyperplane_cellcomplex A t /\
        DISJOINT s t
        ==> euler_characteristic A (s UNION t) =
            euler_characteristic A s + euler_characteristic A t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[euler_characteristic] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
  ASM_SIMP_TAC[FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNION] THEN
  CONJ_TAC THEN X_GEN_TAC `c:real^N->bool` THENL
   [ASM_CASES_TAC `c:real^N->bool = {}` THENL
     [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ASM SET_TAC[]];
    ASM_CASES_TAC `hyperplane_cell A (c:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `A:(real^N#real)->bool` CELL_SUBSET_CELLCOMPLEX) THEN
    ASM_SIMP_TAC[HYPERPLANE_CELLCOMPLEX_UNION] THEN SET_TAC[]]);;
```
### Informal statement
For any predicate `A` on `real^N`, and any sets of cells `s` and `t` that are finite and form hyperplane cell complexes relative to `A`, if `s` and `t` are disjoint, then the Euler characteristic of the union of `s` and `t` is equal to the sum of the Euler characteristics of `s` and `t`.

### Informal sketch
The proof proceeds by:
- Stripping the assumptions and goal.
- Rewriting with the definition of `euler_characteristic`.
- Applying the symmetric conversion to prepare for using `SUM_UNION_EQ`.
- Matching with `SUM_UNION_EQ`.
- Simplifying using `FINITE_RESTRICT_HYPERPLANE_CELLS`.
- Performing rewrites using `EXTENSION`, `IN_INTER`, `IN_ELIM_THM`, `NOT_IN_EMPTY`, and `IN_UNION`.
- Splitting the goal into two subgoals for further analysis.
- Considering cases where the cell `c` is the empty set, and then handling the non-empty case using `NONEMPTY_HYPERPLANE_CELL` and `SET_TAC`.
- Considering cases whether a given cell `c` constitutes a `hyperplane_cell A c`, rewriting by assumptions, utilizing `CELL_SUBSET_CELLCOMPLEX`, simplifying using `HYPERPLANE_CELLCOMPLEX_UNION` and completing the proof using `SET_TAC`.

### Mathematical insight
The theorem demonstrates a fundamental property of the Euler characteristic: its additivity over disjoint unions of cell complexes. This reflects the Euler characteristic's role as a measure of topological size, where disjoint pieces contribute independently to the overall measure. The theorem provides a valuable tool for computing the Euler characteristic of complex arrangements by decomposing them into simpler, disjoint components.

### Dependencies
- `FINITE`
- `hyperplane_cellcomplex`
- `DISJOINT`
- `euler_characteristic`
- `SUM_UNION_EQ`
- `FINITE_RESTRICT_HYPERPLANE_CELLS`
- `EXTENSION`
- `IN_INTER`
- `IN_ELIM_THM`
- `NOT_IN_EMPTY`
- `IN_UNION`
- `NONEMPTY_HYPERPLANE_CELL`
- `hyperplane_cell`
- `CELL_SUBSET_CELLCOMPLEX`
- `HYPERPLANE_CELLCOMPLEX_UNION`


---

## EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS

### Name of formal statement
EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS = prove
 (`!A C. FINITE A /\
         (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c) /\
         pairwise DISJOINT C
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. euler_characteristic A c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `FINITE(C:(real^N->bool)->bool)` THENL
   [UNDISCH_TAC `FINITE(C:(real^N->bool)->bool)`;
    ASM_MESON_TAC[FINITE_SET_OF_HYPERPLANE_CELLS]] THEN
  SPEC_TAC(`C:(real^N->bool)->bool`,`C:(real^N->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[EULER_CHARACTERISTIC_EMPTY; SUM_CLAUSES; UNIONS_0] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNIONS_INSERT] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) EULER_CHARACTERISTIC_CELLCOMPLEX_UNION o
        lhs o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC[DISJOINT; INTER_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                  FORALL_IN_INSERT; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC[INTER_COMM]];
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
    ASM_REWRITE_TAC[pairwise] THEN ASM SET_TAC[]]);;
```

### Informal statement
For any set `A` of real vectors in `N` dimensions and any set `C` of hyperplane cell complexes such that `A` is finite, each element `c` in `C` is a hyperplane cell complex with respect to `A`, and the elements in `C` are pairwise disjoint, the Euler characteristic of `A` with respect to the union of the elements in `C` is equal to the sum, over all `c` in `C`, of the Euler characteristic of `A` with respect to `c`.

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `C` of hyperplane cell complexes:
- Base Case: If `C` is empty, then the union of the elements in `C` is empty; the Euler characteristic of `A` with respect to the empty set is zero, and the sum over the empty set `C` is also zero.
- Inductive Step: Assume that the theorem holds for any set `C` of hyperplane cell complexes that satisfy assumptions of finiteness, the cell complexes being defined w.r.t `A`, and pairwise disjointness. Need to show that the theorem holds for `INSERT c C`, where `c` is a hyperplane complex
    - Rewrite `UNIONS (INSERT c C)` as `c UNION UNIONS C`.
    - Apply `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION` to get `euler_characteristic A (c UNION UNIONS C) = euler_characteristic A c + euler_characteristic A (UNIONS C) - euler_characteristic A (c INTER UNIONS C)`.
    - From the fact that `C` is pairwise disjoint, show that `c INTER UNIONS C` is empty. This relies on showing that `c` is disjoint from each element of `C`.
    - Since `c INTER UNIONS C` is empty, `euler_characteristic A (c INTER UNIONS C)` is `euler_characteristic A {} = 0`.
    - By the inductive hypothesis: `euler_characteristic A (UNIONS C) = sum C (\c. euler_characteristic A c)`.
    - So, `euler_characteristic A (UNIONS(INSERT c C)) = euler_characteristic A c + sum C (\c. euler_characteristic A c) = sum (INSERT c C) (\c. euler_characteristic A c)`.

The proof uses rewriting and simplification with theorems about Euler characteristics, unions, intersections, sets, and sums.

### Mathematical insight
This theorem states that the Euler characteristic is additive for pairwise disjoint hyperplane cell complexes. This is an important property that allows us to compute the Euler characteristic of a complex by decomposing it into simpler disjoint pieces.

### Dependencies
- `FINITE`
- `hyperplane_cellcomplex`
- `DISJOINT`
- `euler_characteristic`
- `UNIONS`
- `SUM_CLAUSES`
- `EULER_CHARACTERISTIC_EMPTY`
- `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`
- `UNIONS_0`
- `UNIONS_INSERT`
- `HYPERPLANE_CELLCOMPLEX_UNIONS`
- `INTER_UNIONS`
- `pairwise`
- `DISJOINT`
- `pairwise`
- `INTER_COMM`
- `EMPTY_UNIONS`
- `FORALL_IN_GSPEC`
- `IMP_CONJ`
- `RIGHT_FORALL_IMP_THM`
- `FORALL_IN_INSERT`
- `FINITE_SET_OF_HYPERPLANE_CELLS`

### Porting notes (optional)
- Ensure availability of appropriate definitions of `FINITE`, `DISJOINT` (or equivalent notions of pairwise disjointness), `UNIONS`, `INTER`, and `euler_characteristic`.
- The definition of `hyperplane_cellcomplex` may require adjustments based on the target system's representation of real vectors and hyperplanes.
- The inductive proof might require adjustments based on the automation available in the target system.


---

## EULER_CHARACTERISTIC

### Name of formal statement
EULER_CHARACTERISTIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC = prove
 (`!A s:real^N->bool.
        FINITE A
        ==> euler_characteristic A s =
            sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {c | hyperplane_cell A c /\ c SUBSET s /\
                                 aff_dim c = &d}))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[euler_characteristic] THEN
  MP_TAC(ISPECL [`\c:real^N->bool. aff_dim c`;
                 `\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c))`;
                 `{c:real^N->bool | hyperplane_cell A c /\ c SUBSET s}`;
                 `IMAGE int_of_num (0..dimindex(:N))`]
                SUM_GROUP) THEN
  SIMP_TAC[SUM_IMAGE; INT_OF_NUM_EQ; o_DEF; NUM_OF_INT_OF_NUM] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; INT_EXISTS_POS] THEN
    EXISTS_TAC `aff_dim(c:real^N->bool)` THEN
    REWRITE_TAC[AFF_DIM_LE_UNIV; AFF_DIM_POS_LE] THEN
    ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL];
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
    REWRITE_TAC[REAL_MUL_AC]]);;
```

### Informal statement
For any finite set of hyperplanes `A` in `real^N` and any set `s` in `real^N`, the Euler characteristic of `A` with respect to `s` is equal to the sum, from 0 to `dimindex(:N)`, of `(-- &1) pow d * &(CARD {c | hyperplane_cell A c /\ c SUBSET s /\ aff_dim c = &d})`, where `d` is the dimension. In other words, it is the alternating sum of the number of hyperplane cells of a given dimension which are subsets of `s`.

### Informal sketch
The proof proceeds as follows:
- Start by expanding the definition of `euler_characteristic`.
- Apply `SUM_GROUP` to rearrange the summation according to affine dimension, after specializing it with appropriate parameters. This step manipulates the sum so we can group terms by the affine dimension of the cells.
- Simplify the summation using `SUM_IMAGE`, `INT_OF_NUM_EQ`, `o_DEF`, and `NUM_OF_INT_OF_NUM`.
- The proof splits into two branches using `ANTS_TAC`.
- First branch: Assuming `hyperplane_cell A c /\ c SUBSET s`.
  - Use `FINITE_RESTRICT_HYPERPLANE_CELLS` to deduce that this is a finite set.
  - Use subset rewriting, and then rewrite with `FORALL_IN_IMAGE` and `IN_ELIM_THM`.
  - Generalize the variable `c`.
  - Rewrite with `IN_IMAGE` and `IN_NUMSEG`, and then with `LE_0`.
  - Rewrite with `GSYM INT_OF_NUM_LE` and `INT_EXISTS_POS`.
  - Introduce the witness `aff_dim(c:real^N->bool)` and rewrite with `AFF_DIM_LE_UNIV` and `AFF_DIM_POS_LE`.
  - Apply `NONEMPTY_HYPERPLANE_CELL` using the Meson tactic.
- Second branch: Discharges assumption using `DISCH_THEN`, substitutes using `SUBST1_TAC o SYM`, and rewrites using `IN_ELIM_THM` and `GSYM CONJ_ASSOC`.  Then, simplify the assumption using `SUM_CONST` and `FINITE_RESTRICT_HYPERPLANE_CELLS`. Finally, rewrite using `REAL_MUL_AC`.

### Mathematical insight
The Euler characteristic is a topological invariant that, in this context, provides a way to count the "complexity" of a space partitioned by hyperplanes. The theorem provides a concrete way to compute the Euler characteristic by summing the number of cells of each dimension, weighted by alternating signs.

### Dependencies
- Definitions:
  - `euler_characteristic`
  - `FINITE`
  - `hyperplane_cell`
  - `SUBSET`
  - `aff_dim`
  - `dimindex`
  - `CARD`
  - `sum`
- Theorems:
  - `SUM_IMAGE`
  - `INT_OF_NUM_EQ`
  - `NUM_OF_INT_OF_NUM`
  - `FINITE_RESTRICT_HYPERPLANE_CELLS`
  - `FORALL_IN_IMAGE`
  - `IN_ELIM_THM`
  - `IN_IMAGE`
  - `IN_NUMSEG`
  - `LE_0`
  - `INT_OF_NUM_LE`
  - `INT_EXISTS_POS`
  - `AFF_DIM_LE_UNIV`
  - `AFF_DIM_POS_LE`
  - `NONEMPTY_HYPERPLANE_CELL`
  - `CONJ_ASSOC`
  - `SUM_CONST`
  - `REAL_MUL_AC`

### Porting notes (optional)
- The use of `dimindex(:N)` as the upper bound of the summation may need careful translation depending on how dimension types are handled in the target proof assistant.
- The tactic `ASM_MESON_TAC` is a powerful automated reasoner in HOL Light, so its effect may need to be replicated by a series of simpler steps in other systems.


---

## HYPERPLANE_CELLS_DISTINCT_LEMMA

### Name of formal statement
HYPERPLANE_CELLS_DISTINCT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLS_DISTINCT_LEMMA = prove
 (`!a b. {x | a dot x = b} INTER {x | a dot x < b} = {} /\
         {x | a dot x = b} INTER {x | a dot x > b} = {} /\
         {x | a dot x < b} INTER {x | a dot x = b} = {} /\
         {x | a dot x < b} INTER {x | a dot x > b} = {} /\
         {x | a dot x > b} INTER {x | a dot x = b} = {} /\
         {x | a dot x > b} INTER {x | a dot x < b} = {}`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For all real numbers `a` and `b`, the intersection of the set of points `x` such that `a dot x = b` and the set of points `x` such that `a dot x < b` is the empty set, and the intersection of the set of points `x` such that `a dot x = b` and the set of points `x` such that `a dot x > b` is the empty set, and the intersection of the set of points `x` such that `a dot x < b` and the set of points `x` such that `a dot x = b` is the empty set, and the intersection of the set of points `x` such that `a dot x < b` and the set of points `x` such that `a dot x > b` is the empty set, and the intersection of the set of points `x` such that `a dot x > b` and the set of points `x` such that `a dot x = b` is the empty set, and the intersection of the set of points `x` such that `a dot x > b` and the set of points `x` such that `a dot x < b` is the empty set.

### Informal sketch
The proof uses rewriting with the following theorems:
- `EXTENSION`: Axiom stating extensionality for sets.
- `IN_INTER`: Theorem stating that `x IN (a INTER b)` is equivalent to `x IN a /\ x IN b`.
- `IN_ELIM_THM`: A theorem to eliminate set membership.
- `NOT_IN_EMPTY`: Theorem stating that `!(x. x IN {})` (i.e. nothing is in the empty set).

Then, `REAL_ARITH_TAC` is used to prove the arithmetic facts.

### Mathematical insight
This lemma expresses the mutual exclusivity of the equality, less-than, and greater-than relations for the dot product of two vectors. In other words, a point cannot simultaneously satisfy `a dot x = b` and `a dot x < b`, `a dot x = b` and `a dot x > b`, or `a dot x < b` and `a dot x > b`. This disjointness is fundamental for understanding hyperplane arrangements.

### Dependencies
- `EXTENSION`
- `IN_INTER`
- `IN_ELIM_THM`
- `NOT_IN_EMPTY`


---

## EULER_CHARACTERSTIC_LEMMA

### Name of formal statement
EULER_CHARACTERSTIC_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERSTIC_LEMMA = prove
 (`!A h s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> euler_characteristic (h INSERT A) s = euler_characteristic A s`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC
   [`A:(real^N#real)->bool`; `a:real^N`; `b:real`; `s:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[hyperplane_cellcomplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c /\
                                hyperplane_cellcomplex ((a,b) INSERT A) c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    EXISTS_TAC `A:(real^N#real)->bool` THEN
    ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pairwise DISJOINT (C:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PAIRWISE_DISJOINT_HYPERPLANE_CELLS]; ALL_TAC] THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS; FINITE_INSERT] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `hyperplane_cell ((a,b) INSERT A) (c:real^N->bool)` THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELL] THEN
  SUBGOAL_THEN `~(a:real^N = vec 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    SIMP_TAC[CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
    REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN
    REWRITE_TAC[HYPERPLANE_CELL_SING; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[INTER_UNIV; UNWIND_THM1] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[euler_characteristic] THEN
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {c' INTER c |c'| hyperplane_cell {(a,b)} c' /\ ~(c' INTER c = {})}
        (\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `c':real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c1:real^N->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `c2:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(DISJOINT c2 (c:real^N->bool))` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[DISJOINT_HYPERPLANE_CELLS_EQ]];
      DISCH_THEN(X_CHOOSE_THEN `c1:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN
      MAP_EVERY EXISTS_TAC [`c1:real^N->bool`; `c:real^N->bool`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[HYPERPLANE_CELL_SING] THEN
  SUBGOAL_THEN `~(c:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ALL_TAC] THEN
  MAP_EVERY (fun t ->
   ASM_CASES_TAC t THENL
    [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
      `sum {c} (\c:real^N->bool. (-- &1) pow num_of_int (aff_dim c))` THEN
     CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_SING]] THEN
     MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
     GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `c':real^N->bool` THEN
     REWRITE_TAC[IN_SING; IN_ELIM_THM] THEN
     REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
     REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2; GSYM CONJ_ASSOC] THEN
     EQ_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
     MP_TAC(ISPECL [`a:real^N`; `b:real`] HYPERPLANE_CELLS_DISTINCT_LEMMA) THEN
     ASM SET_TAC[];
     ALL_TAC])
   [`c SUBSET {x:real^N | a dot x < b}`;
    `c SUBSET {x:real^N | a dot x > b}`;
    `c SUBSET {x:real^N | a dot x = b}`] THEN
  SUBGOAL_THEN `~(c INTER {x:real^N | a dot x = b} = {})` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?u v:real^N. u IN c /\ ~(a dot u < b) /\ v IN c /\ ~(a dot v > b)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_gt; REAL_NOT_LT; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN SIMP_TAC[REAL_LE_LT] THEN
    ASM_CASES_TAC `(a:real^N) dot u = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(a:real^N) dot v = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `v + (b - a dot v) / (a dot u - a dot v) % (u - v):real^N` THEN
    SUBGOAL_THEN `(a:real^N) dot v < a dot u` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB; REAL_DIV_RMUL; REAL_SUB_LT;
                 REAL_LT_IMP_NZ; REAL_SUB_ADD2] THEN
    REWRITE_TAC[VECTOR_ARITH
     `v + a % (u - v):real^N = (&1 - a) % v + a % u`] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_MESON_TAC[HYPERPLANE_CELL_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c INTER {x:real^N | a dot x < b} = {}) /\
                ~(c INTER {x:real^N | a dot x > b} = {})`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?u v:real^N.
         u IN c /\ a dot u = b /\ v IN c /\ ~(a dot v = b) /\ ~(u = v)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (affine hull c)) (c:real^N->bool)`
    MP_TAC THENL [ASM_MESON_TAC[HYPERPLANE_CELL_RELATIVELY_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[open_in] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `u:real^N`)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `e:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `u - e / &2 / norm(v - u) % (v - u):real^N`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(u - a:real^N,u) = norm a`] THEN
      REWRITE_TAC[VECTOR_ARITH `x - a % (y - z):real^N = x + a % (z - y)`] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
      ASM_REWRITE_TAC[REAL_ARITH `abs e / &2 < e <=> &0 < e`] THEN
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC];
      DISCH_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(a:real^N) dot v < b \/ a dot v > b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `u - e / &2 / norm(v - u) % (v - u):real^N` THEN
      ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
      REWRITE_TAC[REAL_ARITH `b - x * y > b <=> &0 < x * --y`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC;
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]] THEN
    EXISTS_TAC `u - e / &2 / norm(v - u) % (v - u):real^N` THEN
    ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
    REWRITE_TAC[REAL_ARITH `b - x * y > b <=> &0 < x * --y`;
                REAL_ARITH `b - x < b <=> &0 < x`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum {{x | a dot x = b} INTER c,
         {x | a dot x > b} INTER c,
         {x | a dot x < b} INTER c}
        (\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `c':real^N->bool` THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2; GSYM CONJ_ASSOC] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  ASM_SIMP_TAC[HYPERPLANE_CELLS_DISTINCT_LEMMA; REAL_ADD_RID; SET_RULE
   `s INTER t = {} /\ ~(c INTER s = {}) ==> ~(c INTER s = c INTER t)`] THEN
  SUBGOAL_THEN
   `aff_dim (c INTER {x:real^N | a dot x < b}) = aff_dim c /\
    aff_dim (c INTER {x:real^N | a dot x > b}) = aff_dim c`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN CONJ_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
    ASM_MESON_TAC[HYPERPLANE_CELL_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `aff_dim c = aff_dim(c INTER {x:real^N | a dot x = b}) + &1`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`A:real^N#real->bool`; `c:real^N->bool`]
        HYPERPLANE_CELL_INTER_OPEN_AFFINE) THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    SUBGOAL_THEN
     `affine hull (s INTER t) = affine hull t /\
      affine hull ((s INTER t) INTER {x:real^N | a dot x = b}) =
      affine hull (t INTER {x:real^N | a dot x = b})`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [REWRITE_TAC[INTER_ASSOC] THEN CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [INTER_COMM] THEN
      MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
      ASM_SIMP_TAC[CONVEX_INTER; CONVEX_HYPERPLANE; AFFINE_IMP_CONVEX] THEN
      ASM SET_TAC[];
      REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_SUB_ADD]) THEN
      ASM SET_TAC[]];
    SUBGOAL_THEN `&0 <= aff_dim (c INTER {x:real^N | a dot x = b})` MP_TAC
    THENL [REWRITE_TAC[AFF_DIM_POS_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`aff_dim (c INTER {x:real^N | a dot x = b})`,`i:int`) THEN
    REWRITE_TAC[GSYM INT_FORALL_POS] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC]);;
```
### Informal statement
For all sets `A` of hyperplanes in `real^N` (i.e., `A` is a function from `real^N` product `real` to boolean), and for all functions `s` from `real^N` to boolean satisfying the condition that `A` is a `hyperplane_cellcomplex` with respect to `s`; it holds that the `euler_characteristic` of the set `A` with a single hyperplane `h` inserted, `h INSERT A`, with respect to `s` equals the `euler_characteristic` of `A` with respect to `s`.

### Informal sketch
The proof proceeds by induction on the number of hyperplanes.

- First, choose a cellcomplex `C` such that `s` is the union of cells in `C`.

- Verify that if `c` is in `C`, then `c` is both a hyperplane cellcomplex with respect to `A` and a hyperplane cellcomplex with respect to `(a,b) INSERT A`.

- Show that `C` is pairwise disjoint.

- Apply the theorem `EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS` and simplify using `FINITE_INSERT`.

- Perform a case split based on whether `hyperplane_cell ((a,b) INSERT A) (c:real^N->bool)` holds.

- Assume `~(a:real^N = vec 0)`.

- Expand the definition of `euler_characteristic`.

- Rewrite `x INSERT s = {x} UNION s` and `HYPERPLANE_CELL_UNION`.

- Construct a sum over intersections.

- Show that `~(c:real^N->bool = {})`.

- Perform case splits based on whether `c SUBSET {x:real^N | a dot x < b}`, `c SUBSET {x:real^N | a dot x > b}` or `c SUBSET {x:real^N | a dot x = b}`.

- Assume and prove that `~(c INTER {x:real^N | a dot x = b} = {})`.

- Assume and prove that `~(c INTER {x:real^N | a dot x < b} = {}) /\ ~(c INTER {x:real^N | a dot x > b} = {})`.

- Construct a sum over `{x | a dot x = b} INTER c`, `{x | a dot x > b} INTER c`, `{x | a dot x < b} INTER c`.

- Show that `aff_dim (c INTER {x:real^N | a dot x < b}) = aff_dim c /\ aff_dim (c INTER {x:real^N | a dot x > b}) = aff_dim c`.

- Show that `aff_dim c = aff_dim(c INTER {x:real^N | a dot x = b}) + &1`.

- Finish the proof by real arithmetic.

### Mathematical insight
This lemma is a key step in proving that the Euler characteristic is invariant under subdivisions of hyperplane arrangements. The Euler characteristic is useful for counting objects and showing topological properties of geometric structures, and this lemma extends its formal use.

### Dependencies
- `FORALL_PAIR_THM`
- `hyperplane_cellcomplex`
- `HYPERPLANE_CELL_CELLCOMPLEX`
- `HYPERPLANE_CELLCOMPLEX_MONO`
- `PAIRWISE_DISJOINT_HYPERPLANE_CELLS`
- `EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS`
- `FINITE_INSERT`
- `SUM_EQ`
- `EULER_CHARACTERISTIC_CELL`
- `CONTRAPOS_THM`
- `SET_RULE x INSERT s = {x} UNION s`
- `HYPERPLANE_CELL_UNION`
- `HYPERPLANE_CELL_SING`
- `RIGHT_EXISTS_AND_THM`
- `UNWIND_THM2`
- `CONJ_TAC`
- `NONEMPTY_HYPERPLANE_CELL`
- `CONJ_SYM`
- `INTER_UNIV`
- `UNWIND_THM1`
- `euler_characteristic`
- `EXTENSION`
- `IN_ELIM_THM`
- `MONO_EXISTS`
- `DISJOINT_HYPERPLANE_CELLS_EQ`
- `INTER_SUBSET`
- `NONEMPTY_HYPERPLANE_CELL`
- `SUM_SING`
- `IN_SING`
- `TAUT (a \/ b) /\ c <=> a /\ c \/ b /\ c`
- `EXISTS_OR_THM`
- `GSYM CONJ_ASSOC`
- `HYPERPLANE_CELLS_DISTINCT_LEMMA`
- `REAL_NOT_LT`
- `MEMBER_NOT_EMPTY`
- `IN_INTER`
- `LEFT_IMP_EXISTS_THM`
- `REAL_LE_LT`
- `HYPERPLANE_CELL_CONVEX`
- `HYPERPLANE_CELL_RELATIVELY_OPEN`
- `NORM_ARITH dist(u - a:real^N,u) = norm a`
- `VECTOR_ARITH x - a % (y - z):real^N = x + a % (z - y)`
- `NORM_MUL`
- `REAL_ABS_DIV`
- `REAL_ABS_NUM`
- `REAL_ABS_NORM`
- `REAL_DIV_RMUL`
- `NORM_EQ_0`
- `VECTOR_SUB_EQ`
- `REAL_ARITH abs e / &2 < e <=> &0 < e`
- `AFFINE_AFFINE_HULL`
- `HULL_INC`
- `IN_AFFINE_ADD_MUL_DIFF`
- `AFFINE_IMP_CONVEX`
- `REAL_ARITH b - x * y > b <=> &0 < x * --y`
- `REAL_LT_MUL`
- `REAL_LT_DIV`
- `REAL_HALF`
- `NORM_POS_LT`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `HYPERPLANE_CELLS_DISTINCT_LEMMA`
- `REAL_ADD_RID`
- `REAL_ADD_LID`
- `INT_SUB_ADD`
- `GSYM AFF_DIM_AFFINE_HULL`
- `AFFINE_HULL_CONVEX_INTER_OPEN`
- `OPEN_HALFSPACE_LT`
- `OPEN_HALFSPACE_GT`
- `AFF_DIM_POS_LE`
- `INT_FORALL_POS`
- `NUM_OF_INT_OF_NUM`
- `INT_OF_NUM_ADD`
- `REAL_POW_ADD`


---

## EULER_CHARACTERSTIC_INVARIANT

### Name of formal statement
EULER_CHARACTERSTIC_INVARIANT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERSTIC_INVARIANT = prove
 (`!A B h s:real^N->bool.
        FINITE A /\ FINITE B /\
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex B s
        ==> euler_characteristic A s = euler_characteristic B s`,
  SUBGOAL_THEN
   `!A s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> !B. FINITE B
                ==> euler_characteristic (A UNION B) s =
                    euler_characteristic A s`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_REWRITE_TAC[UNION_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`h:real^N#real`; `B:real^N#real->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SET_RULE `s UNION (x INSERT t) = x INSERT (s UNION t)`] THEN
    MATCH_MP_TAC EULER_CHARACTERSTIC_LEMMA THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    EXISTS_TAC `A:real^N#real->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `euler_characteristic (A UNION B) (s:real^N->bool)` THEN
    ASM_MESON_TAC[UNION_COMM]]);;
```

### Informal statement
For all sets `A` and `B` of type `real^N -> bool` (sets of `real^N` points), and for all `h` and `s` of type `real^N -> bool` (also sets of `real^N` points), if `A` is finite and `B` is finite, and `A` forms a hyperplane cell complex with respect to `s`, and `B` forms a hyperplane cell complex with respect to `s`, then the Euler characteristic of `A` with respect to `s` equals the Euler characteristic of `B` with respect to `s`.
, assuming that, for all sets `A` of type `real^N -> bool`, and for all `s` of type `real^N -> bool`, if `A` is finite and `A` forms a hyperplane cell complex with respect to `s`, then for all `B` of type `real^N -> bool`, if `B` is finite then the Euler characteristic of `A UNION B` with respect to `s` equals the Euler characteristic of `A` with respect to `s`.

### Informal sketch
The proof proceeds as follows:

- The main goal is to prove that if two finite sets `A` and `B` both form hyperplane cell complexes with respect to `s`, then their Euler characteristics with respect to `s` are equal. This is achieved by assuming the following subgoal.

- The assumed subgoal states that if `A` is finite and forms a hyperplane cell complex with respect to `s`, then for any finite set `B`, the Euler characteristic of `A UNION B` with respect to `s` equals the Euler characteristic of `A` with respect to `s`.

- To prove the main goal using the subgoal, we first generalize the statement.
- Then, inductive reasoning (`FINITE_INDUCT_STRONG`) is applied, using the base case `UNION_EMPTY`.
- After generalizing `h` and `B`, we use two conjuncts and strip assumptions.
- We rewrite `s UNION (x INSERT t) = x INSERT (s UNION t)`.
- Apply `EULER_CHARACTERSTIC_LEMMA` to relate Euler characteristics when adding an element.
- Rewrite using `FINITE_UNION` and apply `HYPERPLANE_CELLCOMPLEX_MONO`.
- Existentially quantify `A` and use assumption rewriting and then use a set tactic.
- Use assumption rewriting and implication rules repeatedly.
- Use `EQ_TRANS` and existentially quantify `euler_characteristic (A UNION B) (s:real^N->bool)`
- Invoke `ASM_MESON_TAC` with `UNION_COMM`.

### Mathematical insight
The theorem `EULER_CHARACTERSTIC_INVARIANT` asserts that the Euler characteristic is invariant under hyperplane cell complexes. This means that if two different sets `A` and `B` both form hyperplane cell complexes with respect to the same set `s`, then they must have the same Euler characteristic. This reflects a topological property: the Euler characteristic is a topological invariant, meaning it doesn't change under certain transformations. The proof uses induction and properties of finite sets, unions, and hyperplane cell complexes, ultimately showing that the Euler characteristic is preserved when forming unions under appropriate conditions.

### Dependencies
- `FINITE`
- `hyperplane_cellcomplex`
- `euler_characteristic`
- `FINITE_INDUCT_STRONG`
- `UNION_EMPTY`
- `EULER_CHARACTERSTIC_LEMMA`
- `FINITE_UNION`
- `HYPERPLANE_CELLCOMPLEX_MONO`
- `RIGHT_IMP_FORALL_THM`
- `IMP_IMP`
- `EQ_TRANS`
- `UNION_COMM`


---

## EULER_CHARACTERISTIC_INCLUSION_EXCLUSION

### Name of formal statement
EULER_CHARACTERISTIC_INCLUSION_EXCLUSION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_INCLUSION_EXCLUSION = prove
 (`!A s:(real^N->bool)->bool.
        FINITE A /\ FINITE s /\ (!k. k IN s ==> hyperplane_cellcomplex A k)
        ==> euler_characteristic A (UNIONS s) =
            sum {t | t SUBSET s /\ ~(t = {})}
                (\t. (-- &1) pow (CARD t + 1) *
                     euler_characteristic A (INTERS t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`hyperplane_cellcomplex A :(real^N->bool)->bool`;
    `euler_characteristic A :(real^N->bool)->real`;
    `s:(real^N->bool)->bool`]
        INCLUSION_EXCLUSION_REAL_RESTRICTED) THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELLCOMPLEX_UNION] THEN
  SIMP_TAC[HYPERPLANE_CELLCOMPLEX_EMPTY; HYPERPLANE_CELLCOMPLEX_INTER;
           HYPERPLANE_CELLCOMPLEX_UNION; HYPERPLANE_CELLCOMPLEX_DIFF]);;
```
### Informal statement
For any set `A` of type `real^N->bool` and any set `s` of type `(real^N->bool)->bool`, if `A` is finite, `s` is finite, and every element `k` of `s` satisfies that `k` is a hyperplane cell complex with respect to `A`, then the Euler characteristic of `A` intersected with the union of the sets in `s` is equal to the sum over all nonempty subsets `t` of `s` of `(-1)^(CARD t + 1)` times the Euler characteristic of `A` intersected with the intersection of the sets in `t`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and assumptions of the goal.
- Applying the theorem `INCLUSION_EXCLUSION_REAL_RESTRICTED`, instantiating it with `hyperplane_cellcomplex A`, `euler_characteristic A`, and `s`.
- Simplifying using `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`.
- Simplifying using the properties of hyperplane cell complexes: `HYPERPLANE_CELLCOMPLEX_EMPTY`, `HYPERPLANE_CELLCOMPLEX_INTER`, `HYPERPLANE_CELLCOMPLEX_UNION`, and `HYPERPLANE_CELLCOMPLEX_DIFF`.

### Mathematical insight
This theorem expresses the Euler characteristic of a union of sets in terms of the Euler characteristics of their intersections. This is a standard inclusion-exclusion principle, adapted to the context of hyperplane cell complexes and their Euler characteristics. The condition that each element of `s` is a hyperplane cell complex with respect to `A` is essential for the result to hold. The theorem provides a way to compute the Euler characteristic of a complex shape by decomposing it into simpler, overlapping shapes.

### Dependencies
- `INCLUSION_EXCLUSION_REAL_RESTRICTED`
- `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`
- `HYPERPLANE_CELLCOMPLEX_EMPTY`
- `HYPERPLANE_CELLCOMPLEX_INTER`
- `HYPERPLANE_CELLCOMPLEX_UNION`
- `HYPERPLANE_CELLCOMPLEX_DIFF`


---

## EULER_POLYHEDRAL_CONE

### Name of formal statement
EULER_POLYHEDRAL_CONE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_POLYHEDRAL_CONE = prove
 (`!s. polyhedron s /\ conic s /\ ~(interior s = {}) /\ ~(s = (:real^N))
       ==> sum (0..dimindex(:N))
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of s /\ aff_dim f = &d })) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `affine hull s = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s. s = UNIV /\ s SUBSET t ==> t = UNIV`) THEN
    EXISTS_TAC `affine hull (interior s:real^N->bool)` THEN
    SIMP_TAC[INTERIOR_SUBSET; HULL_MONO] THEN
    MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  ASM_REWRITE_TAC[INTER_UNIV; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `H:(real^N->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(vec 0:real^N) IN s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN
    ASM_MESON_TAC[SUBSET_EMPTY; INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^N->bool. h IN H ==> ?a. ~(a = vec 0) /\ h = {x | a dot x <= &0}`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MATCH_MP_TAC MONO_EXISTS]  THEN
    X_GEN_TAC `a:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `b = &0` SUBST_ALL_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ ~(&0 < b) ==> b = &0`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(vec 0:real^N) IN INTERS H` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_INTERS]] THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_ELIM_THM; DOT_RZERO];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `H DELETE (h:real^N->bool)`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[PSUBSET_ALT]] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC o CONJUNCT2) THEN
      SUBGOAL_THEN `?e. &0 < e /\ e < &1 /\
                        (e % x:real^N) IN h` STRIP_ASSUME_TAC THENL
       [EXISTS_TAC `min (&1 / &2) (b / ((a:real^N) dot x))` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; DOT_RMUL] THEN
        SUBGOAL_THEN `&0 < (a:real^N) dot x` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `b:real` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~((x:real^N) IN s)` THEN EXPAND_TAC "s" THEN
          ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
          REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
          SUBGOAL_THEN `H:(real^N->bool)->bool = h INSERT (H DELETE h)`
          SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[INTERS_INSERT; IN_INTER] THEN
          ASM_REWRITE_TAC[IN_ELIM_THM];
          ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_MIN_LT] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
        UNDISCH_TAC `~((x:real^N) IN s)` THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `x:real^N = inv e % e % x` SUBST1_TAC THENL
         [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                       VECTOR_MUL_LID];
          ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[conic]) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
        EXPAND_TAC "s" THEN
        SUBGOAL_THEN `H:(real^N->bool)->bool = h INSERT (H DELETE h)`
        SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[INTERS_INSERT; IN_INTER] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^N) IN INTERS (H DELETE h)` THEN
        REWRITE_TAC[IN_INTERS] THEN MATCH_MP_TAC MONO_FORALL THEN
        X_GEN_TAC `k:real^N->bool` THEN REWRITE_TAC[IN_DELETE] THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN
        ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`a':real^N`; `b':real`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&0 <= x ==> y <= x) /\ (&0 <= --x ==> &0 <= --y) /\ &0 <= b
          ==> x <= b ==> y <= b`) THEN
        REWRITE_TAC[DOT_RMUL; GSYM REAL_MUL_RNEG] THEN
        REWRITE_TAC[REAL_ARITH `e * x <= x <=> &0 <= x * (&1 - e)`] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
        SUBGOAL_THEN `(vec 0:real^N) IN INTERS H` MP_TAC THENL
         [ASM SET_TAC[]; REWRITE_TAC[IN_INTERS]] THEN
        DISCH_THEN(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IN_ELIM_THM; DOT_RZERO]]];
    FIRST_X_ASSUM(K ALL_TAC o SPEC `h:real^N->bool`)] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `fa:(real^N->bool)->real^N` THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o funpow 2 RAND_CONV)
   [EQ_SYM_EQ] THEN
  DISCH_TAC THEN ABBREV_TAC
   `A = IMAGE (\h. (fa:(real^N->bool)->real^N) h,&0) H` THEN
  SUBGOAL_THEN `FINITE(A:real^N#real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `euler_characteristic A (s:real^N->bool)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[EULER_CHARACTERISTIC] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    ASM_SIMP_TAC[FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
    EXISTS_TAC `relative_interior:(real^N->bool)->(real^N->bool)` THEN
    EXISTS_TAC `closure:(real^N->bool)->(real^N->bool)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `closure(relative_interior f):real^N->bool = f`
      ASSUME_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `closure f:real^N->bool` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN
          ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
          REWRITE_TAC[CLOSURE_EQ] THEN MATCH_MP_TAC FACE_OF_IMP_CLOSED THEN
          ASM_MESON_TAC[POLYHEDRON_IMP_CLOSED; POLYHEDRON_IMP_CONVEX]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ALL_TAC;
        ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
        ONCE_REWRITE_TAC[GSYM AFFINE_HULL_CLOSURE] THEN
        ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET_TRANS;
                      FACE_OF_IMP_SUBSET]] THEN
      SUBGOAL_THEN `~(f:real^N->bool = {})` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM AFF_DIM_POS_LE; INT_POS]; ALL_TAC] THEN
      SUBGOAL_THEN
       `?J. J SUBSET H /\
            f = INTERS {{x:real^N | fa h dot x <= &0} | h IN H} INTER
                INTERS {{x | fa(h:real^N->bool) dot x = &0} | h IN J}`
      ASSUME_TAC THENL
       [ASM_CASES_TAC `f:real^N->bool = s` THENL
         [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
          REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY; INTERS_0; INTER_UNIV;
                      SET_RULE `{f x | x | F} = {}`] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SYM(ASSUME `INTERS H = (s:real^N->bool)`)] THEN
          AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
           `(!x. x IN s ==> f x = x) ==> s = {f x | x IN s}`) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC
        `{h:real^N->bool | h IN H /\
                     f SUBSET s INTER {x:real^N | fa h dot x = &0}}` THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `H:(real^N->bool)->bool`;
                       `fa:(real^N->bool)->real^N`;
                       `\h:real^N->bool. &0`]
          FACE_OF_POLYHEDRON_EXPLICIT) THEN
        ASM_SIMP_TAC[INTER_UNIV] THEN
        DISCH_THEN(MP_TAC o SPEC `f:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `INTERS {{x:real^N | fa(h:real^N->bool) dot x <= &0} | h IN H} = s`
        ASSUME_TAC THENL
         [EXPAND_TAC "s" THEN AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
           `(!x. x IN s ==> f x = x) ==> {f x | x IN s} = s`) THEN
          ASM_SIMP_TAC[];
         ALL_TAC] THEN
        ASM_CASES_TAC `{h:real^N->bool | h IN H /\
                           f SUBSET s INTER {x:real^N | fa h dot x = &0}} =
                       {}`
        THENL
         [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0] THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
        X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER; IN_INTERS] THEN
        REWRITE_TAC[FORALL_IN_GSPEC; IN_INTER] THEN
        ASM_CASES_TAC `(y:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC
       `H' = IMAGE (\h:real^N->bool. {x:real^N | --(fa h) dot x <= &0}) H` THEN
      SUBGOAL_THEN
       `?J. FINITE J /\
            J SUBSET (H UNION H') /\
            f:real^N->bool = affine hull f INTER INTERS J`
      MP_TAC THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `J:(real^N->bool)->bool`
          STRIP_ASSUME_TAC) THEN
        EXISTS_TAC
         `H UNION IMAGE (\h:real^N->bool.
             {x:real^N | --(fa h) dot x <= &0}) J` THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[FINITE_UNION] THEN MATCH_MP_TAC FINITE_IMAGE THEN
          ASM_MESON_TAC[FINITE_SUBSET];
          EXPAND_TAC "H'" THEN ASM SET_TAC[];
          MATCH_MP_TAC(SET_RULE `s SUBSET f /\ s = t ==> s = f INTER t`) THEN
          REWRITE_TAC[HULL_SUBSET] THEN
          FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
          REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
          REWRITE_TAC[INTERS_UNION] THEN MATCH_MP_TAC(SET_RULE
           `s = s' /\ (!x. x IN s ==> (x IN t <=> x IN t'))
            ==> s INTER t = s' INTER t'`) THEN
          CONJ_TAC THENL
           [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
             `(!x. x IN s ==> f x = x) ==> {f x | x IN s} = s`) THEN
            ASM_SIMP_TAC[];
            ALL_TAC] THEN
          X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTERS] THEN
          REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
          REWRITE_TAC[IN_ELIM_THM; DOT_LNEG] THEN
          REWRITE_TAC[REAL_ARITH `--x <= &0 <=> &0 <= x`] THEN
          ASM SET_TAC[]];
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV
         [MESON[HAS_SIZE]
           `(?f. FINITE f /\ P f) <=> (?n f. f HAS_SIZE n /\ P f)`] THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      DISCH_THEN(X_CHOOSE_THEN `nn:num`
        (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `J:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `!J'. J' PSUBSET J
             ==> (f:real^N->bool) PSUBSET (affine hull f INTER INTERS J')`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `CARD(J':(real^N->bool)->bool)`) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[CARD_PSUBSET; HAS_SIZE]; ALL_TAC] THEN
        REWRITE_TAC[NOT_EXISTS_THM; HAS_SIZE] THEN
        DISCH_THEN(MP_TAC o SPEC `J':(real^N->bool)->bool`) THEN
        MATCH_MP_TAC(TAUT `a /\ b /\ (~c ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[PSUBSET; FINITE_SUBSET; HAS_SIZE]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE
         `s SUBSET t ==> ~(s = t) ==> s PSUBSET t`) THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!h:real^N->bool. h IN J
          ==> ?a. {x | a dot x <= &0} = h /\
                  (h IN H /\ a = fa h \/ ?h'. h' IN H /\ a = --(fa h'))`
      MP_TAC THENL
       [X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(h:real^N->bool) IN (H UNION H')` MP_TAC THENL
         [ASM SET_TAC[]; EXPAND_TAC "H'"] THEN
        UNDISCH_THEN `(h:real^N->bool) IN J` (K ALL_TAC) THEN
        SPEC_TAC(`h:real^N->bool`,`h:real^N->bool`) THEN
        REWRITE_TAC[IN_UNION; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                    FORALL_AND_THM; FORALL_IN_IMAGE] THEN
        CONJ_TAC THEN X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THENL
         [EXISTS_TAC `(fa:(real^N->bool)->real^N) h` THEN
          ASM_SIMP_TAC[];
          EXISTS_TAC `--((fa:(real^N->bool)->real^N) h)` THEN
          REWRITE_TAC[] THEN DISJ2_TAC THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `ga:(real^N->bool)->real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`f:real^N->bool`; `J:(real^N->bool)->bool`;
        `ga:(real^N->bool)->real^N`; `\h:real^N->bool. &0`]
       RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[HAS_SIZE];
          ASM_MESON_TAC[];
          ASM_SIMP_TAC[] THEN ASM_MESON_TAC[VECTOR_NEG_EQ_0; SUBSET]];
        DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
      SUBGOAL_THEN
       `!h:real^N->bool. h IN J ==> h IN H /\ ga h:real^N = fa h`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `~(relative_interior f:real^N->bool = {})` MP_TAC THENL
         [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; FACE_OF_IMP_CONVEX];
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]] THEN
        DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
        SUBGOAL_THEN `(z:real^N) IN f /\ z IN s` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET; FACE_OF_IMP_SUBSET; RELATIVE_INTERIOR_SUBSET];
          ALL_TAC] THEN
        X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `h':real^N->bool` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(z:real^N) IN relative_interior f` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[DOT_LNEG] THEN
        UNDISCH_TAC `(z:real^N) IN s` THEN EXPAND_TAC "s" THEN
        REWRITE_TAC[IN_INTERS] THEN
        DISCH_THEN(MP_TAC o SPEC `h':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h':real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(CONJUNCT2 th)]) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN
        MP_TAC(SYM th)) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `K:(real^N->bool)->bool` MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(fun th -> ASSUME_TAC(SYM th) THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
      REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_GSPEC; GSYM CONJ_ASSOC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(relative_interior f:real^N->bool = {})` ASSUME_TAC THENL
       [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; FACE_OF_IMP_CONVEX];
        ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (J:(real^N->bool)->bool) K` ASSUME_TAC THENL
       [UNDISCH_TAC `~(relative_interior f:real^N->bool = {})` THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
         (LAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[IN_DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        ASM_MESON_TAC[REAL_LT_REFL];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `relative_interior f =
          INTERS {(if (h:real^N->bool) IN J then {x | fa h dot x < &0}
                   else if h IN K then {x:real^N | fa h dot x = &0}
                   else if relative_interior f SUBSET {x | fa h dot x = &0}
                   then {x | fa h dot x = &0}
                   else {x | fa h dot x < &0}) | h IN H}`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [ALL_TAC;
          FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
          GEN_REWRITE_TAC I [SUBSET] THEN
          REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; AND_FORALL_THM] THEN
          X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
          MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h:real^N->bool` THEN
          ASM_CASES_TAC `(h:real^N->bool) IN H` THENL
           [ALL_TAC; DISCH_THEN(K ALL_TAC) THEN ASM SET_TAC[]] THEN
          ASM_REWRITE_TAC[] THEN
          ASM_CASES_TAC `(h:real^N->bool) IN J` THEN
          ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE] THENL
           [ASM SET_TAC[]; ALL_TAC] THEN
          ASM_CASES_TAC `(h:real^N->bool) IN K` THEN
          ASM_SIMP_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
          COND_CASES_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
          REAL_ARITH_TAC] THEN
        GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
        DISCH_TAC THEN REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
        REPEAT(COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
        REWRITE_TAC[IN_ELIM_THM; REAL_LT_LE] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
         [SET_RULE `~(s SUBSET t) <=> ?y. y IN s /\ ~(y IN t)`]) THEN
        REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
         `~(x:real = &0) ==> ~(x <= &0) \/ x < &0`))
        THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ASSUME `(x:real^N) IN relative_interior f`) THEN
        REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `e:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_CBALL] THEN
        SUBGOAL_THEN `~(y:real^N = x)` ASSUME_TAC THENL
         [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `x + e / norm(y - x) % (x - y):real^N`) THEN
        SUBGOAL_THEN
         `(x:real^N) IN affine hull f /\ y IN affine hull f`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; HULL_SUBSET];
          ASM_SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF; AFFINE_AFFINE_HULL]] THEN
        REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + r) = norm r`] THEN
        REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; NORM_SUB;
                       REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
          ASM_REAL_ARITH_TAC;
          DISCH_TAC] THEN
        SUBGOAL_THEN `(x + e / norm(y - x) % (x - y):real^N) IN s` MP_TAC THENL
         [ASM_MESON_TAC[SUBSET; FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
        EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTERS] THEN
        DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
         [SYM(CONJUNCT2(MATCH_MP th (ASSUME `(h:real^N->bool) IN H`)))]) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; DOT_RADD; REAL_ADD_LID; DOT_RMUL] THEN
        ASM_REWRITE_TAC[DOT_RSUB; REAL_SUB_LZERO; REAL_NOT_LE] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `~(relative_interior f:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; hyperplane_cell] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
      GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
      ONCE_ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN MP_TAC th) THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [IN] THEN
      REWRITE_TAC[hyperplane_equiv; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC(MESON[]
       `(!h. P h ==> (Q h <=> R h))
        ==> (!h. P h) ==> ((!h. Q h) <=> (!h. R h))`) THEN
      X_GEN_TAC `h:real^N->bool` THEN
      ASM_CASES_TAC `(h:real^N->bool) IN H` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[hyperplane_side; REAL_SUB_RZERO] THEN
      REPEAT(COND_CASES_TAC THEN
        SIMP_TAC[IN_ELIM_THM] THENL [MESON_TAC[REAL_SGN_EQ]; ALL_TAC]) THEN
      MESON_TAC[REAL_SGN_EQ];
      X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
      REWRITE_TAC[AFFINE_HULL_CLOSURE] THEN
      ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `relative_interior c:real^N->bool` THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR_CLOSURE THEN
          ASM_MESON_TAC[HYPERPLANE_CELL_CONVEX];
          ASM_MESON_TAC[HYPERPLANE_CELL_RELATIVE_INTERIOR]]] THEN
      SUBGOAL_THEN
       `?J. J SUBSET H /\
            c = INTERS {{x | (fa(h:real^N->bool)) dot x < &0} | h IN J} INTER
                INTERS {{x:real^N | (fa h) dot x = &0} | h IN (H DIFF J)}`
      MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HYPERPLANE_CELL]) THEN
        EXPAND_TAC "A" THEN REWRITE_TAC[hyperplane_equiv; FORALL_IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
        REWRITE_TAC[hyperplane_side; REAL_SUB_RZERO] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
         [EQ_SYM_EQ] THEN
        DISCH_THEN(ASSUME_TAC o SYM) THEN EXISTS_TAC
         `{h:real^N->bool | h IN H /\
                            real_sgn(fa h dot (z:real^N)) = -- &1}` THEN
        REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} SUBSET s`] THEN
        REWRITE_TAC[GSYM INTERS_UNION] THEN EXPAND_TAC "c" THEN
        GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INTERS] THEN REWRITE_TAC[IN_UNION] THEN
        REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                    FORALL_AND_THM] THEN
        REWRITE_TAC[FORALL_IN_GSPEC] THEN
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
        REWRITE_TAC[TAUT `a /\ ~(a /\ b) <=> a /\ ~b`] THEN
        REWRITE_TAC[AND_FORALL_THM] THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N->bool` THEN
        ASM_CASES_TAC `(h:real^N->bool) IN H` THEN ASM_REWRITE_TAC[] THEN
        REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPEC `(fa:(real^N->bool)->real^N) h dot z` REAL_SGN_CASES) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[REAL_SGN_EQ] THEN
        SUBGOAL_THEN `?x:real^N. x IN c /\ x IN s` MP_TAC THENL
         [ASM_MESON_TAC[MEMBER_NOT_EMPTY; SUBSET; NONEMPTY_HYPERPLANE_CELL];
          MATCH_MP_TAC(TAUT `~p ==> p ==> q`)] THEN
        MAP_EVERY EXPAND_TAC ["s"; "c"] THEN
        REWRITE_TAC[IN_INTERS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `x:real^N` THEN REWRITE_TAC[AND_FORALL_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[REAL_SGN_EQ] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN
      EXPAND_TAC "c" THEN
      W(MP_TAC o PART_MATCH (lhand o rand) CLOSURE_INTER_CONVEX o
        lhand o snd) THEN
      ANTS_TAC THENL
       [SIMP_TAC[CONVEX_INTERS; FORALL_IN_GSPEC; CONVEX_HALFSPACE_LT;
                 CONVEX_HYPERPLANE] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_INTERIOR_OPEN o
          lhand o lhand o rand o snd) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC OPEN_INTERS THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
          REWRITE_TAC[FORALL_IN_IMAGE; OPEN_HALFSPACE_LT] THEN
          MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[FINITE_SUBSET];
          DISCH_THEN SUBST1_TAC] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_INTERIOR_OPEN_IN o
          rand o lhand o rand o snd) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC(MESON[OPEN_IN_SUBTOPOLOGY_REFL]
           `s SUBSET topspace tp /\ t = s
            ==> open_in (subtopology tp t) s`) THEN
          REWRITE_TAC[SUBSET_UNIV; TOPSPACE_EUCLIDEAN] THEN
          REWRITE_TAC[AFFINE_HULL_EQ] THEN
          SIMP_TAC[AFFINE_INTERS; AFFINE_HYPERPLANE; FORALL_IN_GSPEC];
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[CLOSURE_INTERS_CONVEX_OPEN; FORALL_IN_GSPEC;
               CONVEX_HALFSPACE_LT; OPEN_HALFSPACE_LT] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_FACE_OF; INTER_EMPTY] THEN
      SUBGOAL_THEN
       `IMAGE closure {{x | fa h dot x < &0} | h IN J} =
        {{x | (fa:(real^N->bool)->real^N) h dot x <= &0} | h IN J}`
      SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
        REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC IMAGE_EQ THEN
        GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC CLOSURE_HALFSPACE_LT THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
      `closure (INTERS {{x | fa h dot x = &0} | h IN H DIFF J}) =
       INTERS {{x | (fa:(real^N->bool)->real^N) h dot x = &0} | h IN H DIFF J}`
      SUBST1_TAC THENL
       [REWRITE_TAC[CLOSURE_EQ] THEN
        SIMP_TAC[CLOSED_INTERS; FORALL_IN_GSPEC; CLOSED_HYPERPLANE];
        ALL_TAC] THEN
      ASM_CASES_TAC `J:(real^N->bool)->bool = H` THENL
       [ASM_REWRITE_TAC[DIFF_EQ_EMPTY; INTER_UNIV; NOT_IN_EMPTY;
                        SET_RULE `{f x | x | F} = {}`; INTERS_0] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_REFL o
         MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        EXPAND_TAC "s" THEN AP_TERM_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = x) ==> s = {f x | x IN s}`) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `INTERS {{x | fa(h:real^N->bool) dot x <= &0} | h IN J} INTER
        INTERS {{x:real^N | fa h dot x = &0} | h IN H DIFF J} =
        INTERS {s INTER {x | fa h dot x = &0} | h IN H DIFF J}`
      SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[INTERS_IMAGE] THEN
        GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        ASM_CASES_TAC `(y:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
         [MATCH_MP_TAC(TAUT `a ==> (a /\ b <=> b)`) THEN
          UNDISCH_TAC `(y:real^N) IN s` THEN EXPAND_TAC "s" THEN
          REWRITE_TAC[IN_INTERS] THEN MATCH_MP_TAC MONO_FORALL THEN
          X_GEN_TAC `h:real^N->bool` THEN
          DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; SET_TAC[]];
          UNDISCH_TAC `~((y:real^N) IN s)` THEN MATCH_MP_TAC
           (TAUT `~q /\ (p ==> r) ==> ~r ==> (p <=> q)`) THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTERS; AND_FORALL_THM] THEN
          MATCH_MP_TAC MONO_FORALL THEN
          X_GEN_TAC `h:real^N->bool` THEN
          DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
           [GSYM(CONJUNCT2 th)]) THEN
          ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
          ASM_CASES_TAC `(h:real^N->bool) IN J` THEN
          ASM_SIMP_TAC[REAL_LE_REFL]];
        ALL_TAC] THEN
      MATCH_MP_TAC FACE_OF_INTERS THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `h:real^N->bool` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
      ASM_SIMP_TAC[POLYHEDRON_IMP_CONVEX] THEN X_GEN_TAC `y:real^N` THEN
      EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTERS] THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [GSYM(CONJUNCT2 th)]) THEN
      REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. h IN H ==> hyperplane_cellcomplex A ((:real^N) DIFF h)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    EXISTS_TAC `{((fa:(real^N->bool)->real^N) h,&0)}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_SING] THEN REPEAT DISJ2_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM(CONJUNCT2 th)]) THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "A" THEN
      REWRITE_TAC[IN_IMAGE; SUBSET; FORALL_UNWIND_THM2; IN_SING] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^N->bool. h IN H ==> hyperplane_cellcomplex A h`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[HYPERPLANE_CELLCOMPLEX_COMPL;
                  COMPL_COMPL];
    ALL_TAC] THEN
  SUBGOAL_THEN `hyperplane_cellcomplex A (s:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^N#real->bool`;
                 `INTERS H:real^N->bool`;
                 `(:real^N) DIFF INTERS H`]
        EULER_CHARACTERISTIC_CELLCOMPLEX_UNION) THEN
  REWRITE_TAC[SET_RULE `DISJOINT s (UNIV DIFF s)`] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[HYPERPLANE_CELLCOMPLEX_DIFF; HYPERPLANE_CELLCOMPLEX_UNIV];
    REWRITE_TAC[SET_RULE `s UNION (UNIV DIFF s) = UNIV`]] THEN
  REWRITE_TAC[DIFF_INTERS] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = (--(&1)) pow (dimindex(:N)) /\
    y = (--(&1)) pow (dimindex(:N))
    ==> x = s + y ==> s = &0`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `euler_characteristic {} (:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC EULER_CHARACTERSTIC_INVARIANT THEN
      ASM_REWRITE_TAC[FINITE_EMPTY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
        EXISTS_TAC `{}:real^N#real->bool` THEN REWRITE_TAC[EMPTY_SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
      REWRITE_TAC[HYPERPLANE_CELL_EMPTY];
      SIMP_TAC[EULER_CHARACTERISTIC_CELL; HYPERPLANE_CELL_EMPTY] THEN
      REWRITE_TAC[AFF_DIM_UNIV; NUM_OF_INT_OF_NUM]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) EULER_CHARACTERISTIC_INCLUSION_EXCLUSION o
    lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET {(:real^N) DIFF t | t IN H} /\ ~(t = {})}
             (\t. -- &1 pow (CARD t + 1) * (--(&1)) pow (dimindex(:N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMP_CONJ; FORALL_SUBSET_IMAGE] THEN
    X_GEN_TAC `J:(real^N->bool)->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN AP_TERM_TAC THEN
    ABBREV_TAC `B = IMAGE (\h:real^N->bool. fa h:real^N,&0) J` THEN
    SUBGOAL_THEN `(B:real^N#real->bool) SUBSET A` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `INTERS (IMAGE (\t. (:real^N) DIFF t) H) =
      IMAGE (--) (interior s)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `H:(real^N->bool)->bool`;
                     `fa:(real^N->bool)->real^N`;
                     `\h:real^N->bool. &0`]
                RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
      ASM_SIMP_TAC[INTER_UNIV] THEN
      ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR] THEN
      DISCH_THEN(K ALL_TAC) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC[VECTOR_ARITH `--x:real^N = y <=> x = --y`; EXISTS_REFL] THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
      MATCH_MP_TAC(TAUT `(c ==> b) /\ (a <=> c) ==> (a <=> b /\ c)`) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTERS] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h:real^N->bool` THEN
        ASM_CASES_TAC `(h:real^N->bool) IN H` THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC(MESON[]
         `(!h. P h ==> (Q h <=> R h))
          ==> ((!h. P h ==> Q h) <=> (!h. P h ==> R h))`) THEN
        X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [SYM(CONJUNCT2(MATCH_MP th (ASSUME `(h:real^N->bool) IN H`)))]) THEN
        REWRITE_TAC[IN_ELIM_THM; DOT_RNEG] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `hyperplane_cell B (INTERS (IMAGE (\t. (:real^N) DIFF t) J))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `~(INTERS (IMAGE (\t. (:real^N) DIFF t) J) = {})`
      MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[hyperplane_cell; GSYM MEMBER_NOT_EMPTY; IN_INTERS] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[IN_UNIV; IN_DIFF] THEN
      GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN MP_TAC th) THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [IN] THEN
      REWRITE_TAC[hyperplane_equiv] THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[FORALL_IN_IMAGE; hyperplane_side] THEN
      MATCH_MP_TAC(MESON[]
       `(!h. P h ==> (Q h <=> R h))
        ==> (!h. P h) ==> ((!h. Q h) <=> (!h. R h))`) THEN
      X_GEN_TAC `h:real^N->bool` THEN
      ASM_CASES_TAC `(h:real^N->bool) IN J` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(h:real^N->bool) IN H` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME
       `(h:real^N->bool) IN H`)) THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [SYM th] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
      REWRITE_TAC[IN_ELIM_THM; REAL_SUB_RZERO; REAL_NOT_LE] THEN
      MESON_TAC[REAL_SGN_EQ; real_gt];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `euler_characteristic B (INTERS (IMAGE (\t. (:real^N) DIFF t) J))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EULER_CHARACTERSTIC_INVARIANT THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
      EXISTS_TAC `B:real^N#real->bool` THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(MESON[NUM_OF_INT_OF_NUM] `i = &n ==> num_of_int i = n`) THEN
    REWRITE_TAC[AFF_DIM_EQ_FULL] THEN
    MATCH_MP_TAC(SET_RULE `!t. t SUBSET s /\ t = UNIV ==> s = UNIV`) THEN
    EXISTS_TAC `affine hull (INTERS (IMAGE (\t. (:real^N) DIFF t) H))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IMAGE_EQ_EMPTY; OPEN_NEGATIONS; OPEN_INTERIOR];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  MATCH_MP_TAC(REAL_RING `s = &1 ==> s * t = t`) THEN
  MP_TAC(ISPECL [`\t:(real^N->bool)->bool. CARD t`;
                 `\t:(real^N->bool)->bool. (-- &1) pow (CARD t + 1)`;
                 `{t |  t SUBSET
                     {(:real^N) DIFF t | t IN H} /\ ~(t = {})}`;
                 `1..CARD(H:(real^N->bool)->bool)`]
        SUM_GROUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t |  t SUBSET {(:real^N) DIFF t | t IN H}}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_NUMSEG] THEN
      REWRITE_TAC[SIMPLE_IMAGE; FORALL_SUBSET_IMAGE; IMP_CONJ] THEN
      X_GEN_TAC `J:(real^N->bool)->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN
      SUBGOAL_THEN `FINITE(J:(real^N->bool)->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_EQ_0; FINITE_IMAGE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                   IMAGE_EQ_EMPTY] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(J:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[CARD_SUBSET; CARD_IMAGE_LE]];
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (1..CARD(H:(real^N->bool)->bool))
        (\n. -- &1 pow (n + 1) * &(binom(CARD H,n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    SIMP_TAC[IN_ELIM_THM] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_CONST o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t |  t SUBSET {(:real^N) DIFF t | t IN H}}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE];
      DISCH_THEN SUBST1_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD {t | t SUBSET {(:real^N) DIFF t | t IN H} /\
                          t HAS_SIZE n}` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      X_GEN_TAC `t:(real^N->bool)->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_CASES_TAC `t:(real^N->bool)->bool = {}` THEN
      ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY] THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(p ==> r) ==> (p /\ q <=> p /\ r /\ q)`) THEN
      SPEC_TAC(`t:(real^N->bool)->bool`,`u:(real^N->bool)->bool`) THEN
      REWRITE_TAC[SIMPLE_IMAGE; FORALL_SUBSET_IMAGE] THEN
      ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`CARD(H:(real^N->bool)->bool)`;
                   `n:num`; `{(:real^N) DIFF t | t IN H}`]
        NUMBER_OF_COMBINATIONS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[HAS_SIZE]] THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[GSYM FINITE_HAS_SIZE] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`CARD(H:(real^N->bool)->bool)`; `--(&1)`; `&1`]
        REAL_BINOMIAL_THEOREM) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; REAL_ADD_LINV] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; REAL_POW_ADD; REAL_POW_ONE; LE_0] THEN
  REWRITE_TAC[REAL_ARITH `(x * --(&1) pow 1) * y = --(y * x)`] THEN
  REWRITE_TAC[real_pow; SUM_NEG; ADD_CLAUSES; REAL_MUL_RID] THEN
  REWRITE_TAC[binom] THEN MATCH_MP_TAC(REAL_ARITH
   `x = &0 ==> x = &1 + y ==> --y = &1`) THEN
  REWRITE_TAC[REAL_POW_ZERO] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `CARD(H:(real^N->bool)->bool) = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]);;
```

### Informal statement
For any set `s` in real N-dimensional space (`:real^N`) satisfying the conditions that `s` is a polyhedron, `s` is conic, the interior of `s` is non-empty, and `s` is not equal to the entire space `:real^N`, it holds that the following alternating sum, indexed by dimension `d` from 0 to the dimension index of `:N`, is equal to zero: `sum (0..dimindex(:N)) (\d. (-- &1) pow d * &(CARD {f | f face_of s /\ aff_dim f = &d })) = &0`.  Here, `face_of s` denotes a face of `s`, `aff_dim f` is the affine dimension of `f`, and `CARD` denotes the cardinality of a set.

### Informal sketch
The proof proceeds by showing that under the given conditions for `s`, the Euler characteristic can be expressed as an alternating sum of the number of faces of each dimension.

- First, assume `affine hull s = (:real^N)`. With this assumption, it is shown that the interior of `s` is non-empty by using `INTERIOR_SUBSET`, `HULL_MONO`, `AFFINE_HULL_OPEN`, and `OPEN_INTERIOR`.
- From the assumption that `s` is a polyhedron and that `affine hull s = (:real^N)`, show that `s` is the intersection of half-spaces.
- Use the fact that `s` is conic to show that the origin `(vec 0:real^N)` is an element of `s`.
- Express `s` as the intersection of half-spaces, where each half-space is defined by `h = {x | a dot x <= &0}` for some `a`.
- Define `A` as the image of the set of half-spaces `H: real^N->bool` under the mapping `h -> (fa h, &0)`.
- Show that `A` is finite.
- Show that the Euler characteristic of `A` with respect to `s` equals the `sum` using the theorems `EULER_CHARACTERISTIC`, `SUM_EQ_NUMSEG`, `BIJECTIONS_CARD_EQ`, `FINITE_RESTRICT_HYPERPLANE_CELLS` and the fact face `f = closure(relative_interior f)`. Introduce `relative_interior` and `closure` for this purpose.
- The proof then uses `FACE_OF_POLYHEDRON_EXPLICIT` to show that the faces of `s` are determined by intersections of supporting hyperplanes.
- Then, `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT` is used to express the relative interior of each face as an intersection of halfspaces and hyperplanes. This involves constructing a set `J` representing the hyperplanes needed to define the face.
- The proof constructs auxiliary sets `J` and `K` related to the faces of `s`.
- Show that `hyperplane_cellcomplex A ((:real^N) DIFF h)` and `hyperplane_cellcomplex A h` for any `h IN H`.
- The theorem `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION` along with the properties derived from cell complexes and hyperplane arrangements yields the desired result after simplification and algebraic manipulation using `REAL_BINOMIAL_THEOREM`.

### Mathematical insight
The theorem generalizes Euler's polyhedron formula to polyhedral cones. It relates the alternating sum of the number of faces of various dimensions to zero, which provides topological information about the structure of the cone. This theorem essentially provides a way to compute the Euler characteristic for a certain class of polyhedral cones from the dimension of the faces

### Dependencies
- `POLYHEDRON_INTER_AFFINE_MINIMAL`:  Specifies the condition when the affine hull equal the space.
- `CONIC_CONTAINS_0`: Conic set contains the origin.
- `MONO_EXISTS`: states that if some property is satisfied then an existential quanification of it is satisfied as well.
- `REAL_ARITH`: Collection of Theorems for Real Arithmetic.
- `EULER_CHARACTERISTIC`: Definition of `euler_characteristic`.
- `FINITE_RESTRICT_HYPERPLANE_CELLS`: States the a restrictied hyperplane has a finite number of cells.
- `FACE_OF_POLYHEDRON_EXPLICIT`: How to calculate the face of a polyhedron.
- `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT`: Definition of `relative_interior_polyhedron`.
- `HAS_SIZE`: Definition of `has_size`.
- `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`: Expression for `euler_characteristic` of cellcomplex unions.
- `HULL_MONO`: States that hull is monotonic.
- `AFFINE_HULL_OPEN`: Details on `affine_hull_open`.
- `OPEN_INTERIOR`: Details on `open_interior`.
- `INTERIOR_SUBSET`: States that the interior of a set is a subset of the set.

### Porting notes (optional)
- The proof is quite involved and makes heavy use of HOL Light's automation. In another proof assistant, it might be necessary to decompose the proof into smaller lemmas and be more explicit about the reasoning steps.
- The tactic `REAL_ARITH_TAC` is used frequently. Ensure that the target proof assistant has similar automation for real arithmetic.
- The heavy use of set theory in this proof will likely require a robust library for sets and relations.


---

## EULER_POINCARE_LEMMA

### Name of formal statement
EULER_POINCARE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_POINCARE_LEMMA = prove
 (`!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &1}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`basis 1:real^N`; `&1`] AFF_DIM_HYPERPLANE) THEN
  SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
  ASM_CASES_TAC `p:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    REWRITE_TAC[INT_ARITH `--(&1):int = x - &1 <=> x = &0`] THEN
    SIMP_TAC[INT_OF_NUM_EQ; LE_1; DIMINDEX_GE_1];
    DISCH_TAC] THEN
  ABBREV_TAC `s:real^N->bool = conic hull p` THEN
  MP_TAC(ISPEC `s:real^N->bool` EULER_POLYHEDRAL_CONE) THEN
  SUBGOAL_THEN
   `!f. f SUBSET {x:real^N | x$1 = &1}
        ==> (conic hull f) INTER {x:real^N | x$1 = &1} = f`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_SIMP_TAC[HULL_SUBSET; SUBSET_INTER] THEN
    REWRITE_TAC[SUBSET; CONIC_HULL_EXPLICIT; IN_INTER; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_RID; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `polyhedron(s:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^N->bool` MP_TAC o
      GEN_REWRITE_RULE I [polytope]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC th) THEN
    MP_TAC(ISPEC `k:real^N->bool` CONVEX_CONE_HULL_SEPARATE_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONVEX_HULL_EQ_EMPTY]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC POLYHEDRON_CONVEX_CONE_HULL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
  SUBGOAL_THEN `conic(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONIC_CONIC_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s = (:real^N))` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[HULL_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[INTER_UNIV] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    UNDISCH_TAC `polytope(p:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP POLYTOPE_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; NOT_EXISTS_THM] THEN X_GEN_TAC `B:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC
     `(lambda i. if i = 1 then &1 else B + &1):real^N`) THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_GE_1; LE_REFL; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN
    MP_TAC(ISPECL
    [`(lambda i. if i = 1 then &1 else B + &1):real^N`; `2`]
      COMPONENT_LE_NORM) THEN
    ASM_SIMP_TAC[ARITH; LAMBDA_BETA; DIMINDEX_GE_1; LE_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONIC_HULL_EQ_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` CONIC_CONTAINS_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior(s:real^N->bool) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN MP_TAC(ISPEC `s:real^N->bool`
     EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s SUBSET {x:real^N | x$1 = &1}` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s SUBSET h' ==> h SUBSET h' /\ ~(h PSUBSET h') ==> s SUBSET h`)) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HULL_SUBSET];
        DISCH_TAC THEN
        MP_TAC(ISPECL [`a:real^N`; `b:real`] AFF_DIM_HYPERPLANE) THEN
        MP_TAC(ISPECL [`basis 1:real^N`; `&1`] AFF_DIM_HYPERPLANE) THEN
        ASM_SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
        MATCH_MP_TAC(INT_ARITH `a:int < b ==> a = n ==> ~(b = n)`) THEN
        MATCH_MP_TAC AFF_DIM_PSUBSET THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (SET_RULE `s PSUBSET t ==> s' = s /\ t' = t ==> s' PSUBSET t'`)) THEN
        REWRITE_TAC[AFFINE_HULL_EQ; AFFINE_HYPERPLANE] THEN
        MP_TAC(ISPECL [`basis 1:real^N`; `&1`] AFFINE_HYPERPLANE) THEN
        SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL]];
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `vec 0:real^N` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^N. x IN s /\ ~(x = vec 0) ==> &0 < x$1`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[CONIC_HULL_EXPLICIT; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN affine hull p` MP_TAC THENL
     [ASM_MESON_TAC[HULL_SUBSET; SUBSET]; ASM_REWRITE_TAC[]] THEN
    SIMP_TAC[IN_ELIM_THM; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> &0 <= x$1` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_SIMP_TAC[VEC_COMPONENT; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_CLAUSES_LEFT o
    lhand o lhand o snd) THEN
  REWRITE_TAC[LE_0] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[AFF_DIM_EQ_0; real_pow; REAL_MUL_LID] THEN
  SUBGOAL_THEN `{f | f face_of s /\ (?a:real^N. f = {a})} = {{vec 0}}`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `f:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `a:real^N`)) THEN
      ASM_REWRITE_TAC[FACE_OF_SING] THEN
      ASM_MESON_TAC[EXTREME_POINT_OF_CONIC];
      DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      ASM_REWRITE_TAC[FACE_OF_SING; extreme_point_of; IN_SEGMENT] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `u:real` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[CART_EQ] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VEC_COMPONENT] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `&0 < (a:real^N)$1 \/ &0 < (b:real^N)$1` DISJ_CASES_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(&0 = a + b)`);
        MATCH_MP_TAC(REAL_ARITH `&0 < b /\ &0 <= a ==> ~(&0 = a + b)`)] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL; REAL_SUB_LT]];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY; GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_ARITH `s = --t ==> (&0 + &1) + s = &0 ==> t = &1`) THEN
  SUBGOAL_THEN `dimindex(:N) = (dimindex(:N)-1)+1`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  EXISTS_TAC `\f:real^N->bool. f INTER {x | x$1 = &1}` THEN
  EXISTS_TAC `\f:real^N->bool. conic hull f` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{f:real^N->bool | f face_of s}` THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_FACES] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM; GSYM INT_OF_NUM_ADD]] THEN
  SUBGOAL_THEN
   `!f:real^N->bool. f face_of p ==> conic hull f INTER {x | x$1 = &1} = f`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `affine hull p:real^N->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET_TRANS];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `!f:real^N->bool. f face_of s ==> f INTER {x | x$1 = &1} face_of p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `p = conic hull p INTER {x:real^N | x$1 = &1}` SUBST1_TAC
    THENL [ASM_MESON_TAC[FACE_OF_REFL; POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
    MATCH_MP_TAC FACE_OF_SLICE THEN
    ASM_REWRITE_TAC[CONVEX_STANDARD_HYPERPLANE];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `!f. f face_of s  /\ &0 < aff_dim f
        ==> conic hull (f INTER {x:real^N | x$1 = &1}) = f`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; CONIC_HULL_EXPLICIT; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_MESON_TAC[FACE_OF_CONIC; conic];
      REWRITE_TAC[SUBSET; CONIC_HULL_EXPLICIT] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
      ASM_CASES_TAC `x:real^N = vec 0` THENL
       [SUBGOAL_THEN `?y:real^N. y IN f /\ ~(y = vec 0)` STRIP_ASSUME_TAC THENL
         [MATCH_MP_TAC(SET_RULE
           `a IN s /\ ~(s = {a}) ==> ?y. y IN s /\ ~(y = a)`) THEN
          ASM_MESON_TAC[AFF_DIM_EQ_0; INT_LT_REFL];
          SUBGOAL_THEN `&0 < (y:real^N)$1` ASSUME_TAC THENL
           [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
          EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO] THEN
          EXISTS_TAC `inv(y$1) % y:real^N` THEN
          ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV;
                       REAL_LT_IMP_NZ] THEN
          ASM_MESON_TAC[FACE_OF_CONIC; conic; REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
        SUBGOAL_THEN `&0 < (x:real^N)$1` ASSUME_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
        EXISTS_TAC `(x:real^N)$1` THEN EXISTS_TAC `inv(x$1) % x:real^N` THEN
        ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV; REAL_LT_IMP_LE;
          REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
        ASM_MESON_TAC[FACE_OF_CONIC; conic; REAL_LE_INV_EQ; REAL_LT_IMP_LE]]];
    ASM_SIMP_TAC[INT_ARITH `&0:int < &d + &1`]] THEN
  SUBGOAL_THEN
   `!f:real^N->bool. f face_of p ==> (conic hull f) face_of s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `f:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[CONIC_HULL_EMPTY; EMPTY_FACE_OF] THEN
    REWRITE_TAC[face_of] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC HULL_MONO THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ASM_MESON_TAC[CONVEX_CONIC_HULL; FACE_OF_IMP_CONVEX];
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[CONIC_HULL_EXPLICIT; IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`ca:real`; `a:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`cb:real`; `b:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`cx:real`; `x:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `cx % x:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[IN_SEGMENT] THEN
      MATCH_MP_TAC(TAUT `(a ==> ~b) ==> a /\ b ==> c`) THEN
      DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[CART_EQ] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VEC_COMPONENT] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT] THEN
      ONCE_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `&0 < (ca % a:real^N)$1 \/ &0 < (cb % b:real^N)$1`
      DISJ_CASES_TAC THENL
       [SUBGOAL_THEN `(ca % a:real^N) IN s /\ (cb % b:real^N) IN s`
          (fun th -> ASM_MESON_TAC[th]) THEN
        ASM_MESON_TAC[conic; HULL_SUBSET; SUBSET];
        MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(&0 = a + b)`);
        MATCH_MP_TAC(REAL_ARITH `&0 < b /\ &0 <= a ==> ~(&0 = a + b)`)] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL; REAL_SUB_LT] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_LT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[conic; HULL_SUBSET; SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `~(cx % x:real^N = vec 0)` THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^N = a` THENL
     [REWRITE_TAC[IN_SEGMENT] THEN DISCH_THEN
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` MP_TAC)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
       `x % a:real^N = y % a + z % b <=> (x - y) % a = z % b`] THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(a:real^N) IN affine hull p /\ b IN affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_ENTIRE; REAL_LT_IMP_NZ] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`ca:real`; `a:real^N`] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          MAP_EVERY EXISTS_TAC [`&0`; `x:real^N`] THEN
          ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL]];
        CONJ_TAC THENL [EXISTS_TAC `ca:real`; EXISTS_TAC `cb:real`] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:real^N = b` THENL
     [REWRITE_TAC[IN_SEGMENT] THEN DISCH_THEN
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` MP_TAC)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
       `x % b:real^N = y % a + z % b <=> (x - z) % b = y % a`] THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(a:real^N) IN affine hull p /\ b IN affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_ENTIRE;
                   REAL_LT_IMP_NE; REAL_SUB_0] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`&0`; `x:real^N`] THEN
          ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL];
          MAP_EVERY EXISTS_TAC [`cb:real`; `b:real^N`] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
        CONJ_TAC THENL [EXISTS_TAC `ca:real`; EXISTS_TAC `cb:real`] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN segment(a,b)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_OPEN_SEGMENT]) THEN
      ASM_REWRITE_TAC[IN_OPEN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(x:real^N) IN affine hull p /\
                    a IN affine hull p /\ b IN affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      DISCH_THEN(MP_TAC o AP_TERM `(%) (inv cx) :real^N->real^N`) THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
      DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `inv(cx) * u * cb` THEN
      REWRITE_TAC[REAL_ARITH `inv(cx) * x:real = x / cx`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_LE] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `a + b = cx ==> &0 <= a ==> b <= &1 * cx`)) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB] THEN
        BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`(&1 - u) * ca + u * cb = cx`; `~(cx = &0)`] THEN
        CONV_TAC REAL_FIELD];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [face_of]) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `x:real^N`]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `!f:real^N->bool. f face_of p /\ ~(f = {})
                     ==> aff_dim(conic hull f) = aff_dim f + &1`
  (LABEL_TAC "*") THENL
   [ALL_TAC;
    CONJ_TAC THEN X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THENL
     [REMOVE_THEN "*" (MP_TAC o SPEC `f INTER {x:real^N | x$1 = &1}`) THEN
      ASM_SIMP_TAC[INT_ARITH `&0:int < &d + &1`; INT_EQ_ADD_RCANCEL] THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      SUBGOAL_THEN `?y:real^N. y IN f /\ ~(y = vec 0)` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `a IN s /\ ~(s = {a}) ==> ?y. y IN s /\ ~(y = a)`) THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`]
            FACE_OF_CONIC) THEN
          ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN REPEAT DISCH_TAC;
          DISCH_TAC] THEN
        UNDISCH_TAC `aff_dim(f:real^N->bool) = &d + &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SING; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        SUBGOAL_THEN `&0 < (y:real^N)$1` ASSUME_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
        EXISTS_TAC `inv(y$1) % y:real^N` THEN
        ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV;
                     REAL_LT_IMP_NZ] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`]
          FACE_OF_CONIC) THEN
        ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN
        REWRITE_TAC[conic] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
      REMOVE_THEN "*" (MP_TAC o SPEC `f:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(f:real^N->bool) = &d` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC]] THEN
  X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(INT_ARITH `f < a /\ a <= f + &1 ==> a:int = f + &1`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC AFF_DIM_PSUBSET THEN
    SIMP_TAC[PSUBSET; HULL_MONO; HULL_SUBSET] THEN
    REWRITE_TAC[EXTENSION; NOT_FORALL_THM] THEN EXISTS_TAC `vec 0:real^N` THEN
    MATCH_MP_TAC(TAUT `~p /\ q ==> ~(p <=> q)`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!t. ~(x IN t) /\ s SUBSET t ==> ~(x IN s)`) THEN
      EXISTS_TAC `affine hull p:real^N->bool` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC HULL_MONO THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
      MATCH_MP_TAC(SET_RULE
       `x IN s /\ s SUBSET P hull s ==> x IN P hull s`) THEN
      ASM_SIMP_TAC[CONIC_CONTAINS_0; HULL_SUBSET; CONIC_CONIC_HULL] THEN
      ASM_REWRITE_TAC[CONIC_HULL_EQ_EMPTY]];
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `aff_dim((vec 0:real^N) INSERT (affine hull f))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[AFF_DIM_INSERT; AFF_DIM_AFFINE_HULL] THEN INT_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    MATCH_MP_TAC AFF_DIM_SUBSET THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL; SUBSET; CONIC_HULL_EXPLICIT] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `c % x:real^N = vec 0 + c % (x - vec 0)`] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC; IN_INSERT]]);;
```

### Informal statement
For all `p` of type `real^N->bool`, if 2 is less than or equal to the dimension index of `:N`, `p` is a polytope, and the affine hull of `p` is the set of all `x` such that `x$1` (the first component of `x`) equals 1, then the sum from 0 to `dimindex(:N)-1` of `(-- &1) pow d * &(CARD {f | f face_of p /\ aff_dim f = &d })` equals 1.

### Informal sketch
The proof proceeds as follows:
- First, the case where `p` is empty is handled directly.
- The conic hull `s` of `p` is introduced as an abbreviation.
- It is shown that `(conic hull f) INTER {x:real^N | x$1 = &1} = f` if `f` is a subset of `{x:real^N | x$1 = &1}`.
- It is proven that `s` is a polyhedron, a conic, not equal to `real^N`, and not empty.
- It is shown that 0 is in `s` and that the interior of `s` is not empty.
- It is shown that for all `x` in `s`, if `x` is not the zero vector, then 0 < `x$1` and that for all `x` in `s`, 0 <= `x$1`.
- The main theorem is then derived using a summation over the faces of `s`, connecting the faces of `p` and `s` by showing that `conic hull f INTER {x | x$1 = &1} = f` for `f face_of p` and `f INTER {x | x$1 = &1} face_of p` for `f face_of s`.
- It's proven that `conic hull (f INTER {x:real^N | x$1 = &1}) = f` if `f face_of s` and `0 < aff_dim f`.
- Finally, it is demonstrated that if `f face_of p`, then `(conic hull f) is a face of s`. Also, `aff_dim(conic hull f) = aff_dim f + &1` if `f face_of p` and `~(f = {})`.

### Mathematical insight
The Euler-Poincaré lemma relates the alternating sum of the number of faces of a polytope to 1. This specific version considers a polytope embedded in a hyperplane where the first coordinate is fixed to 1. The core idea is to lift the polytope to a cone, apply the existing Euler-Poincaré theorem for cones, and then relate the faces of the original polytope to the faces of the cone within this hyperplane. The restriction `affine hull p = {x | x$1 = &1}` simplifies the connection between the faces of `p` and faces of the corresponding cone constructed from `p`.

### Dependencies
**Definitions/Theorems:**
- `AFF_DIM_HYPERPLANE`
- `BASIS_NONZERO`
- `DOT_BASIS`
- `DIMINDEX_GE_1`
- `LE_REFL`
- `AFF_DIM_AFFINE_HULL`
- `AFF_DIM_EMPTY`
- `INT_ARITH `--(&1):int = x - &1 <=> x = &0``
- `INT_OF_NUM_EQ`
- `LE_1`
- `EULER_POLYHEDRAL_CONE`
- `HULL_SUBSET`
- `SUBSET_INTER`
- `SUBSET`
- `CONIC_HULL_EXPLICIT`
- `IN_INTER`
- `IMP_CONJ`
- `FORALL_IN_GSPEC`
- `VECTOR_MUL_COMPONENT`
- `REAL_MUL_RID`
- `VECTOR_MUL_LID`
- `CONVEX_CONE_HULL_SEPARATE_NONEMPTY`
- `CONVEX_HULL_EQ_EMPTY`
- `POLYHEDRON_CONVEX_CONE_HULL`
- `POLYHEDRON_IMP_CONVEX`
- `CONIC_CONIC_HULL`
- `POLYTOPE_IMP_BOUNDED`
- `BOUNDED_POS`
- `NOT_EXISTS_THM`
- `COMPONENT_LE_NORM`
- `CONIC_HULL_EQ_EMPTY`
- `CONIC_CONTAINS_0`
- `EMPTY_INTERIOR_SUBSET_HYPERPLANE`
- `HULL_MINIMAL`
- `AFFINE_HYPERPLANE`
- `AFF_DIM_PSUBSET`
- `AFFINE_HULL_EQ`
- `VEC_COMPONENT`
- `REAL_POS`
- `REAL_LT_IMP_LE`
- `EXTREME_POINT_OF_CONIC`
- `FACE_OF_SING`
- `IN_SEGMENT`
- `FINITE_EMPTY`
- `NOT_IN_EMPTY`
- `GSYM REAL_OF_NUM_SUC`
- `SUM_CLAUSES_LEFT`
- `LE_0`
- `AFF_DIM_EQ_0`
- `real_pow`
- `REAL_MUL_LID`
- `SUM_OFFSET`
- `GSYM SUM_NEG`
- `SUM_EQ_NUMSEG`
- `REAL_POW_ADD`
- `REAL_POW_1`
- `REAL_MUL_RNEG`
- `REAL_MUL_LNEG`
- `BIJECTIONS_CARD_EQ`
- `FINITE_SUBSET`
- `FINITE_POLYHEDRON_FACES`
- `FACE_OF_IMP_SUBSET`
- `FACE_OF_SLICE`
- `CONVEX_STANDARD_HYPERPLANE`
- `FACE_OF_CONIC`
- `conic`
- `INT_ARITH &0:int < &d + &1`
- `HULL_MONO`
- `HULL_SUBSET`
- `FACE_OF_IMP_CONVEX`
- `CONVEX_CONIC_HULL`
- `CONIC_HULL_EMPTY`
- `EMPTY_FACE_OF`
- `IN_OPEN_SEGMENT`
- `VECTOR_ARITH c % x:real^N = y % a + z % b <=> (x - y) % a = z % b`
- `AFF_DIM_PSUBSET`
- `AFF_DIM_INSERT`
- `AFFINE_AFFINE_HULL`
- `AFF_DIM_SUBSET`
- `AFFINE_ADD_MUL_DIFF`
- `HULL_INC`
- `PSUBSET`
- `REAL_MUL_LINV`
- `REAL_SUB_0`

### Porting notes
- Care is needed when translating the real powers and arithmetic reasoning.
- The tactic `ASM_CASES_TAC` is used to perform case splits on assumptions; an equivalent construct should be used in other proof assistants.
- Converting from numerals to reals, like with `&1` may need special attention


---

## EULER_POINCARE_SPECIAL

### Name of formal statement
EULER_POINCARE_SPECIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_POINCARE_SPECIAL = prove
 (`!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &0}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. basis 1 + x) p` EULER_POINCARE_LEMMA) THEN
  ASM_REWRITE_TAC[POLYTOPE_TRANSLATION_EQ; AFFINE_HULL_TRANSLATION] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[EXISTS_REFL; VECTOR_ARITH
     `a + x:real^N = y <=> x = y - a`] THEN
    SIMP_TAC[IN_ELIM_THM; VECTOR_ADD_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SET_RULE `{f | f face_of s /\ P f} =
                          {f | f IN {f | f face_of s} /\ P f}`] THEN
    REWRITE_TAC[FACES_OF_TRANSLATION] THEN
    REWRITE_TAC[SET_RULE `{y | y IN IMAGE f s /\ P y} =
                          {f x |x| x IN s /\ P(f x)}`] THEN
    REWRITE_TAC[AFF_DIM_TRANSLATION_EQ; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `(!x y. Q x y ==> x = y)
        ==> (!x y. P x /\ P y /\ Q x y ==> x = y)`) THEN
      REWRITE_TAC[INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{f:real^N->bool | f face_of p}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[]]]);;
```

### Informal statement
For all `p` of type real^N -> bool (representing a subset of N-dimensional real space), if 2 is less than or equal to the dimension index of `:N`, `p` is a polytope, and the affine hull of `p` is the set of all `x` such that `x$1 = &0` (the first component of x is 0), then the sum from 0 to dimindex(:N)-1 of `(-- &1) pow d * &(CARD {f | f face_of p /\ aff_dim f = &d })` equals `&1`. This is equivalent to sum from 0 to dimindex(:N)-1 of `(-1)^d * (number of faces f of p such that the affine dimension of f is d)` equals 1.

### Informal sketch
The proof proceeds as follows:
- Apply `EULER_POINCARE_LEMMA` to the image of `p` under the translation `IMAGE (\x:real^N. basis 1 + x) p`, where `basis 1` is the first standard basis vector.
- Rewrite using `POLYTOPE_TRANSLATION_EQ` and `AFFINE_HULL_TRANSLATION`.
- Use `ANTS_TAC` to access the assumptions.
- Prove that the translation defined by `IMAGE (\x:real^N. basis 1 + x) p` is a surjective image, followed by simplifications involving vector arithmetic and set operations. The goal is to massage the hypothesis about the affine hull so it applies in the image.
- Rewrite the set `{f | f face_of s /\ P f}` as `{f | f IN {f | f face_of s} /\ P f}`.
- Rewrite the faces using `FACES_OF_TRANSLATION`.
- Rewrite the set `{y | y IN IMAGE f s /\ P y}` as `{f x |x| x IN s /\ P(f x)}`.
- Rewrite the affine dimension using `AFF_DIM_TRANSLATION_EQ` and eliminate the `IN` predicate.
- Discharge and generalize using `GEN_REWRITE_TAC RAND_CONV [SYM th]`.
- Apply `SUM_EQ_NUMSEG`.
- Generalize `d:num` and strip.
- Apply and then apply termwise twice.
- Rewrite the image using `SIMPLE_IMAGE_GEN`.
- Convert using symmetry, then match with `CARD_IMAGE_INJ`.
- Split into two goals, rewriting and matching with a variant of injectivity and using vector arithmetic for the first goal.
- For the second goal, match with `FINITE_SUBSET` and introduce the set of faces of `p`.
- Simplify using `FINITE_POLYTOPE_FACES` and apply `SET_TAC[]`.

### Mathematical insight
This theorem is a specialization of the Euler-Poincaré lemma for polytopes. It imposes the condition that the affine hull of the polytope `p` is the hyperplane where the first coordinate is zero. This condition simplifies the general formula, resulting in the sum of alternating counts of faces of different dimensions being equal to 1. This is a fundamental result in combinatorial topology and geometry, relating the number of faces of different dimensions of a polytope. The standardization of `p` simplifies the counting argument in the proof.

### Dependencies
- `EULER_POINCARE_LEMMA`
- `POLYTOPE_TRANSLATION_EQ`
- `AFFINE_HULL_TRANSLATION`
- `SURJECTIVE_IMAGE_EQ`
- `EXISTS_REFL`
- `VECTOR_ARITH`
- `IN_ELIM_THM`
- `VECTOR_ADD_COMPONENT`
- `BASIS_COMPONENT`
- `DIMINDEX_GE_1`
- `LE_REFL`
- `SET_RULE`
- `FACES_OF_TRANSLATION`
- `AFF_DIM_TRANSLATION_EQ`
- `SUM_EQ_NUMSEG`
- `SIMPLE_IMAGE_GEN`
- `CARD_IMAGE_INJ`
- `INJECTIVE_IMAGE`
- `FINITE_SUBSET`
- `FINITE_POLYTOPE_FACES`

### Porting notes (optional)
- The theorem makes significant use of real vector space properties and set manipulations, so the target proof assistant must have well-developed libraries for these. Translating the tactic-based proof into a more declarative style is advisable for better maintainability and portability.
- The `MESON` call suggests the use of a first-order prover.


---

## EULER_POINCARE_FULL

### Name of formal statement
EULER_POINCARE_FULL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_POINCARE_FULL = prove
 (`!p:real^N->bool.
        polytope p /\ aff_dim p = &(dimindex(:N))
        ==> sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`,
  REPEAT STRIP_TAC THEN ABBREV_TAC
   `f:real^N->real^(N,1)finite_sum =
          \x. lambda i. if i = 1 then &0 else x$(i-1)` THEN
  ABBREV_TAC `s = IMAGE (f:real^N->real^(N,1)finite_sum) p` THEN
  MP_TAC(ISPEC `s:real^(N,1)finite_sum->bool` EULER_POINCARE_SPECIAL) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; ADD_SUB] THEN
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `2 <= n + 1 <=> 1 <= n`] THEN
  SUBGOAL_THEN `linear(f:real^N->real^(N,1)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "s" THEN
  ASM_SIMP_TAC[POLYTOPE_LINEAR_IMAGE; AFFINE_HULL_LINEAR_IMAGE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EQ_FULL]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:real^(N,1)finite_sum` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^N` SUBST1_TAC) THEN
      EXPAND_TAC "f" THEN SIMP_TAC[LAMBDA_BETA; LE_REFL; DIMINDEX_GE_1];
      DISCH_TAC THEN
      EXISTS_TAC `(lambda i. (y:real^(N,1)finite_sum)$(i+1)):real^N` THEN
      EXPAND_TAC "f" THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_1;
       DIMINDEX_GE_1; ARITH_RULE `1 <= i /\ ~(i = 1) ==> 1 <= i - 1`;
       ARITH_RULE `1 <= n /\ i <= n + 1 ==> i - 1 <= n`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC];
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `!x y. (f:real^N->real^(N,1)finite_sum) x = f y <=> x = y`
    ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN
      ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_1;
        DIMINDEX_GE_1; ARITH_RULE `1 <= i /\ ~(i = 1) ==> 1 <= i - 1`;
        ARITH_RULE `1 <= n /\ i <= n + 1 ==> i - 1 <= n`] THEN
      REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ADD_SUB] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
        ASM_ARITH_TAC;
        STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN
    MP_TAC(ISPECL [`f:real^N->real^(N,1)finite_sum`; `p:real^N->bool`]
        FACES_OF_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[SET_RULE `{f | f face_of s /\ P f} =
                          {f | f IN {f | f face_of s} /\ P f}`] THEN
    ASM_REWRITE_TAC[SET_RULE `{y | y IN IMAGE f s /\ P y} =
                              {f x |x| x IN s /\ P(f x)}`] THEN
    ASM_SIMP_TAC[AFF_DIM_INJECTIVE_LINEAR_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `(!x y. Q x y ==> x = y)
        ==> (!x y. P x /\ P y /\ Q x y ==> x = y)`) THEN
      ASM_REWRITE_TAC[INJECTIVE_IMAGE];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{f:real^N->bool | f face_of p}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[]]]);;
```

### Informal statement
For any `p` that is a polytope in `real^N` such that the affine dimension of `p` is equal to the dimension index of `N`, then the following holds: the sum from 0 to the dimension index of `N`, of `(-- &1)` raised to the power of `d` multiplied by the cardinality of the set of `f` such that `f` is a face of `p` and the affine dimension of `f` is equal to `d`, is equal to `&1`.

### Informal sketch
The proof proceeds as follows:
- Define a linear map `f` from `real^N` to `real^(N,1)finite_sum` that maps `x` to a vector where the first component is 0 and the subsequent components are the components of `x`.
- Define `s` as the image of `p` under `f`.
- Apply the theorem `EULER_POINCARE_SPECIAL` to `s`.
- Simplify using properties of `DIMINDEX`.
- Prove that `f` is linear.
- Simplify, using the fact that the image of a polytope under a linear transformation is a polytope and using properties of affine hulls.
- Show that `f` is injective.
- Use the fact that the faces of a linear image are the images of the faces.
- Show that distinct faces are mapped to distinct faces.
- Show that the faces are finite.
- Show that the cardinality of the image is the cardinality of the pre-image since `f` is injective.

### Mathematical insight
This theorem extends the Euler-Poincaré characteristic from a special case to general full-dimensional polytopes. It states that for a full-dimensional polytope `p`, a weighted sum of the number of faces of each dimension is equal to 1. Here, faces are weighted by (-1)^d, where d is the dimension of the face.

### Dependencies
- `EULER_POINCARE_SPECIAL`
- `DIMINDEX_FINITE_SUM`
- `DIMINDEX_1`
- `ADD_SUB`
- `DIMINDEX_GE_1`
- `POLYTOPE_LINEAR_IMAGE`
- `AFFINE_HULL_LINEAR_IMAGE`
- `AFF_DIM_EQ_FULL`
- `EXTENSION`
- `IN_IMAGE`
- `IN_ELIM_THM`
- `IN_UNIV`
- `SUM_EQ_NUMSEG`
- `FACES_OF_LINEAR_IMAGE`
- `AFF_DIM_INJECTIVE_LINEAR_IMAGE`
- `SIMPLE_IMAGE_GEN`
- `CARD_IMAGE_INJ`
- `INJECTIVE_IMAGE`
- `FINITE_SUBSET`
- `FINITE_POLYTOPE_FACES`
- `linear` (definition of linearity)
- `CART_EQ`
- `VECTOR_ADD_COMPONENT`
- `VECTOR_MUL_COMPONENT`
- `LAMBDA_BETA`


---

## EULER_RELATION

### Name of formal statement
EULER_RELATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_RELATION = prove
 (`!p:real^3->bool.
        polytope p /\ aff_dim p = &3
        ==> (CARD {v | v face_of p /\ aff_dim(v) = &0} +
             CARD {f | f face_of p /\ aff_dim(f) = &2}) -
            CARD {e | e face_of p /\ aff_dim(e) = &1} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^3->bool` EULER_POINCARE_FULL) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `3`; SUM_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG] THEN
  SUBGOAL_THEN `{f:real^3->bool | f face_of p /\ aff_dim f = &3} = {p}`
   (fun th -> SIMP_TAC[th; NOT_IN_EMPTY; FINITE_EMPTY; CARD_CLAUSES])
  THENL
   [MATCH_MP_TAC(SET_RULE
     `P a /\ (!x. P x ==> x = a) ==> {x | P x} = {a}`) THEN
    ASM_SIMP_TAC[FACE_OF_REFL; POLYTOPE_IMP_CONVEX] THEN
    X_GEN_TAC `f:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^3->bool`; `p:real^3->bool`]
        FACE_OF_AFF_DIM_LT) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; INT_LT_REFL];
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_ARITH `((x + --y) + z) + -- &1:real = &1 <=>
                            x + z = y + &2`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_SUB2]]);;
```

### Informal statement
For all `p` of type `real^3 -> bool`, if `p` is a polytope and the affine dimension of `p` is equal to 3, then the number of vertices (faces of dimension 0) of `p` plus the number of 2-dimensional faces of `p` minus the number of edges (faces of dimension 1) of `p` is equal to 2.

### Informal sketch
The proof proceeds as follows:

- First, apply `EULER_POINCARE_FULL` to obtain a more general Euler-Poincaré formula.
- Rewrite using `DIMINDEX_3` to specialize to 3 dimensions.
- Simplify the summation using `TOP_DEPTH_CONV num_CONV `3` and `SUM_CLAUSES_NUMSEG`.
- Perform numerical reductions using `NUM_REDUCE_CONV` and `REAL_RAT_REDUCE_CONV`.
- Simplify the real arithmetic expression using identities like `REAL_MUL_LID` and `REAL_MUL_LNEG`.
- Show that the set of 3-dimensional faces of `p` is equal to `{p}`
    - Use the fact that if `P a` and for all `x`, `P x` implies `x = a`, then the set of `x` such that `P x` is equal to `{a}`.
    - Simplify using `FACE_OF_REFL` and `POLYTOPE_IMP_CONVEX`.
    - Introduce a variable and strip.
    - Apply the theorem `FACE_OF_AFF_DIM_LT` to show that no face can have dimension greater or equal to the dimension of the polytope itself if it's a face.
    - Use rewrite rules such as convert successor numbers to reals, additive identity for reals, simplify real arithmetic, convert addition and equality of natural numbers to reals, perform variable substitution, finally, reduce addition and subtraction.
   

### Mathematical insight
This theorem formalizes Euler's formula for 3-dimensional polytopes, a fundamental result in geometry and topology. It states that for any convex polyhedron (satisfying the polytope and dimension assumptions), the number of vertices (V), edges (E), and faces (F) are related by the equation V - E + F = 2.

### Dependencies

**Theorems:**
- `EULER_POINCARE_FULL`
- `DIMINDEX_3`
- `FACE_OF_REFL`
- `POLYTOPE_IMP_CONVEX`
- `FACE_OF_AFF_DIM_LT`
- `SET_RULE`

**Definitions/Axioms/Constants:**
- `polytope`
- `aff_dim`
- `face_of`
- `CARD` (cardinality)
- `REAL_MUL_LID`
- `REAL_MUL_LNEG`
- `NOT_IN_EMPTY`
- `FINITE_EMPTY`
- `CARD_CLAUSES`
- `REAL_OF_NUM_SUC`
- `REAL_ADD_LID`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_EQ`
- `ADD_SUB2`
- `INT_LT_REFL`
- `GSYM`
- `NUM_REDUCE_CONV`
- `REAL_RAT_REDUCE_CONV`
- `TOP_DEPTH_CONV`
- `num_CONV`
- `SUM_CLAUSES_NUMSEG`

### Porting notes (optional)
- The theorem relies on set theory (`{x | P x}`) and cardinality (`CARD`). Ensure the target proof assistant has adequate support for these.
- The proof makes heavy use of rewriting with arithmetic identities over real numbers. The porter must ensure similarly powerful simplification tactics (or manual rewriting) are available.
- The tactic `MATCH_MP_TAC` and its arguments may need adjustments depending on how the target prover handles set theory. Specifically, the `SET_RULE` might be expressed differently or require custom automation in another prover.


---

