# pascal.ml

## Overview

Number of statements: 64

The file `pascal.ml` formalizes Pascal's hexagon theorem. It covers both the projective and affine plane versions of the theorem. It imports `Multivariate/cross.ml`, suggesting a reliance on cross-product definitions for its geometric constructions.


## NORMAL_EXISTS

### Name of formal statement
NORMAL_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORMAL_EXISTS = prove
 (`!u v:real^3. ?w. ~(w = vec 0) /\ orthogonal u w /\ orthogonal v w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
  MP_TAC(ISPEC `{u:real^3,v}` ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; DIMINDEX_3] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `CARD {u:real^3,v}` THEN CONJ_TAC THEN
  SIMP_TAC[DIM_LE_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC);;
```

### Informal statement
For all vectors `u` and `v` in real 3-dimensional space, there exists a vector `w` such that `w` is not the zero vector, `w` is orthogonal to `u`, and `w` is orthogonal to `v`.

### Informal sketch
The proof demonstrates that given any two vectors `u` and `v` in `real^3`, there exists a non-zero vector `w` orthogonal to both.
- The proof starts by exploiting `ORTHOGONAL_SYM` to express the orthogonality conditions in terms of `u` and `v` instead of `w`.
- It uses `ORTHOGONAL_TO_SUBSPACE_EXISTS` to show the existence of a non-zero vector orthogonal to the subspace spanned by `u` and `v`.
- The goal is then reduced to showing that the cardinality of `{u, v}` is not greater than the dimension of the space, which is `3`.
- The proof involves rewriting using facts about `FORALL_IN_INSERT`, `NOT_IN_EMPTY` and `DIMINDEX_3`, using cardinality reasoning and simplifying using arithmetic tactics. Facts about finiteness of sets are also used, e.g. `FINITE_INSERT`, `FINITE_EMPTY`.

### Mathematical insight
This theorem states a fundamental property of 3-dimensional space: given any two vectors, there is always a non-zero vector orthogonal to both. This is closely related to the existence and properties of the cross product. It ensures that the orthogonal complement of the subspace spanned by two vectors is non-trivial.

### Dependencies
Basic real vector space theory and set theory.
- Theorems: `ORTHOGONAL_SYM`, `ORTHOGONAL_TO_SUBSPACE_EXISTS`, `FORALL_IN_INSERT`, `NOT_IN_EMPTY`, `DIMINDEX_3`, `DIM_LE_CARD` (cardinality less than or equal to dimension), `CARD_CLAUSES`
- Definitions: `orthogonal`, `vec` (zero vector)
- Finiteness: `FINITE_INSERT`, `FINITE_EMPTY`

### Porting notes (optional)
*   The `ORTHOGONAL_TO_SUBSPACE_EXISTS` theorem encapsulates significant reasoning about orthogonal complements. Make sure the target proof assistant has a similar theorem or can easily derive it.
*   The proof relies on cardinality reasoning, which may require specific libraries or tactics in other proof assistants.
*   Understanding the definitions of `orthogonal` and `vec` in HOL Light is crucial for ensuring compatibility with the target environment.


---

## direction_tybij

### Name of formal statement
direction_tybij

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let direction_tybij = new_type_definition "direction" ("mk_dir","dest_dir")
 (MESON[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] `?x:real^3. ~(x = vec 0)`);;
```

### Informal statement
A new type called `direction` is defined, with constructor function `mk_dir` and destructor function `dest_dir`. The defining property of this type is that it is isomorphic to the set of all vectors in `real^3` that are not equal to the zero vector `vec 0`. That is, every element of the type `direction` can be represented as a non-zero vector in 3-dimensional real space.

### Informal sketch
The formal statement constructs a new type, `direction`, which is a sub-type of the vector space `real^3`.

- The `new_type_definition` function in HOL Light requires a proof that the set being represented by the new type is non-empty.
- In this case, the set is `{x:real^3 | ~(x = vec 0)}`, which is the set of all non-zero vectors in `real^3`.
- The proof of non-emptiness is automated using `MESON` with the hints `BASIS_NONZERO`, `LE_REFL`, and `DIMINDEX_GE_1` that provides axioms and theorems needed to automatically complete the proof. The tactic automatically proves the non-emptiness by finding a suitable non-zero vector.

### Mathematical insight
The `direction` type represents a direction in 3D space, without regard to magnitude. It is represented by non-zero vectors because the zero vector has no meaningful direction. Defining such a type is a common step in formalizing geometric or physical concepts. The underlying representation as a non-zero vector facilitates reasoning about directions using vector algebra.

### Dependencies
- `BASIS_NONZERO`
- `LE_REFL`
- `DIMINDEX_GE_1`


---

## perpdir

### Name of formal statement
- `perpdir`

### Type of the formal statement
- `new_definition`

### Formal Content
```ocaml
let perpdir = new_definition
 `x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)`;;
```

### Informal statement
- For any `x` and `y` in the type `line`, `x` is perpendicular to `y` is defined to be equivalent to `(dest_dir x)` is orthogonal to `(dest_dir y)`.

### Informal sketch
- The definition introduces the concept of perpendicularity between two lines (`x` and `y`).
- It relates this concept to the orthogonality of the directions of the lines, which are obtained by applying the function `dest_dir` to each line.
- The definition establishes that two lines are perpendicular if and only if their corresponding direction vectors are orthogonal.

### Mathematical insight
- This definition provides a way to formally define perpendicularity between lines using the existing notion of orthogonality between direction vectors.
- The `dest_dir` function is used to extract the direction vector of a line. By checking the orthogonality of these direction vectors, we can determine whether the lines are perpendicular.
- This definition connects geometric intuition with a formal definition that can be used in proofs and calculations.

### Dependencies
- Definitions:
  - `orthogonal`
  - `dest_dir`


---

## pardir

### Name of formal statement
pardir

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pardir = new_definition
 `x || y <=> (dest_dir x) cross (dest_dir y) = vec 0`;;
```

### Informal statement
For any `x` and `y`, `x` is parallel to `y` if and only if the cross product of the direction vector of `x` and the direction vector of `y` equals the zero vector.

### Informal sketch
The definition introduces the concept of parallelism between two directions. It states that two directions, represented by `x` and `y`, are parallel if and only if a specific condition holds. The condition involves the `dest_dir` function, which extracts the direction vector corresponding to a given direction. The cross product of these direction vectors is then computed. The directions are defined to be parallel if and only if this cross product is equal to the zero vector, `vec 0`.

### Mathematical insight
This definition captures the standard mathematical notion of parallelism between two directions in a three-dimensional space. Two directions are parallel if their direction vectors are scalar multiples of each other. In terms of the cross product, this is equivalent to stating that the cross product of their direction vectors is the zero vector.

### Dependencies
- Definitions:
  - `dest_dir`
  - `cross`
  - `vec`


---

## DIRECTION_CLAUSES

### Name of formal statement
DIRECTION_CLAUSES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRECTION_CLAUSES = prove
 (`((!x. P(dest_dir x)) <=> (!x. ~(x = vec 0) ==> P x)) /\
   ((?x. P(dest_dir x)) <=> (?x. ~(x = vec 0) /\ P x))`,
  MESON_TAC[direction_tybij]);;
```
### Informal statement
The following conjunction holds:
1. For any predicate `P` on vectors, the statement that `P` holds for all vectors obtained by the function `dest_dir` is equivalent to the statement that for all vectors `x` not equal to the zero vector `vec 0`, `P` holds for `x`.
2. For any predicate `P` on vectors, the statement that `P` holds for some vector obtained by the function `dest_dir` is equivalent to the statement that there exists a vector `x` not equal to the zero vector `vec 0` such that `P` holds for `x`.

### Informal sketch
The proof uses `MESON_TAC` with the `direction_tybij` theorem. This likely resolves the equivalences using the bijectivity properties related to `dest_dir` and vectors not equal to `vec 0`.

*   The theorem likely relies on the fact that `dest_dir` maps non-zero vectors bijectively to a specific type (presumably directions). The `MESON_TAC` likely uses `direction_tybij` to discharge both directions of each equivalence.

### Mathematical insight
This theorem provides a way to reason about predicates over directions by reasoning about predicates over non-zero vectors and vice versa. `dest_dir` is likely a function that maps non-zero vectors to a canonical representation of direction. This allows for simpler reasoning in many cases by avoiding explicit manipulation of the representation of direction.

### Dependencies
*   Theorems: `direction_tybij`
*   Tactics: `MESON_TAC`


---

## [PARDIR_REFL;

### Name of formal statement
`PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let [PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS] = (CONJUNCTS o prove)
 (`(!x. x || x) /\
   (!x y. x || y <=> y || x) /\
   (!x y z. x || y /\ y || z ==> x || z)`,
  REWRITE_TAC[pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;
```

### Informal statement
The following three statements are theorems, where `x || y` means that the vectors `x` and `y` point in the same direction:
1. For all vectors `x`, `x || x` (reflexivity).
2. For all vectors `x` and `y`, `x || y` if and only if `y || x` (symmetry).
3. For all vectors `x`, `y`, and `z`, if `x || y` and `y || z`, then `x || z` (transitivity).

### Informal sketch
The proof proceeds by proving the three conjuncts within the main goal using `CONJUNCTS`. 
- The initial rewriting uses `pardir` and `DIRECTION_CLAUSES` (likely related to component-wise representation or definitions for vectors).
- The final `VEC3_TAC` tactic likely expands vector operations and simplifies the expressions to complete the proof for each component. The proofs would involve basic algebraic manipulation and potentially case splitting on vector components.

### Mathematical insight
The theorem establishes that the relation "points in the same direction" (`||`) between vectors is an equivalence relation. This is a fundamental property used in many areas of linear algebra and geometry.

### Dependencies
- `prove`
- `CONJUNCTS`
- `pardir`
- `DIRECTION_CLAUSES`
- `VEC3_TAC`


---

## PARDIR_EQUIV

### Name of formal statement
PARDIR_EQUIV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PARDIR_EQUIV = prove
 (`!x y. ((||) x = (||) y) <=> x || y`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS]);;
```
### Informal statement
For all `x` and `y`, the parallel direction of `x` is equal to the parallel direction of `y` if and only if `x` is parallel to `y`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the equivalence using `FUN_EQ_THM`, which likely expands the definition of function equality.
- Then, use a Meson-based automatic proof search, providing the reflexivity (`PARDIR_REFL`), symmetry (`PARDIR_SYM`), and transitivity (`PARDIR_TRANS`) theorems for the `||` relation. This allows Meson to automatically deduce the equivalence.

### Mathematical insight
This theorem establishes the fundamental connection between the equality of parallel directions, represented by the function `(||)`, and the parallelism relation `||` itself. It states that two lines have the same parallel direction if and only if they are parallel. This connection is essential for reasoning about parallelism geometrically.

### Dependencies
- Theorems: `FUN_EQ_THM`, `PARDIR_REFL`, `PARDIR_SYM`, `PARDIR_TRANS`


---

## DIRECTION_AXIOM_1

### Name of formal statement
DIRECTION_AXIOM_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRECTION_AXIOM_1 = prove
 (`!p p'. ~(p || p') ==> ?l. p _|_ l /\ p' _|_ l /\
                             !l'. p _|_ l' /\ p' _|_ l' ==> l' || l`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real^3`; `p':real^3`] NORMAL_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC);;
```
### Informal statement
For all vectors `p` and `p'`: if it is not the case that `p` or `p'`, then there exists a line `l` such that `p` is perpendicular to `l`, `p'` is perpendicular to `l`, and for all lines `l'`, if `p` is perpendicular to `l'` and `p'` is perpendicular to `l'`, then `l'` is parallel to `l`.

### Informal sketch
- The proof starts by rewriting using definitions related to perpendicularity (`perpdir`), parallelism (`pardir`), and `DIRECTION_CLAUSES`.
- After simplification using `REPEAT STRIP_TAC`, the goal becomes an existential statement and the tactic `MP_TAC(SPECL \[`p:real^3`; `p':real^3`\] NORMAL_EXISTS)` introduces an existential variable.
- `MATCH_MP_TAC MONO_EXISTS` is then applied, which matches with an existing existential quantifier.
- The proof then proceeds by discharging assumptions using `POP_ASSUM_LIST(MP_TAC o end_itlist CONJ)`, which handles conjunctions in the assumptions.
- Finally, `VEC3_TAC` is used to prove the vector-specific parts of the goal.

### Mathematical insight
This theorem states that given two vectors `p` and `p'` that are not both true (non-zero), there exists a unique line `l` (up to parallelism) that is perpendicular to both `p` and `p'`. This captures the geometric intuition that two vectors define a plane, and `l` is the normal vector to that plane.

### Dependencies
- Definitions: `perpdir`, `pardir`
- Theorems: `DIRECTION_CLAUSES`


---

## DIRECTION_AXIOM_2

### Name of formal statement
DIRECTION_AXIOM_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRECTION_AXIOM_2 = prove
 (`!l l'. ?p. p _|_ l /\ p _|_ l'`,
  REWRITE_TAC[perpdir; DIRECTION_CLAUSES] THEN
  MESON_TAC[NORMAL_EXISTS; ORTHOGONAL_SYM]);;
```

### Informal statement
For any two lines `l` and `l'`, there exists a line `p` that is perpendicular to both `l` and `l'`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using `perpdir` and `DIRECTION_CLAUSES`. The term `perpdir` likely defines what it means for a line to be perpendicular to a direction, and `DIRECTION_CLAUSES` expands definitions related to directions.
- Then apply `MESON_TAC` using the theorems `NORMAL_EXISTS` and `ORTHOGONAL_SYM`. `NORMAL_EXISTS` likely asserts the existence of a normal vector, or direction, of a given line. `ORTHOGONAL_SYM` likely asserts the symmetry of orthogonality between two lines, i.e. "if line `a` is orthogonal to line `b`, then line `b` is orthogonal to line `a`". The `MESON_TAC` tactic attempts to automatically prove the goal using the provided assumptions.

### Mathematical insight
The theorem asserts that for any two lines, there exists a line that is perpendicular to both. This reflects a property of 3-dimensional space (or higher), where any two lines have a common perpendicular. In 2-dimensional space, this is not generally true. This theorem encapsulates a fundamental geometric concept.

### Dependencies
- Definitions: `perpdir`
- Theorems: `NORMAL_EXISTS`, `ORTHOGONAL_SYM`, `DIRECTION_CLAUSES`


---

## DIRECTION_AXIOM_3

### Name of formal statement
DIRECTION_AXIOM_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRECTION_AXIOM_3 = prove
 (`?p p' p''.
        ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
        ~(?l. p _|_ l /\ p' _|_ l /\ p'' _|_ l)`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN MAP_EVERY
   (fun t -> EXISTS_TAC t THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH])
   [`basis 1 :real^3`; `basis 2 : real^3`; `basis 3 :real^3`] THEN
  VEC3_TAC);;
```

### Informal statement
There exist vectors `p`, `p'`, and `p''` such that:
1. `p` and `p'` are not parallel;
2. `p'` and `p''` are not parallel;
3. `p` and `p''` are not parallel;
4. There does not exist a vector `l` such that `p` is perpendicular to `l`, `p'` is perpendicular to `l`, and `p''` is perpendicular to `l`.

### Informal sketch
The proof demonstrates the existence of three non-parallel vectors in 3D space that do not share a common perpendicular vector.

- First, the definition of parallel (`pardir`), perpendicular (`perpdir`) and simplification rules (`DIRECTION_CLAUSES`) are rewritten to expand the statement.
- Then, the existential quantifiers are satisfied by instantiating `p`, `p'`, and `p''` with `basis 1`, `basis 2`, and `basis 3`, respectively. This is done using `EXISTS_TAC` for each existential quantifier. Simplification using `BASIS_NONZERO`, `DIMINDEX_3` and `ARITH` shows these are distinct basis vectors.
- Finally, `VEC3_TAC` is used to prove vector-specific goals.

### Mathematical insight
This theorem establishes a fundamental property of three-dimensional space: it is possible to find three vectors that are pairwise non-parallel and do not have a common perpendicular vector. These three vectors span the entire space. This is because the last part of the theorem states that there is no line `l` to which all the vectors are perpendicular.

### Dependencies
- `perpdir`
- `pardir`
- `DIRECTION_CLAUSES`
- `BASIS_NONZERO`
- `DIMINDEX_3`
- `ARITH`
- `VEC3_TAC`


---

## DIRECTION_AXIOM_4_WEAK

### Name of formal statement
DIRECTION_AXIOM_4_WEAK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRECTION_AXIOM_4_WEAK = prove
 (`!l. ?p p'. ~(p || p') /\ p _|_ l /\ p' _|_ l`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 2) l /\
    ~((l cross basis 1) cross (l cross basis 2) = vec 0) \/
    orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 1) cross (l cross basis 3) = vec 0) \/
    orthogonal (l cross basis 2) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 2) cross (l cross basis 3) = vec 0)`
  MP_TAC THENL [POP_ASSUM MP_TAC THEN VEC3_TAC; MESON_TAC[CROSS_0]]);;
```
### Informal statement
For any vector `l`, it is not the case that there exist vectors `p` and `p'` such that `p` and `p'` are not both the zero vector, `p` is perpendicular to `l`, and `p'` is perpendicular to `l`.

### Informal sketch
The proof proceeds by contradiction, assuming the existence of such vectors `p` and `p'`.
- The goal is to show, given `l`, that we cannot find two non-zero vectors `p` and `p'` both orthogonal to `l`. The rewriting with `DIRECTION_CLAUSES`, `pardir`, and `perpdir` likely expands the definitions of orthogonality and direction.
- The proof is structured to consider different cases for `l`. It reduces the problem to showing that at least one of the following three conditions holds:
    - `l cross basis 1` and `l cross basis 2` are orthogonal to `l`, and their cross product is not the zero vector.
    - `l cross basis 1` and `l cross basis 3` are orthogonal to `l`, and their cross product is not the zero vector.
    - `l cross basis 2` and `l cross basis 3` are orthogonal to `l`, and their cross product is not the zero vector.
- The proof uses `VEC3_TAC` to solve some goal related to vector arithmetic, likely dealing with the cross product and orthogonality.
- The proof uses `MESON_TAC` to automatically discharge the remaining goal, utilizing `CROSS_0` (likely a lemma about the cross product being zero if and only if the vectors are parallel or one of them is zero). This suggests that contradiction is reached by showing p and p' are identical.

### Mathematical insight
The theorem states a necessary condition for vectors in 3D space: it's impossible to find two non-zero and non-parallel vectors both orthogonal to a given vector. This captures a fundamental aspect of 3D geometry, implying that the space of vectors orthogonal to a given vector is at most one-dimensional (a line).

### Dependencies
- Theorem: `DIRECTION_CLAUSES`
- Definition: `pardir`
- Definition: `perpdir`
- Theorem: `CROSS_0`


---

## ORTHOGONAL_COMBINE

### Name of formal statement
ORTHOGONAL_COMBINE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ORTHOGONAL_COMBINE = prove
 (`!x a b. a _|_ x /\ b _|_ x /\ ~(a || b)
           ==> ?c. c _|_ x /\ ~(a || c) /\ ~(b || c)`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `a + b:real^3` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC);;
```
### Informal statement
For all vectors `x`, `a`, and `b` in 3-dimensional real space, if `a` is orthogonal to `x` and `b` is orthogonal to `x` and `a` is not parallel to `b`, then there exists a vector `c` such that `c` is orthogonal to `x` and `a` is not parallel to `c` and `b` is not parallel to `c`.

### Informal sketch
*   The proof begins by using rewrite theorems `DIRECTION_CLAUSES`, `pardir`, and `perpdir`.
*   The goal is stripped, and then a vector `c` is introduced as `a + b`.
*   The goal is reduced to showing the orthogonality of `a + b` to `x`, the non-parallelism of `a` to `a + b`, and the non-parallelism of `b` to `a + b`.
*   The assumptions are moved into the assumption list and combined using conjunction.
*   Vector tactics are applied to prove the resulting goal.

### Mathematical insight
This theorem demonstrates that given two non-parallel vectors `a` and `b` both orthogonal to a vector `x`, it is possible to find a third vector `c` (in this case, `a + b`) which is also orthogonal to `x` but is not parallel to either `a` or `b`. Geometrically, this means that we can always find a linear combination of `a` and `b` that maintains orthogonality to `x` while differing in direction from both input vectors.

### Dependencies
*   Theorems: `DIRECTION_CLAUSES`, `pardir`, `perpdir`
*   Tactics: `REWRITE_TAC`, `STRIP_TAC`, `EXISTS_TAC`, `MP_TAC`, `CONJ`, `VEC3_TAC`, `POP_ASSUM_LIST`, `REPEAT`

### Porting notes (optional)
The proof relies heavily on rewriting with geometric definitions, assumptions management, and vector space reasoning within HOL Light's `VEC3_TAC`. When porting, ensure that the target proof assistant has similar geometrical definitions and can perform similar term re-writing. Also, a corresponding `VEC3_TAC`-like automation may be needed for the vector space axioms.


---

## DIRECTION_AXIOM_4

### Name of formal statement
DIRECTION_AXIOM_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRECTION_AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
                  p _|_ l /\ p' _|_ l /\ p'' _|_ l`,
  MESON_TAC[DIRECTION_AXIOM_4_WEAK; ORTHOGONAL_COMBINE]);;
```
### Informal statement
For any line `l`, there exist points `p`, `p'`, and `p''` such that `p`, `p'`, and `p''` are distinct (i.e., `p` is not equal to `p'`, `p'` is not equal to `p''`, and `p` is not equal to `p''`), and `p`, `p'`, and `p''` are all orthogonal to `l`.

### Informal sketch
The theorem states the existence of three distinct points orthogonal to a given line. The proof uses `MESON_TAC` tactic along with the theorems `DIRECTION_AXIOM_4_WEAK` and `ORTHOGONAL_COMBINE`. This suggests a proof by contradiction or a combination of existing results regarding orthogonality and distinctness of points and lines.

*   The tactic `MESON_TAC` indicates that the proof uses a first-order automatic theorem prover.
*   `DIRECTION_AXIOM_4_WEAK` likely provides some weaker form of existence of orthogonal points to a line.
*   `ORTHOGONAL_COMBINE` suggests a rule or theorem about combining orthogonality relations to derive the existence of the required three distinct points

### Mathematical insight
This theorem is essential for demonstrating the richness of the space, showing that there are always at least three points that share the property of being orthogonal to any given line. This contributes to the geometric structure and properties related to orthogonality.

### Dependencies
*   Theorems: `DIRECTION_AXIOM_4_WEAK`, `ORTHOGONAL_COMBINE`


---

## line_tybij

### Name of formal statement
line_tybij

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let line_tybij = define_quotient_type "line" ("mk_line","dest_line") `(||)`;;
```

### Informal statement
Define a new type called `line` as a quotient type, using `mk_line` as a constructor and `dest_line` as a destructor, with the equivalence relation `(||)`.

### Informal sketch
The function `define_quotient_type` from HOL Light constructs a new type `line` by taking the quotient of an existing type (inferred by HOL Light from the signatures of `mk_line` and `dest_line`) with respect to the equivalence relation given by `(||)`. The constructor `mk_line` lifts elements from the original type to the quotient type `line`. The destructor `dest_line` maps elements of the quotient type `line` back to the original type, but its behavior is only specified up to the equivalence relation `(||)`.

The process involves several steps:
- Define a raw type `line`.
- Define functions `mk_line` and `dest_line` between the raw type and the intended representing type.
- Prove that `(||)` is an equivalence relation on the representing type.
- Define the abstract type `line` as the quotient.
- Establish the properties of `mk_line` and `dest_line` with respect to the quotient.

### Mathematical insight
This definition introduces the type of lines as a quotient. The exact meaning of `(||)` determines what constitutes equivalent representatives of lines. The purpose of defining a quotient type is to work with abstract mathematical objects (lines) rather than concrete representations.

### Dependencies
- `define_quotient_type`


---

## PERPDIR_WELLDEF

### Name of formal statement
PERPDIR_WELLDEF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERPDIR_WELLDEF = prove
 (`!x y x' y'. x || x' /\ y || y' ==> (x _|_ y <=> x' _|_ y')`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;
```
### Informal statement
For all vectors `x`, `y`, `x'`, and `y'`, if `x` is parallel to `x'` and `y` is parallel to `y'`, then `x` is perpendicular to `y` if and only if `x'` is perpendicular to `y'`.

### Informal sketch
The proof establishes that the perpendicularity of directions is well-defined with respect to parallelism. It relies on rewriting with the definitions of `perpdir` (perpendicular direction) and `pardir` (parallel direction), and uses basic properties of vectors to conclude the result.
- The theorem states an equivalence, so the proof must show implication in both directions. The high-level structure of the proof involves rewriting with the definitions of these concepts and appealing to vector space properties.
- The tactic `REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES]` unfolds the definitions of perpendicularity and parallelism for directions, and applies some elementary identities about directions.
- `VEC3_TAC` then uses vector space reasoning to complete the proof.

### Mathematical insight
The theorem demonstrates that the concept of perpendicularity between directions is invariant under parallelism. This means if two vectors define directions that are parallel to two other vectors, then if the first two vectors are perpendicular, so are the second two. This is a crucial property when dealing with directions as equivalence classes of parallel vectors.

### Dependencies
- Definitions: `perpdir`, `pardir`
- Theorems: `DIRECTION_CLAUSES`


---

## perpl,perpl_th

### Name of formal statement
- perpl,perpl_th

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;
```
### Informal statement
- A total function `perpl` from `(real^3) dir` to `(real^3) dir` and a theorem named `perpl_th` asserting its well-definedness are introduced by lifting a function taking a value of type `real^3 line` to its second component (which has type `(real^3) dir`) using the equivalence relation `PARDIR_WELLDEF` and the fact that `PARDIR_REFL` and `PARDIR_TRANS` hold.

### Informal sketch
- The function `perpl` is defined using `lift_function`.
- `lift_function` requires:
    - A type bijection `line_tybij` between the type `real^3 line` and some other type (here `(real^3 * (real^3)dir)`)
    - An equivalence relation `PERPDIR_WELLDEF` on the type `(real^3) dir`.
    - A function that is the second projection `snd` that extracts the direction component from a line representation `(real^3 * (real^3)dir)`. This is the function to be lifted.
- The theorem `perpl_th` asserts that the equivalence relation `PERPDIR_WELLDEF` is preserved under `perpl`, meaning the definition is well-defined.

### Mathematical insight
- `perpl` maps a direction to its perpendicular direction, constructed by viewing direction as existing within a `real^3 line` and lifting the perpendicular concept from lines. This provides a formal definition of taking the perpendicular of a direction, which is necessary because the `direction` type is really just a representation of an equivalence class of lines.

### Dependencies
- Definitions:
    - `line_tybij`
    - `PERPDIR_WELLDEF`
- Theorems:
    - `PARDIR_REFL`
    - `PARDIR_TRANS`


---

## line_lift_thm

### Name of formal statement
line_lift_thm

### Type of the formal statement
theorem

### Formal Content
```ocaml
let line_lift_thm = lift_theorem line_tybij
 (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th];;
```
### Informal statement
The theorem `line_lift_thm` states that if `line_tybij` establishes a type bijection between the type `'a line` and the type `real * real`, then lifting the theorems `PARDIR_REFL`, `PARDIR_SYM`, `PARDIR_TRANS` and `perpl_th` will result in a valid theorem. Here, `PARDIR_REFL` asserts that the parallel direction relation is reflexive, `PARDIR_SYM` asserts that it is symmetric, `PARDIR_TRANS` asserts that it is transitive, and `perpl_th` is a theorem about perpendicularity.

### Informal sketch
The theorem `line_lift_thm` uses `lift_theorem` to transfer properties established on the type `'a line` to the type `real * real` using the type bijection given by `line_tybij`.

- The function `lift_theorem` takes a type bijection `line_tybij` and a list of theorems about lines:
  - `PARDIR_REFL`: Reflexivity of the parallel direction relation.
  - `PARDIR_SYM`:  Symmetry of the parallel direction relation.
  - `PARDIR_TRANS`: Transitivity of the parallel direction relation.
  - `perpl_th`: A theorem about perpendicularity.
  These theorems are then transferred to corresponding theorems about pairs of reals, using the type bijection `line_tybij`.

### Mathematical insight
This theorem provides a method to transfer existing theorems about lines by using a type bijection between lines and pairs of reals. This highlights the usefulness of type bijections to transfer properties between equivalent types. This approach promotes code reuse; theorems already proven about lines do not need to be manually reproved for the real-pairs representation.

### Dependencies
- `line_tybij`
- `PARDIR_REFL`
- `PARDIR_SYM`
- `PARDIR_TRANS`
- `perpl_th`

### Porting notes (optional)
The `lift_theorem` function is specific to HOL Light. Other proof assistants often have mechanisms for transferring theorems along type isomorphisms or equivalences, but the syntax and usage may differ substantially. In Coq, one might use `relation_morphims` or similar tools to achieve a similar effect. In Isabelle/HOL, one could use `transfer` method. One needs to find the corresponding tools in the specific proof assistant.


---

## LINE_AXIOM_1

### Name of formal statement
LINE_AXIOM_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LINE_AXIOM_1 = line_lift_thm DIRECTION_AXIOM_1;;
```

### Informal statement
The theorem `LINE_AXIOM_1` states that the result of lifting the theorem `DIRECTION_AXIOM_1` using the function `line_lift_thm` is true.

### Informal sketch
The theorem `LINE_AXIOM_1` is proved by applying the higher-order theorem `line_lift_thm` to the theorem `DIRECTION_AXIOM_1`. The theorem `line_lift_thm` presumably takes a theorem about directions and lifts it to a theorem about lines. Thus, the proof is a direct application of a lifting theorem.

### Mathematical insight
This theorem represents an automated step in transferring properties from directions to lines, likely within a geometric context. The lifted theorem likely states a property about lines that is analogous to the property about directions stated by `DIRECTION_AXIOM_1`.

### Dependencies
- Theorems: `DIRECTION_AXIOM_1`, `line_lift_thm`


---

## LINE_AXIOM_2

### Name of formal statement
LINE_AXIOM_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
```

### Informal statement
For all lines `l`, there exists a point `p` on the line `l`. This theorem is derived by lifting the theorem `DIRECTION_AXIOM_2` to the context of lines using `line_lift_thm`.

### Informal sketch
The theorem `LINE_AXIOM_2` is proven by applying the theorem prover `line_lift_thm` to the axiom `DIRECTION_AXIOM_2`. The `line_lift_thm` theorem prover likely transforms a statement about directions into an equivalent statement about lines. `DIRECTION_AXIOM_2` asserts the existence of a direction, and `line_lift_thm` then relates this direction to the existence of point on a line.

### Mathematical insight
This theorem establishes a fundamental property of lines: that every line must contain at least one point. It's a basic axiom in Euclidean geometry and is essential for building up more complex geometric results. The lifting process via `line_lift_thm` suggests that the underlying axiom `DIRECTION_AXIOM_2` may concern the existence or properties of directions, which are then translated into a statement about lines through a suitable transformation.

### Dependencies
- Theorems: `DIRECTION_AXIOM_2`
- Theorem provers: `line_lift_thm`


---

## LINE_AXIOM_3

### Name of formal statement
LINE_AXIOM_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
```

### Informal statement
`LINE_AXIOM_3` states that if for all points `p`, there exists a point `q` such that `p` is not equal to `q`, and `collinear p q (direction p + direction q)`, then for all lines `l`, there exists a point `p` not on `l`. The theorem is obtained by lifting `DIRECTION_AXIOM_3` through the `line_lift_thm` transformation.

### Informal sketch
The proof involves lifting `DIRECTION_AXIOM_3` to line space using `line_lift_thm`. Essentially, the proof starts with an assumption about the existence of points and collinearity involving a direction function. This assumption, originally concerning `direction`, is translated into a statement about lines and points not lying on those lines. `line_lift_thm` performs this transformation.

### Mathematical insight
This theorem formalizes a basic geometric property: if any point has a distinct point collinear with its direction then any line has points off the line. It establishes a connection between the existence of distinct points and the property that no line fills the entire plane. This is an important axiom in constructing models of geometry, as it provides a basic dimensionality property.

### Dependencies
- Axioms: `DIRECTION_AXIOM_3`
- Theorems: `line_lift_thm`

### Porting notes (optional)
The function `line_lift_thm` performs a transformation dependent on the representation of lines and directions. The specific details of this transformation will have to be re-implemented in another proof assistant, depending on how lines and directions are defined. The main difficulty is replicating the effect of `line_lift_thm` which translates a statement about directions to one about lines, likely involving unfolding definitions and applying appropriate rewriting rules.


---

## LINE_AXIOM_4

### Name of formal statement
LINE_AXIOM_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4;;
```

### Informal statement
The theorem states that the lifted version, produced by `line_lift_thm`, of `DIRECTION_AXIOM_4` is true.

### Informal sketch
The theorem `LINE_AXIOM_4` is a direct result of lifting the theorem `DIRECTION_AXIOM_4` using the function `line_lift_thm`. This essentially propagates the theorem about directions to lines.

### Mathematical insight
This statement reflects a standard technique in formalizing geometry where properties established for simpler objects (like directions) are then transferred or lifted to more complex objects (like lines) that are built upon them. It provides a mechanism to extend geometric relationships from directions to lines.

### Dependencies
- `DIRECTION_AXIOM_4`
- `line_lift_thm`


---

## point_tybij

### Name of formal statement
point_tybij

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let point_tybij = new_type_definition "point" ("mk_point","dest_point")
 (prove(`?x:line. T`,REWRITE_TAC[]));;
```

### Informal statement
Define a new type named `point` with a constructor function `mk_point` and a destructor function `dest_point`. The type is inhabited, which is justified by proving that there exists an element `x` of type `line` such that `T` (true) holds.

### Informal sketch
- The type definition is created using `new_type_definition`.
- The first argument is the name of the new type: `"point"`.
- The second argument provides constructor and destructor functions: `mk_point` and `dest_point` respectively.
- The third argument is a proof of the existence of an element of type `line` that satisfies a trivial condition `T`. The trivial condition guarantees that the new type is not empty.  The proof is performed by `REWRITE_TAC[]`, which proves `?x:line. T` by rewriting `T` to `T`. Therefore, any inhabitant of `line` witnesses the existence.

### Mathematical insight
The core idea is to define a new type called `point`. The existence proof ensures that the type is inhabited, i.e., there is at least one element of this type. The type definition introduces a constructor and destructor to work with elements of the newly defined type. In this case, the type is shown to be inhabited because the existential statement `?x:line. T` is trivially true with the condition `T` (true).  This is a standard way to define a new type in HOL Light.

### Dependencies
- Type `line` must be defined previously.


---

## on

### Name of formal statement
on

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let on = new_definition `p on l <=> perpl (dest_point p) l`;;
```

### Informal statement
For any point `p` and any line `l`, `p` is on `l` if and only if the perpendicular from the destination point of `p` to `l`.

### Informal sketch
- The definition introduces a predicate `on` that determines if a point lies on a line.
- It states that a point `p` is on a line `l` if and only if `perpl (dest_point p) l` holds.
- `dest_point p` extracts the destination point associated with point `p`.
- `perpl (dest_point p) l` checks if the point `dest_point p` is perpendicular to `l`, presumably meaning that `dest_point p` lies on the line `l`.

### Mathematical insight
This definition captures the geometric notion of a point lying on a line. It leverages the concept of the "destination point" of `p`, presumably in a vector space setting, and the notion of perpendicularity (`perpl`) to formalize this relationship. The definition essentially states that `p` is considered to lie on `l` if its corresponding position vector points to a location that is perpendicular to `l`. This seems to mean that the point is on the line.

### Dependencies
- Definition: `dest_point`
- Definition: `perpl`


---

## POINT_CLAUSES

### Name of formal statement
POINT_CLAUSES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POINT_CLAUSES = prove
 (`((p = p') <=> (dest_point p = dest_point p')) /\
   ((!p. P (dest_point p)) <=> (!l. P l)) /\
   ((?p. P (dest_point p)) <=> (?l. P l))`,
  MESON_TAC[point_tybij]);;
```
### Informal statement
The following statements hold for the type `:point`:
1. Two points `p` and `p'` are equal if and only if their `dest_point` components are equal.
2. For any predicate `P` on the type of `dest_point` components, `P` holds for all `dest_point` components of points if and only if `P` holds for all elements of the type of `dest_point` components.
3. For any predicate `P` on the type of `dest_point` components, `P` holds for some `dest_point` component of a point if and only if `P` holds for some element of the type of `dest_point` components.

### Informal sketch
The theorem establishes equivalences relating points to their underlying representations via `dest_point`. The proof is performed using `MESON_TAC` with the theorem `point_tybij`. This likely indicates that `point_tybij` provides the necessary type bijection properties to rewrite the equivalences cleanly. Essentially, we are using the fact that the type `:point` is isomorphic to the type of its underlying representation. Consequently, equality is determined by the representation, and quantification over points can be reduced to quantification over the representation type.

### Mathematical insight
This theorem is important for reasoning about points. The first part clarifies the extensionality of points: two points are equal if and only if their underlying representations are equal. The second and third parts show that quantification over the underlying representation type is equivalent to quantification over points when accessing the representation using `dest_point`. This simplifies reasoning because we can often work directly with the underlying representations rather than having to deal with the `:point` type directly.

### Dependencies
- `point_tybij`


---

## POINT_TAC

### Name of formal statement
POINT_TAC

### Type of the formal statement
Theorem-proving tactic

### Formal Content
```ocaml
let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;
```

### Informal statement
`POINT_TAC` is a tactic, which, when applied to a theorem `th`, first rewrites the goal using the list of rewrite rules contained in the list `POINT_CLAUSES`, applying the rewriting only on the assumption part of the goal, and then attempts to solve the goal via `ACCEPT_TAC`.

### Informal sketch
The tactic `POINT_TAC` aims to prove a theorem `th` by the following procedure:
- Rewrite the assumptions of the current goal using the clauses in `POINT_CLAUSES`. The `REWRITE_TAC` is configured to apply rewriting (`REWRITE_TAC`) using the provided rewrite rules only within the assumptions part of the goal (`on`).
- Attempt to complete the proof using `ACCEPT_TAC`. This tactic tries to automatically prove the resulting goal, assuming that the rewriting step has simplified the assumptions sufficiently.

### Mathematical insight
The function `POINT_TAC` is designed to automate proofs related to points and their properties by simplifying assumptions about points and then attempting to complete the proof automatically. The `POINT_CLAUSES` likely contains a collection of rewrite rules that capture fundamental relationships about points (e.g., properties of coordinates, relationships between collinearity and coordinates, etc.). This tactic represents a common pattern of simplification followed by an attempt at automatic proof completion.

### Dependencies
- Definition: `POINT_CLAUSES`
- Tactic: `REWRITE_TAC`, `ACCEPT_TAC`


---

## AXIOM_1

### Name of formal statement
AXIOM_1

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let AXIOM_1 = prove
 (`!p p'. ~(p = p') ==> ?l. p on l /\ p' on l /\
          !l'. p on l' /\ p' on l' ==> (l' = l)`,
  POINT_TAC LINE_AXIOM_1);;
```
### Informal statement
For all points `p` and `p'`, if `p` is not equal to `p'`, then there exists a line `l` such that `p` lies on `l` and `p'` lies on `l`, and for all lines `l'`, if `p` lies on `l'` and `p'` lies on `l'`, then `l'` is equal to `l`.

### Informal sketch
The axiom states that for any two distinct points, there exists a unique line that contains both points. The proof is achieved by:
- Applying `POINT_TAC` to introduce assumptions that the points `p` and `p'` are distinct.
- Applying `LINE_AXIOM_1` which is a predefined axiom that asserts the existence and uniqueness of the line passing through two distinct points.

### Mathematical insight
This axiom captures a fundamental property of Euclidean geometry: that two distinct points uniquely determine a line. It formalizes the intuitive idea that you can draw only one straight line through two given points.

### Dependencies
- Axioms: `LINE_AXIOM_1`

### Porting notes (optional)
This axiom is a fundamental geometric postulate. In other proof assistants, one might need to explicitly define the notion of points, lines, and the `on` relation and then prove uniqueness. The main challenge in porting this would depend on how the geometry is axiomatized in the target theorem prover. Some theorem provers might provide this axiom or a similar one as a built-in.


---

## AXIOM_2

### Name of formal statement
AXIOM_2

### Type of the formal statement
Axiom

### Formal Content
```ocaml
let AXIOM_2 = prove
 (`!l l'. ?p. p on l /\ p on l'`,
  POINT_TAC LINE_AXIOM_2);;
```

### Informal statement
For all lines `l` and `l'`, there exists a point `p` such that `p` lies on `l` and `p` lies on `l'`.

### Informal sketch
The proof uses `POINT_TAC` to introduce the assumption that lines correspond to sets of points (a common assumption in geometry formalizations), and `LINE_AXIOM_2` which likely asserts the existence of a common point between any two lines.
- The tactic `POINT_TAC` likely expands the `on` relation based on a point/line incidence axiom (i.e., if `p on l` then `p mem l` where `l` is treated as a set). Thus, it transforms the goal to: `!l l'. ?p. p mem l /\ p mem l'`.
- `LINE_AXIOM_2` should then assert the existence of a point `p` in the intersection of any two lines `l` and `l'`.

### Mathematical insight
This axiom states that any two lines intersect in at least one point. This is a fundamental axiom in some Euclidean geometries, while in other geometries (e.g., projective geometry) it holds unconditionally, and in yet others (e.g., some non-Euclidean geometries) it does not hold. The axiom is crucial for establishing basic geometric properties and relationships between lines and points.

### Dependencies
- `LINE_AXIOM_2`
- `on` (implicitly defined)

### Porting notes (optional)
The definition of `on` is critical. Ensure that lines are treated as sets of points, or that the `on` predicate models the point/line incidence relationship adequately. The axiom `LINE_AXIOM_2` is also crucial and needs to be ported or proven using other axioms of the geometry. If the target proof assistant has built-in geometry libraries, this axiom may already be present or provable within that library.


---

## AXIOM_3

### Name of formal statement
AXIOM_3

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let AXIOM_3 = prove
 (`?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p on l /\ p' on l /\ p'' on l)`,
  POINT_TAC LINE_AXIOM_3);;
```
### Informal statement
For any points `p`, `p'`, and `p''`, it is not the case that `p` is distinct from `p'`, and `p'` is distinct from `p''`, and `p` is distinct from `p''`, and it is not the case that there exists a line `l` such that `p` lies on `l` and `p'` lies on `l` and `p''` lies on `l`.

### Informal sketch
The proof is performed using the tactic `POINT_TAC` and `LINE_AXIOM_3`.

*   The tactic `POINT_TAC` presumably introduces three distinct points `p`, `p'`, and `p''`.
*   The axiom `LINE_AXIOM_3` is applied. This axiom likely implies that if three distinct points lie on a line, a contradiction arises in the current axiomatic system.
*   The combination of introducing distinct points and invoking `LINE_AXIOM_3` concludes the proof by contradiction.

### Mathematical insight
This axiom states that it is not possible for every three distinct points to lie on the same line. This axiom is crucial for establishing the geometry of the space under consideration. The absence of such an axiom would imply a degenerate geometry where all points are collinear. It is a fundamental statement embodying a geometric notion of dimension.

### Dependencies
*Tactics:*
- `POINT_TAC`

*Axioms:*
- `LINE_AXIOM_3`


---

## AXIOM_4

### Name of formal statement
AXIOM_4

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p on l /\ p' on l /\ p'' on l`,
  POINT_TAC LINE_AXIOM_4);;
```
### Informal statement
For any line `l`, there exist three distinct points `p`, `p'`, and `p''` such that `p` lies on `l`, `p'` lies on `l`, and `p''` lies on `l`.

### Informal sketch
The proof uses the tactic `POINT_TAC`, which is likely a specialized tactic to prove the existence of points satisfying certain properties. It is then followed by `LINE_AXIOM_4`, which seems to be a call to a axiom stating/implying the existence of three distinct points on a line. The tactic likely infers or constructs the existential witnesses `p`, `p'`, and `p''` and then uses `LINE_AXIOM_4` to establish the relationship `p on l /\ p' on l /\ p'' on l` and the distinctness condition `~(p = p') /\ ~(p' = p'') /\ ~(p = p'')`.

### Mathematical insight
This axiom asserts that every line contains at least three distinct points. This is a basic axiom of geometry and is essential for establishing the properties of lines and configurations of points and lines.

### Dependencies
- Axioms: `LINE_AXIOM_4`
- Tactics: `POINT_TAC`


---

## projl

### Name of formal statement
projl

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let projl = new_definition
 `projl x = mk_line((||) (mk_dir x))`;;
```

### Informal statement
Define `projl` as a function that takes a vector `x` as input, and returns a projective line constructed by applying the `mk_line` function to the direction obtained by applying `mk_dir` to `x` and then applying the parallelity relation `(||)` to the result.

### Informal sketch
The definition introduces a function `projl` that maps vectors to projective lines. The process involves:
- Taking a vector `x`.
- Transforming the vector `x` into a direction using `mk_dir`.
- Applying the parallelity relation `(||)` to the direction to obtain something parallel to it.
- Constructing a projective line from the parallel direction using `mk_line`.

### Mathematical insight
This definition provides a way to associate a projective line with a vector. The `mk_dir` function likely converts a vector into some representation of direction. Applying `(||)` likely provides a line parallel direction, ensuring proper projective representation regardless of the exact vector provided is chosen. Finally `mk_line` turns a parallel direction into the line itself. This is useful for relating vector spaces and projective geometry.

### Dependencies
- Definition: `mk_line`
- Definition: `(||)`
- Definition: `mk_dir`


---

## projp

### Name of formal statement
`projp`

### Type of the formal statement
`new_definition`

### Formal Content
```ocaml
let projp = new_definition
 `projp x = mk_point(projl x)`;;
```

### Informal statement
The function `projp` is defined such that, for any `x`, `projp x` is equal to the point constructed from the line projection of `x` (i.e., `projl x`).

### Informal sketch
The definition introduces `projp` as a function. The right-hand side of the definition applies the function `projl` to `x` and then uses the result to construct a point using the function `mk_point`. Thus, the construction of `projp` is immediate from prior definitions of `projl` and `mk_point`.

### Mathematical insight
This definition combines the line projection (`projl`) with the point constructor (`mk_point`) to define a function that projects a given object onto a point in the line. This is useful for converting a line projection to a geometric point as might be needed in a specific geometrical argument.

### Dependencies
- Definition: `projl`
- Definition: `mk_point`


---

## PROJL_TOTAL

### Name of formal statement
PROJL_TOTAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PROJL_TOTAL = prove
 (`!l. ?x. ~(x = vec 0) /\ l = projl x`,
  GEN_TAC THEN
  SUBGOAL_THEN `?d. l = mk_line((||) d)` (CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[fst line_tybij; snd line_tybij];
    REWRITE_TAC[projl] THEN EXISTS_TAC `dest_dir d` THEN
    MESON_TAC[direction_tybij]]);;
```

### Informal statement
For all lines `l`, there exists a vector `x` such that `x` is not equal to the zero vector and `l` is equal to the projective line of `x` (i.e., `projl x`).

### Informal sketch
The proof demonstrates that every line can be represented as the projective line of some non-zero vector.
- The proof proceeds by first assuming an arbitrary line `l`.
- It then introduces a subgoal `?d. l = mk_line((||) d)`, aiming to show that `l` can be represented as `mk_line` of some direction vector `d`.
- The existence of such a direction vector `d` follows from `line_tybij` which maps lines to and from homogeneous coordinates. This justifies choosing such a `d` and substituting.
- The proof is then split into two branches, one uses `MESON_TAC with fst line_tybij; snd line_tybij` to justify the initial goal.
- The other branch expands `projl`, introduces a direction `dest_dir d` and then uses `direction_tybij` to show the equivalence holds between the line `l` and `projl x`.

### Mathematical insight
This theorem shows that the `projl` function is surjective onto the set of lines. That is, every line can be represented as the projective representation of some vector. The theorem demonstrates that the `projl` function effectively covers all possible lines.

### Dependencies
- `projl`
- `mk_line`
- `(||)`
- `line_tybij`
- `direction_tybij`
- `dest_dir`


---

## homol

### Name of formal statement
homol

### Type of the formal statement
New Specification

### Formal Content
```ocaml
let homol = new_specification ["homol"]
  (REWRITE_RULE[SKOLEM_THM] PROJL_TOTAL);;
```
### Informal statement
The function `homol` is specified such that for any type `:('a,'b)fun`, `homol` maps this type to `PROJL_TOTAL` after applying the rewrite rule `SKOLEM_THM`.

### Informal sketch
- The specification of `homol` is derived by applying the rewrite rule `SKOLEM_THM` to `PROJL_TOTAL`.
- The `new_specification` declaration introduces a new function `homol` and simultaneously proves its existence by providing a witness derived from `PROJL_TOTAL` and `SKOLEM_THM`.

### Mathematical insight
This specification likely involves Skolemization and the introduction of a total function `homol` based on the properties established by `PROJL_TOTAL`. The selection and application of `SKOLEM_THM` indicates the intent to make a partial function total or to eliminate existential quantifiers.

### Dependencies
- Theorems: `SKOLEM_THM`
- Constants: `PROJL_TOTAL`


---

## PROJP_TOTAL

### Name of formal statement
PROJP_TOTAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PROJP_TOTAL = prove
 (`!p. ?x. ~(x = vec 0) /\ p = projp x`,
  REWRITE_TAC[projp] THEN MESON_TAC[PROJL_TOTAL; point_tybij]);;
```

### Informal statement
For every `p`, there exists an `x` such that `x` is not equal to the zero vector (`vec 0`) and `p` is equal to the projection of `x` (`projp x`).

### Informal sketch
- The goal is to prove that the function `projp` is total.
- First, the definition of `projp` is expanded using `REWRITE_TAC[projp]`.
- Then, `MESON_TAC` is used with the theorems `PROJL_TOTAL` and `point_tybij` to automatically discharge the goal. The theorem `PROJL_TOTAL` probably asserts that for every vector `p`, there exists a line through the origin, call it `l`, such that `p` is on line `l`. The theorem `point_tybij` is used to prove that any point is a vector.

### Mathematical insight
The theorem `PROJP_TOTAL` states that the function `projp`, which maps a non-zero vector `x` to its corresponding point in projective space, is total. In other words, every point `p` in projective space is the image of some non-zero vector `x` under the `projp` mapping. This establishes that the `projp` mapping covers the entire projective space, meaning no point is "missed" by the mapping.

### Dependencies
- Definitions: `projp`, `vec`
- Theorems: `PROJL_TOTAL`, `point_tybij`


---

## homop_def

### Name of formal statement
homop_def

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let homop_def = new_definition
 `homop p = homol(dest_point p)`;;
```

### Informal statement
The homography `homop` of a point `p` is defined to be the homography `homol` of the destination point `dest_point` of `p`.

### Informal sketch
- The definition introduces `homop` as a shorthand for applying `homol` to the result of applying `dest_point` to the input `p`.
- The definition directly uses the definition of `homol` and `dest_point`, applying them in sequence.

### Mathematical insight
The definition expresses a composition relationship between the functions `homol` and `dest_point`. It is likely part of a larger theory where the destination point of `p` possesses some special significance when transformed by `homol`.

### Dependencies
- `dest_point`
- `homol`


---

## homop

### Name of formal statement
homop

### Type of the formal statement
theorem

### Formal Content
```ocaml
let homop = prove
 (`!p. ~(homop p = vec 0) /\ p = projp(homop p)`,
  GEN_TAC THEN REWRITE_TAC[homop_def; projp; MESON[point_tybij]
   `p = mk_point l <=> dest_point p = l`] THEN
  MATCH_ACCEPT_TAC homol);;
```

### Informal statement
For all `p`, it is the case that `homop p` is not equal to `vec 0`, and `p` is equal to `projp(homop p)`.

### Informal sketch
The proof proceeds as follows:
- Expand the definition of `homop` using `homop_def`.
- Simplify using the definition of `projp`.
- Use `MESON` with the theorem `point_tybij` and the equivalence `p = mk_point l <=> dest_point p = l` to complete the proof.
- Accept the goal by matching with `homol`.

### Mathematical insight
The theorem essentially states that the map `homop` maps a point `p` to a vector in such a way that `p` is the projective point represented by `homop p`, and that `homop p` is not the zero vector.
This relates points to vectors and connects the `homop` function with the `projp` function, stating that `homop` is an injection modulo scalar multiplication and that `homop` maps points to non-zero vectors.

### Dependencies
- Definitions: `homop_def`, `projp`
- Theorems: `point_tybij`
- Terms: `p = mk_point l <=> dest_point p = l`
- Axioms: `homol`


---

## parallel

### Name of formal statement
parallel

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let parallel = new_definition
 `parallel x y <=> x cross y = vec 0`;;
```

### Informal statement
The vectors `x` and `y` are defined to be parallel if and only if their cross product is equal to the zero vector `vec 0`.

### Informal sketch
The definition introduces the concept of parallelism between two vectors in terms of their cross product. The core idea is that two vectors are parallel if their cross product yields the zero vector. There is no proof, as this is a definition.

### Mathematical insight
This definition accurately captures the geometric notion of parallelism. The cross product of two parallel vectors is zero because the area of the parallelogram they span is zero, since parallel vectors lie on the same line (or one is the zero vector). This definition is essential for reasoning about the geometric relationships between vectors in a formal setting and will likely be used in subsequent theorems and proofs related to linear algebra and geometry.

### Dependencies
*   Definitions: `cross`, `vec`


---

## ON_HOMOL

### Name of formal statement
ON_HOMOL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ON_HOMOL = prove
 (`!p l. p on l <=> orthogonal (homop p) (homol l)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [homop; homol] THEN
  REWRITE_TAC[on; projp; projl; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[GSYM perpl_th; perpdir] THEN BINOP_TAC THEN
  MESON_TAC[homol; homop; direction_tybij]);;
```

### Informal statement
For all points `p` and lines `l`, `p` lies on `l` if and only if the homogeneous representation of `p` (`homop p`) is orthogonal to the homogeneous representation of `l` (`homol l`).

### Informal sketch
The proof proceeds as follows:
- Introduce the universally quantified variables `p` (a point) and `l` (a line).
- Rewrite using definitions of `homop` and `homol`.
- Rewrite using the definitions of `on`, `projp`, `projl`, and `point_tybij`.
- Rewrite using `perpl_th` (after applying `GSYM` to reverse the direction of the implication) and `perpdir`.
- Apply `BINOP_TAC`.
- Apply `MESON_TAC` using the theorems `homol`, `homop`, and `direction_tybij`.

### Mathematical insight
This theorem connects the geometric notion of a point lying on a line with the algebraic notion of orthogonality in homogeneous coordinates. It establishes that `p on l` is equivalent to `homop p` being orthogonal to `homol l`. This provides a powerful way to reason about incidence geometrically via linear algebra.

### Dependencies
- Definitions: `homop`, `homol`, `on`, `projp`, `projl`, `perpdir`, `orthogonal`, `point_tybij`,
- Theorems: `perpl_th`, `homol`, `homop`, `direction_tybij`


---

## EQ_HOMOL

### Name of formal statement
EQ_HOMOL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EQ_HOMOL = prove
 (`!l l'. l = l' <=> parallel (homol l) (homol l')`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [homol] THEN
  REWRITE_TAC[projl; MESON[fst line_tybij; snd line_tybij]
   `mk_line((||) l) = mk_line((||) l') <=> (||) l = (||) l'`] THEN
  REWRITE_TAC[PARDIR_EQUIV] THEN REWRITE_TAC[pardir; parallel] THEN
  MESON_TAC[homol; direction_tybij]);;
```
### Informal statement
For all lines `l` and `l'`, `l` is equal to `l'` if and only if the line at infinity `homol l` is parallel to the line at infinity `homol l'`.

### Informal sketch
The proof proceeds as follows:
- Introduce universal quantifiers for `l` and `l'`.
- Rewrite using the definition of `homol`, expanding `homol l` and `homol l'`.
- Use the properties of `projl` and the bijectivity lemmas `fst line_tybij` and `snd line_tybij` to rewrite the equality of lines in terms of equality of their projections `(||) l = (||) l'`.
- Rewrite using `PARDIR_EQUIV` to relate parallelism to having the same direction.
- Rewrite using definitions of `pardir` and `parallel`.
- Apply `MESON_TAC` using `homol` and `direction_tybij` for equational reasoning to complete the proof.

### Mathematical insight
This theorem establishes a fundamental link between the equality of lines in the original plane and the parallelism of their corresponding lines at infinity (homologous lines). It highlights how the concept of lines at infinity, introduced by the `homol` function, captures the notion of direction and equality in the Euclidean plane.

### Dependencies
- Definitions: `homol`, `projl`, `parallel`, `pardir`
- Theorems/Lemmas: `fst line_tybij`, `snd line_tybij`, `PARDIR_EQUIV`, `direction_tybij`


---

## EQ_HOMOP

### Name of formal statement
EQ_HOMOP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EQ_HOMOP = prove
 (`!p p'. p = p' <=> parallel (homop p) (homop p')`,
  REWRITE_TAC[homop_def; GSYM EQ_HOMOL] THEN
  MESON_TAC[point_tybij]);;
```
### Informal statement
For all `p` and `p'`, `p` is equal to `p'` if and only if `parallel (homop p) (homop p')`.

### Informal sketch
The proof proceeds as follows:
- The definition of `homop` is rewritten using `homop_def`.
- The equality `EQ_HOMOL` is rewritten in the opposite direction using `GSYM EQ_HOMOL`.
- The resulting goal is proven using the MESON proof tool, with `point_tybij` as the relevant axiom.

### Mathematical insight
The theorem `EQ_HOMOP` states that two points `p` and `p'` are equal if and only if their homogeneous representation `homop p` and `homop p'` are parallel. This result provides a connection between equality of points and parallelism of their homogeneous representations.

### Dependencies
- Definitions: `homop_def`
- Theorems: `EQ_HOMOL`, `point_tybij`


---

## PARALLEL_PROJL_HOMOL

### Name of formal statement
PARALLEL_PROJL_HOMOL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PARALLEL_PROJL_HOMOL = prove
 (`!x. parallel x (homol(projl x))`,
  GEN_TAC THEN REWRITE_TAC[parallel] THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[CROSS_0] THEN MP_TAC(ISPEC `projl x` homol) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [projl] THEN
  DISCH_THEN(MP_TAC o AP_TERM `dest_line`) THEN
  REWRITE_TAC[MESON[fst line_tybij; snd line_tybij]
   `dest_line(mk_line((||) l)) = (||) l`] THEN
  REWRITE_TAC[PARDIR_EQUIV] THEN REWRITE_TAC[pardir] THEN
  ASM_MESON_TAC[direction_tybij]);;
```
### Informal statement
For all `x`, `parallel x (homol(projl x))` holds.

### Informal sketch
The proof proceeds as follows:
- Start by generalizing the variable `x`.
- Rewrite using the definition of `parallel`.
- Perform case analysis on whether `x` is equal to the zero vector `vec 0`.
- In the case where `x` is the zero vector, rewrite using the theorem `CROSS_0`. Apply the specialization of the theorem `homol` to `projl x`, then discharge the antecedent of the implication using assumptions derived from the case split(conjuncts) and apply the definition of `projl` to the goal.
- Apply a theorem stating equivalence between `dest_line(mk_line((||) l))` and `(||) l` after partially applying `dest_line` to the `mk_line` constructor.
- Rewrite using the definition of `PARDIR_EQUIV` and then rewrite using definition of `pardir`.
- Finally apply a MESON using `direction_tybij` to complete the proof.

### Mathematical insight
This theorem shows that the projection of a line in homogeneous coordinates, after being transformed by `homol`, is parallel to the original direction vector. This signifies a welldefinedness property of the homogeneous coordinates map. The theorem bridges the gap between lines represented by homogeneous coordinates and their corresponding direction vectors in 3D space, confirming that the homogeneous transformation preserves the directional information.

### Dependencies
- Definitions: `parallel`, `homol`, `projl`, `pardir`, `dest_line`, `mk_line`, `direction_tybij`, `line_tybij`, `PARDIR_EQUIV`
- Theorems: `CROSS_0`, `MESON[fst line_tybij; snd line_tybij] `


---

## PARALLEL_PROJP_HOMOP

### Name of formal statement
PARALLEL_PROJP_HOMOP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PARALLEL_PROJP_HOMOP = prove
 (`!x. parallel x (homop(projp x))`,
  REWRITE_TAC[homop_def; projp; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[PARALLEL_PROJL_HOMOL]);;
```

### Informal statement
For all `x`, `parallel x (homop(projp x))` holds, which means for any `x`, the direction of `x` is parallel to the direction of the homogeneous representation applied to the projection of `x`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the goal using the definitions of `homop`, `projp`, and rewrite with `point_tybij`. This expands the definitions and applies a type bijection.
- Then, rewrite with the theorem `PARALLEL_PROJL_HOMOL`. This completes the proof by relating the homogeneous representation to the direction of the line.

### Mathematical insight
This theorem establishes that the direction of a point `x` is parallel to the direction of the homogeneous representation applied to the projection of `x`. It essentially connects the geometric notion of parallelism to the algebraic representation using homogeneous coordinates and projections. This is important for reasoning about geometric relationships in a formal setting by relating points to lines via their homogeneous representations and projections.

### Dependencies
- Definitions: `homop_def`, `projp`
- Theorems: `point_tybij`, `PARALLEL_PROJL_HOMOL`


---

## PARALLEL_PROJP_HOMOP_EXPLICIT

### Name of formal statement
PARALLEL_PROJP_HOMOP_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PARALLEL_PROJP_HOMOP_EXPLICIT = prove
 (`!x. ~(x = vec 0) ==> ?a. ~(a = &0) /\ homop(projp x) = a % x`,
  MP_TAC PARALLEL_PROJP_HOMOP THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[parallel; CROSS_EQ_0; COLLINEAR_LEMMA] THEN
  GEN_TAC THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[homop] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `c:real` THEN ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[homop; VECTOR_MUL_LZERO]);;
```

### Informal statement
For all vectors `x` in real 3-dimensional space, if `x` is not equal to the zero vector, then there exists a real number `a` such that `a` is not equal to 0 and the homogeneous part of the projection `projp x` is equal to `a % x` (scalar multiplication of `a` and `x`).

### Informal sketch
The proof proceeds as follows:
- Assume `x` is not the zero vector.
- Apply `PARALLEL_PROJP_HOMOP` theorem.
- Rewrite using `parallel`, `CROSS_EQ_0`, and `COLLINEAR_LEMMA`.
- Generalize to introduce the variable `a`.
- Perform case split on `x = vec 0`; the false case is discharged by assumption.
- Rewrite using the definition of `homop`.
- Apply the existence introduction rule `MONO_EXISTS`.
- Introduce a variable `c:real` to represent the scalar `a`.
- Perform case split on `c = &0`.
- If `c = &0`, rewrite using the definition of `homop` and `VECTOR_MUL_LZERO` to show `homop(projp x)` equals the zero vector, contradicting the assumption that `x` is not the zero vector. Therefore, `c` must not be zero.

### Mathematical insight
This theorem establishes that if `x` is a non-zero vector, then the homogeneous part of the projection `projp x` is equal to some scalar multiple of `x`.

### Dependencies
- Definitions: `parallel`, `projp`, `homop`
- Theorems: `CROSS_EQ_0`, `COLLINEAR_LEMMA`, `PARALLEL_PROJP_HOMOP`, `VECTOR_MUL_LZERO`


---

## bracket

### Name of formal statement
bracket

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let bracket = define
 `bracket[a;b;c] = det(vector[homop a;homop b;homop c])`;;
```
### Informal statement
The `bracket` of three objects `a`, `b`, and `c` is defined as the determinant of the matrix whose columns are the homogeneous representations `homop a`, `homop b`, and `homop c` of the objects `a`, `b`, and `c` respectively.

### Informal sketch
The definition introduces the concept of a bracket using the determinant (`det`) of a matrix formed by the homogeneous representations (`homop`) of three objects. The definition is direct: Compute the homogeneous representation of each object, arrange them as columns in a matrix, and compute the determinant of that matrix. There is no proof involved since this is a definition.

### Mathematical insight
This definition introduces the notion of a bracket, which is central to projective geometry and the study of incidence relations. The bracket represents a fundamental invariant that determines collinearity or coplanarity of points, depending on the dimension considered. Using homogeneous coordinates and determinants provides a powerful algebraic tool to represent projective geometric concepts.

### Dependencies
- Definition: `det`
- Definition: `vector`
- Definition: `homop`


---

## COLLINEAR

### Name of formal statement
COLLINEAR

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let COLLINEAR = new_definition
 `COLLINEAR s <=> ?l. !p. p IN s ==> p on l`;;
```
### Informal statement
A set of points `s` is `COLLINEAR` if and only if there exists a line `l` such that for all points `p`, if `p` is in `s`, then `p` lies on `l`.

### Informal sketch
The definition introduces the concept of collinearity for a set of points. It states that a set of points is collinear if there exists a line on which all the points in the set lie. There is no proof associated with a definition, so there are no logical stages to describe here. The definition itself embodies all the necessary mathematical content.

### Mathematical insight
This definition formalizes the intuitive notion of points lying on the same line. It's a fundamental concept in geometry and is used as a building block for more complex geometric theorems and constructions.

### Dependencies
None

### Porting notes (optional)
The existential quantifier over lines combined with the universal quantifier over points might require careful attention when porting to proof assistants with different automation levels. Ensure the target system can effectively handle the interplay of these quantifiers in geometric contexts.


---

## COLLINEAR_SINGLETON

### Name of formal statement
COLLINEAR_SINGLETON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLLINEAR_SINGLETON = prove
 (`!a. COLLINEAR {a}`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[AXIOM_1; AXIOM_3]);;
```

### Informal statement
For any point `a`, the set containing only `a` (i.e., `{a}`) is collinear.

### Informal sketch
The proof proceeds as follows:
- Reduce `COLLINEAR {a}` using the definition of `COLLINEAR` (`COLLINEAR s` is `!x y z. x IN s /\ y IN s /\ z IN s ==> EXISTS a b. &a * VECT(x,y) + &b * VECT(x,z) = ZERO`).
- Simplify the resulting expression `!x y z. x IN {a} /\ y IN {a} /\ z IN {a} ==> EXISTS a b. &a * VECT(x,y) + &b * VECT(x,z) = ZERO` by expanding the `FORALL_IN_INSERT` (repeatedly) and simplifying with `NOT_IN_EMPTY`. This transforms the universally quantified variables (`x`, `y`, `z`) that must be in the singleton set `{a}` and simplifies the implication with the definition of `IN` for sets.
- Complete the proof using `MESON_TAC` with `AXIOM_1` (vector space axiom stating: `VECT(x,x) = ZERO`) and `AXIOM_3` (vector space axiom stating: `!t:real. VECT x y = ZERO ==> VECT x (t %: y) = ZERO`).

### Mathematical insight
This theorem states that any singleton set of points is collinear. This is because collinearity requires that for any three points in the set, there exists a linear combination of the vectors formed by those points that equals zero. In the case of a singleton set, all three points `x`, `y`, and `z` must be the same point `a`. Therefore, `VECT(x, y)` and `VECT(x, z)` become `VECT(a, a)`, which is `ZERO`, and `&1 * ZERO + &1 * ZERO = ZERO`.

### Dependencies
- Definitions: `COLLINEAR`
- Theorems: `FORALL_IN_INSERT`, `NOT_IN_EMPTY`, `AXIOM_1`, `AXIOM_3`


---

## COLLINEAR_PAIR

### Name of formal statement
COLLINEAR_PAIR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLLINEAR_PAIR = prove
 (`!a b. COLLINEAR{a,b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:point = b` THEN
  ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SINGLETON] THEN
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[AXIOM_1]);;
```
### Informal statement
For all points `a` and `b`, the set `{a, b}` is collinear.

### Informal sketch
The proof proceeds by considering two cases:
- Case 1: `a` = `b`. In this case, we use the theorem `COLLINEAR_SINGLETON` which states that any singleton set containing only `a` is collinear, as well as `INSERT_AC`(Insert Associativity and Commutativity) to show sets `{a, a}` and `{a}` are equivalent.
- Case 2: `a` is not equal to `b`. We expand the definition of `COLLINEAR{a, b}` using `COLLINEAR`, apply `FORALL_IN_INSERT` and `NOT_IN_EMPTY`, which reduces the goal to showing that `COLLINEAR{a}` and `COLLINEAR{b}`, which holds by `AXIOM_1` (Every singleton is collinear), and `ASM_MESON_TAC` completes the proof.

### Mathematical insight
This theorem states that any pair of points form a collinear set. It's a foundational result in geometry, ensuring that the basic notion of collinearity is well-behaved.

### Dependencies
- Axioms: `AXIOM_1`
- Theorems: `COLLINEAR_SINGLETON`
- Definitions: `COLLINEAR`
- Other: `INSERT_AC`, `FORALL_IN_INSERT`, `NOT_IN_EMPTY`


---

## COLLINEAR_TRIPLE

### Name of formal statement
COLLINEAR_TRIPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLLINEAR_TRIPLE = prove
 (`!a b c. COLLINEAR{a,b,c} <=> ?l. a on l /\ b on l /\ c on l`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY]);;
```
### Informal statement
For all points `a`, `b`, and `c`, `COLLINEAR{a,b,c}` is true if and only if there exists a line `l` such that `a` lies on `l`, `b` lies on `l`, and `c` lies on `l`.

### Informal sketch
The proof establishes the equivalence between the predicate `COLLINEAR{a,b,c}` and the existence of a line containing the points `a`, `b`, and `c`.

*   The proof starts by rewriting the definition of `COLLINEAR`.
*   It uses `FORALL_IN_INSERT` which likely deals with universal quantification within set membership, probably generated since `COLLINEAR` involves set based notions.
*   Finally, `NOT_IN_EMPTY` likely eliminates cases based on points not belonging to the empty set, likely to deal with edge cases within the sets definitions.

### Mathematical insight
This theorem provides a fundamental characterization of collinearity: three points are collinear if and only if there exists a line that passes through all three points. This is a standard definition of collinearity in geometry.

### Dependencies
- Definitions: `COLLINEAR`
- Theorems: `FORALL_IN_INSERT`, `NOT_IN_EMPTY`


---

## COLLINEAR_BRACKET

### Name of formal statement
COLLINEAR_BRACKET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLLINEAR_BRACKET = prove
 (`!p1 p2 p3. COLLINEAR {p1,p2,p3} <=> bracket[p1;p2;p3] = &0`,
  let lemma = prove
   (`!a b c x y.
          x cross y = vec 0 /\ ~(x = vec 0) /\
          orthogonal a x /\ orthogonal b x /\ orthogonal c x
          ==> orthogonal a y /\ orthogonal b y /\ orthogonal c y`,
    REWRITE_TAC[orthogonal] THEN VEC3_TAC) in
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[COLLINEAR_TRIPLE; bracket; ON_HOMOL; LEFT_IMP_EXISTS_THM] THEN
    MP_TAC homol THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[DET_3; orthogonal; DOT_3; VECTOR_3; CART_EQ;
              DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
    CONV_TAC REAL_RING;
    ASM_CASES_TAC `p1:point = p2` THENL
     [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_PAIR]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[parallel; COLLINEAR_TRIPLE; bracket; EQ_HOMOP; ON_HOMOL] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `mk_line((||) (mk_dir(homop p1 cross homop p2)))` THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `homop p1 cross homop p2` THEN
    ASM_REWRITE_TAC[ORTHOGONAL_CROSS] THEN
    REWRITE_TAC[orthogonal] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    ONCE_REWRITE_TAC[CROSS_TRIPLE] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    ASM_REWRITE_TAC[DOT_CROSS_DET] THEN
    REWRITE_TAC[GSYM projl; GSYM parallel; PARALLEL_PROJL_HOMOL]]);;
```
### Informal statement
For all points `p1`, `p2`, and `p3`, the set `{p1, p2, p3}` is collinear if and only if `bracket[p1; p2; p3]` equals 0.

### Informal sketch
The proof proceeds as follows:
- First, prove a lemma stating that if vectors `x` and `y` are orthogonal to vectors `a`, `b`, and `c`, and `x` is not the zero vector, then if `x` cross `y` is the zero vector, it implies `y` is orthogonal to `a`, `b`, and `c`. This lemma uses `REWRITE_TAC[orthogonal]` and `VEC3_TAC`.
- Start by rewriting `COLLINEAR {p1, p2, p3}` using `COLLINEAR_TRIPLE`, `bracket`, `ON_HOMOL`, and `LEFT_IMP_EXISTS_THM`. This reduces the goal to proving that points are collinear if and only if their homogeneous representations satisfy certain conditions related to the bracket.
- Then, apply `homol` and use monotonicity to further reduce the goal.
- Introduce the variables `p1`, `p2`, and `p3`, and break the equivalence into two implications.
- Rewrite the involved terms based on definitions of `DET_3`, `orthogonal`, `DOT_3`, `VECTOR_3`, `CART_EQ`, `DIMINDEX_3`, `FORALL_3`, `VEC_COMPONENT` and simplify using real ring properties.
- Perform case analysis on `p1 = p2`. If `p1 = p2`, the points are collinear by `COLLINEAR_PAIR`.
- If `p1 != p2`, rewrite using definitions of `parallel`, `COLLINEAR_TRIPLE`, `bracket`, `EQ_HOMOP`, and `ON_HOMOL`, and strip the implications.
- Then, show the existence of a line defined by the cross product of the homogeneous representations of `p1` and `p2`.
- Apply the previously proved lemma with the appropriate instantiation.
- Use existing theorems to simplify the goal related to orthogonality, parallelism, and the relationship between the cross product and orthogonality. Theorems `ORTHOGONAL_CROSS`, `DOT_SYM`, `CROSS_TRIPLE`, `DOT_CROSS_DET`, `GSYM projl`, `GSYM parallel`, `PARALLEL_PROJL_HOMOL` are used for this purpose.

### Mathematical insight
This theorem provides a fundamental connection between the geometric notion of collinearity and the algebraic concept of the `bracket` function (determinant). It states that three points are collinear precisely when the bracket of these points, which can be interpreted as twice the signed area of the triangle formed by the points, vanishes. The homogeneous coordinates and the cross product are used to determine a line that passes through the three points.

### Dependencies
- `COLLINEAR_TRIPLE`
- `bracket`
- `ON_HOMOL`
- `LEFT_IMP_EXISTS_THM`
- `DET_3`
- `orthogonal`
- `DOT_3`
- `VECTOR_3`
- `CART_EQ`
- `DIMINDEX_3`
- `FORALL_3`
- `VEC_COMPONENT`
- `COLLINEAR_PAIR`
- `parallel`
- `EQ_HOMOP`
- `ORTHOGONAL_CROSS`
- `DOT_SYM`
- `CROSS_TRIPLE`
- `DOT_CROSS_DET`
- `projl`
- `PARALLEL_PROJL_HOMOL`

### Porting notes (optional)
- The definition `bracket` and `homol` are crucial and need to be ported carefully. It would be useful to note the algebraic and geometric meaning of `bracket` when porting the definition.
- Handling of homogeneous coordinates and the cross product of vectors may vary across different proof assistants. Ensure consistency in definitions during porting.
- The proof relies on a series of rewrites with specific definitions and algebraic simplifications. Pay close attention to ensuring that the corresponding theorems are available or can be derived in the target proof assistant.


---

## homogeneous_conic

### Name of formal statement
homogeneous_conic

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let homogeneous_conic = new_definition
 `homogeneous_conic con <=>
    ?a b c d e f.
       ~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0) /\
       con = {x:real^3 | a * x$1 pow 2 + b * x$2 pow 2 + c * x$3 pow 2 +
                         d * x$1 * x$2 + e * x$1 * x$3 + f * x$2 * x$3 = &0}`;;
```
### Informal statement
A `homogeneous_conic` `con` is defined as a set of points in real 3-dimensional space such that there exist real numbers `a`, `b`, `c`, `d`, `e`, and `f`, not all zero, such that for any point `x` in `real^3`, `x` belongs to `con` if and only if `a * (x$1)^2 + b * (x$2)^2 + c * (x$3)^2 + d * (x$1) * (x$2) + e * (x$1) * (x$3) + f * (x$2) * (x$3) = 0`.

### Informal sketch
- The definition introduces the concept of a homogeneous conic in 3D real space.
- It asserts the existence of coefficients `a`, `b`, `c`, `d`, `e`, and `f`, not all zero, such that the defining quadratic equation holds for points belonging to the conic.
- The condition `~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0)` ensures that the conic is not trivially defined by all coefficients being zero.

### Mathematical insight
This definition formalizes the notion of a conic section in a homogeneous coordinate system. The equation `a * x$1 pow 2 + b * x$2 pow 2 + c * x$3 pow 2 + d * x$1 * x$2 + e * x$1 * x$3 + f * x$2 * x$3 = &0` represents a general quadratic form, and the constraint that not all coefficients are zero ensures that we have a non-trivial conic. This representation is useful for projective geometry, where points at infinity are represented as finite points in the homogeneous coordinate system.

### Dependencies
None.


---

## projective_conic

### Name of formal statement
projective_conic

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let projective_conic = new_definition
 `projective_conic con <=>
        ?c. homogeneous_conic c /\ con = {p | (homop p) IN c}`;;
```
### Informal statement
For any `con`, `projective_conic con` is true if and only if there exists a `c` such that `c` is a `homogeneous_conic` and `con` is equal to the set of all `p` such that `(homop p)` is in `c`.

### Informal sketch
The definition `projective_conic` defines what it means for a set of points `con` to be a projective conic. It states that `con` must be the set of points whose homogeneous versions `homop p` are in a homogeneous conic `c`.
- The definition introduces an existential quantifier `?c` that binds homogeneous conics to `c`.
- The `homogeneous_conic c` predicate asserts that `c` represents a conic in homogeneous coordinates.
- The definition connects projective points `p` to homogeneous space via the `homop` function.
- Finally, the definition states `con` is the set of projective points such that their homogeneous representation lie in `c`

### Mathematical insight
This definition provides a way to represent projective conics by relating them to homogeneous conics. The `homop` function maps a projective point to its homogeneous representation which is used to determine if projective points lie on the conic `c`. This definition allows the use of homogeneous coordinates, which simplifies many calculations and proofs related to conics.

### Dependencies
- Definitions: `homogeneous_conic`, `homop`


---

## HOMOGENEOUS_CONIC_BRACKET

### Name of formal statement
HOMOGENEOUS_CONIC_BRACKET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOMOGENEOUS_CONIC_BRACKET = prove
 (`!con x1 x2 x3 x4 x5 x6.
        homogeneous_conic con /\
        x1 IN con /\ x2 IN con /\ x3 IN con /\
        x4 IN con /\ x5 IN con /\ x6 IN con
        ==> det(vector[x6;x1;x4]) * det(vector[x6;x2;x3]) *
            det(vector[x5;x1;x3]) * det(vector[x5;x2;x4]) =
            det(vector[x6;x1;x3]) * det(vector[x6;x2;x4]) *
            det(vector[x5;x1;x4]) * det(vector[x5;x2;x3])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homogeneous_conic; EXTENSION] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; DET_3; VECTOR_3] THEN
  CONV_TAC REAL_RING);;
```
### Informal statement
For all `con`, `x1`, `x2`, `x3`, `x4`, `x5`, and `x6`, if `con` is a homogeneous conic, and `x1`, `x2`, `x3`, `x4`, `x5`, and `x6` are all in `con`, then
`det(vector[x6;x1;x4]) * det(vector[x6;x2;x3]) * det(vector[x5;x1;x3]) * det(vector[x5;x2;x4])` = `det(vector[x6;x1;x3]) * det(vector[x6;x2;x4]) * det(vector[x5;x1;x4]) * det(vector[x5;x2;x3])`.

### Informal sketch
The proof proceeds as follows:
- Start by generalizing the goal using `REPEAT GEN_TAC`.
- Rewrite using the definition of `homogeneous_conic` and `EXTENSION`.
- Split the implication using `IMP_CONJ`.
- Eliminate the existential quantifier on the left side of the implication using `LEFT_IMP_EXISTS_THM`.
- Generalize again and discharge assumptions using `REPEAT GEN_TAC` and `DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)`. This makes the assumptions about the conic and the points being on the conic available.
- Rewrite using assumptions and the definitions of `IN_ELIM_THM`, `DET_3`, and `VECTOR_3` to expand the determinants and vectors.
- Use `REAL_RING` to prove the equality.

### Mathematical insight
This theorem states a property of six points on a homogeneous conic. It expresses a relationship between the determinants of vectors formed by these points. The equality of the two products of determinants indicates a cross-ratio type relationship.

### Dependencies
- Definitions:
  - `homogeneous_conic`
  - `EXTENSION`
- Theorems/Lemmas:
  - `IMP_CONJ`
  - `LEFT_IMP_EXISTS_THM`
  - `IN_ELIM_THM`
  - `DET_3`
  - `VECTOR_3`


---

## PROJECTIVE_CONIC_BRACKET

### Name of formal statement
PROJECTIVE_CONIC_BRACKET

### Type of the formal statement
theorem

### Formal Content
```ocaml
!con p1 p2 p3 p4 p5 p6.
        projective_conic con /\
        p1 IN con /\ p2 IN con /\ p3 IN con /\
        p4 IN con /\ p5 IN con /\ p6 IN con
        ==> bracket[p6;p1;p4] * bracket[p6;p2;p3] *
            bracket[p5;p1;p3] * bracket[p5;p2;p4] =
            bracket[p6;p1;p3] * bracket[p6;p2;p4] *
            bracket[p5;p1;p4] * bracket[p5;p2;p3]
```

### Informal statement
For all conics `con` and points `p1`, `p2`, `p3`, `p4`, `p5`, `p6`, if `con` is a projective conic and `p1`, `p2`, `p3`,  `p4`, `p5`, and `p6` all lie on `con`, then the following equation holds:
`bracket[p6;p1;p4] * bracket[p6;p2;p3] * bracket[p5;p1;p3] * bracket[p5;p2;p4] = bracket[p6;p1;p3] * bracket[p6;p2;p4] * bracket[p5;p1;p4] * bracket[p5;p2;p3]`.

### Informal sketch
The proof proceeds as follows:
- First, universally quantify over all variables.
- Rewrite using the definitions of `bracket` and `projective_conic`.
- Discharge the assumptions `projective_conic con`, `p1 IN con`, `p2 IN con`, `p3 IN con`, `p4 IN con`, `p5 IN con`, and `p6 IN con`.
- Rewrite using `IN_ELIM_THM`.
- Apply `HOMOGENEOUS_CONIC_BRACKET` after matching.
- Finally, use an `ASM_MESON_TAC` to complete the proof.

### Mathematical insight
This theorem represents a property of points lying on a projective conic, relating the bracket operation (which likely calculates some geometric invariant related to triples of points) evaluated on different combinations of these points. The equation itself is a statement of equality between two products of bracket terms, asserting that no matter which six points are chosen on a projective conic, this relationship will always be true. The underlying geometric meaning of this theorem is that projective conics satisfy certain cross-ratio properties.

### Dependencies
Definitions:
- `bracket`
- `projective_conic`

Theorems:
- `IN_ELIM_THM`
- `HOMOGENEOUS_CONIC_BRACKET`


---

## PASCAL_DIRECT

### Name of formal statement
PASCAL_DIRECT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PASCAL_DIRECT = prove
 (`!con x1 x2 x3 x4 x5 x6 x6 x8 x9.
        ~COLLINEAR {x2,x5,x7} /\
        ~COLLINEAR {x1,x2,x5} /\
        ~COLLINEAR {x1,x3,x6} /\
        ~COLLINEAR {x2,x4,x6} /\
        ~COLLINEAR {x3,x4,x5} /\
        ~COLLINEAR {x1,x5,x7} /\
        ~COLLINEAR {x2,x5,x9} /\
        ~COLLINEAR {x1,x2,x6} /\
        ~COLLINEAR {x3,x6,x8} /\
        ~COLLINEAR {x2,x4,x5} /\
        ~COLLINEAR {x2,x4,x7} /\
        ~COLLINEAR {x2,x6,x8} /\
        ~COLLINEAR {x3,4,x6} /\
        ~COLLINEAR {x3,x5,x8} /\
        ~COLLINEAR {x1,x3,x5}
        ==> projective_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            COLLINEAR {x1,x9,x5} /\
            COLLINEAR {x1,x8,x6} /\
            COLLINEAR {x2,x9,x4} /\
            COLLINEAR {x2,x7,x6} /\
            COLLINEAR {x3,x8,x4} /\
            COLLINEAR {x3,x7,x5}
            ==> COLLINEAR {x7,x8,x9}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e /\ f /\ g /\ h ==> p <=>
                    a /\ b /\ c /\ d /\ e /\ f /\ g ==> h ==> p`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PROJECTIVE_CONIC_BRACKET) THEN
  REWRITE_TAC[COLLINEAR_BRACKET; IMP_IMP; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `!q. (p ==> q) /\ (q ==> r) ==> p ==> r`) THEN
  EXISTS_TAC
   `bracket[x1;x2;x5] * bracket[x1;x3;x6] *
    bracket[x2;x4;x6] * bracket[x3;x4;x5] =
    bracket[x1;x2;x6] * bracket[x1;x3;x5] *
    bracket[x2;x4;x5] * bracket[x3;x4;x6] /\
    bracket[x1;x5;x7] * bracket[x2;x5;x9] =
    --bracket[x1;x2;x5] * bracket[x5;x9;x7] /\
    bracket[x1;x2;x6] * bracket[x3;x6;x8] =
    bracket[x1;x3;x6] * bracket[x2;x6;x8] /\
    bracket[x2;x4;x5] * bracket[x2;x9;x7] =
    --bracket[x2;x4;x7] * bracket[x2;x5;x9] /\
    bracket[x2;x4;x7] * bracket[x2;x6;x8] =
    --bracket[x2;x4;x6] * bracket[x2;x8;x7] /\
    bracket[x3;x4;x6] * bracket[x3;x5;x8] =
    bracket[x3;x4;x5] * bracket[x3;x6;x8] /\
    bracket[x1;x3;x5] * bracket[x5;x8;x7] =
    --bracket[x1;x5;x7] * bracket[x3;5;x8]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(ONCE_REWRITE_TAC[IMP_IMP] THEN
         DISCH_THEN(MP_TAC o MATCH_MP (REAL_RING
          `a = b /\ x:real = y ==> a * x = b * y`))) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BRACKET]) THEN
  REWRITE_TAC[REAL_MUL_AC] THEN ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING);;
```

### Informal statement
For all `con`, `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x8`, and `x9`, if the points `{x2, x5, x7}`, `{x1, x2, x5}`, `{x1, x3, x6}`, `{x2, x4, x6}`, `{x3, x4, x5}`, `{x1, x5, x7}`, `{x2, x5, x9}`, `{x1, x2, x6}`, `{x3, x6, x8}`, `{x2, x4, x5}`, `{x2, x4, x7}`, `{x2, x6, x8}`, `{x3, x4, x6}`, `{x3, x5, x8}`, and `{x1, x3, x5}` are non-collinear, and `con` is a projective conic containing `x1`, `x2`, `x3`, `x4`, `x5`, and `x6`, and the points `{x1, x9, x5}`, `{x1, x8, x6}`, `{x2, x9, x4}`, `{x2, x7, x6}`, `{x3, x8, x4}`, and `{x3, x7, x5}` are collinear, then the points `{x7, x8, x9}` are collinear.

### Informal sketch
The proof proceeds by:
- Assuming the non-collinearity conditions and that `con` is a projective conic containing the six points.
- Applying `PROJECTIVE_CONIC_BRACKET` to replace the `projective_conic` hypothesis with a bracket expression.
- Using `COLLINEAR_BRACKET` to rewrite collinearity in terms of brackets and reorganizing the conjunction.
- Applying a tautology to prepare for introducing an existential.
- Introducing an existential quantifier with a specific formula based on cross-ratios of brackets, which represents the condition for the six points to lie on a conic. This formula is split into two parts by conjunction.
- Proving the two parts of the conjunction separately. The first part simplifies the bracket expression for the conic using determinant and vector operations and ring arithmetic. The second part involves manipulating the conditions arising from the collinearity assumptions, using properties of real multiplication (associativity, commutativity, negation). These are then combined to derive the collinearity of {x7, x8, x9}.
- Real ring arithmetic is used extensively to cancel out terms in bracket expressions using associativity, commutativity and other laws to arrive at the desired conclusion

### Mathematical insight
This theorem states Pascal's theorem for projective conics. Given six points on a projective conic, the intersections of opposite sides of the hexagon formed by the points are collinear. The non-collinearity conditions are necessary to avoid degenerate cases. The `bracket` notation represents Plücker coordinates or determinants of point coordinates, which provide an algebraic way to express geometric concepts like collinearity and conics.

### Dependencies
**Definitions:** 
- `COLLINEAR`
- `projective_conic`
- `bracket`
- `DET_3`
- `VECTOR_3`

**Theorems/Axioms:**
- `PROJECTIVE_CONIC_BRACKET`
- `TAUT`
- `IMP_IMP`
- `GSYM`
- `CONJ_ASSOC`
- `MONO_AND`
- `REAL_RING` (various ring axioms for real numbers)
- `REAL_MUL_ASSOC`
- `REAL_MUL_LNEG`
- `REAL_MUL_RNEG`
- `REAL_NEG_NEG`
- `REAL_MUL_AC`
- `REAL_EQ_MUL_LCANCEL`
- `REAL_MUL_SYM`

### Porting notes (optional)
- The `bracket` notation representing determinants may need to be defined separately, depending on the target proof assistant.
- The extensive use of real arithmetic and ring properties requires a well-developed real number theory in the target assistant.
- The proof relies heavily on rewriting and equational reasoning in rings, which may require custom tactics or automation support in other provers.
- Care should be paid to non-collinearity constraints in porting, as HOL Light's handling of them is explicit in the antecedent of the implication.


---

## PASCAL

### Name of formal statement
PASCAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PASCAL = prove
 (`!con x1 x2 x3 x4 x5 x6 x6 x8 x9.
        ~COLLINEAR {x1,x2,x4} /\
        ~COLLINEAR {x1,x2,x5} /\
        ~COLLINEAR {x1,x2,x6} /\
        ~COLLINEAR {x1,x3,x4} /\
        ~COLLINEAR {x1,x3,x5} /\
        ~COLLINEAR {x1,x3,x6} /\
        ~COLLINEAR {x2,x3,x4} /\
        ~COLLINEAR {x2,x3,x5} /\
        ~COLLINEAR {x2,x3,x6} /\
        ~COLLINEAR {x4,x5,x1} /\
        ~COLLINEAR {x4,x5,x2} /\
        ~COLLINEAR {x4,x5,x3} /\
        ~COLLINEAR {x4,x6,x1} /\
        ~COLLINEAR {x4,x6,x2} /\
        ~COLLINEAR {x4,x6,x3} /\
        ~COLLINEAR {x5,x6,x1} /\
        ~COLLINEAR {x5,x6,x2} /\
        ~COLLINEAR {x5,x6,x3}
        ==> projective_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            COLLINEAR {x1,x9,x5} /\
            COLLINEAR {x1,x8,x6} /\
            COLLINEAR {x2,x9,x4} /\
            COLLINEAR {x2,x7,x6} /\
            COLLINEAR {x3,x8,x4} /\
            COLLINEAR {x3,x7,x5}
            ==> COLLINEAR {x7,x8,x9}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(fun th ->
    MATCH_MP_TAC(TAUT `(~p ==> p) ==> p`) THEN DISCH_TAC THEN
    MP_TAC th THEN MATCH_MP_TAC PASCAL_DIRECT THEN
    ASSUME_TAC(funpow 7 CONJUNCT2 th)) THEN
  REPEAT CONJ_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[COLLINEAR_BRACKET; bracket; DET_3; VECTOR_3] THEN
  CONV_TAC REAL_RING);;
```
### Informal statement
For all `con`, `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x7`, `x8`, `x9`, if the points `x1`, `x2`, `x4` are not collinear, and the points `x1`, `x2`, `x5` are not collinear, and the points `x1`, `x2`, `x6` are not collinear, and the points `x1`, `x3`, `x4` are not collinear, and the points `x1`, `x3`, `x5` are not collinear, and the points `x1`, `x3`, `x6` are not collinear, and the points `x2`, `x3`, `x4` are not collinear, and the points `x2`, `x3`, `x5` are not collinear, and the points `x2`, `x3`, `x6` are not collinear, and the points `x4`, `x5`, `x1` are not collinear, and the points `x4`, `x5`, `x2` are not collinear, and the points `x4`, `x5`, `x3` are not collinear, and the points `x4`, `x6`, `x1` are not collinear, and the points `x4`, `x6`, `x2` are not collinear, and the points `x4`, `x6`, `x3` are not collinear, and the points `x5`, `x6`, `x1` are not collinear, and the points `x5`, `x6`, `x2` are not collinear, and the points `x5`, `x6`, `x3` are not collinear, then, if `con` is a projective conic, and `x1` is in `con`, and `x2` is in `con`, and `x3` is in `con`, and `x4` is in `con`, and `x5` is in `con`, and `x6` is in `con`, and `x1`, `x9`, `x5` are collinear, and `x1`, `x8`, `x6` are collinear, and `x2`, `x9`, `x4` are collinear, and `x2`, `x7`, `x6` are collinear, and `x3`, `x8`, `x4` are collinear, and `x3`, `x7`, `x5` are collinear, then `x7`, `x8`, `x9` are collinear.

### Informal sketch
The theorem proves Pascal's theorem for projective conics.

- The proof starts by discharging the assumptions of non-collinearity to the assumption list using `REPEAT GEN_TAC THEN DISCH_TAC`.
- It then rewrites the goal using `TAUT `(~p ==> p) ==> p`` to handle the negated clauses and discharges the hypothesis.
- The proof then applies the theorem `PASCAL_DIRECT`.
- After that it applies `CONJUNCT2` to extract the needed parts from `th` to apply the `ASSUME_TAC` tactic.
- The proof then splits the goal into smaller parts using `REPEAT CONJ_TAC`.
- It applies the assumptions to the goal within the `REPEAT(POP_ASSUM MP_TAC)` tactic.
- The proof then simplifies the collinearity conditions, using `COLLINEAR_BRACKET`, `bracket`, `DET_3`, and `VECTOR_3`.
- Finally, it uses the `REAL_RING` conversion to prove the resulting arithmetic goal.

### Mathematical insight
Pascal's theorem states that if six arbitrary points are chosen on a conic (which may be an ellipse, parabola or hyperbola) and joined in any order to form a hexagon, then the three pairs of opposite sides of the hexagon (extended if necessary) meet at three points which lie on a straight line. This theorem is a fundamental result in projective geometry, demonstrating a relationship between six points on a conic section and collinearity of intersection points of the hexagon formed by these points.

### Dependencies
Definitions:
- `COLLINEAR`
- `projective_conic`

Theorems:
- `PASCAL_DIRECT`
- `COLLINEAR_BRACKET`
- `bracket`
- `DET_3`
- `VECTOR_3`


---

## homogenize

### Name of formal statement
homogenize

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let homogenize = new_definition
 `(homogenize:real^2->real^3) x = vector[x$1; x$2; &1]`;;
```
### Informal statement
The function `homogenize`, mapping a two-dimensional real vector to a three-dimensional real vector, is defined such that for any two-dimensional real vector `x`, `homogenize x` is the three-dimensional real vector whose first component is the first component of `x`, whose second component is the second component of `x`, and whose third component is 1.

### Informal sketch
The definition of `homogenize` directly constructs the three-dimensional vector from the two-dimensional input vector `x` by appending `&1` as the third component. There is no proof involved; it is a definitional construction.

### Mathematical insight
The `homogenize` function maps a point in the affine plane (represented as a 2D vector) to its corresponding representation in the projective plane (represented as a 3D vector). This is achieved by adding a third coordinate, which is set to 1. This embedding allows affine transformations to be represented as linear transformations in the projective space, which is a fundamental technique in computer graphics and geometry.

### Dependencies
- vector
- real operations : `$1`, `$2`


---

## projectivize

### Name of formal statement
projectivize

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let projectivize = new_definition
 `projectivize = projp o homogenize`;;
```

### Informal statement
The function `projectivize` is defined to be the composition of the function `projp` with the function `homogenize`.

### Informal sketch
The definition introduces a new function `projectivize` and equates it to the functional composition of two existing functions, `projp` and `homogenize`.  There is no proof; it's definitional.

### Mathematical insight
The definition of `projectivize` likely aims to combine the effects of `homogenize` (embedding a vector into a higher-dimensional space) and `projp` (projecting a homogeneous vector into projective space). This combination likely creates a function that maps a vector to its corresponding point in projective space.

### Dependencies
- Definitions:
  - `projp`
  - `homogenize`


---

## HOMOGENIZE_NONZERO

### Name of formal statement
HOMOGENIZE_NONZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOMOGENIZE_NONZERO = prove
 (`!x. ~(homogenize x = vec 0)`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_3;
              homogenize] THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For all `x`, it is not the case that `homogenize x` is equal to the zero vector.

### Informal sketch
The proof proceeds by rewriting the statement using the definitions of `CART_EQ`, `DIMINDEX_3`, `FORALL_3`, `VEC_COMPONENT`, `VECTOR_3`, and `homogenize`, and then applying a real arithmetic tactic.
- The definition of `homogenize x` is used to expand the equality `homogenize x = vec 0` into an equality of vectors in 3-dimensional space.
- The components of the vectors are then compared using `VEC_COMPONENT`.
- The resulting arithmetic statement is then proved using `REAL_ARITH_TAC`.

### Mathematical insight
The theorem states that the `homogenize` function never maps a value to the zero vector. This is a crucial property when working with homogeneous coordinates, as the zero vector is often excluded from the space of homogeneous representations.

### Dependencies
- Definitions: `CART_EQ`, `DIMINDEX_3`, `FORALL_3`, `VEC_COMPONENT`, `VECTOR_3`, `homogenize`

### Porting notes (optional)
- Many proof assistants have built-in tactics for real arithmetic. The `REAL_ARITH_TAC` is a relatively powerful tactic that automatically solves a wide range of arithmetic goals.
- Some proof assistants may require explicit unrolling and simplification of the vector component comparisons rather than solving it automatically with an arithmetic tactic.


---

## affine_conic

### Name of formal statement
affine_conic

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let affine_conic = new_definition
 `affine_conic con <=>
    ?a b c d e f.
       ~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0) /\
       con = {x:real^2 | a * x$1 pow 2 + b * x$2 pow 2 + c * x$1 * x$2 +
                         d * x$1 + e * x$2 + f = &0}`;;
```

### Informal statement
The predicate `affine_conic con` holds if and only if there exist real numbers `a`, `b`, `c`, `d`, `e`, and `f`, not all zero, such that the set `con` is equal to the set of points `x` in the real plane satisfying the equation `a * (x$1)^2 + b * (x$2)^2 + c * (x$1) * (x$2) + d * (x$1) + e * (x$2) + f = 0`.

### Informal sketch
- The definition introduces a predicate `affine_conic` to characterize sets in the real plane that can be described as affine conics.
- The predicate `affine_conic con` is defined to be true if and only if there exist real coefficients `a, b, c, d, e, f`, not all zero, such that the set `con` is exactly the set of solutions `x` to the general quadratic equation `a * x$1^2 + b * x$2^2 + c * x$1 * x$2 + d * x$1 + e * x$2 + f = 0`.
- The condition that not all of `a`, `b`, `c`, `d`, `e`, and `f` are zero ensures that the equation is non-trivial.

### Mathematical insight
This definition formalizes the notion of an affine conic in the real plane. It provides a precise characterization of conic sections (ellipses, parabolas, hyperbolas, and degenerate cases) using a general quadratic equation. The condition that the coefficients are not all zero ensures that we are actually dealing with a quadratic equation and not a trivial case.

### Dependencies
None


---

## COLLINEAR_PROJECTIVIZE

### Name of formal statement
COLLINEAR_PROJECTIVIZE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLLINEAR_PROJECTIVIZE = prove
 (`!a b c. collinear{a,b,c} <=>
           COLLINEAR{projectivize a,projectivize b,projectivize c}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
  REWRITE_TAC[COLLINEAR_BRACKET; projectivize; o_THM; bracket] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `det(vector[homogenize a; homogenize b; homogenize c]) = &0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homogenize; DOT_2; VECTOR_SUB_COMPONENT; DET_3; VECTOR_3] THEN
    CONV_TAC REAL_RING;
    MAP_EVERY (MP_TAC o C SPEC PARALLEL_PROJP_HOMOP)
     [`homogenize a`; `homogenize b`; `homogenize c`] THEN
    MAP_EVERY (MP_TAC o C SPEC HOMOGENIZE_NONZERO)
     [`a:real^2`; `b:real^2`; `c:real^2`] THEN
    MAP_EVERY (MP_TAC o CONJUNCT1 o C SPEC homop)
     [`projp(homogenize a)`; `projp(homogenize b)`; `projp(homogenize c)`] THEN
    REWRITE_TAC[parallel; cross; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                DET_3; VEC_COMPONENT] THEN
    CONV_TAC REAL_RING]);;
```
### Informal statement
For all points `a`, `b`, and `c` in the real plane (real^2), `a`, `b`, and `c` are collinear if and only if `projectivize a`, `projectivize b`, and `projectivize c` are collinear.

### Informal sketch
The theorem proves that the collinearity of three points in the affine plane is equivalent to the collinearity of their images under the `projectivize` map in the projective plane. The proof proceeds as follows:

- Start by rewriting the definition `COLLINEAR_3` which defines collinearity in terms of the determinant of a matrix constructed from the given points.
- Apply the Cauchy-Schwarz equality using `DOT_CAUCHY_SCHWARZ_EQUAL`.
- Rewrite using `COLLINEAR_BRACKET`, `projectivize`, `o_THM`, and `bracket` to express collinearity in terms of bracket notation and the `projectivize` function.
- Use transitivity of equality.
- Introduce an existential quantifier stating that the determinant of the matrix formed by the homogenized vectors of `a`, `b`, and `c` is zero.
- Split the goal into two subgoals using `CONJ_TAC`. The first subgoal proves that if `collinear{a,b,c}`, then `det(vector[homogenize a; homogenize b; homogenize c]) = &0`. The second subgoal proves that if `det(vector[homogenize a; homogenize b; homogenize c]) = &0`, then `collinear{a,b,c}`.
  - In the fisrt subgoal, rewrite using `homogenize`, `DOT_2`, `VECTOR_SUB_COMPONENT`, `DET_3`, and `VECTOR_3` to expand the determinant expression, and then simplify using real ring arithmetic.
  - In the second subgoal, instantiate three theorems for vectors `homogenize a`, `homogenize b` and `homogenize c` using `PARALLEL_PROJP_HOMOP`. Instantiate `HOMOGENIZE_NONZERO` for`a`,`b`,`c`. Instantiate`homop` for `projp(homogenize a)`, `projp(homogenize b)` and `projp(homogenize c)`
  - Rewrite using definitions pertaining to parallelity (`parallel`), cross product (`cross`), Cartesian equality (`CART_EQ`), index bounds (`DIMINDEX_3`), universal quantifiers (`FORALL_3`), vector construction (`VECTOR_3`), determinant evaluation (`DET_3`), and vector component extraction (`VEC_COMPONENT`). Finally simplify using real ring arithmetic again.

### Mathematical insight
This theorem bridges affine and projective geometry, showing that collinearity, a fundamental affine concept, is preserved under projectivization. This is essential because projective geometry often simplifies reasoning about incidence properties by treating parallel lines as intersecting at a point at infinity. The theorem formalizes that this intuition is valid.

### Dependencies
- `COLLINEAR_3`
- `DOT_CAUCHY_SCHWARZ_EQUAL`
- `COLLINEAR_BRACKET`
- `projectivize`
- `o_THM`
- `bracket`
- `homogenize`
- `DOT_2`
- `VECTOR_SUB_COMPONENT`
- `DET_3`
- `VECTOR_3`
- `PARALLEL_PROJP_HOMOP`
- `HOMOGENIZE_NONZERO`
- `homop`
- `parallel`
- `cross`
- `CART_EQ`
- `DIMINDEX_3`
- `FORALL_3`
- `VEC_COMPONENT`

### Porting notes (optional)
- The tactic `CONV_TAC REAL_RING` is used to simplify expressions based on real number field properties. Ensure the target proof assistant has similar capabilities for handling real arithmetic.
- The tactics `MAP_EVERY (MP_TAC o C SPEC ...)` apply a series of theorems by specialization and modus ponens. The order in which these are applied is crucial; the target proof assistant needs a similarly precise mechanism for controlling inference steps.


---

## AFFINE_PROJECTIVE_CONIC

### Name of formal statement
AFFINE_PROJECTIVE_CONIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AFFINE_PROJECTIVE_CONIC = prove
 (`!con. affine_conic con <=> ?con'. projective_conic con' /\
                                     con = {x | projectivize x IN con'}`,
  REWRITE_TAC[affine_conic; projective_conic; homogeneous_conic] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(?con' con a b c d e f. P con' con a b c d e f) <=>
    (?a b d e f c con' con. P con' con a b c d e f)`] THEN
  MAP_EVERY (fun s ->
   AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
   X_GEN_TAC(mk_var(s,`:real`)) THEN REWRITE_TAC[])
   ["a"; "b"; "c"; "d"; "e"; "f"] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[IN_ELIM_THM; projectivize; o_THM] THEN
  BINOP_TAC THENL [CONV_TAC TAUT; AP_TERM_TAC] THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  MP_TAC(SPEC `x:real^2` HOMOGENIZE_NONZERO) THEN
  DISCH_THEN(MP_TAC o MATCH_MP PARALLEL_PROJP_HOMOP_EXPLICIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[homogenize; VECTOR_3] THEN
  UNDISCH_TAC `~(k = &0)` THEN CONV_TAC REAL_RING);;
```
### Informal statement
For any set `con` of pairs of real numbers (i.e., a conic section in an affine plane), `con` is an affine conic if and only if there exists a set `con'` of triples of real numbers (i.e., a conic section in a projective plane) such that `con'` is a projective conic, and `con` is equal to the set of all points `x` in the affine plane such that the projectivization of `x` is an element of `con'`.

### Informal sketch
The proof establishes the equivalence between affine and projective conics.
- It starts by expanding the definitions of `affine_conic` and `projective_conic` and `homogeneous_conic`.
- The proof involves rearranging the existential quantifiers and applying rewriting rules based on equality and simplification. It introduces existential variables `a`, `b`, `c`, `d`, `e`, and `f`, which represent the coefficients of the conic equations in both affine and projective spaces.
- Steps use tactic `AP_TERM_TAC` and rewriting to reduce terms. The goal is to show that an affine conic corresponds to a projective conic when points in the affine plane are projectivized and viewed within the projective plane.
- The proof manipulates the expressions by introducing a parameter `k` such that the homogenized coordinates of `x` are then `(k * x1, k * x2, k)`.
- It also utilizes the fact that `homogenize` of a nonzero vector can be represented using `VECTOR_3`.
- It eliminates `k = 0` to reach equality using `REAL_RING`.

### Mathematical insight
This theorem formalizes the relationship between affine conics and projective conics. It states that every affine conic can be obtained by taking the projectivization points of a projective conic. This connection is fundamental in projective geometry as it allows us to study affine conics with the more powerful tools of projective geometry.

### Dependencies
- `affine_conic`
- `projective_conic`
- `homogeneous_conic`
- `LEFT_AND_EXISTS_THM`
- `FUN_EQ_THM`
- `RIGHT_EXISTS_AND_THM`
- `UNWIND_THM2`
- `GSYM`
- `CONJ_ASSOC`
- `IN_ELIM_THM`
- `projectivize`
- `o_THM`
- `EXTENSION`
- `HOMOGENIZE_NONZERO`
- `PARALLEL_PROJP_HOMOP_EXPLICIT`
- `VECTOR_MUL_COMPONENT`
- `homogenize`
- `VECTOR_3`
- `REAL_RING`

### Porting notes (optional)
- The handling of existential quantifiers and rewriting rules might need special attention when porting this theorem. Some proof assistants might require more explicit steps for quantifier manipulation.
- The tactic `REAL_RING` is used for ring arithmetic simplification; ensure the target proof assistant has similar automation for real arithmetic.


---

## PASCAL_AFFINE

### Name of formal statement
PASCAL_AFFINE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PASCAL_AFFINE = prove
 (`!con x1 x2 x3 x4 x5 x6 x7 x8 x9:real^2.
        ~collinear {x1,x2,x4} /\
        ~collinear {x1,x2,x5} /\
        ~collinear {x1,x2,x6} /\
        ~collinear {x1,x3,x4} /\
        ~collinear {x1,x3,x5} /\
        ~collinear {x1,x3,x6} /\
        ~collinear {x2,x3,x4} /\
        ~collinear {x2,x3,x5} /\
        ~collinear {x2,x3,x6} /\
        ~collinear {x4,x5,x1} /\
        ~collinear {x4,x5,x2} /\
        ~collinear {x4,x5,x3} /\
        ~collinear {x4,x6,x1} /\
        ~collinear {x4,x6,x2} /\
        ~collinear {x4,x6,x3} /\
        ~collinear {x5,x6,x1} /\
        ~collinear {x5,x6,x2} /\
        ~collinear {x5,x6,x3}
        ==> affine_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            collinear {x1,x9,x5} /\
            collinear {x1,x8,x6} /\
            collinear {x2,x9,x4} /\
            collinear {x2,x7,x6} /\
            collinear {x3,x8,x4} /\
            collinear {x3,x7,x5}
            ==> collinear {x7,x8,x9}`,
  REWRITE_TAC[COLLINEAR_PROJECTIVIZE; AFFINE_PROJECTIVE_CONIC] THEN
  REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP PASCAL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;
```

### Informal statement
For all `con`, `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x7`, `x8`, `x9` in the real plane, if the points `x1`, `x2`, `x4` are not collinear, and the points `x1`, `x2`, `x5` are not collinear, and the points `x1`, `x2`, `x6` are not collinear, and the points `x1`, `x3`, `x4` are not collinear, and the points `x1`, `x3`, `x5` are not collinear, and the points `x1`, `x3`, `x6` are not collinear, and the points `x2`, `x3`, `x4` are not collinear, and the points `x2`, `x3`, `x5` are not collinear, and the points `x2`, `x3`, `x6` are not collinear, and the points `x4`, `x5`, `x1` are not collinear, and the points `x4`, `x5`, `x2` are not collinear, and the points `x4`, `x5`, `x3` are not collinear, and the points `x4`, `x6`, `x1` are not collinear, and the points `x4`, `x6`, `x2` are not collinear, and the points `x4`, `x6`, `x3` are not collinear, and the points `x5`, `x6`, `x1` are not collinear, and the points `x5`, `x6`, `x2` are not collinear, and the points `x5`, `x6`, `x3` are not collinear, then if `con` is an affine conic, and `x1` is in `con`, and `x2` is in `con`, and `x3` is in `con`, and `x4` is in `con`, and `x5` is in `con`, and `x6` is in `con`, and `x1`, `x9`, `x5` are collinear, and `x1`, `x8`, `x6` are collinear, and `x2`, `x9`, `x4` are collinear, and `x2`, `x7`, `x6` are collinear, and `x3`, `x8`, `x4` are collinear, and `x3`, `x7`, `x5` are collinear, then `x7`, `x8`, `x9` are collinear.

### Informal sketch
The proof proceeds by:
- Projectivizing the affine plane using `COLLINEAR_PROJECTIVIZE` and `AFFINE_PROJECTIVE_CONIC` to transform the problem into the projective plane. This step removes affine-specific notions.
- Repeatedly discharging assumptions.
- Applying Pascal's theorem (`PASCAL`).
- Applying assumptions using `ASM_REWRITE_TAC`.
- Using existential instantiation (`MONO_EXISTS`).
- Performing set operations (`ASM SET_TAC`).

### Mathematical insight
This theorem demonstrates Pascal's theorem within the affine plane. Pascal's theorem is a fundamental result in projective geometry that states that if six points lie on a conic, then the three intersection points of pairs of lines joining opposite sides of the hexagon are collinear. The theorem is lifted from affine space to projective space to apply a more straighforward form of Pascal's theorem, then translated back to the affine plane.

### Dependencies
- `COLLINEAR_PROJECTIVIZE`
- `AFFINE_PROJECTIVE_CONIC`
- `PASCAL`
- `MONO_EXISTS`


---

## COLLINEAR_NOT_COCIRCULAR

### Name of formal statement
COLLINEAR_NOT_COCIRCULAR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLLINEAR_NOT_COCIRCULAR = prove
 (`!r c x y z:real^2.
        dist(c,x) = r /\ dist(c,y) = r /\ dist(c,z) = r /\
        ~(x = y) /\ ~(x = z) /\ ~(y = z)
        ==> ~collinear {x,y,z}`,
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM DOT_EQ_0] THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL; DOT_2] THEN
  REWRITE_TAC[dist; NORM_EQ_SQUARE; CART_EQ; DIMINDEX_2; FORALL_2;
              DOT_2; VECTOR_SUB_COMPONENT] THEN
  CONV_TAC REAL_RING);;
```
### Informal statement
For any real numbers `r`, and any points `c`, `x`, `y`, and `z` in the 2-dimensional real plane (`real^2`), if the distance from `c` to `x` equals `r`, the distance from `c` to `y` equals `r`, the distance from `c` to `z` equals `r`, `x` is not equal to `y`, `x` is not equal to `z`, and `y` is not equal to `z`; then the points `x`, `y`, and `z` are not collinear.

### Informal sketch
The theorem states that if three distinct points `x`, `y`, and `z` are equidistant from a common point `c` (i.e., they lie on a circle centered at `c`), then these three points cannot be collinear.

The proof proceeds as follows:
- First, rewrite `VECTOR_SUB_EQ` by symmetry to change `a = b` into `b = a`.
- Rewrite `DOT_EQ_0` by symmetry to prepare for using `COLLINEAR_3`.
- Apply `COLLINEAR_3` to expand the definition of `collinear {x, y, z}` into a dot product equation.
- Rewrite using `DOT_CAUCHY_SCHWARZ_EQUAL` (by symmetry) and `DOT_2`. This likely aims to show that an inequality arises from assuming collinearity when we know the points lie on a circle, thus deriving a contradiction.
- Rewrite using definitions of `dist`, `NORM_EQ_SQUARE`, `CART_EQ`, `DIMINDEX_2`, `FORALL_2`, `DOT_2`, and `VECTOR_SUB_COMPONENT` to express the distances in terms of vector components and Cartesian coordinates.
- Apply `REAL_RING` to attempt to automatically discharge the resulting goal using real arithmetic simplification.

### Mathematical insight
The theorem formalizes a fundamental geometric property: three distinct points on a circle cannot lie on a single straight line. This is a special case concerning circles where a non-degeneracy condition (distinctness of points) simplifies the condition for points not being collinear.

### Dependencies
- `VECTOR_SUB_EQ`
- `DOT_EQ_0`
- `COLLINEAR_3`
- `DOT_CAUCHY_SCHWARZ_EQUAL`
- `DOT_2`
- `dist`
- `NORM_EQ_SQUARE`
- `CART_EQ`
- `DIMINDEX_2`
- `FORALL_2`
- `VECTOR_SUB_COMPONENT`
- `REAL_RING`

### Porting notes (optional)
- The core dependencies are definitions of distance, collinearity and Cauchy-Schwarz inequality for dot products. Ensure these are available or can be defined within the target proof assistant.
- The `REAL_RING` tactic in HOL Light performs polynomial simplification and equality proving in the real field. An equivalent tactic or manual simplification may be needed in other proof assistants.


---

## PASCAL_AFFINE_CIRCLE

### Name of formal statement
PASCAL_AFFINE_CIRCLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PASCAL_AFFINE_CIRCLE = prove
 (`!c r x1 x2 x3 x4 x5 x6 x7 x8 x9:real^2.
        PAIRWISE (\x y. ~(x = y)) [x1;x2;x3;x4;x5;x6] /\
        dist(c,x1) = r /\ dist(c,x2) = r /\ dist(c,x3) = r /\
        dist(c,x4) = r /\ dist(c,x5) = r /\ dist(c,x6) = r /\
        collinear {x1,x9,x5} /\
        collinear {x1,x8,x6} /\
        collinear {x2,x9,x4} /\
        collinear {x2,x7,x6} /\
        collinear {x3,x8,x4} /\
        collinear {x3,x7,x5}
        ==> collinear {x7,x8,x9}`,
  GEN_TAC THEN GEN_TAC THEN
  MP_TAC(SPEC `{x:real^2 | dist(c,x) = r}` PASCAL_AFFINE) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[PAIRWISE; ALL; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [IMP_IMP] THEN
  DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC COLLINEAR_NOT_COCIRCULAR THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `c:real^2`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[affine_conic; dist; NORM_EQ_SQUARE] THEN
    ASM_CASES_TAC `&0 <= r` THEN ASM_REWRITE_TAC[] THENL
     [MAP_EVERY EXISTS_TAC
       [`&1`; `&1`; `&0`; `-- &2 * (c:real^2)$1`; `-- &2 * (c:real^2)$2`;
        `(c:real^2)$1 pow 2 + (c:real^2)$2 pow 2 - r pow 2`] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      REWRITE_TAC[DOT_2; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      REPLICATE_TAC 5 (EXISTS_TAC `&0`) THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC]]);;
```

### Informal statement
For all points `c`, and for all real number `r`, and for all points `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x7`, `x8`, `x9` in the real plane, if `x1`, `x2`, `x3`, `x4`, `x5`, `x6` are pairwise distinct, and the distance between `c` and `x1` is `r`, and the distance between `c` and `x2` is `r`, and the distance between `c` and `x3` is `r`, and the distance between `c` and `x4` is `r`, and the distance between `c` and `x5` is `r`, and the distance between `c` and `x6` is `r`, and `x1`, `x9`, `x5` are collinear, and `x1`, `x8`, `x6` are collinear, and `x2`, `x9`, `x4` are collinear, and `x2`, `x7`, `x6` are collinear, and `x3`, `x8`, `x4` are collinear, and `x3`, `x7`, `x5` are collinear, then `x7`, `x8`, `x9` are collinear.

### Informal sketch
The proof proceeds as follows:
- Generalize the goal by introducing universal quantifiers for `c`, `r`, `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x7`, `x8`, `x9`.
- Apply the theorem `PASCAL_AFFINE` to the specific set `{x:real^2 | dist(c,x) = r}`. This expresses Pascal's theorem for points on a conic.
- Repeatedly apply `MONO_FORALL` and generalize.
- Rewrite using `PAIRWISE`, `ALL`, and `IN_ELIM_THM` to expand the distinctness conditions.
- Convert conjunctions of implications to implications of conjunctions.
- Discharge the assumptions.
- Strip the goal.
- Use the distinctness assumption to match and apply it.
- Rewrite using the assumptions.
- Split the goal into two subgoals using `CONJ_TAC`.
- The first subgoal proves `collinear {x7,x8,x9}` using `COLLINEAR_NOT_COCIRCULAR`. This requires showing that `x1`, `x2`, `x3`, `x4`, `x5`, `x6` are not cocircular and that there exist `r:real` and `c:real^2`.
- The second subgoal proves `collinear {x7,x8,x9}` by rewriting using `affine_conic`, `dist`, and `NORM_EQ_SQUARE`, then performing case analysis on `&0 <= r`. The goal is then solved by existential introduction and real arithmetic.

### Mathematical insight
This theorem states Pascal's theorem for six points on a circle in the affine plane. It is a special case of Pascal's theorem for conics. Pascal's theorem is a fundamental result in projective geometry. The theorem relates points on a conic section (in this case, a circle) to collinearity properties of the intersections amongst lines formed by connecting those points. This is a specific geometric configuration that holds true even if the configuration is transformed by affine transformations.

### Dependencies
- Definitions:
    - `PAIRWISE`
    - `dist`
    - `collinear`
- Theorems:
    - `PASCAL_AFFINE`
    - `ALL`
    - `IN_ELIM_THM`
    - `COLLINEAR_NOT_COCIRCULAR`
    - `affine_conic`
    - `NORM_EQ_SQUARE`
    - `EXTENSION`
    - `DOT_2`
    - `VECTOR_SUB_COMPONENT`

### Porting notes (optional)
- The most challenging part of porting this theorem will be finding the correct instantiation of `PASCAL_AFFINE`.
- The tactic `ASM_CASES_TAC` might need to be replaced by a suitable case distinction tactic depending on the target proof assistant
- `REAL_ARITH_TAC` call may require manual expansion into primitive real arithmetic inferences in other proof assistants.


---

