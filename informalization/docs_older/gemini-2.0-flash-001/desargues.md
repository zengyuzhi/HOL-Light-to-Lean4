# desargues.ml

## Overview

Number of statements: 52

The file `desargues.ml` formalizes Desargues's theorem. It provides a formal proof of this fundamental theorem in projective geometry. The development imports definitions and theorems related to the cross product from `Multivariate/cross.ml`.


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
For all vectors `u` and `v` in real 3-dimensional space, there exists a vector `w` in real 3-dimensional space such that `w` is not the zero vector and `w` is orthogonal to `u` and `w` is orthogonal to `v`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the statement using the symmetry of the orthogonality relation (`ORTHOGONAL_SYM`).
- Apply a lemma (`ORTHOGONAL_TO_SUBSPACE_EXISTS`) stating that for any subspace, there exists a non-zero vector orthogonal to it. This lemma is instantiated with the subspace spanned by `u` and `v`.
- Rewrite using `FORALL_IN_INSERT`, `NOT_IN_EMPTY`, and `DIMINDEX_3`.
- Discharge using `DISCH_THEN MATCH_MP_TAC` etc.
- Argue that the cardinality of the set `{u, v}` is at most 2 and then perform case analysis on the cardinality being 0, 1, or 2.
- Simplify using facts about cardinality of finite sets and the dimension of the space (arithmetic reasoning with `ARITH_TAC`).

### Mathematical insight
This theorem essentially states that in 3-dimensional space, given any two vectors, one can always find a non-zero vector that is orthogonal to both. This is a fundamental property of 3D space and is related to the existence of the cross product.  It ensures that the orthogonal complement of any subspace of dimension at most 2 is non-trivial in 3D space.

### Dependencies
- Requires `Multivariate/cross.ml`.
- `ORTHOGONAL_SYM`
- `ORTHOGONAL_TO_SUBSPACE_EXISTS`
- `FORALL_IN_INSERT`
- `NOT_IN_EMPTY`
- `DIMINDEX_3`
- `DIM_LE_CARD`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `CARD_CLAUSES`

### Porting notes (optional)
The main challenge in porting this theorem lies in finding or proving the `ORTHOGONAL_TO_SUBSPACE_EXISTS` lemma, and setting up the appropriate facts about cardinality of finite sets.  Also, differences in automation may require more explicit quantifier instantiation than in HOL Light.


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
Define a new type called `direction` with a constructor function `mk_dir` and a destructor function `dest_dir`. The type `direction` is defined as a subset of `real^3` (3-dimensional real vectors) such that for every vector `x` in `real^3`, `x` belongs to the subset if and only if `x` is not equal to the zero vector (`vec 0`).

### Informal sketch
- The `new_type_definition` primitive is used to introduce a new type.
- The representation type is `real^3`.
- The defining predicate is `?x:real^3. ~(x = vec 0)`, stating that the vector `x` is not the zero vector.
- The existence of at least one element satisfying the defining predicate is proven using `MESON` with the hints `BASIS_NONZERO`, `LE_REFL`, and `DIMINDEX_GE_1`. This shows that there exists a non-zero vector in `real^3`.

### Mathematical insight
This definition introduces a type representing directions in 3-dimensional space. A direction is represented by a non-zero vector. The reason for excluding the zero vector is that it does not represent a direction. This type is essential for defining concepts like angles, orientation, and vector fields.

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
- For any `x` and `y` representing directed lines, `x` is perpendicular to `y` if and only if the direction vector of `x` is orthogonal to the direction vector of `y`.

### Informal sketch
- The definition introduces the perpendicularity relation `_|_` between directed lines (`dir`).
- It defines perpendicularity in terms of orthogonality of the corresponding direction vectors.
- The direction vector of a directed line `x` is obtained by applying the function `dest_dir` to `x`.
- The orthogonality of the direction vectors is checked by the existing function `orthogonal`.
- The statement unfolds the definition of `perpdir`.

### Mathematical insight
- This definition links the geometric concept of perpendicularity between directed lines to the algebraic concept of orthogonality between their direction vectors. It allows reasoning about perpendicularity in terms of linear algebra, by translating the directed lines into vectors.

### Dependencies
- Definitions:
  - `dest_dir`
  - `orthogonal`


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
For any `x` and `y`, `x` is parallel to `y` if and only if the cross product of the direction vector of `x` and the direction vector of `y` is equal to the zero vector.

### Informal sketch
The definition introduces the concept of parallelism between two lines. It leverages the existing function `dest_dir` to extract the direction vector of each line. The parallelism condition is then characterized by the cross product of these direction vectors being equal to the zero vector. This is a standard vector calculus characterization of parallelism.

### Mathematical insight
This definition formalizes the geometric concept of parallel lines in terms of vector algebra. Two lines are parallel if their direction vectors are parallel, which is equivalent to their cross product being the zero vector. This is a fundamental concept in vector geometry and linear algebra.

### Dependencies
- Definition: `dest_dir`
- Definition of the cross product `cross`
- Definition of the zero vector `vec 0`

### Porting notes (optional)
- Ensure that the target proof assistant has a suitable definition of vector cross product and the concept of a zero vector in the corresponding vector space.
- The function `dest_dir` may need to be defined depending on how lines are represented in the target system.


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
The theorem states that the following two equivalences hold:
1. For any predicate `P`, the universal quantification of `P` over the result of `dest_dir x` is equivalent to the universal quantification of `P` over `x`, provided `x` is not equal to the zero vector.
2. For any predicate `P`, the existential quantification of `P` over the result of `dest_dir x` is equivalent to the existential quantification of `P` over `x`, where `x` is not equal to the zero vector and `P` holds for `x`.

### Informal sketch
The proof is done using `MESON_TAC` with the theorems in `direction_tybij`.
- The essence of the proof lies in leveraging the bijectivity properties established in `direction_tybij` and predicate calculus to manipulate quantifiers and vector conditions. The function `dest_dir` maps vector directions. The theorem relies on the bijection `direction_tybij`, which relates vectors (excluding zero) and directions.

### Mathematical insight
The theorem clarifies the relationship between quantifying over directions (using `dest_dir`) and quantifying over vectors (excluding the zero vector). This is essential when reasoning about properties that depend on direction but are defined in terms of vectors. The exclusion of the zero vector is crucial because `dest_dir` is not defined for the zero vector.

### Dependencies
- Theorems: `direction_tybij`

### Porting notes (optional)
The `MESON_TAC` call suggests reliance on automated reasoning. Other proof assistants might require a more manual application of `direction_tybij` and quantifier manipulation. Porting might involve explicitly proving equivalences related to quantifiers and vector conditions using the bijectivity properties captured in `direction_tybij`.


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
The following three theorems are proved:
1.  For all `x`, `x || x` holds.
2.  For all `x` and `y`, `x || y` is equivalent to `y || x`.
3.  For all `x`, `y`, and `z`, if `x || y` and `y || z`, then `x || z`.

### Informal sketch
The proof is constructed using the following strategies:

*   The initial goal is a conjunction of three universally quantified statements. The tactic `CONJUNCTS` separates it into three independent goals corresponding to the three conjuncts.
*   `REWRITE_TAC[pardir; DIRECTION_CLAUSES]` simplifies the goal by rewriting using the definition of `pardir` (presumably an inductive definition or similar specifying when two directions/vectors are parallel) and any relevant direction clauses, aiming to unfold the `||` relation in terms of underlying definitions.
*   `VEC3_TAC` likely provides vector-specific reasoning and automation to solve remaining goals. It probably handles any arithmetic or algebraic manipulations related to 3D vectors needed to complete the proof.

### Mathematical insight
The theorem establishes that the `||` relation (`pardir`) is reflexive, symmetric, and transitive. Therefore, it is an equivalence relation. This is a fundamental property needed to reason formally about parallel directions in 3D space.

### Dependencies
*   `pardir`
*   `DIRECTION_CLAUSES` (likely a list of theorems or simplification rules related to directions)

### Porting notes (optional)
*   Ensure that the definition of `pardir` is ported accurately, as the proof relies heavily on its properties being unfolded via rewriting.
*   The `VEC3_TAC` tactic encapsulates vector-specific reasoning. You may need to provide equivalent vector-specific automation or tactics in the target proof assistant. This might involve providing specialized simplification rules or decision procedures for vector arithmetic.


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
For any `x` and `y`, the parallel direction of `x` is equal to the parallel direction of `y` if and only if `x` is parallel to `y`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using `FUN_EQ_THM`. This likely expands the definition of equality of functions (the parallel directions) to a point-wise equality.
- Then, invoke the MESON prover with the theorems `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS`. This indicates that the proof relies on the reflexivity, symmetry, and transitivity of the parallel relation; thus, MESON constructs the rest of the proof based on these properties.

### Mathematical insight
This theorem connects the concept of parallel direction, represented by `(||) x`, with the parallel relation `x || y`. It formalizes the intuitive idea that two lines (or vectors) have the same direction if and only if they are parallel. This provides a crucial link between the geometric concept of direction and the relation of being parallel, allowing reasoning about geometric parallelism through algebraic manipulations of directions.

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
For all vectors `p` and `p'`, if it is not the case that `p` or `p'`, then there exists a vector `l` such that `p` is perpendicular to `l` and `p'` is perpendicular to `l`, and for all vectors `l'`, if `p` is perpendicular to `l'` and `p'` is perpendicular to `l'`, then `l'` is parallel to `l`.

### Informal sketch
The proof proceeds as follows:
- Rewrite using definitions of `perpdir` (definition of perpendicularity between a vector and a direction), `pardir` (definition of parallelism between directions), and `DIRECTION_CLAUSES`.
- Repeatedly apply stripping tactics to eliminate outermost quantifiers and implications.
- Instantiate the existential quantifier with specific values for `p` and `p'`.
- Apply a monotonicity rule for existential quantification.
- Discharge assumptions using conjunction.
- Apply `VEC3_TAC` to complete the proof.

### Mathematical insight
This theorem states that given two non-trivial vectors, there exists a line (`l`) perpendicular to both. Moreover, any other line (`l'`) perpendicular to both vectors must be parallel to `l`. This uniquely defines the direction perpendicular to the plane spanned by vectors `p` and `p'`, i.e., the cross product direction. This result represents a fundamental property of three-dimensional Euclidean space, guaranteeing the existence and uniqueness (up to parallelism) of a direction perpendicular to two given directions.

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
For all lines `l` and `l'`, there exists a point `p` such that `p` is perpendicular to `l` and `p` is perpendicular to `l'`.

### Informal sketch
The proof demonstrates that given any two lines `l` and `l'`, there exists some point `p` that is perpendicular to both lines.
- The initial step involves rewriting using `perpdir` and `DIRECTION_CLAUSES`. This likely expands the definition of perpendicularity to involve direction vectors.
- The proof utilizes `MESON_TAC` along with `NORMAL_EXISTS` and `ORTHOGONAL_SYM`. `NORMAL_EXISTS` likely asserts the existence of a normal vector. `ORTHOGONAL_SYM` likely introduces the symmetric property of orthogonality.

### Mathematical insight
This theorem asserts a fundamental property about lines in a plane: for any two lines, there always exists a point that is orthogonal to both. This point could be thought of as the origin relative to which both lines have simple directional representations. This is quite abstract, since `p` is presented as a direction, which is being orthogonal to a line. So, `p` can probably be thought of here of as a direction vector from some origin to some point on both lines.

### Dependencies
- Theorems: `NORMAL_EXISTS`, `ORTHOGONAL_SYM`
- Definitions: `perpdir`
- Clauses: `DIRECTION_CLAUSES`


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
There exist three lines `p`, `p'`, and `p''` such that no two of them are parallel, and there is no line `l` that is perpendicular to all three.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using `perpdir`, `pardir`, and `DIRECTION_CLAUSES`. This likely expands the definitions of perpendicularity, parallelism, and related concepts involving directions.
- Then, introduce existential variables for the directions using `EXISTS_TAC`. The tactics are applied three times with `basis 1 :real^3`, `basis 2 : real^3`, and `basis 3 :real^3` so the proof exhibits three distinct directions for the existential variables p, p' and p'' using the standard basis vectors in `real^3`. `SIMP_TAC` likely simplifies the statement after the existentials are introduced, using the facts that the basis vectors are non-zero (`BASIS_NONZERO`) and that indices into vectors are within bounds based on dimension (`DIMINDEX_3`), using arithmetic reasoning to simplify the generated arithmetic expressions (`ARITH`).
- Finally, the goal is closed using `VEC3_TAC`, which is a tactic to prove vector space results in 3 dimensions, and likely handles the final arithmetic and vector reasoning needed.

### Mathematical insight
This theorem asserts the existence of three non-parallel lines in 3D space such that no single line is orthogonal to all of them. This is a fundamental geometric fact in 3D Euclidean space. The statement relates to the possible configurations of lines in 3D space and their orthogonality properties.

### Dependencies
- `perpdir`
- `pardir`
- `DIRECTION_CLAUSES`
- `BASIS_NONZERO`
- `DIMINDEX_3`

### Porting notes (optional)
The `VEC3_TAC` tactic likely encapsulates significant automation for vector reasoning in 3D. When porting, one may need to recreate this automation using tactics or decision procedures available in the target proof assistant. The specific definitions expanded by `DIRECTION_CLAUSES` would also be important to port accurately.


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
For any vector `l`, there exist vectors `p` and `p'` such that it is not the case that either `p` or `p'` are true (where truth is presumably related to being non-zero), both `p` and `p'` are orthogonal to `l`.
### Informal sketch
The proof proceeds by rewriting using `DIRECTION_CLAUSES`, `pardir`, and `perpdir` and then stripping the quantifiers and negation. It then sets up a subgoal that asserts the disjunction of three conditions. Each condition involves choosing two basis vectors from `basis 1`, `basis 2`, and `basis 3`. For each pair of basis vectors, say `basis i` and `basis j`, it checks that `l cross basis i` and `l cross basis j` are orthogonal to `l`, and that the cross product `(l cross basis i) cross (l cross basis j)` is not equal to `vec 0`. This subgoal is proved by vector tactics.

*   The main idea is to show the existence of two vectors `p` and `p'` orthogonal to `l`.
*   The proof exploits the properties of `cross` product and orthogonality in 3D space. Specifically, it is using the fact that at least two of the cross products between `l` and basis vectors will be non-zero and also `orthogonal` to l.
*   The cross product of two vectors is orthogonal to both vectors.
*   The condition `~((l cross basis i) cross (l cross basis j) = vec 0)` ensures that the two vectors `l cross basis i` and `l cross basis j` are linearly independent.

### Mathematical insight
The theorem states some basic geometric facts about 3-dimensional space and orthogonality. This essentially guarantees that one can find two independent directions orthogonal to any given direction `l`. It establishes a crucial property concerning the space of vectors orthogonal to a given vector, which is fundamental in geometric reasoning and vector algebra.

### Dependencies
* `DIRECTION_CLAUSES`
* `pardir`
* `perpdir`
* `CROSS_0`
* `VEC3_TAC`
### Porting notes (optional)
The main challenge is to ensure that the target system has suitable automation for vector arithmetic, particularly concerning cross products and orthogonality. The use of `VEC3_TAC` suggests that HOL Light has some level of automation here, so similar tactics may need to be developed in other systems. One should pay attention to how the cross product and orthogonality are defined in the target proof assistant, and how these interact with the vector space structure.


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
For all vectors `x`, `a`, and `b` in 3-dimensional real space, if `a` is orthogonal to `x`, `b` is orthogonal to `x`, and `a` is not parallel to `b`, then there exists a vector `c` such that `c` is orthogonal to `x`, `a` is not parallel to `c`, and `b` is not parallel to `c`.

### Informal sketch
The proof proceeds as follows:
- Rewrite using `DIRECTION_CLAUSES`, `pardir`, and `perpdir` to expand the definitions of orthogonality and non-parallelism in terms of vector operations.
- Repeatedly strip the top-level structure of the goal (implication) to move the assumptions to the assumption list, resulting in a goal to prove an existential statement (`?c. ...`) under several assumptions.
- Instantiate the existential quantifier with `a + b`.
- Discharge the assumptions by proving that `a + b` satisfies the required conditions.
   - We need to show `(a + b) _|_ x`, `~(a || (a + b))`, and `~(b || (a + b))`.
   - This is done by using vector arithmetic and the initial assumptions that `a _|_ x`, `b _|_ x`, and `~(a || b)`.
- Use VEC3_TAC to perform vector reasoning to close the proof.

### Mathematical insight
The theorem states that given two non-parallel vectors `a` and `b` both orthogonal to a vector `x`, we can always find another vector `c` (specifically, `a + b`) that is also orthogonal to `x` and not parallel to either `a` or `b`. Geometrically, this means that we can find a third direction orthogonal to `x` that is distinct from the directions of `a` and `b`. This is a fundamental property of 3-dimensional space.

### Dependencies
- `DIRECTION_CLAUSES` (likely a rewrite list expanding orthogonality and parallelism)
- `pardir` (definition or theorem about parallel vectors)
- `perpdir` (definition or theorem about perpendicular/orthogonal vectors)
- `VEC3_TAC` (tactic for vector arithmetic)


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
For any line `l`, there exist three distinct lines `p`, `p'`, and `p''` such that no two of them are equal (`p` is not equal to `p'`, `p'` is not equal to `p''`, and `p` is not equal to `p''`) and each of them is orthogonal to `l` (`p` is orthogonal to `l`, `p'` is orthogonal to `l`, and `p''` is orthogonal to `l`).

### Informal sketch
The proof demonstrates the existence of three distinct lines (`p`, `p'`, `p''`) that are all orthogonal to a given line `l`.

*   The proof uses `DIRECTION_AXIOM_4_WEAK` which provides the existence of two distinct orthogonal lines and `ORTHOGONAL_COMBINE` which may combine existing orthogonality facts to derive the existence of a third orthogonal line.
*   The tactic `MESON_TAC` then automatically combines these facts to derive the goal.

### Mathematical insight
This theorem is a basic result in geometry, stating that one can always find three different lines that are all perpendicular to a given line. This provides a foundation for reasoning about geometric configurations and relationships.

### Dependencies
Theorems required:
*   `DIRECTION_AXIOM_4_WEAK`
*   `ORTHOGONAL_COMBINE`


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
The type `line` is defined as the quotient of the cartesian plane `(||)` with respect to some equivalence relation. The constructor `mk_line` lifts elements of `(||)` into `line`, and the destructor `dest_line` maps elements of type `line` back to their equivalence class in `(||)`.

### Informal sketch
- The function `define_quotient_type` automatically defines a new type `line` representing the quotient set of the cartesian plane `(||)` by an equivalence relation.
- The equivalence relation is inferred during the construction to produce a well-defined type.
- The constructor `mk_line` takes an element from `(||)` and returns a representative of its equivalence class as an element of the type `line`.
- The destructor `dest_line` takes an element of type `line` and returns the element of `(||)` that it represents.

### Mathematical insight
This construction provides a way to formally define a line as an equivalence class of points in the cartesian plane. The quotient type construction ensures that the type `line` is well-defined, even if the choice of the representative in `(||)` is arbitrary. This is a standard method for constructing new mathematical objects from existing ones by identifying elements that are considered equivalent.

### Dependencies
None

### Porting notes (optional)
The `define_quotient_type` requires a counterpart in the target proof assistant. Many proof assistants provide libraries to define quotient types. In Coq, this can be achieved using the `Quotient` package. Other proof assistants have similar mechanisms. The challenge often lies in automatically inferring the appropriate equivalence relation or providing it explicitly.


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
The proof proceeds by rewriting using the definitions of `perpdir` (perpendicular direction), `pardir` (parallel direction), and `DIRECTION_CLAUSES` (likely containing clauses about vector directions). Then, `VEC3_TAC` (a tactic for vector arithmetic) is used to complete the proof, likely simplifying vector expressions to obtain the desired equivalence.
- The initial rewrite step replaces `x || x'` with `!k. x = k * x'` and `y || y'`  with `!k. y = k * y'`, and `x _|_ y` with `dot(x, y) = 0`.
- Then, `VEC3_TAC` simplifies the resulting expression `dot(x,y) = 0 <=> dot(x',y')=0` using properties of dot products and scalar multiplication, eventually proving the theorem.

### Mathematical insight
This theorem states that the perpendicularity of directions is well-defined: if we have two pairs of vectors that are parallel to each other, then the perpendicularity between the vectors in the first pair is equivalent to the perpendicularity between the vectors in the second pair. This is an important property when dealing with directions, as it allows us to work with any representative vector in a given direction without affecting the perpendicularity relationship.

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
- The full HOL Light statement will be inserted here **after generation**.
```ocaml
let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;
```
### Informal statement
- The function `perpl` and the theorem `perpl_th` are defined by lifting the function `snd line_tybij` (which likely extracts the second component of a line type bijection) to act on parallel directions. The construction uses `PARDIR_REFL` and `PARDIR_TRANS` to ensure well-definedness with respect to equivalence classes of parallel directions, as certified by `PERPDIR_WELLDEF`.

### Informal sketch
- The goal is to define a function `perpl` that relates parallel directions, likely corresponding to the notion of perpendicularity.
- The function `snd line_tybij` likely extracts relevant information from a bijection on lines.
- The `lift_function` construct ensures that the function is well-defined on equivalence classes, here parallel directions. This requires proving that the function respects the equivalence relation, which is handled by `PERPDIR_WELLDEF`.
- `PARDIR_REFL` and `PARDIR_TRANS` are likely used within `PERPDIR_WELLDEF` to show that the lifted function respects the equivalence relation for parallel directions.

### Mathematical insight
- This construction likely defines a notion of perpendicularity between parallel directions by leveraging a bijection on lines. Lifting a function to equivalence classes to deal with quotient types is a standard technique in formal mathematics. The well-definedness proof is crucial to ensure consistent behavior on representatives of the equivalence classes.

### Dependencies
- Definitions: `line_tybij`, `PARDIR_REFL`, `PARDIR_TRANS`
- Theorems: `PERPDIR_WELLDEF`


---

## line_lift_thm

### Name of formal statement
`line_lift_thm`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let line_lift_thm = lift_theorem line_tybij
 (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th];;
```
### Informal statement
The theorem `line_lift_thm` is derived from the theorem `line_tybij` by lifting it through the following relations: `PARDIR_REFL` expressing the reflexivity of parallel direction, `PARDIR_SYM` expressing the symmetry of parallel direction, and `PARDIR_TRANS` expressing the transitivity of parallel direction. The lifting process also takes into account the theorem `perpl_th`.

### Informal sketch
The proof lifts `line_tybij` using a relation mapping between the original type and a target type. The lifting process requires justification that the relations are reflexive, symmetric, and transitive, which are provided by `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` respectively. It also leverages `perpl_th` during the lifting process.

### Mathematical insight
This theorem provides a way to generalize or transfer existing theorems about `line_tybij` to related concepts using the lifting mechanism. This is useful for reusing existing proofs and definitions in new contexts.

### Dependencies
- Theorems: `line_tybij`, `perpl_th`
- Relations: `PARDIR_REFL`, `PARDIR_SYM`, `PARDIR_TRANS`


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
The theorem `LINE_AXIOM_1` states that if `DIRECTION_AXIOM_1` holds, then the lifted version of `DIRECTION_AXIOM_1` under lines also holds. In other words, `LINE_AXIOM_1` is derived from `DIRECTION_AXIOM_1` by lifting it to the context of lines using the `line_lift_thm` operation.

### Informal sketch
*   The theorem `LINE_AXIOM_1` is a direct application of the `line_lift_thm` transformation to the axiom `DIRECTION_AXIOM_1`. This suggests that `line_lift_thm` is a theorem that takes a theorem about directions and generalizes it to lines.
*   The proof consists of applying `line_lift_thm` to `DIRECTION_AXIOM_1`.

### Mathematical insight
The `line_lift_thm` operation represents a common pattern in geometric reasoning: generalizing properties of primitive objects (like directions) to more complex geometric objects (like lines) built upon them. This theorem allows us to quickly derive properties of lines from known properties of directions, establishing a connection between these geometric concepts.

### Dependencies
- Theorems: `line_lift_thm`
- Axioms: `DIRECTION_AXIOM_1`


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
Given `DIRECTION_AXIOM_2`, prove the corresponding lifted version of this axiom using `line_lift_thm`.

### Informal sketch
The theorem `LINE_AXIOM_2` is proved by applying the theorem `line_lift_thm` to the axiom `DIRECTION_AXIOM_2`.

*   The theorem `line_lift_thm` lifts a theorem about directions to a corresponding theorem about lines by replacing direction vectors with lines containing those vectors.
*   The axiom `DIRECTION_AXIOM_2` states a basic property about directions.
*   Applying `line_lift_thm` to `DIRECTION_AXIOM_2` results in `LINE_AXIOM_2`.

### Mathematical insight
This theorem lifts a direction axiom to a line axiom. This is a systematic way to generalize geometric axioms from directions to lines, making them more applicable in geometric proofs involving lines. `line_lift_thm` encapsulates a general method for such lifting, ensuring consistency between direction-based and line-based reasoning.

### Dependencies
- Theorem: `line_lift_thm`
- Axiom: `DIRECTION_AXIOM_2`


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
Given `DIRECTION_AXIOM_3`, if for all triples of points `x`, `y`, and `z`, the point `z` lies on the line through `x` and `y` if and only if the point `x` lies on the line through `y` and `z`, then for all lines `l`, there exist distinct points `x` and `y` such that both `x` and `y` lie on `l`.

### Informal sketch
The theorem `LINE_AXIOM_3` is derived by applying the theorem `line_lift_thm` to the axiom `DIRECTION_AXIOM_3`. The theorem `line_lift_thm` lifts properties about collinearity of points to properties about existence of points on lines. Essentially, it states that if a certain collinearity axiom holds, then we can prove the existence of distinct points on every line. `DIRECTION_AXIOM_3` provides the collinearity axiom required by `line_lift_thm`.

*   The `line_lift_thm` is a higher-order theorem that takes a collinearity axiom as input.
*   `DIRECTION_AXIOM_3` expresses the symmetry of collinearity: `z` is on the line through `x` and `y` iff `x` is on the line through `y` and `z`.
*   The application of `line_lift_thm` to `DIRECTION_AXIOM_3` yields the desired geometrical result about every line containing at least two distinct points.

### Mathematical insight
This theorem demonstrates how an abstract geometrical property (symmetry of collinearity expressed in `DIRECTION_AXIOM_3`) can be used to derive a fundamental property of lines (existence of two distinct points on a line) using the `line_lift_thm`. This connection is important as it shows how to build up geometrical theories from basic axioms.

### Dependencies
* `line_lift_thm`
* `DIRECTION_AXIOM_3`


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
Given `DIRECTION_AXIOM_4`, then it follows `line_lift_thm DIRECTION_AXIOM_4`.

### Informal sketch
The theorem `LINE_AXIOM_4` is directly derived from `DIRECTION_AXIOM_4` by applying the theorem `line_lift_thm`.
- The theorem `line_lift_thm` presumably lifts or transforms `DIRECTION_AXIOM_4` to a similar statement about lines.

### Mathematical insight
The theorem serves to lift an axiom about directions to an equivalent statement about lines. The `line_lift_thm` handles this transformation, likely involving changes in the objects the axiom quantifies over and the predicates used.

### Dependencies
- Theorem: `DIRECTION_AXIOM_4`
- Theorem: `line_lift_thm`


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
Define a new type named `point` using the type definition principle. This creates a new type constructor `point`, along with a constructor function `mk_point` and a destructor function `dest_point`. The proof obligation is to show that there exists an element `x` of type `line` such that `T` is true.

### Informal sketch
- This definition introduces a new type, `point`.
- The type definition principle requires proving the non-emptiness of the representing set.
- Here, we must show the existence of an element `x` of type `line` for which `T` (true) holds.
- `REWRITE_TAC[]` is used to solve the goal `?x:line. T`. This simply rewrites `T` to `T` and then the existential goal becomes trivially provable since `T` is always true.

### Mathematical insight
The type definition principle is a standard way to introduce new types in HOL. In this case, the type `point` is represented by the type `line`, which is assumed to exist. The existential goal confirms that the representing set is non-empty, allowing the type definition to proceed. In HOL Light, type definitions require a nonempty witness set, which is what the given proof obligation ensures.

### Dependencies
- `line` (a pre-existing type).

### Porting notes (optional)
- In other proof assistants like Coq or Lean, the analogue of `new_type_definition` might involve defining a type using `Type` or `Set` (Coq) or `Type` (Lean) and proving a similar non-emptiness condition for the subset that represents the new type. Depending on the axiomatization of `line` in the target system, the proof of existence might require more steps than in HOL Light. However, since we have `T`, any inhabitant of `line` will work.


---

## on

### Name of formal statement
`on`

### Type of the formal statement
`new_definition`

### Formal Content
```ocaml
let on = new_definition `p on l <=> perpl (dest_point p) l`;;
```

### Informal statement
For any point `p` and line `l`, `p` is on `l` if and only if the perpendicular line to `l` at the destination point of `p` exists.

### Informal sketch
The definition introduces the predicate `on` to express the incidence relation between a point and a line.
- The definition states that `p on l` holds if the line perpendicular to `l` going through the destination point of `p` (i.e., the endpoint of the vector representing `p`) exists.

### Mathematical insight
This definition provides a way of expressing the geometric concept of a point lying on a line using the formal machinery of HOL Light. The `perpl` function is presumably defined in terms of vector algebra, and the definition links this algebraic perspective to a geometric interpretation. The existence of the perpendicular line is used to define the `on` predicate.

### Dependencies
- Definitions: `dest_point`, `perpl`


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
The following statements hold:
1. For any `p` and `p'`, `p` is equal to `p'` if and only if the destination point of `p` is equal to the destination point of `p'`.
2. For any predicate `P` on the type of points, for all `p`, `P` holds for the destination point of `p` if and only if for all `l`, `P` holds for `l`.
3. For any predicate `P` on the type of points, there exists a `p` such that `P` holds for the destination point of `p` if and only if there exists an `l` such that `P` holds for `l`.

### Informal sketch
*   The theorem establishes properties related to the injection of `point` objects into their `dest_point` counterparts in the theory of geometry.

*   The proof uses `MESON_TAC` with the single dependency `point_tybij`. This tactic attempts to automatically prove the goal using the provided theorems along with built-in reasoning capabilities of the MESON prover.

*   The first clause states that equality of `point` objects is determined solely by the equality of their projections via `dest_point`.

*   The second and third clauses lift quantification over `dest_point`s to quantification over an arbitrary `l`.

### Mathematical insight
This theorem connects the equality and quantification properties of objects of type `point` with their corresponding projections given by the function `dest_point`. It establishes that equality and universal/existential quantification over the range of `dest_point` are equivalent to equality and quantification over the elements of the point type themselves. This is an important property for reasoning about points and ensures that the `dest_point` function behaves as expected. 

### Dependencies
- `point_tybij`

### Porting notes (optional)
The main difficulty for porting is ensuring that the MESON prover (or equivalent automated reasoning) can handle the theorem given only `point_tybij`. In proof assistants like Coq or Lean, one might need to use a combination of rewriting with `point_tybij` and then applying tactics such as `auto` or `intuition` to complete the proof.


---

## POINT_TAC

### Name of formal statement
POINT_TAC

### Type of the formal statement
Theorem proving tactic

### Formal Content
```ocaml
let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;
```

### Informal statement
The tactic `POINT_TAC` applied to a theorem `th` rewrites `th` using the rewrite rules in the list `POINT_CLAUSES` with the `on` flag to control rewriting, and then attempts to accept the resulting theorem.

### Informal sketch
- Rewrite the input theorem `th` using the equations in `POINT_CLAUSES`. The `on` flag likely restricts rewriting to the top level of the theorem.
- Attempt to prove the rewritten goal using `ACCEPT_TAC`, which discharges the goal if it is trivially true.

### Mathematical insight
This tactic is designed to simplify a goal by applying known rewrite rules about points, likely in a geometric context. The `ACCEPT_TAC` suggests that after rewriting, the goal should be immediately provable. This expresses a strategy of simplification followed by trivial proof.

### Dependencies
- `POINT_CLAUSES`
- `REWRITE_TAC`
- `ACCEPT_TAC`
- `on`


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
The proof is achieved by applying `POINT_TAC` and `LINE_AXIOM_1`. This axiom establishes the uniqueness of a line given two distinct points. More specifically:
- `POINT_TAC`: This tactic likely introduces assumptions related to points, preparing for the application of geometric axioms
- `LINE_AXIOM_1`: This tactic probably asserts the existence and uniqueness of a line passing through two distinct points

### Mathematical insight
This axiom formalizes the fundamental geometric postulate that through any two distinct points, there exists exactly one line. This is a cornerstone of Euclidean geometry.

### Dependencies
- Tactical: `POINT_TAC`
- Axioms: `LINE_AXIOM_1`


---

## AXIOM_2

### Name of formal statement
AXIOM_2

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let AXIOM_2 = prove
 (`!l l'. ?p. p on l /\ p on l'`,
  POINT_TAC LINE_AXIOM_2);;
```

### Informal statement
For any two lines `l` and `l'`, there exists a point `p` that lies on line `l` and also lies on line `l'`.

### Informal sketch
The proof, using `POINT_TAC` tactic and `LINE_AXIOM_2` axiom, establishes that for any two given lines `l` and `l'`, there exists a point `p` such that `p` lies on both `l` and `l'`. This can be seen as an axiom of Euclidean geometry, saying two any lines intersect in (at least) one point. `POINT_TAC` likely uses `LINE_AXIOM_2` tactic/axiom to exhibit the existence of the intersection.

### Mathematical insight
This axiom asserts the existence of an intersection point for any two lines. In the context of geometry, this implies that there are no parallel lines. This axiom is essential for defining the geometric properties of the space by ensuring lines always meet.

### Dependencies
- Axioms: `LINE_AXIOM_2`


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
For any points `p`, `p'`, and `p''`, if `p`, `p'`, and `p''` are distinct (i.e., `p` is not equal to `p'`, `p'` is not equal to `p''`, and `p` is not equal to `p''`), then it is not the case that there exists a line `l` such that `p` lies on `l`, `p'` lies on `l`, and `p''` lies on `l`.

### Informal sketch
The statement is an axiom asserting that there do not exist a line on which three distinct points lie.

*   The axiom `AXIOM_3` is introduced using `prove`.
*   The goal is `?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\ ~(?l. p on l /\ p' on l /\ p'' on l)`.
*   The proof is conducted using `POINT_TAC` and `LINE_AXIOM_3`. Supposedly there is a tactic `POINT_TAC` that introduces the points `p`, `p'`, and `p''` and their inequalities and then `LINE_AXIOM_3` makes use of the third axiom of lines.

### Mathematical insight
This axiom formalizes the geometric notion that three distinct points cannot be collinear. It is a fundamental property assumed in Euclidean geometry.

### Dependencies
* Tactics: `POINT_TAC`
* Axioms: `LINE_AXIOM_3`


---

## AXIOM_4

### Name of formal statement
AXIOM_4

### Type of the formal statement
theorem

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
The proof is achieved by applying the tactic `POINT_TAC` to `LINE_AXIOM_4`. `LINE_AXIOM_4` likely asserts that every line contains at least two points. The `POINT_TAC` tactic probably expands upon `LINE_AXIOM_4`, likely by using additional axioms or constructions to show that a third point is always possible on any given line. The distinctness conditions `~(p = p') /\ ~(p' = p'') /\ ~(p = p'')` are handled within the tactic.

### Mathematical insight
This axiom asserts that there are infinitely many points on any line. Given that `LINE_AXIOM_4` establishes that there are *at least* two points on a line, `AXIOM_4` strengthens this requirement to three. This is important for establishing the richness or non-degeneracy of the geometric space.

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
The function `projl` is defined such that, for any vector `x`, `projl x` is equal to the projective line constructed from the direction `mk_dir x` using the `(||)` operator within `mk_line`.

### Informal sketch
The definition of `projl` directly constructs a projective line from a vector `x`. The process involves the following steps:
- Compute the direction `mk_dir x` associated with the vector `x`.
- Apply the unspecified function `(||)` to the direction `mk_dir x`.
- Construct a projective line using `mk_line` with the result from the previous step.

### Mathematical insight
This definition maps vectors to projective lines. The core idea is to associate a direction with the vector using `mk_dir` and then construct a line from that direction. The unspecified function `(||)` (likely a concatenation or pairing operation) suggests that `mk_line` requires a pair of directions (or a structured object representing a direction) to define the line. The function `projl` provides a way to represent vectors as projective lines, which is a common technique in projective geometry.

### Dependencies
- Definitions: `mk_line`, `mk_dir`, `(||)`


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
Define `projp` of `x` to be `mk_point` applied to `projl` of `x`.

### Informal sketch
The definition introduces a function `projp` which maps a value `x` to a point constructed by applying the function `mk_point` to the result of applying the function `projl` to `x`. There is no proof, as this is a definition.

### Mathematical insight
The definition `projp` likely represents a projection operation to a point-like representation within a geometric or algebraic context. `projl` presumably projects to some intermediate representation, and `mk_point` then constructs an actual point. This is a standard way of defining derived geometric constructs.

### Dependencies
- Definitions:
    - `mk_point`
    - `projl`


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
For every line `l`, there exists a vector `x` that is not the zero vector `vec 0`, such that `l` is equal to the projective line through `x`, denoted by `projl x`.

### Informal sketch
The proof proceeds as follows:
- The goal is to show that for any line `l`, there exists a vector `x` not equal to `vec 0` such that `l = projl x`.
- Use a subgoal tactic to introduce an intermediate goal: to show there exists a direction `d` such that `l = mk_line((||) d)`.
- Decompose the proof into two branches:
    - Use the `line_tybij` theorems to establish the correspondence between lines and directions.
    - Rewrite using the definition of `projl` and then existentially quantify over the direction `dest_dir d` such that the goal can be proven using `direction_tybij`.

### Mathematical insight
The theorem `PROJL_TOTAL` asserts that the mapping from vectors to projective lines (`projl`) covers the entire space of lines. This is a totality result, showing that any line can be represented as the projective line of some non-zero vector. This is a fundamental property when working with projective spaces, as it guarantees that the `projl` function effectively parameterizes the space of lines (modulo scaling of the vector).

### Dependencies
- `projl`
- `mk_line`
- `fst line_tybij`
- `snd line_tybij`
- `direction_tybij`
- `dest_dir`


---

## homol

### Name of formal statement
homol

### Type of the formal statement
new_specification

### Formal Content
```ocaml
let homol = new_specification ["homol"]
  (REWRITE_RULE[SKOLEM_THM] PROJL_TOTAL);;
```

### Informal statement
The function `homol` is specified such that `homol(x, y) = x`.

### Informal sketch
The specification of `homol` is derived by:
- Applying the `REWRITE_RULE` to `SKOLEM_THM`.
- Applying this result to `PROJL_TOTAL`.
The rewrite rule likely uses the Skolem theorem to introduce a function that witnesses the existence claim inherent in `PROJL_TOTAL`. `PROJL_TOTAL` likely asserts the totality of the projection function for product types.

### Mathematical insight
This specification introduces the left projection function (or first projection) from a pair. It formalizes that `homol` when applied to a pair `(x, y)` returns `x`. Projectors are fundamental when reasoning about tuples and are used very often in mathematics. The `SKOLEM_THM` is used to show the existence of a corresponding function for extracting the left part of a pair.

### Dependencies
- Constants:
  - `PROJL_TOTAL`
- Theorems:
  - `SKOLEM_THM`


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
For any `p`, there exists an `x` such that `x` is not equal to the zero vector (`vec 0`) and `p` is equal to the projection of `x` (`projp x`).

### Informal sketch
The theorem states that the `projp` function (which represents the projection to a point) is total. The proof proceeds as follows:
- The tactic `REWRITE_TAC[projp]` rewrites the definition of `projp`. Specifically, `projp x` is defined as `\&(1 / (dot x x)) %* x`. The goal is to show that for any `p`, there exists a nonzero `x` such that `p = \&(1 / (dot x x)) %* x`.
- The tactic `MESON_TAC[PROJL_TOTAL; point_tybij]` then uses the `MESON` automated reasoning tool, along with the theorem `PROJL_TOTAL` and `point_tybij`, to complete the proof.
- `PROJL_TOTAL` establishes the totality of line embedding, meaning that for every point `p`, there exists a line `l` such that `p mem l` where `mem` means membership in a set.
- `point_tybij` probably relates to the type bijection between points and vectors.

The key idea is that every point can be represented as the projection of some non-zero vector.

### Mathematical insight
This theorem establishes that the projection function `projp` covers the entire space of points. In other words, every point can be obtained by projecting some non-zero vector onto it. This is a crucial result for establishing the completeness of the geometric construction based on projections.

### Dependencies
- `projp` (definition of the projection function)
- `PROJL_TOTAL`
- `point_tybij`


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
The function `homop` applied to `p` is defined to be equal to `homol` applied to the result of the function `dest_point` applied to `p`.

### Informal sketch
The definition introduces `homop` as a composition of the functions `dest_point` and `homol`. There is nothing to prove. It simply defines one function in terms of others.
- The function `homop` takes an argument `p`.
- The function `dest_point` is applied to `p`, producing some intermediate result
- The function `homol` is applied to the result of `dest_point p`.

### Mathematical insight
This definition introduces a concise notation, `homop`, for the composition of the functions `dest_point` and `homol`. It is likely that this composition is frequently used, justifying the creation of a short-hand.

### Dependencies
- Definition: `dest_point`
- Definition: `homol`


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
For all `p`, it is the case that `homop p` is not equal to the vector `vec 0`, and `p` is equal to `projp(homop p)`.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `!p. ~(homop p = vec 0) /\ p = projp(homop p)`.
- Rewrite using the definition of `homop` (`homop_def`), unfolding the definition of `projp`, and using the theorem `point_tybij` to prove the statement. The theorem `point_tybij` likely establishes a bijection between points and vectors. Also, a theorem stating `p = mk_point l <=> dest_point p = l` which specifies the relationship between a point `p` and its corresponding vector representation `l` using `mk_point` and `dest_point `is used.
- Apply `MATCH_ACCEPT_TAC homol`. This suggests the proof uses a similar structure to a previously proven theorem named `homol`, likely involving geometric properties or transformations.

### Mathematical insight
The theorem establishes a fundamental property relating a point `p` to its image under the `homop` transformation and its projection `projp`. It states that the `homop` transformation never maps a point to the zero vector. It also shows that projecting the image of `p` under `homop` results in the original point `p`. This result could be related to the invertibility or specific geometric properties of the `homop` transformation.

### Dependencies
- Definitions: `homop_def`, `projp`
- Theorems: `point_tybij`


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
The vectors `x` and `y` are defined to be `parallel` if and only if their cross product `x cross y` is equal to the zero vector `vec 0`.

### Informal sketch
The definition directly introduces the concept of parallelism between two vectors based on the established definition of their cross product. The core idea is that two vectors are parallel if and only if their cross product results in the zero vector. Therefore, no actual proof is required, as it's definitional.

### Mathematical insight
This definition provides a standard algebraic characterization of parallel vectors. It leverages the cross product, which geometrically represents the area of the parallelogram spanned by the two vectors. If the vectors are parallel, this area collapses to zero, resulting in the zero vector. This definition is fundamental in linear algebra and geometry, providing a bridge between geometric intuition and algebraic manipulation.

### Dependencies
- Definition: `cross`
- Definition: `vec`


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
For all points `p` and all lines `l`, `p` lies on `l` if and only if the homogenization of `p` is orthogonal to the homogenization of `l`.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `!p l. p on l <=> orthogonal (homop p) (homol l)`.
- Expand the definitions of `homop` and `homol`.
- Expand the definition of `on` in terms of `projp` and `projl` exploiting `point_tybij`.
- Rewrite using `GSYM perpl_th` and `perpdir`.
- Apply `BINOP_TAC`.
- Finally, use meson to complete the proof, using `homol`, `homop`, and `direction_tybij`.

### Mathematical insight
This theorem connects a geometric relation ("a point lies on a line") to an algebraic relation ("the homogenization of the point is orthogonal to the homogenization of the line"). This is a fundamental result in projective geometry, allowing to leverage linear algebra to reason about geometric incidence relations.

### Dependencies
- Definitions: `homop`, `homol`, `on`, `projp`, `projl`, `perpdir`
- Theorems: `perpl_th`, `point_tybij`, `direction_tybij`


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
For all lines `l` and `l'`, `l` is equal to `l'` if and only if the homogeneous representation of `l` is parallel to the homogeneous representation of `l'`.

### Informal sketch
The proof proceeds as follows:
- Start by generalizing the variables `l` and `l'`.
- Expand the definition of `homol` on both sides of the equivalence.
- Rewrite using the properties of `projl` and the bijection between lines and pairs of reals (excluding (0,0)). This step relies on the theorem stating that two lines constructed from pairs are equal if and only if the pairs are equal.
- Rewrite based on the equivalence `PARDIRDIR_EQUIV`.
- Rewrite using the definitions of `pardir` and `parallel`.
- Use `MESON_TAC` with `homol` and `direction_tybij` to complete the proof, likely relying on the fact that the direction of a line is equivalent to its direction's homogeneous representation.

### Mathematical insight
This theorem establishes the equivalence between equality of lines and parallelism of their homogeneous representations. It connects the geometric notion of line equality to the algebraic notion of parallelism in the projective space, highlighting the relationship between lines and vectors through the `homol` representation. This is important because it provides a convenient way to verify the equality of lines using an algebraic condition on their homogeneous representations.

### Dependencies
- Definitions: `homol`, `parallel`, `pardir`, `projl`, `mk_line`
- Theorems: `fst`, `snd`, `line_tybij`, `PARDIRDIR_EQUIV`, `direction_tybij`


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
For any `p` and `p'`, `p` is equal to `p'` if and only if `parallel (homop p) (homop p')`.

### Informal sketch
The theorem states the equivalence between the equality of two points `p` and `p'` and the parallelism of their respective `homop` images.

- The proof begins by rewriting the expression using the definition of `homop` and the symmetric version of the theorem `EQ_HOMOL`.
- It then uses `MESON_TAC` with the theorem `point_tybij` to automatically prove the rest of the goal.

### Mathematical insight
The theorem `EQ_HOMOP` establishes a connection between point equality and parallelism of their `homop` images. This is a crucial property for reasoning about geometric equivalence and transformations.

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
For all vectors `x` in 3-dimensional real space, `x` is parallel to the homogeneous coordinate map of the projection `projl` of `x`.

### Informal sketch
The proof proceeds as follows:

- Start with the goal `!x. parallel x (homol(projl x))`.
- Rewrite using the definition of `parallel`.
- Perform case distinction on `x = vec 0`.
- If `x = vec 0`, rewrite using `CROSS_0`. Apply `homol` to `projl x` using the theorem that `homol` of any vector `v` is parallel to `v`.
- Discharge the assumption that `x` is a non-zero vector and split the discharged assumption into two conjuncts using `CONJUNCTS_THEN2 ASSUME_TAC MP_TAC`.
- Perform rewriting on the projection `projl` which replaces `projl x` by its definition (`CROSS(e1, (CROSS(x, e2)))`).
- Discharge the result using `dest_line` to obtain the direction.
- Rewrite using theorems involving `line_tybij` such as `dest_line(mk_line((||) l)) = (||) l`.
- Rewrite `PARDIR_EQUIV`, `pardir` and `direction_tybij` for reaching the conclusion, thus showing the statement holds for non-zero vectors `x` as well.

### Mathematical insight
This theorem establishes a fundamental property of the homogeneous coordinate map (`homol`) in relation to the projection `projl` and the parallelism of vectors. It demonstrates that the homogeneous coordinate representation of the projection of a vector `x` is parallel to `x` itself. This relationship is crucial in projective geometry and computer vision, where homogeneous coordinates are used to represent points and lines at infinity.

### Dependencies
- `parallel`
- `CROSS_0`
- `homol`
- `projl`
- `fst line_tybij`
- `snd line_tybij`
- `dest_line`
- `mk_line`
- `PARDIR_EQUIV`
- `pardir`
- `direction_tybij`
- `MESON`


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
For all `x`, `parallel x (homop(projp x))` holds. That is, for any `x`, `x` is parallel to the homogeneous representation of the projective representation of `x`.

### Informal sketch
The proof proceeds by:
- Rewriting using the definition of `homop`, the definition of `projp`, and rewriting using `point_tybij`.
- Rewriting using the theorem `PARALLEL_PROJL_HOMOL`.

### Mathematical insight
This theorem establishes a relationship between a point `x`, its projective representation `projp x`, and the homogeneous representation `homop` of that projective representation. It asserts that `x` is parallel to `homop(projp x)`. This connection is important for relating points in the original space to their representations in projective and homogeneous coordinates and for reasoning about geometric relationships in these spaces.

### Dependencies
- Definitions: `homop_def`, `projp`
- Theorems: `PARALLEL_PROJL_HOMOL`, `point_tybij`


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
For all vectors `x` in `real^3`, if `x` is not the zero vector, then there exists a real number `a` such that `a` is not equal to 0 and the homothety of the parallel projection `projp x` is equal to `a % x`.

### Informal sketch
The proof proceeds as follows:
- Assume `x` is not the zero vector.
- Use `PARALLEL_PROJP_HOMOP` to show that `projp x` is a homothety.
- Rewrite using `parallel`, `CROSS_EQ_0` and `COLLINEAR_LEMMA`.
- Perform a case split on whether `x = vec 0`.
- Apply `homop` definition and `MONO_EXISTS` to introduce a constant `c:real`.
- Perform a case split on whether `c = &0`.
- Apply `homop` definition and simplify using `VECTOR_MUL_LZERO`.

### Mathematical insight
This theorem establishes that the homothety of the parallel projection `projp x` has an explicit representation in terms of a scalar multiple of the vector `x`. This provides a concrete way to compute or reason about the homothety associated with the parallel projection. The theorem essentially states that the homothety factor is collinear with the projected vector, after excluding the trivial case where the vector `x` is zero.

### Dependencies
- Definitions: `parallel`, `homop`
- Theorems: `CROSS_EQ_0`, `COLLINEAR_LEMMA`, `PARALLEL_PROJP_HOMOP`, `VECTOR_MUL_LZERO`

### Porting notes (optional)
- The tactic `ASM_CASES_TAC` is used for case splitting, which is supported in most provers.
- The tactic `MATCH_MP_TAC` is used for applying a theorem whose hypothesis matches an assumption. This is widely supported, although the specific tactic name may vary.
- Theorems like `VECTOR_MUL_LZERO` may need to be proven separately in a new environment, depending on the available library.


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
The `bracket` of three points `a`, `b`, and `c` is defined as the determinant of the matrix whose columns are the homogeneous coordinates of the points `a`, `b`, and `c`.

### Informal sketch
- Define `bracket[a; b; c]` as the determinant of a matrix.
- The columns of this matrix are formed by applying the `homop` function to each of the points `a`, `b`, and `c`, resulting in their homogeneous coordinates.
- The `det` function then calculates the determinant of this matrix, yielding the bracket value.

### Mathematical insight
The bracket operation calculates the determinant of the matrix formed by the homogeneous coordinates of three points. In the context of projective geometry, the sign of the bracket indicates the orientation of the three points. A zero bracket means the points are collinear. This definition connects geometric concepts (collinearity, orientation) with algebraic computations (determinants).

### Dependencies
- Definitions:
  - `det` (determinant)
  - `vector` (vector formation)
  - `homop` (homogeneous coordinates)


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
A set `s` of points is collinear if and only if there exists a line `l` such that for all points `p`, if `p` is in `s`, then `p` lies on `l`.

### Informal sketch
The definition `COLLINEAR s` introduces the concept of collinearity for a set of points `s`. It asserts that a set of points is collinear if there exists a line such that every point in the set lies on that line.

*   The definition begins with the quantifier `?l`, which asserts the existence of a line `l`.
*   The core of the definition is a universal quantifier `!p` ranging over all points `p`.
*   For each point `p`, if `p` is an element of the set `s` (expressed as `p IN s`), then `p` must lie on the line `l` (expressed as `p on l`).

### Mathematical insight
This definition captures the standard mathematical notion of collinearity: a set of points is collinear if all the points lie on the same line. The definition formalizes this notion using quantifiers and the membership relation `IN` to specify the set of points and the relation `on` to express that a point lies on a line. This definition serves as a foundation for proving theorems about collinear points and lines in the HOL Light geometry formalization.

### Dependencies
*   `IN` (set membership relation)
*   `on` (point lies on a line relation)


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
For all `a`, the set consisting only of `a` is collinear.

### Informal sketch
The proof proceeds as follows:
- Rewrite the goal using the definition of `COLLINEAR`, which states that a set is collinear if all pairs of its elements are collinear.
- Instantiate the universally quantified `FORALL_IN_INSERT` theorem, and the theorem `NOT_IN_EMPTY`.
- Apply `MESON_TAC`, using `AXIOM_1` and `AXIOM_3`, to complete the proof. Note that `AXIOM_1` and `AXIOM_3` likely refer to axioms/theorems that establish the collinearity of sets with zero or one points, respectively.

### Mathematical insight
This theorem states a basic but important property of collinearity: a set containing only one point is trivially collinear. This is a foundational result upon which more complex collinearity theorems can be built.

### Dependencies

Definitions:
- `COLLINEAR`

Theorems:
- `FORALL_IN_INSERT`
- `NOT_IN_EMPTY`
- `AXIOM_1`
- `AXIOM_3`


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
- Case 1: `a` is equal to `b`. In this case, the set `{a, b}` is equal to the singleton set `{a}`, and singleton sets are collinear by the theorem `COLLINEAR_SINGLETON`.
- Case 2: `a` is not equal to `b`. In this case, we rewrite the condition `COLLINEAR{a, b}` using the definition of `COLLINEAR` and the properties of set membership (`FORALL_IN_INSERT`, `NOT_IN_EMPTY`), which essentially reduces to showing that for all points `x` in `{a,b}`, `COLLINEAR{a,b}` holds, which is proven using `AXIOM_1`.

### Mathematical insight
This theorem establishes a fundamental property of collinearity: any pair of points trivially forms a collinear set. This is a basic geometric fact.

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
For any points `a`, `b`, and `c`, the points `a`, `b`, and `c` are collinear if and only if there exists a line `l` such that `a` lies on `l`, `b` lies on `l`, and `c` lies on `l`.

### Informal sketch
The proof demonstrates the biconditional relationship defining collinearity for three points.

*   The theorem states that three points are collinear if and only if there exists a line on which they all lie.
*   The proof uses rewriting with the definition of `COLLINEAR` to expand the left-hand side of the equivalence. `COLLINEAR` is defined as a set of three points being collinear if and only if there exists a line that contains all three points.
*   `FORALL_IN_INSERT` is used to rewrite quantifications over sets to explicit quantifications over elements being inserted in it.
*   `NOT_IN_EMPTY` likely simplifies cases where the set is empty.

### Mathematical insight
This theorem formalizes the intuitive geometric notion of collinearity: three points are collinear if they lie on the same line. It provides a formal definition that can be used in proofs and constructions within the formal system.

### Dependencies
- Definitions:
    - `COLLINEAR`
- Theorems:
    - `FORALL_IN_INSERT`
    - `NOT_IN_EMPTY`


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
For all points `p1`, `p2`, and `p3`, the points `p1`, `p2`, and `p3` are collinear if and only if `bracket[p1; p2; p3]` equals 0.

### Informal sketch
The proof proceeds as follows:
- Start by expanding the definitions of `COLLINEAR`, `bracket`, and `ON_HOMOL` and using `LEFT_IMP_EXISTS_THM`. Also use `homol`.
- Simplify determinant, orthogonality, dot product, vector representation, and coordinate representations. `REAL_RING` is used to perform simplifications in real arithmetic.
- Perform case split on whether `p1` equals `p2`.
  - If `p1` equals `p2`, use the fact that two identical points constitute a collinear set and complete the proof.
  - If `p1` does not equal `p2`, rewrite using definitions of `parallel`, `COLLINEAR_TRIPLE`, `bracket`, `EQ_HOMOP`, and `ON_HOMOL`.
  - Prove the existence of a line using definition based on a cross product of homogeneous coordinates of the points.
  - Apply lemma stating that if three vectors are orthogonal to `x` and `x cross y = vec 0 /\ ~(x = vec 0)` then those vectors are orthogonal to `y`.
  - Prove the requirements of the lemma with existing assumptions.
  - Manipulate the expression by cross product and dot product identities.

The proof uses a helper lemma stating that if `x cross y = vec 0 /\ ~(x = vec 0)` and `a`, `b`, `c` are orthogonal to `x`, then `a`, `b`, `c` are orthogonal to `y`.

### Mathematical insight
This theorem links the geometric concept of collinearity of three points to an algebraic condition involving the `bracket` function, which is presumably related to determinants or cross products of the vectors representing the points. This kind of result is useful for translating geometric reasoning into algebraic manipulation, and vice versa, for the purpose of automation.

### Dependencies
- `COLLINEAR_TRIPLE`
- `bracket`
- `ON_HOMOL`
- `LEFT_IMP_EXISTS_THM`
- `homol`
- `DET_3`
- `orthogonal`
- `DOT_3`
- `VECTOR_3`
- `CART_EQ`
- `DIMINDEX_3`
- `FORALL_3`
- `VEC_COMPONENT`
- `INSERT_AC`
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
The proof makes heavy use of rewriting and simplification tactics, particularly `REAL_RING` for real arithmetic. Porting to another theorem prover may require adapting these tactics or using alternative methods for algebraic simplification. The lemma stating a property of orthogonal vectors may need to be proved separately in the target prover, or an existing library result may be applicable.


---

## BRACKET_SWAP,BRACKET_SHUFFLE

### Name of formal statement
- BRACKET_SWAP
- BRACKET_SHUFFLE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let BRACKET_SWAP,BRACKET_SHUFFLE = (CONJ_PAIR o prove)
 (`bracket[x;y;z] = --bracket[x;z;y] /\
   bracket[x;y;z] = bracket[y;z;x] /\
   bracket[x;y;z] = bracket[z;x;y]`,
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING);;
```
### Informal statement
The theorem proves the conjunction of three properties concerning the ternary function `bracket[x; y; z]`:
1. `bracket[x; y; z]` is equal to `--bracket[x; z; y]`.
2. `bracket[x; y; z]` is equal to `bracket[y; z; x]`.
3. `bracket[x; y; z]` is equal to `bracket[z; x; y]`.

### Informal sketch
- The proof proceeds by rewriting the initial goal using the definition of the `bracket` function (using `REWRITE_TAC[bracket]`).
- It then applies a decision procedure or simplification rule for fields or rings (`CONV_TAC REAL_RING`), using the commutativity and associativity of multiplication and addition, as well as the definition of additive inverse.
- The tactics `DET_3` and `VECTOR_3` are likely used to manage assumptions or address specific details related to the vector or determinant properties of the `bracket` function.
- The `CONJ_PAIR` applies proof to both sides of the conjunction.

### Mathematical insight
The theorem establishes basic identities that allow the arguments of the `bracket` function to be permuted in various ways, possibly up to a sign change. These identities are fundamental for simplifying expressions involving the `bracket` function and for reasoning about its algebraic properties. The identities reflect symmetries and anti-symmetries of the bracket operation under argument permutations.

### Dependencies
- Definitions: `bracket`
- Theorems: `DET_3`, `VECTOR_3`
- Tactics: `REWRITE_TAC`, `CONV_TAC`, `REAL_RING`, `CONJ_PAIR`


---

## BRACKET_SWAP_CONV

### Name of formal statement
BRACKET_SWAP_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let BRACKET_SWAP_CONV =
  let conv = GEN_REWRITE_CONV I [BRACKET_SWAP] in
  fun tm -> let th = conv tm in
            let tm' = rand(rand(concl th)) in
            if term_order tm tm' then th else failwith "BRACKET_SWAP_CONV";;
```

### Informal statement
The function `BRACKET_SWAP_CONV` takes a term `tm` as input. It applies the conversion `GEN_REWRITE_CONV I [BRACKET_SWAP]` to `tm`, resulting in a theorem `th`. It then extracts the term `tm'` from the conclusion of `th` by taking the right-hand side of the right-hand side. If `tm` is less than or equal to `tm'` according to `term_order`, then the theorem `th` is returned. Otherwise, the function fails.

### Informal sketch
The conversion `BRACKET_SWAP_CONV` aims to apply the `BRACKET_SWAP` rewrite rule and ensure that the resulting term is ordered in some way.
- First, a generic rewrite conversion `conv` is built using `GEN_REWRITE_CONV I [BRACKET_SWAP]`.
- Given a term `tm`, the rewrite conversion `conv` is applied, producing a theorem `th`. The conclusion of this theorem has the form `tm = tm'`, where `tm'` is produced by rewriting `tm` via `BRACKET_SWAP`.
- `rand(rand(concl th))` extracts the term `tm'` from the right-hand side of the equation in the conclusion of `th`.
- A comparison is made between the original term `tm` and the rewritten term `tm'` using `term_order tm tm'`.
- If `term_order tm tm'` is true (meaning `tm` is less than or equal to `tm'` according to some term ordering), the theorem `th` is returned; otherwise, the conversion fails, indicating that the swap resulted in a term that is not greater than the original term. This ordering check is probably used to prevent infinite loops, by ensuring the conversion makes progress.

### Mathematical insight
This conversion applies a `BRACKET_SWAP` rewrite rule but also incorporates an ordering check to potentially prevent infinite rewriting loops. The `term_order` check ensures that the transformation moves towards a canonical form according to the defined term ordering; if the swap results in a term that is not "larger" than the original term, the conversion fails. The function is intended to rewrite terms using `BRACKET_SWAP` only if this rewriting "simplifies" the term according to the term order.

### Dependencies
- `BRACKET_SWAP`
- `GEN_REWRITE_CONV`
- `term_order`


---

## DESARGUES_DIRECT

### Name of formal statement
DESARGUES_DIRECT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DESARGUES_DIRECT = prove
 (`~COLLINEAR {A',B,S} /\
   ~COLLINEAR {A,P,C} /\
   ~COLLINEAR {A,P,R} /\
   ~COLLINEAR {A,C,B} /\
   ~COLLINEAR {A,B,R} /\
   ~COLLINEAR {C',P,A'} /\
   ~COLLINEAR {C',P,B} /\
   ~COLLINEAR {C',P,B'} /\
   ~COLLINEAR {C',A',S} /\
   ~COLLINEAR {C',A',B'} /\
   ~COLLINEAR {P,C,A'} /\
   ~COLLINEAR {P,C,B} /\
   ~COLLINEAR {P,A',R} /\
   ~COLLINEAR {P,B,Q} /\
   ~COLLINEAR {P,Q,B'} /\
   ~COLLINEAR {C,B,S} /\
   ~COLLINEAR {A',Q,B'}
   ==> COLLINEAR {P,A',A} /\
       COLLINEAR {P,B,B'} /\
       COLLINEAR {P,C',C} /\
       COLLINEAR {B,C,Q} /\
       COLLINEAR {B',C',Q} /\
       COLLINEAR {A,R,C} /\
       COLLINEAR {A',C',R} /\
       COLLINEAR {B,S,A} /\
       COLLINEAR {A',S,B'}
       ==> COLLINEAR {Q,S,R}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_BRACKET] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(bracket[P;A';A] = &0
     ==> bracket[P;A';R] * bracket[P;A;C] =
         bracket[P;A';C] * bracket[P;A;R]) /\
    (bracket[P;B;B'] = &0
     ==> bracket[P;B;Q] * bracket[P;B';C'] =
         bracket[P;B;C'] * bracket[P;B';Q]) /\
    (bracket[P;C';C] = &0
     ==> bracket[P;C';B] * bracket[P;C;A'] =
         bracket[P;C';A'] * bracket[P;C;B]) /\
    (bracket[B;C;Q] = &0
     ==> bracket[B;C;P] * bracket[B;Q;S] =
         bracket[B;C;S] * bracket[B;Q;P]) /\
    (bracket[B';C';Q] = &0
     ==> bracket[B';C';A'] * bracket[B';Q;P] =
         bracket[B';C';P] * bracket[B';Q;A']) /\
    (bracket[A;R;C] = &0
     ==> bracket[A;R;P] * bracket[A;C;B] =
         bracket[A;R;B] * bracket[A;C;P]) /\
    (bracket[A';C';R] = &0
     ==> bracket[A';C';P] * bracket[A';R;S] =
         bracket[A';C';S] * bracket[A';R;P]) /\
    (bracket[B;S;A] = &0
     ==> bracket[B;S;C] * bracket[B;A;R] =
         bracket[B;S;R] * bracket[B;A;C]) /\
    (bracket[A';S;B'] = &0
     ==> bracket[A';S;C'] * bracket[A';B';Q] =
         bracket[A';S;Q] * bracket[A';B';C'])`
  MP_TAC THENL
   [REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC(TAUT
   `(c ==> d ==> b ==> e) ==> ((a ==> b) /\ c ==> a /\ d ==> e)`)) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  REPEAT(ONCE_REWRITE_TAC[IMP_IMP] THEN
         DISCH_THEN(MP_TAC o MATCH_MP (REAL_RING
          `a = b /\ x:real = y ==> a * x = b * y`))) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[BRACKET_SHUFFLE] THEN
  CONV_TAC(ONCE_DEPTH_CONV BRACKET_SWAP_CONV) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; REAL_NEG_EQ_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `!b. (a ==> b) /\ (b ==> c) ==> a ==> c`) THEN
  EXISTS_TAC `bracket[B;Q;S] * bracket[A';R;S] =
              bracket[B;R;S] * bracket[A';Q;S]` THEN
  CONJ_TAC THENL [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING);;
```

### Informal statement
Given points A, B, S, A', P, C, R, C', B', Q in a plane, if:
- A', B, S are not collinear, and
- A, P, C are not collinear, and
- A, P, R are not collinear, and
- A, C, B are not collinear, and
- A, B, R are not collinear, and
- C', P, A' are not collinear, and
- C', P, B are not collinear, and
- C', P, B' are not collinear, and
- C', A', S are not collinear, and
- C', A', B' are not collinear, and
- P, C, A' are not collinear, and
- P, C, B are not collinear, and
- P, A', R are not collinear, and
- P, B, Q are not collinear, and
- P, Q, B' are not collinear, and
- C, B, S are not collinear, and
- A', Q, B' are not collinear,
and if:
- P, A', A are collinear, and
- P, B, B' are collinear, and
- P, C', C are collinear, and
- B, C, Q are collinear, and
- B', C', Q are collinear, and
- A, R, C are collinear, and
- A', C', R are collinear, and
- B, S, A are collinear, and
- A', S, B' are collinear,
then:
- Q, S, R are collinear.

### Informal sketch
The proof proceeds as follows:

- It imports `COLLINEAR_BRACKET`, which expresses collinearity using the bracket function (determinant of a matrix of coordinates).
- The core idea is to express all collinearity conditions in terms of the bracket function.
- It uses assumptions about collinearity to rewrite bracket expressions. Specifically, it establishes several equations that relate products of brackets, based on the assumption that `bracket[P;A';A] = 0`, `bracket[P;B;B'] = 0`, `bracket[P;C';C] = 0`, `bracket[B;C;Q] = 0`, `bracket[B';C';Q] = 0`, `bracket[A;R;C] = 0`, `bracket[A';C';R] = 0`, `bracket[B;S;A] = 0`, and `bracket[A';S;B'] = 0`.
- The proof introduces a subgoal that captures all the required relationships between products of brackets. It proves that assuming some bracket expressions are zero implies that other bracket expressions can be related by multiplication.
- It rewrites using definitions of `bracket`, `DET_3` (determinant of a 3x3 matrix), and `VECTOR_3` (representation of a point as a vector).
- It uses ring tactics to simplify the arithmetic expressions.
- It uses tautological reasoning to simplify logical implications, iteratively eliminating assumptions.
- The proof uses bracket shuffling and swapping to rearrange the terms in the bracket expressions.
- The proof introduces an existential variable `bracket[B;Q;S] * bracket[A';R;S] = bracket[B;R;S] * bracket[A';Q;S]`.

### Mathematical insight
The theorem is the direct Desargues' theorem, a fundamental result in projective geometry. It states that if two triangles are perspective from a point, then they are perspective from a line. The proof uses the bracket function (or Cayley bracket) to represent collinearity, which allows the theorem to be proven by algebraic manipulation. The degenerate conditions ensure that none of the points coincide or that the lines joining them are parallel in a way that would trivialize the calculation.

### Dependencies
- `COLLINEAR_BRACKET`
- `bracket`
- `DET_3`
- `VECTOR_3`
- `BRACKET_SHUFFLE`
- `BRACKET_SWAP_CONV`
- `REAL_MUL_ASSOC`
- `REAL_MUL_LNEG`
- `REAL_MUL_RNEG`
- `REAL_NEG_NEG`
- `REAL_NEG_EQ_0`
- `REAL_RING`

### Porting notes (optional)
- The heavy use of rewriting and ring tactics suggests that a proof assistant with good automation for algebraic simplification will be beneficial.
- The `COLLINEAR_BRACKET` definition or its equivalent needs to be established first.
- The manipulations of determinants might require some care depending on how determinants are defined in the target proof assistant.


---

