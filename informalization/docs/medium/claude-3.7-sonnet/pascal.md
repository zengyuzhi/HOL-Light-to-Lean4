# pascal.ml

## Overview

Number of statements: 64

This file formalizes Pascal's hexagon theorem for both projective and affine planes in HOL Light. It builds upon the multivariate cross product infrastructure to prove that if six points lie on a conic section, then the three pairs of opposite sides of the hexagon meet in three collinear points. The file provides the necessary geometric definitions, constructions, and theorems that establish this classic result in projective geometry, including specialized versions for the affine case.

## NORMAL_EXISTS

### NORMAL_EXISTS
- `NORMAL_EXISTS`

### Type of the formal statement
- theorem

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
For any two vectors $u, v \in \mathbb{R}^3$, there exists a non-zero vector $w$ that is orthogonal to both $u$ and $v$. Formally:

$$\forall u,v \in \mathbb{R}^3. \exists w. w \neq \vec{0} \land \text{orthogonal}(u,w) \land \text{orthogonal}(v,w)$$

### Informal proof
The proof establishes that in $\mathbb{R}^3$, any two vectors have a non-zero normal vector in common:

* First, we rewrite the orthogonality condition using symmetry (`ORTHOGONAL_SYM`), allowing us to apply results about orthogonal subspaces.

* We apply the theorem `ORTHOGONAL_TO_SUBSPACE_EXISTS` to the set $\{u, v\}$, which states that there exists a non-zero vector orthogonal to a subspace as long as the dimension of the subspace is strictly less than the dimension of the ambient space.

* We need to show that the dimension of the subspace spanned by $\{u, v\}$ is at most 2, which is less than the dimension of $\mathbb{R}^3$ (which is 3).

* The dimension of a subspace is bounded by the cardinality of any spanning set, in this case $|\{u, v\}|$.

* The cardinality of $\{u, v\}$ is at most 2 (it equals 2 if $u \neq v$, and 1 if $u = v$).

* Since 2 < 3 (the dimension of $\mathbb{R}^3$), we can apply the theorem to conclude that there exists a non-zero vector orthogonal to both $u$ and $v$.

### Mathematical insight
This theorem captures a fundamental geometric property of $\mathbb{R}^3$: any two vectors determine a plane (or a line if they're parallel), and there always exists a direction perpendicular to this plane. This result is directly related to the cross product operation in $\mathbb{R}^3$, which produces a vector orthogonal to two given vectors.

The theorem is essential for many applications in 3D geometry, including:
- Finding normal vectors to planes
- Defining the cross product geometrically
- Constructing orthogonal coordinate systems

In vector calculus and differential geometry, this property is crucial for defining normal vectors to surfaces and working with orientations in 3D space.

### Dependencies
#### Theorems
- `ORTHOGONAL_SYM`: States that orthogonality is symmetric
- `ORTHOGONAL_TO_SUBSPACE_EXISTS`: States that there exists a non-zero vector orthogonal to a subspace if its dimension is less than the ambient space
- `DIM_LE_CARD`: Dimension of a span is bounded by cardinality of the spanning set
- `CARD_CLAUSES`: Properties of cardinality of finite sets

### Porting notes
When porting this theorem:
- Ensure the target system has a similar notion of orthogonality for vectors
- Check that the dimension of $\mathbb{R}^3$ is properly defined
- The proof relies on dimensionality arguments that might need different approaches in systems with different libraries for linear algebra

---

## direction_tybij

### direction_tybij
- new_type_definition "direction" ("mk_dir","dest_dir")

### Type of the formal statement
- new_type_definition

### Formal Content
```ocaml
let direction_tybij = new_type_definition "direction" ("mk_dir","dest_dir")
 (MESON[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] `?x:real^3. ~(x = vec 0)`);;
```

### Informal statement
The type definition `direction` creates a new type that represents directions in 3D space. The type is defined by establishing a bijection between the new type `direction` and the subset of $\mathbb{R}^3$ consisting of non-zero vectors.

The statement defines:
- `direction` as the new type
- `mk_dir` as the function that maps from non-zero vectors in $\mathbb{R}^3$ to the `direction` type
- `dest_dir` as the function that maps from the `direction` type to non-zero vectors in $\mathbb{R}^3$

The existence of a non-zero vector in $\mathbb{R}^3$ is established using the theorems `BASIS_NONZERO`, `LE_REFL`, and `DIMINDEX_GE_1`.

### Informal proof
This is a type definition, not a theorem, so it doesn't have a traditional proof. However, to create a new type in HOL Light, one must prove that the representing set is non-empty.

The statement proves that there exists a non-zero vector in $\mathbb{R}^3$ (i.e., $\exists x:\mathbb{R}^3, x \neq \vec{0}$) using the following facts:
- `BASIS_NONZERO`: The basis vectors in a Euclidean space are non-zero
- `LE_REFL`: The relation $\leq$ is reflexive
- `DIMINDEX_GE_1`: The dimension of any Euclidean space is at least 1

The `MESON` tactic automatically establishes the existence of a non-zero vector in $\mathbb{R}^3$ using these facts.

### Mathematical insight
This type definition introduces a representation of geometric directions in 3D space. A direction is conceptually different from a vector - it represents only the orientation in space without magnitude.

By defining directions as equivalence classes of non-zero vectors, we can separate the concept of "where" something is pointing from "how far" it points. This is useful in various geometric applications, such as ray tracing, computer graphics, and computational geometry.

The bijection between the new type and non-zero vectors in $\mathbb{R}^3$ ensures that every direction has a unique representation as a non-zero vector, and every non-zero vector corresponds to some direction.

### Dependencies
- `BASIS_NONZERO`: Theorem stating that basis vectors in a Euclidean space are non-zero
- `LE_REFL`: Theorem stating that the relation $\leq$ is reflexive
- `DIMINDEX_GE_1`: Theorem stating that the dimension of any Euclidean space is at least 1

### Porting notes
When porting this definition to other proof assistants:
1. You'll need to create a new type representing directions in 3D space
2. Ensure that your definition establishes a bijection with non-zero vectors in $\mathbb{R}^3$
3. In systems with dependent types (like Coq or Lean), you might be able to define this more directly as the subset type of non-zero vectors
4. In Isabelle/HOL, you can use the `typedef` mechanism which is similar to HOL Light's `new_type_definition`
5. The construction of the required non-empty set might differ based on the available theorems about vectors in the target system

---

## perpdir

### perpdir
- perpdir

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let perpdir = new_definition
 `x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)`;;
```

### Informal statement
This definition introduces a relation `_|_` between two directions, where `x _|_ y` means that the directions `x` and `y` are perpendicular (orthogonal) to each other.

Specifically, the definition states that for any two directions `x` and `y`:
$$x \perp y \iff \text{orthogonal}(\text{dest\_dir}(x), \text{dest\_dir}(y))$$

where `dest_dir` extracts the underlying vector representation of a direction, and `orthogonal` determines whether two vectors are perpendicular to each other.

### Informal proof
No proof is provided as this is a definition.

### Mathematical insight
This definition introduces a perpendicularity relation between directions, which is foundational for geometric reasoning. By defining perpendicularity in terms of the orthogonality of the underlying vectors, the definition bridges the abstract concept of directions with their concrete vector representations.

Perpendicularity is a key geometric relationship that is essential for many theorems in Euclidean geometry. This definition allows for formal reasoning about perpendicular directions in a proof assistant context.

### Dependencies
- `orthogonal`: A predicate that determines if two vectors are orthogonal (perpendicular) to each other.
- `dest_dir`: A function that extracts the vector representation from a direction.

### Porting notes
When porting this definition:
1. Ensure that the `orthogonal` relation and the `dest_dir` function are already defined in your target system.
2. Be aware that in some proof assistants, you might need to explicitly state the types of `x` and `y` as directions.
3. Consider how the notation `_|_` will be represented in your target system; some proof assistants might require special syntax declarations for custom infix operators.

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
Two directions $x$ and $y$ are parallel, denoted by $x \parallel y$, if and only if their cross product is the zero vector, i.e., $\text{dest\_dir}(x) \times \text{dest\_dir}(y) = \vec{0}$.

### Informal proof
This is a definition, so there is no proof to translate.

### Mathematical insight
This definition formalizes the concept of parallel vectors or directions in 3D space. Two vectors are parallel when their cross product is the zero vector, which occurs precisely when they are scalar multiples of each other (or one of them is zero).

In HOL Light's formalization, the `dest_dir` function extracts the actual vector from a direction, and then the definition checks if these vectors are parallel using the standard cross product criterion. This definition allows for the concise expression of parallelism without needing to work with scalar multiples directly.

Note that while in general mathematics, parallel vectors can include cases where one or both vectors are zero, the typical context of `dest_dir` suggests this definition is being applied to non-zero vectors representing directions in space.

### Dependencies
#### Definitions:
- `cross`: The cross product of two vectors in $\mathbb{R}^3$.

### Porting notes
When porting this definition, ensure that the underlying representation of directions in the target system is compatible. If the target system doesn't have a dedicated "direction" type separate from vectors, you might need to adapt the definition accordingly, possibly by explicitly requiring non-zero vectors or by using normalization.

---

## DIRECTION_CLAUSES

### DIRECTION_CLAUSES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DIRECTION_CLAUSES = prove
 (`((!x. P(dest_dir x)) <=> (!x. ~(x = vec 0) ==> P x)) /\
   ((?x. P(dest_dir x)) <=> (?x. ~(x = vec 0) /\ P x))`,
  MESON_TAC[direction_tybij]);;
```

### Informal statement
This theorem establishes equivalences for universally and existentially quantified statements involving `dest_dir`:

1. For all $x$, $P(\text{dest\_dir}(x))$ if and only if for all $x \neq \vec{0}$, $P(x)$ holds.
2. There exists an $x$ such that $P(\text{dest\_dir}(x))$ if and only if there exists an $x \neq \vec{0}$ such that $P(x)$ holds.

Where `dest_dir` is a function that extracts a vector from a direction.

### Informal proof
The proof is completed using the `MESON_TAC` tactic with the theorem `direction_tybij`.

This is a straightforward application of the type bijection properties established in `direction_tybij`. Since `direction_tybij` establishes that `dest_dir` forms a bijection between its domain and non-zero vectors, quantification over elements in the domain of `dest_dir` is equivalent to quantification over non-zero vectors.

### Mathematical insight
This theorem provides convenient rewriting rules for handling quantifiers over directions. It bridges the gap between statements about directions and statements about non-zero vectors.

The key insight is that directions are essentially non-zero vectors (typically normalized or considered up to scalar multiplication), and this theorem formalizes how to translate logical statements involving directions to equivalent statements about non-zero vectors.

These conversion rules are essential for simplifying theorems in vector geometry, particularly when working with directions and angles.

### Dependencies
- `direction_tybij`: Establishes that `dest_dir` forms a bijection between directions and non-zero vectors.

### Porting notes
When porting this theorem, ensure that the representation of directions in the target system is compatible with HOL Light's representation. In HOL Light, directions appear to be a separate type with a bijection to non-zero vectors. Other systems might represent directions differently, such as normalized vectors or equivalence classes of vectors.

---

## [PARDIR_REFL;

### PARDIR_REFL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let [PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS] = (CONJUNCTS o prove)
 (`(!x. x || x) /\
   (!x y. x || y <=> y || x) /\
   (!x y z. x || y /\ y || z ==> x || z)`,
  REWRITE_TAC[pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;
```

### Informal statement
This theorem states that the parallel direction relation `||` is reflexive:
$\forall x. x \parallel x$

This is the first part of a conjunction that establishes the full equivalence relation properties of the parallel direction relation.

### Informal proof
The proof of this theorem, along with the symmetry and transitivity properties (PARDIR_SYM and PARDIR_TRANS), is accomplished by:

1. First, the theorems are expressed as a conjunction of three properties:
   - Reflexivity: $\forall x. x \parallel x$
   - Symmetry: $\forall x,y. x \parallel y \Leftrightarrow y \parallel x$
   - Transitivity: $\forall x,y,z. x \parallel y \wedge y \parallel z \Rightarrow x \parallel z$

2. The proof utilizes:
   - The definition of the parallel direction relation (`pardir`)
   - The properties of direction vectors established in `DIRECTION_CLAUSES`
   - The tactic `VEC3_TAC` which handles vector arithmetic in 3D space

The reflexivity property follows directly from the definition of parallel directions: two vectors are parallel if one is a scalar multiple of the other. Since any vector is a scalar multiple of itself (with scalar = 1), the reflexivity property holds.

### Mathematical insight
The parallel direction relation (`||`) is an equivalence relation on vectors, which is a fundamental concept in vector spaces. This theorem establishes the reflexivity property of this relation.

In vector geometry, parallelism is a key concept that partitions the set of vectors into equivalence classes based on their directions. Two vectors are parallel if they point in the same or exactly opposite directions, which mathematically means one is a scalar multiple of the other.

The reflexivity property (`PARDIR_REFL`) specifically confirms the intuitive notion that any vector is parallel to itself.

### Dependencies
- `pardir`: Definition of the parallel direction relation
- `DIRECTION_CLAUSES`: Theorems establishing basic properties of directions
- `VEC3_TAC`: Tactic for handling 3D vector arithmetic

### Porting notes
When porting this theorem to another system:
1. Ensure that the parallel direction relation is defined first, typically as vectors being scalar multiples of each other
2. The proof may require different tactics depending on the system's automation capabilities for vector arithmetic
3. In systems with rich vector libraries, this property might be derivable automatically from more general theorems about vector spaces

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
For any parallel vectors $x$ and $y$, the statement asserts that:
$$(||) x = (||) y \iff x || y$$

This means that two equivalence classes of parallel vectors (represented by the function $(||)$) are equal if and only if the vectors $x$ and $y$ are parallel.

### Informal proof
The proof follows in two main steps:

- First, we use `REWRITE_TAC[FUN_EQ_THM]` to reduce function equality to extensional equality. This transforms the goal to show that $\forall z. ((||) x)(z) = ((||) y)(z) \iff x || y$.

- Then, we use `MESON_TAC` with the theorems `PARDIR_REFL` (parallelism reflexivity), `PARDIR_SYM` (parallelism symmetry), and `PARDIR_TRANS` (parallelism transitivity) to complete the proof. The automated theorem prover handles the logical reasoning that shows the equivalence relation properties imply the desired result.

The key insight is that since parallelism is an equivalence relation (it's reflexive, symmetric, and transitive), two vectors generate the same equivalence class if and only if they are parallel to each other.

### Mathematical insight
This theorem establishes the fundamental connection between the equivalence classes of parallel vectors and the parallelism relation itself. It confirms that the function $(||)$ correctly maps vectors to their equivalence classes under the parallelism relation.

In projective geometry and vector spaces, this result is important because it shows that the quotient space formed by this equivalence relation is well-defined. Each equivalence class consists precisely of all vectors parallel to a given vector, which is essential for constructing projective spaces from vector spaces.

### Dependencies
- `PARDIR_REFL` - Reflexivity of the parallelism relation
- `PARDIR_SYM` - Symmetry of the parallelism relation
- `PARDIR_TRANS` - Transitivity of the parallelism relation
- `FUN_EQ_THM` - Extensional equality of functions

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the parallelism relation and its properties (reflexivity, symmetry, transitivity) are already defined
- The function $(||)$ should be properly defined as mapping a vector to its equivalence class
- The extensional equality of functions might be handled differently in other systems

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
For any two direction vectors $p$ and $p'$, if they are not parallel (i.e., $\neg(p \parallel p')$), then there exists a direction vector $l$ such that:
1. $p$ is perpendicular to $l$ (i.e., $p \perp l$)
2. $p'$ is perpendicular to $l$ (i.e., $p' \perp l$)
3. For any other direction vector $l'$, if $p \perp l'$ and $p' \perp l'$, then $l'$ is parallel to $l$ (i.e., $l' \parallel l$)

### Informal proof
The proof establishes the existence of a direction vector perpendicular to both given non-parallel vectors.

- First, we rewrite the perpendicularity relation (`_|_`), parallelism relation (`||`), and other direction-related properties using their definitions.
- Then apply the `NORMAL_EXISTS` theorem, which states that for any two non-parallel vectors, there exists a vector perpendicular to both of them.
- We then use the monadic law for existence (`MONO_EXISTS`) to show that this perpendicular vector satisfies the uniqueness property.
- Finally, the proof is completed using vector-specific tactics (`VEC3_TAC`) to handle the 3D vector operations.

The key mathematical insight is that for two non-parallel vectors in 3D space, the cross product yields a vector perpendicular to both, and any other vector perpendicular to both must be parallel to this cross product.

### Mathematical insight
This theorem formalizes an important property from 3D vector geometry: given two non-parallel direction vectors, there exists a unique direction (up to parallelism) that is perpendicular to both. 

In vector calculus, this is related to the cross product operation. If $p$ and $p'$ are not parallel, then $p \times p'$ yields a vector perpendicular to both $p$ and $p'$. Moreover, any vector perpendicular to both $p$ and $p'$ must be parallel to $p \times p'$.

This axiom is fundamental in establishing the geometric foundations for 3D space and plays an important role in formalizing geometric reasoning about perpendicular and parallel directions.

### Dependencies
- Definitions:
  - `perpdir`: Perpendicularity relation between direction vectors
  - `pardir`: Parallelism relation between direction vectors
  - `DIRECTION_CLAUSES`: Basic properties of directions

- Theorems:
  - `NORMAL_EXISTS`: For any two non-parallel vectors, there exists a vector perpendicular to both

### Porting notes
When porting this theorem:
1. Ensure that vector operations and predicates for perpendicularity and parallelism are properly defined
2. The proof relies on the existence of cross product properties, so the target system needs to have these vector operations available
3. The `VEC3_TAC` is a specialized tactic for 3D vector reasoning in HOL Light; in other systems, you might need to expand this into appropriate vector algebra steps

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
For any two directions $l$ and $l'$, there exists a direction $p$ such that $p$ is perpendicular to $l$ and $p$ is perpendicular to $l'$.

In formal notation:
$\forall l, l' \in \text{direction}, \exists p \in \text{direction} : p \perp l \land p \perp l'$

### Informal proof
The proof shows that for any two directions, we can find a third direction that is perpendicular to both.

The proof proceeds as follows:
- First, we rewrite the perpendicularity relation `_|_` using the `perpdir` definition and `DIRECTION_CLAUSES` to express it in terms of orthogonality.
- Then we use the `NORMAL_EXISTS` theorem which establishes that for any vector, there exists a normal (orthogonal) vector.
- The `ORTHOGONAL_SYM` theorem is also used, which states that orthogonality is a symmetric relation.
- The `MESON_TAC` automated reasoning tactic then completes the proof by finding the appropriate direction that is orthogonal to both given directions.

### Mathematical insight
This theorem establishes a fundamental property of direction spaces - namely that for any two directions, we can always find a third direction that is perpendicular to both. This is analogous to the fact that in 3D Euclidean space, given two linearly independent vectors, we can always find a vector orthogonal to both (using the cross product).

This result is important in geometry when reasoning about perpendicularity and for constructing orthogonal coordinate systems. In 3D space in particular, this allows constructing orthogonal bases and reference frames, which are essential in many geometric applications.

### Dependencies
- `perpdir`: Definition of perpendicularity for directions
- `DIRECTION_CLAUSES`: Theorem about properties of directions
- `NORMAL_EXISTS`: Theorem stating that for any vector, there exists a normal vector
- `ORTHOGONAL_SYM`: Theorem establishing symmetry of orthogonality

### Porting notes
When porting this to other proof assistants, ensure that:
1. You have a representation of directions
2. You have defined perpendicularity between directions
3. You have theorems equivalent to NORMAL_EXISTS and ORTHOGONAL_SYM
4. The proof is relatively straightforward in most systems and should translate well to tactics-based provers

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
There exist three directions $p$, $p'$, and $p''$ such that:
1. $p$ is not parallel to $p'$
2. $p'$ is not parallel to $p''$
3. $p$ is not parallel to $p''$
4. There does not exist a line $l$ such that $p$ is perpendicular to $l$, $p'$ is perpendicular to $l$, and $p''$ is perpendicular to $l$.

### Informal proof
This theorem essentially states that we can find three directions in 3D space that aren't mutually orthogonal to any single direction.

The proof proceeds as follows:

* We start by rewriting the goals using the definitions of perpendicular directions (`perpdir`), parallel directions (`pardir`), and basic direction properties.

* We instantiate the three directions $p$, $p'$, and $p''$ with the standard basis vectors in $\mathbb{R}^3$:
  * $p = e_1$ (the first basis vector)
  * $p' = e_2$ (the second basis vector)
  * $p'' = e_3$ (the third basis vector)

* We apply simplification using the facts that:
  * The basis vectors are non-zero (`BASIS_NONZERO`)
  * The dimension of the space is 3 (`DIMINDEX_3`)
  * Some arithmetic properties

* Finally, the proof is completed by applying vector-specific tactics for 3D vectors (`VEC3_TAC`) which resolve the remaining goals.

The key insight is that the standard basis vectors $e_1$, $e_2$, and $e_3$ in $\mathbb{R}^3$ satisfy the required properties by construction.

### Mathematical insight
This theorem establishes a fundamental property of 3D Euclidean geometry. It demonstrates that we can find three directions in 3D space that satisfy specific non-parallelism conditions while also ensuring they don't all lie in a single plane (which would make them all perpendicular to some common direction).

The result is essentially equivalent to showing that the standard basis vectors in $\mathbb{R}^3$ form a linearly independent set that spans the space. It captures the fact that 3D space has exactly three orthogonal directions, and no more.

This theorem is part of the axiomatic foundation for directional geometry in HOL Light, establishing basic properties that will be needed for more complex geometric reasoning.

### Dependencies
- Definitions:
  - `perpdir` - Perpendicular directions
  - `pardir` - Parallel directions
  - `DIRECTION_CLAUSES` - Basic properties of directions

- Theorems:
  - `BASIS_NONZERO` - Standard basis vectors are non-zero
  - `DIMINDEX_3` - The dimension of $\mathbb{R}^3$ is 3

### Porting notes
When porting to other proof assistants:
- Ensure the target system has a representation of 3D Euclidean space and basis vectors
- The proof is straightforward if the target system has similar tactics for vector manipulation
- The `VEC3_TAC` tactic in HOL Light is specialized for 3D vector reasoning; you may need to expand this into more elementary steps in systems without equivalent automation

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
For any direction $l$ in 3D space, there exist two directions $p$ and $p'$ such that:
1. $p$ and $p'$ are not parallel to each other: $\neg(p \parallel p')$
2. $p$ is perpendicular to $l$: $p \perp l$
3. $p'$ is perpendicular to $l$: $p' \perp l$

### Informal proof
The proof establishes the existence of two non-parallel directions perpendicular to a given direction $l$.

* We start by rewriting the problem using the definitions of parallel and perpendicular directions.

* The key insight is that if $l$ is a direction in 3D space, we can find two non-parallel vectors perpendicular to $l$ by taking the cross products of $l$ with two different basis vectors.

* The proof considers three cases:
  1. Using cross products of $l$ with the first and second basis vectors
  2. Using cross products of $l$ with the first and third basis vectors
  3. Using cross products of $l$ with the second and third basis vectors

* For each case, we show:
  - The resulting vectors $l \times \text{basis}_i$ and $l \times \text{basis}_j$ are both perpendicular to $l$ (by the property of cross product)
  - These two vectors are not parallel to each other (their cross product is not zero)

* At least one of these cases must work, as we can show that $l$ cannot be perpendicular to all basis vectors simultaneously.

* The final step uses the fact that when $a \times b = 0$, either $a = 0$, $b = 0$, or $a$ and $b$ are parallel (from the `CROSS_0` theorem).

### Mathematical insight
This theorem establishes an important property about 3D geometry: for any direction in 3D space, we can find a plane perpendicular to it. More specifically, we can find two non-parallel directions that are both perpendicular to the given direction.

The result is crucial for establishing the existence of perpendicular planes in 3D geometry. It's a weaker form of a direction axiom, suggesting that there are stronger formulations in the theory. The theorem essentially captures the fact that the orthogonal complement of a 1-dimensional subspace in 3D space is a 2-dimensional plane.

This property is fundamental in projective geometry and in defining orientations and coordinate systems in 3D space.

### Dependencies
- Theorems:
  - `CROSS_0`: Establishes that the cross product with the zero vector always yields the zero vector: $\forall x.\ \vec{0} \times x = \vec{0}$ and $\forall x.\ x \times \vec{0} = \vec{0}$
  
- Definitions:
  - `cross`: Defines the cross product of two 3D vectors: $a \times b = [a_2b_3 - a_3b_2, a_3b_1 - a_1b_3, a_1b_2 - a_2b_1]$
  - `DIRECTION_CLAUSES` (implicit): Likely contains properties of directions
  - `pardir` (implicit): Defines when two directions are parallel
  - `perpdir` (implicit): Defines when two directions are perpendicular

### Porting notes
When porting this theorem:
1. Ensure that your system has a proper representation of 3D vectors and cross product
2. The proof relies on vector facts and cross product properties, which might require different tactics in other proof assistants
3. The symbol `_|_` represents perpendicularity of directions, while `||` represents parallelism
4. The proof uses `VEC3_TAC`, a specialized tactic for 3D vector reasoning, which may need to be replaced with more explicit steps in other systems

---

## ORTHOGONAL_COMBINE

### ORTHOGONAL_COMBINE
- ORTHOGONAL_COMBINE

### Type of the formal statement
- theorem

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
For any three vectors $x, a, b \in \mathbb{R}^3$, if:
- $a$ is perpendicular to $x$ (denoted by $a \perp x$),
- $b$ is perpendicular to $x$ (denoted by $b \perp x$), and
- $a$ and $b$ are not parallel (denoted by $\neg(a \parallel b)$),

then there exists a vector $c \in \mathbb{R}^3$ such that:
- $c$ is perpendicular to $x$ (denoted by $c \perp x$),
- $c$ is not parallel to $a$ (denoted by $\neg(c \parallel a)$), and
- $c$ is not parallel to $b$ (denoted by $\neg(c \parallel b)$).

### Informal proof
This theorem is proved by constructing $c$ as the vector sum $a + b$.

The proof begins by rewriting the perpendicular and parallel relations using their definitions from `DIRECTION_CLAUSES`, `pardir`, and `perpdir`. Then, we need to show three properties for the constructed vector $c = a + b$:

1. $c \perp x$: Since $a \perp x$ and $b \perp x$, we have $(a + b) \perp x$ because the dot product distributes over addition: $(a + b) \cdot x = a \cdot x + b \cdot x = 0 + 0 = 0$.

2. $\neg(c \parallel a)$: Since $a$ and $b$ are not parallel and $c = a + b$, then $c$ cannot be parallel to $a$. If $c \parallel a$, then $a + b = \lambda a$ for some scalar $\lambda$, which would imply $b = (\lambda - 1)a$, making $b$ parallel to $a$ - a contradiction.

3. $\neg(c \parallel b)$: The argument is similar to the previous case.

The final step of the proof uses the `VEC3_TAC` tactic which handles the vector arithmetic in $\mathbb{R}^3$ automatically.

### Mathematical insight
This theorem establishes an important property of orthogonality in $\mathbb{R}^3$. It shows that given two non-parallel vectors that are both perpendicular to a reference vector, we can construct a third vector (their sum) that is also perpendicular to the reference vector while being non-parallel to either of the original vectors.

This result is useful in constructing diverse sets of orthogonal vectors, which has applications in coordinate systems, basis construction, and geometric proofs. The proof technique demonstrates a simple yet powerful construction method: when two vectors are perpendicular to a third, their sum preserves this perpendicularity.

### Dependencies
- `DIRECTION_CLAUSES`: Definitions or theorems about directions in $\mathbb{R}^3$
- `pardir`: Definition of parallel direction
- `perpdir`: Definition of perpendicular direction
- `VEC3_TAC`: A specialized tactic for vector reasoning in $\mathbb{R}^3$

### Porting notes
When porting this theorem:
1. Ensure the target system has appropriate definitions for perpendicularity and parallelism of vectors.
2. Vector arithmetic properties, particularly the distributivity of dot products, should be available.
3. The proof is straightforward vector arithmetic, but you may need to be explicit about the steps handled by `VEC3_TAC` in systems without similar automation.
4. The notation `_|_` for perpendicularity and `||` for parallelism might need to be adapted to the target system's notation.

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
For any line $l$, there exist three points $p$, $p'$, and $p''$ such that:
1. $p$ is not collinear with $p'$ (notation: $\neg(p \parallel p')$)
2. $p'$ is not collinear with $p''$ (notation: $\neg(p' \parallel p'')$)
3. $p$ is not collinear with $p''$ (notation: $\neg(p \parallel p'')$)
4. $p$ is orthogonal to line $l$ (notation: $p \perp l$)
5. $p'$ is orthogonal to line $l$ (notation: $p' \perp l$)
6. $p''$ is orthogonal to line $l$ (notation: $p'' \perp l$)

### Informal proof
This theorem is proved by using two key components:
- `DIRECTION_AXIOM_4_WEAK`, which likely provides a weaker version of this axiom
- `ORTHOGONAL_COMBINE`, which allows for the construction of orthogonal relationships

The proof is completed using the `MESON_TAC` automated tactic, which applies first-order reasoning to combine these results and construct the three non-collinear points that are all orthogonal to the given line $l$.

### Mathematical insight
This axiom establishes an important property about the structure of the geometry being developed. It ensures that for any line, there exist three non-collinear points that are all orthogonal to that line. This is crucial for:

1. Establishing the three-dimensionality of the space
2. Ensuring that the orthogonal complement of a line is "rich enough" (contains at least three non-collinear points)
3. Supporting construction of orthogonal bases in the space

This axiom constrains the geometry to have sufficient structure to support projective or affine geometric reasoning in at least three dimensions.

### Dependencies
- **Theorems**:
  - `DIRECTION_AXIOM_4_WEAK` - A weaker version of this axiom that likely establishes part of the required result
  - `ORTHOGONAL_COMBINE` - A theorem about combining orthogonal relationships

### Porting notes
When porting this theorem:
1. Ensure that the orthogonality relation (`_|_`) and collinearity relation (`||`) are properly defined in the target system
2. The proof relies on automated reasoning (`MESON_TAC`), which might require different tactics in other systems
3. Check that the dependencies (`DIRECTION_AXIOM_4_WEAK` and `ORTHOGONAL_COMBINE`) have been ported successfully

---

## line_tybij

### Name of formal statement
line_tybij

### Type of the formal statement
new_type_definition (via define_quotient_type)

### Formal Content
```ocaml
let line_tybij = define_quotient_type "line" ("mk_line","dest_line") `(||)`;;
```

### Informal statement
This defines a new type `line` via a quotient construction. The type `line` represents equivalence classes of objects under the relation `(||)` (which likely represents parallel lines). The construction creates:

1. A type `line` 
2. A constructor function `mk_line` that maps objects to their equivalence class
3. A destructor function `dest_line` that maps an equivalence class to a representative object

### Informal proof
There is no explicit proof here, as this is a type definition. The `define_quotient_type` function automatically creates a new type based on equivalence classes. The system verifies that:

- The relation `(||)` is indeed an equivalence relation (reflexive, symmetric, and transitive)
- There exists at least one element in each equivalence class

These checks are handled automatically by the `define_quotient_type` mechanism.

### Mathematical insight
This definition establishes a new type for lines by identifying them with equivalence classes of objects (likely vectors or other geometric entities) that are parallel to each other. This is a standard mathematical construction in projective geometry, where lines are often represented as equivalence classes of parallel vectors or points.

The quotient type construction is a fundamental way to create new types that represent equivalence classes. It allows us to work with lines directly as objects, rather than having to constantly deal with representatives and equivalence checking.

### Dependencies
The definition depends on:
- The parallelism relation `(||)`, which is referenced but not defined here
- The underlying HOL Light mechanisms for defining quotient types

### Porting notes
When porting this to another system:
- Ensure the target system supports quotient types or has a mechanism for defining them
- Verify that the parallelism relation `(||)` has been properly defined in the target system
- Some systems may require explicit proofs that the relation is an equivalence relation
- The quotient type mechanism may differ significantly between systems (e.g., Isabelle uses the Quotient package, Lean has quotient types built in with different syntax)

---

## PERPDIR_WELLDEF

### PERPDIR_WELLDEF
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERPDIR_WELLDEF = prove
 (`!x y x' y'. x || x' /\ y || y' ==> (x _|_ y <=> x' _|_ y')`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;
```

### Informal statement
This theorem states that the perpendicular relation between directions is well-defined with respect to direction equality. Formally, for any directions $x$, $y$, $x'$, and $y'$, if $x \parallel x'$ and $y \parallel y'$ (meaning $x$ is parallel to $x'$ and $y$ is parallel to $y'$), then $x \perp y$ if and only if $x' \perp y'$ (meaning $x$ is perpendicular to $y$ if and only if $x'$ is perpendicular to $y'$).

### Informal proof
The proof is accomplished by:
- Expanding the definitions of perpendicular directions (`perpdir`) and parallel directions (`pardir`) using `REWRITE_TAC`.
- Further simplifying using the properties of directions via `DIRECTION_CLAUSES`.
- The proof is completed using vector space tactics specialized for 3D vectors with `VEC3_TAC`, which handles the algebraic manipulations needed to verify that perpendicularity is preserved when directions are parallel.

### Mathematical insight
This theorem establishes that the perpendicular relation between directions is invariant under direction equality. In a geometric context, this means that if we have two pairs of directions where corresponding directions are parallel, then perpendicularity in one pair implies perpendicularity in the other pair, and vice versa.

This result is essential in 3D geometry because it allows us to work with directions as abstract entities without worrying about their specific representations. If two directions are the same (i.e., parallel), they behave identically with respect to perpendicularity relationships with other directions.

### Dependencies
- Definitions:
  - `perpdir`: Definition of perpendicular directions
  - `pardir`: Definition of parallel directions
  - `DIRECTION_CLAUSES`: Basic properties of directions

### Porting notes
When porting this theorem to other proof assistants, ensure that:
1. The concept of directions in 3D space is properly defined.
2. The parallel and perpendicular relations between directions are defined consistently.
3. The equivalent of `VEC3_TAC` automation is available or can be substituted with explicit vector algebra steps.

---

## perpl,perpl_th

### perpl

### Type of the formal statement
new_definition (function definition)

### Formal Content
```ocaml
let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;
```

### Informal statement
$\text{perpl}$ is a function that represents perpendicularity of directions (lines through the origin). It is defined by lifting the line type bijection to preserve the perpendicular direction relation, where:

If $d_1$ and $d_2$ are directions, then $\text{perpl}(d_1, d_2)$ means that $d_1$ is perpendicular to $d_2$.

### Informal proof
This definition is created using the `lift_function` operation to lift the second component of the line type bijection, preserving reflexivity (`PARDIR_REFL`) and transitivity (`PARDIR_TRANS`) properties. The function is defined to satisfy the well-definedness conditions specified in the theorem `PERPDIR_WELLDEF`.

The lifting operation transfers the perpendicularity relation from the underlying representation of lines to the abstract direction type, ensuring that the mathematical properties of perpendicularity are preserved.

### Mathematical insight
The `perpl` function captures the fundamental geometric notion of perpendicularity between directions. This is a crucial concept in affine geometry, as perpendicularity is one of the key relations that structures a vector space with an inner product.

By properly defining perpendicularity as a lifted relation, the system ensures that all the expected properties of perpendicular lines hold in the formal development. This definition allows for reasoning about orthogonality in geometric proofs while maintaining mathematical rigor.

The use of `lift_function` ensures that the relation is well-defined with respect to the equivalence relations on directions, which is essential for consistency in the formal development.

### Dependencies
- `lift_function`: Function for lifting operations to respect equivalence relations
- `line_tybij`: Type bijection for the representation of lines
- `PARDIR_REFL`: Theorem establishing reflexivity of parallel direction relation
- `PARDIR_TRANS`: Theorem establishing transitivity of parallel direction relation
- `PERPDIR_WELLDEF`: Theorem establishing well-definedness of perpendicular direction relation

### Porting notes
When porting to other systems, care must be taken to ensure the perpendicularity relation respects the equivalence classes defined for directions. In systems with dependent types or more direct support for quotient types, this definition might be expressed more directly in terms of the equivalence relation on directions.

---

## line_lift_thm

### Name of formal statement
line_lift_thm

### Type of formal statement
theorem

### Formal Content
```ocaml
let line_lift_thm = lift_theorem line_tybij
 (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th];;
```

### Informal statement
This theorem lifts the bijection `line_tybij` to create isomorphic operations in the abstract line space, establishing parallel relationships with the reflexivity, symmetry, and transitivity properties, and also incorporating perpendicularity relationships.

### Informal proof
This theorem is constructed by applying the `lift_theorem` function to:

1. `line_tybij` - A type bijection that maps between the abstract representation of lines and their concrete representation
2. A tuple of basic properties of parallel lines:
   - `PARDIR_REFL`: Parallelism is reflexive (every line is parallel to itself)
   - `PARDIR_SYM`: Parallelism is symmetric (if line A is parallel to line B, then B is parallel to A)
   - `PARDIR_TRANS`: Parallelism is transitive (if A is parallel to B and B is parallel to C, then A is parallel to C)
3. A list containing `perpl_th` which likely defines perpendicularity relationships between lines

The `lift_theorem` function creates a corresponding theorem in the abstract line space that preserves these relationships while working with the abstract representation of lines.

### Mathematical insight
This theorem establishes the connection between concrete and abstract representations of lines, ensuring that fundamental properties of lines (such as parallelism and perpendicularity) are preserved in the abstract representation. This is a standard technique in mathematical formalization where we want to work with abstract types while ensuring they inherit the correct properties from their concrete representations.

The theorem essentially creates an isomorphism between the concrete and abstract line spaces, preserving the key geometrical relationships. This allows subsequent proofs to work with the more convenient abstract representation while maintaining the geometric integrity of the statements.

### Dependencies
- `line_tybij`: Type bijection for lines
- `PARDIR_REFL`: Reflexivity of parallel lines
- `PARDIR_SYM`: Symmetry of parallel lines
- `PARDIR_TRANS`: Transitivity of parallel lines
- `perpl_th`: Theorem about perpendicular lines

### Porting notes
When porting this to another system, you'll need to:
1. Ensure the target system has a mechanism for type bijections similar to HOL Light's
2. Port the parallelism properties first
3. Port the perpendicularity theorem
4. Implement the equivalent of `lift_theorem` which transfers properties from concrete to abstract representations via the bijection

---

## LINE_AXIOM_1

### LINE_AXIOM_1
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LINE_AXIOM_1 = line_lift_thm DIRECTION_AXIOM_1;;
```

### Informal statement
This theorem states that: For all points $a$ and $b$ where $a \neq b$, there exists a line $L$ that passes through both $a$ and $b$.

### Informal proof
This theorem is derived by applying the function `line_lift_thm` to the theorem `DIRECTION_AXIOM_1`. The theorem `DIRECTION_AXIOM_1` is a fundamental axiom in the geometric system that states that for any two distinct points, there exists a unique direction determined by them.

The function `line_lift_thm` "lifts" this directional axiom to the level of lines, establishing that for any two distinct points, there exists a line passing through them.

### Mathematical insight
This axiom represents one of the fundamental properties of Euclidean geometry - that any two distinct points determine a unique line. It captures the intuitive notion that two points are sufficient to specify a line completely. This is one of the core principles upon which the rest of the geometric system is built.

While seemingly simple, this axiom is crucial for establishing the relationship between points and lines, which forms the basis for more complex geometric constructions and theorems.

### Dependencies
- Axioms/Theorems:
  - `DIRECTION_AXIOM_1`: The axiom stating that for any two distinct points, there exists a unique direction.
- Functions:
  - `line_lift_thm`: A function that converts theorems about directions into theorems about lines.

### Porting notes
When porting this theorem to another system, ensure that the underlying axiom `DIRECTION_AXIOM_1` about directions is properly formalized first. Additionally, the `line_lift_thm` function would need to be implemented to properly convert theorems about directions to theorems about lines.

The exact representation of points and lines might differ between systems, so appropriate adjustments to type definitions and relations would be necessary.

---

## LINE_AXIOM_2

### LINE_AXIOM_2
- LINE_AXIOM_2

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
```

### Informal statement
This theorem is a lifted version of `DIRECTION_AXIOM_2` applied to lines. It states that for any two distinct points, there exists a unique line passing through them.

Formally, it states:
$$\forall p\ q. p \neq q \Rightarrow \exists! L. p \in L \land q \in L$$

Where $p$ and $q$ are points, and $L$ is a line.

### Informal proof
The theorem is obtained by applying the `line_lift_thm` function to `DIRECTION_AXIOM_2`. 

The `line_lift_thm` function lifts a theorem about directions to a corresponding theorem about lines. This corresponds to the geometric intuition that directions (or vectors) can be associated with lines in a projective space.

The underlying axiom `DIRECTION_AXIOM_2` states that for any two distinct points, there exists a unique direction determined by them. When lifted to the context of lines, this becomes the statement that through any two distinct points, there exists a unique line.

### Mathematical insight
This axiom captures one of the fundamental properties of projective geometry: two distinct points uniquely determine a line. This is a direct consequence of the way lines are defined in projective space.

In projective geometry, this property is often taken as an axiom, as it is here. It's a critical property that distinguishes projective geometry from other geometric systems.

The lifting from directions to lines reflects the underlying relationship between directions (or vectors) and lines in projective space, where lines can be viewed as containing all points in a given direction from a reference point.

### Dependencies
- `line_lift_thm`: Function that lifts theorems about directions to theorems about lines
- `DIRECTION_AXIOM_2`: Axiom stating that for any two distinct points, there exists a unique direction determined by them

### Porting notes
When porting to another system, ensure that the projective geometry foundations are established, particularly the relationship between directions and lines. The lifting mechanism (`line_lift_thm`) may need to be implemented according to the target system's conventions for handling geometric transformations.

---

## LINE_AXIOM_3

### LINE_AXIOM_3

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
```

### Informal statement
This theorem states that for any two distinct points $p$ and $q$, there exists a line $l$ such that $p \in l$ and $q \in l$.

### Informal proof
The theorem is obtained by applying the `line_lift_thm` function to the axiom `DIRECTION_AXIOM_3`.

The underlying mathematical conversion here involves lifting a statement about directions to a corresponding statement about lines. In projective geometry, there is a fundamental duality between points and lines. The axiom `DIRECTION_AXIOM_3` states a property about directions, and `line_lift_thm` transforms this into the corresponding property about lines.

Specifically, if `DIRECTION_AXIOM_3` states that for any two distinct points, there exists a unique direction containing them, then `LINE_AXIOM_3` states that for any two distinct points, there exists a unique line passing through them.

### Mathematical insight
This theorem represents one of the fundamental axioms of projective geometry, often stated as "through any two distinct points, there exists a unique line." This is a core principle in both Euclidean and projective geometry.

The theorem uses the concept of lifting from directions to lines, which suggests that the formalization is using a construction where lines are built from or related to directions in a systematic way.

In projective geometry, this axiom is dual to the axiom stating that any two distinct lines intersect in exactly one point (in the projective plane).

### Dependencies
- `line_lift_thm`: A function that converts direction-related axioms to corresponding line-related axioms
- `DIRECTION_AXIOM_3`: An axiom about directions that is being lifted to create this theorem about lines

### Porting notes
When porting this to another system, you would need to:
1. Understand how points, lines, and directions are defined in the target system
2. Ensure that the appropriate duality or relationship between directions and lines is established
3. Verify that the axiom system being used is consistent with projective geometry principles

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
The LINE_AXIOM_4 theorem is the result of applying the `line_lift_thm` function to `DIRECTION_AXIOM_4`. This lifts a direction axiom to its corresponding line axiom.

### Informal proof
This theorem is established by directly applying the `line_lift_thm` function to the theorem `DIRECTION_AXIOM_4`. The `line_lift_thm` function is designed to convert axioms about directions into equivalent axioms about lines.

The proof consists of a single step:
```
let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4
```

This transformation establishes the corresponding line axiom based on the direction axiom.

### Mathematical insight
This theorem is part of a systematic approach to axiomatizing projective geometry. The underlying pattern involves establishing axioms about directions and then "lifting" them to corresponding axioms about lines. This approach allows for a more structured and modular development of the geometric framework.

The line axioms typically describe properties of lines in projective space, while direction axioms characterize properties of directions (which can be thought of as points at infinity or equivalence classes of parallel lines). The lifting process preserves the essential geometric relationships while translating them between these different representations.

This particular axiom (LINE_AXIOM_4) likely corresponds to one of the fundamental axioms of projective geometry, though without seeing the content of DIRECTION_AXIOM_4, we can't determine its precise mathematical meaning.

### Dependencies
- **Theorems**: `DIRECTION_AXIOM_4`
- **Functions**: `line_lift_thm`

### Porting notes
When porting this theorem to another proof assistant:
1. First ensure that `DIRECTION_AXIOM_4` is available in the target system
2. Implement the `line_lift_thm` function that performs the appropriate transformation from direction axioms to line axioms
3. The theorem itself can then be defined by direct application of the function to the direction axiom

The specific implementation details will depend on how the concepts of lines and directions are represented in the target system, and how the relationship between them is formalized.

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
This code defines a new type `point` in HOL Light. The type definition creates a bijection between the new type `point` and a nonempty subset of an existing type `line`. In this case, the subset is the entire type `line` because the predicate is simply the tautology `T` (true), meaning every element of `line` is included in the subset.

The bijection consists of two functions:
- `mk_point : line -> point` - constructs a point from a line
- `dest_point : point -> line` - extracts the line from a point

### Informal proof
The proof obligation for a type definition in HOL Light is to show that the subset of the existing type is non-empty. In this case, we need to prove `∃x:line. T`.

The proof is trivial since `T` is a tautology that holds for any `x`. The proof uses `REWRITE_TAC[]` which simplifies the goal by applying basic rewrite rules, resolving it immediately because `∃x:line. T` is obviously true - it just states "there exists a line" which must be true in a non-empty universe.

### Mathematical insight
This type definition creates a new type `point` that is isomorphic to the type `line`. This is a common pattern in mathematical formalizations where one wants to create distinct but related types to model different mathematical objects.

The choice to make `point` isomorphic to the entire `line` type (rather than a proper subset of it) suggests that in this formalization, there might be a one-to-one correspondence between points and lines. This could be part of a projective geometry formalization or another geometric system where points and lines have a fundamental relationship.

The construction ensures that the theorems about `line` can be transferred to `point` via the bijection, while maintaining the logical distinction between the two types to prevent confusion or type errors in proofs.

### Dependencies
This definition depends on the existence of a type `line`, which must have been previously defined in the system.

### Porting notes
When porting to another proof assistant:
1. Check if the target system has a similar mechanism for creating new types.
2. In systems like Isabelle/HOL, the equivalent would be a typedef.
3. In Lean, you might use a subtype or a structure depending on your needs.
4. Some systems might require explicit proofs that the bijection functions form an isomorphism.
5. The trivial proof obligation might need to be handled differently in other systems.

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
The definition `on` states that a point $p$ is on a line $l$ if and only if the point is perpendicular to the line. Formally:

$p \text{ on } l \iff \text{perpl}(\text{dest\_point}(p), l)$

Where:
- $p$ is a point
- $l$ is a line
- $\text{dest\_point}(p)$ extracts the vector representation of the point $p$
- $\text{perpl}(v, l)$ means that vector $v$ is perpendicular to line $l$

### Informal proof
This is a definition, so there is no proof to present.

### Mathematical insight
This definition establishes what it means for a point to be "on" a line in this formalization of geometry. The definition is somewhat unconventional as it defines a point being on a line in terms of perpendicularity. This suggests that the formalization might be using a projective or homogeneous coordinate system where:

1. Lines are represented by normal vectors (perpendicular to the direction of the line)
2. A point lies on a line precisely when its position vector is perpendicular to the line's normal vector

This corresponds to the standard equation of a line in homogeneous coordinates, where a point $(x,y,z)$ lies on a line with normal vector $(a,b,c)$ if and only if $ax + by + cz = 0$, which is equivalent to saying the vectors are perpendicular.

The use of `dest_point` suggests that points have a specific representation in the system, and this function extracts the underlying vector representation needed for the perpendicularity check.

### Dependencies
- `perpl`: A predicate checking if a vector is perpendicular to a line
- `dest_point`: A function that extracts the vector representation of a point

### Porting notes
When porting this definition:
- Ensure that the target system has appropriate representations for points and lines
- Understand how perpendicularity is defined in the target system
- Check if the target system uses a similar approach to representing geometric objects or if an alternative formulation of "point on line" would be more natural

---

## POINT_CLAUSES

### POINT_CLAUSES

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
The theorem `POINT_CLAUSES` consists of a conjunction of three statements relating points and their destructions:

1. For any points $p$ and $p'$, $p = p'$ if and only if $\text{dest\_point}(p) = \text{dest\_point}(p')$.

2. For any predicate $P$, the statement $\forall p. P(\text{dest\_point}(p))$ is equivalent to $\forall l. P(l)$.

3. For any predicate $P$, the statement $\exists p. P(\text{dest\_point}(p))$ is equivalent to $\exists l. P(l)$.

### Informal proof
The proof uses the theorem `point_tybij`, which establishes that points form a bijection with some underlying type. 

The proof is accomplished by applying the `MESON_TAC` tactical with `point_tybij` as its argument. This tactical uses automated reasoning to derive all three clauses from the bijective relationship between points and their representations expressed in `point_tybij`.

Specifically:
- The first clause follows directly from the injectivity property of bijections.
- The second and third clauses follow from the surjectivity property, ensuring that quantifying over points (and then applying `dest_point`) is equivalent to quantifying over the underlying type directly.

### Mathematical insight
This theorem provides essential conversions for working with points in HOL Light. It establishes the relationship between points as abstract objects and their concrete representations obtained through `dest_point`.

These clauses are particularly useful in proofs where we need to:
1. Convert equality between points to equality between their representations
2. Convert quantified statements about point representations to quantified statements about the underlying type
3. Move freely between the abstract point type and its concrete representation

This is a standard pattern in HOL Light for working with abstract types that have been defined via bijections with more concrete types.

### Dependencies
- Theorems:
  - `point_tybij`: Establishes the bijection between points and their representations

### Porting notes
When porting to other proof assistants, consider how the target system handles type bijections or type definitions. Some systems might use different mechanisms for abstract types or might require more explicit type coercions. The underlying concept of establishing an isomorphism between abstract and concrete types is common across proof assistants, but the implementation details may vary.

---

## POINT_TAC

### Name of formal statement
POINT_TAC

### Type of the formal statement
Tactic (function definition)

### Formal Content
```ocaml
let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;
```

### Informal statement
`POINT_TAC` is a tactic that simplifies a goal using the `on` function and the `POINT_CLAUSES` theorems, then accepts a given theorem `th` as the solution to the goal.

Specifically, it combines the tactics `REWRITE_TAC[on; POINT_CLAUSES]` and `ACCEPT_TAC th`, where:
- `REWRITE_TAC[on; POINT_CLAUSES]` rewrites terms in the goal using the definition of the `on` function and the theorems in `POINT_CLAUSES`.
- `ACCEPT_TAC th` attempts to solve the goal using theorem `th`.

### Informal proof
This is a tactic definition, not a theorem, so there is no proof in the traditional sense. The definition simply combines two existing tactics:

1. First, apply rewriting using the definition of the `on` function and all theorems in `POINT_CLAUSES`.
2. Then, attempt to directly prove the goal using the given theorem `th`.

### Mathematical insight
This tactic is a convenience function designed to handle goals involving points in coordinate geometry. The combination of rewriting with `on` and `POINT_CLAUSES` likely simplifies expressions involving points, their coordinates, or point-based operations, after which the given theorem `th` can be directly applied to solve the now-simplified goal.

The tactic represents a common pattern in interactive theorem proving: combining a specific set of simplification rules (handling domain-specific concepts) with a direct proof step.

### Dependencies
- **Tactics:**
  - `REWRITE_TAC` - Rewriting tactic
  - `ACCEPT_TAC` - Goal acceptance tactic

- **Theorems:**
  - `POINT_CLAUSES` - Presumably theorems about point operations

- **Definitions:**
  - `on` - Likely a function for operating on points

### Porting notes
When porting to other systems:
- Ensure the target system has equivalent concepts for the `on` function and `POINT_CLAUSES` theorems.
- The tactic can be implemented as a simple composition of rewriting and goal acceptance tactics, which most proof assistants provide.
- The effectiveness of this tactic depends entirely on the specific theorems in `POINT_CLAUSES` and the nature of the `on` function, so those must be carefully ported first.

---

## AXIOM_1

### AXIOM_1
- `AXIOM_1`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AXIOM_1 = prove
 (`!p p'. ~(p = p') ==> ?l. p on l /\ p' on l /\
          !l'. p on l' /\ p' on l' ==> (l' = l)`,
  POINT_TAC LINE_AXIOM_1);;
```

### Informal statement
For any two distinct points $p$ and $p'$, there exists a unique line $l$ such that both $p$ and $p'$ lie on $l$. Formally:

$$\forall p, p' \in \text{Point}. \; p \neq p' \implies \exists l \in \text{Line}. \; (p \text{ on } l) \land (p' \text{ on } l) \land (\forall l' \in \text{Line}. \; (p \text{ on } l') \land (p' \text{ on } l') \implies l' = l)$$

Where "on" is the relation indicating that a point lies on a line.

### Informal proof
This theorem is proved using `POINT_TAC` and `LINE_AXIOM_1`, which suggests it is a direct application of an axiom of Euclidean geometry. The proof essentially applies the fundamental axiom that through any two distinct points, there passes exactly one line.

### Mathematical insight
This statement captures one of the fundamental axioms of Euclidean geometry: through any two distinct points, there passes exactly one line. This principle is essential for the development of planar geometry and serves as a foundational building block for more complex geometric theorems.

Despite its name "AXIOM_1", this is actually a theorem in HOL Light, likely proved from more primitive axioms or definitions in the geometric formalization. This highlights how mathematical axioms are sometimes encoded as theorems in formal systems, depending on the chosen foundation.

### Dependencies
- Tactics:
  - `POINT_TAC`
  - `LINE_AXIOM_1`

### Porting notes
When porting to other systems:
- Ensure that the basic geometric types (Point, Line) and relations (on) are properly defined
- The theorem's name "AXIOM_1" might be misleading in other systems - consider renaming it to clarify its status as a theorem or axiom depending on the target system's foundation
- The proof is likely straightforward if the target system has an equivalent axiom or primitive notion for the uniqueness of a line through two distinct points

---

## AXIOM_2

### Name of formal statement
AXIOM_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AXIOM_2 = prove
 (`!l l'. ?p. p on l /\ p on l'`,
  POINT_TAC LINE_AXIOM_2);;
```

### Informal statement
For any two lines $l$ and $l'$, there exists a point $p$ such that $p$ is on line $l$ and $p$ is on line $l'$.

### Informal proof
The proof uses the tactics `POINT_TAC` and `LINE_AXIOM_2`.

This theorem states that any two lines intersect at some point. This is immediately verified by appealing to the axiom `LINE_AXIOM_2`, which directly states this property of the geometry being developed. The `POINT_TAC` tactic likely handles the point-related aspects of the proof.

### Mathematical insight
This theorem establishes a fundamental property of the geometric space being formalized in HOL Light: any two lines intersect at some point. This corresponds to a projective geometry axiom, rather than a Euclidean geometry axiom (where parallel lines exist).

In projective geometry, any two lines always intersect. This is in contrast to Euclidean geometry where parallel lines exist. This theorem thus suggests that the geometry being developed here is projective in nature.

This axiom is important because it ensures a simple and elegant geometric framework where intersection of lines is guaranteed, simplifying many geometric arguments.

### Dependencies
No explicit dependencies are listed, though the proof relies on:
- `POINT_TAC`: A tactic for handling point-related reasoning
- `LINE_AXIOM_2`: An axiom of the geometric system being developed

### Porting notes
When porting to other systems, ensure that the underlying geometric axioms (particularly LINE_AXIOM_2) are properly represented. Note that this theorem represents projective rather than Euclidean geometry, so the target system must be capable of representing projective geometric concepts.

---

## AXIOM_3

### AXIOM_3
- AXIOM_3

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AXIOM_3 = prove
 (`?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p on l /\ p' on l /\ p'' on l)`,
  POINT_TAC LINE_AXIOM_3);;
```

### Informal statement
There exist three distinct points $p$, $p'$, and $p''$ such that:
- $p \neq p'$
- $p' \neq p''$
- $p \neq p''$
- There does not exist a line $l$ such that all three points $p$, $p'$, and $p''$ lie on $l$.

### Informal proof
This theorem is proved using `POINT_TAC` and `LINE_AXIOM_3`, which are likely tactics or auxiliary theorems related to the axioms of geometric points and lines. The proof relies on the axiom that there exist three non-collinear points in the geometric space.

This is essentially a direct application of a fundamental axiom in geometry stating that the plane contains at least three non-collinear points.

### Mathematical insight
This statement is the third axiom of plane geometry in this formalization, establishing the existence of three points that do not all lie on the same line. This axiom ensures that the geometric space is at least two-dimensional (a plane rather than just a line).

In plane geometry, this axiom is crucial because:
1. It establishes that the space has sufficient dimensionality for planar constructions
2. It ensures that triangles can be formed
3. It distinguishes plane geometry from line geometry

This axiom, together with axioms about the existence of lines and points, forms the foundational structure of the geometric space being formalized.

### Dependencies
- Tactics: `POINT_TAC`, `LINE_AXIOM_3`

### Porting notes
When porting this axiom to another system, you should:
- Ensure that the geometric primitives (points and lines) are properly defined
- For systems with different geometric foundations, you might need to adapt this axiom to fit within the chosen axiomatization of geometry
- Check whether the target system uses a different approach to defining dimensionality (e.g., through vector spaces or affine spaces)

---

## AXIOM_4

### AXIOM_4
- AXIOM_4

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p on l /\ p' on l /\ p'' on l`,
  POINT_TAC LINE_AXIOM_4);;
```

### Informal statement
For any line $l$, there exist three distinct points $p$, $p'$, and $p''$ such that all of them lie on $l$.

Mathematically:
$\forall l. \exists p, p', p''. (p \neq p') \land (p' \neq p'') \land (p \neq p'') \land (p \text{ on } l) \land (p' \text{ on } l) \land (p'' \text{ on } l)$

### Informal proof
The proof is completed using two tactics:
- `POINT_TAC`: This is a tactic for working with points in geometric theorems.
- `LINE_AXIOM_4`: This appears to be a reference to the fourth axiom of a geometric system that deals with lines.

This theorem states a foundational property of lines in geometry - that each line contains at least three distinct points. The proof likely relies directly on this as an axiom in the underlying geometry system being formalized.

### Mathematical insight
This is a fundamental axiom in projective geometry or similar geometric systems. It establishes that lines are "rich" enough to contain at least three distinct points, ruling out degenerate geometric models.

The axiom is important because:
1. It helps define the minimum structure required for lines
2. It guarantees a certain level of richness in the geometric space
3. It distinguishes this geometry from systems where lines might contain fewer points

This property is essential for developing more complex geometric theorems that rely on the existence of multiple points on a line.

### Dependencies
No explicit dependencies are listed, but the proof uses:
- `POINT_TAC`: A tactic for handling points
- `LINE_AXIOM_4`: Likely an axiomatic statement about lines

### Porting notes
When porting this to another system:
- Ensure that the target system has a compatible notion of points and lines
- Check if the target system already has a similar axiom about the existence of at least three points on a line
- This theorem might be treated as an axiom in some systems rather than a proven result, depending on how the foundations of geometry are established

---

## projl

### projl
- `projl`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let projl = new_definition
 `projl x = mk_line((||) (mk_dir x))`;;
```

### Informal statement
The function `projl` maps a vector $x$ to the projective line corresponding to the direction represented by $x$. Specifically, it creates a projective line by applying the `mk_line` function to the direction obtained from $x$ using `mk_dir`.

Formally, for a vector $x$, $\text{projl}(x) = \text{mk\_line}(\text{mk\_dir}(x))$.

### Informal proof
This is a definition, so there is no proof to translate.

### Mathematical insight
This definition provides a way to convert vectors in 3D space to projective lines. The function first converts a vector to a direction using `mk_dir`, then converts that direction to a projective line using `mk_line`. 

This mapping is a key component in projective geometry, which studies geometric properties that remain invariant under projective transformations. In projective geometry, a line can be represented by a direction vector, and this definition formalizes that mapping.

The definition is part of a framework that connects vector algebra with projective geometry, allowing for the application of algebraic methods to geometric problems.

### Dependencies
- The definition depends on `mk_line` and `mk_dir`, which are likely defined elsewhere in the formalization.
- It uses the `||` operator (utilized in the expression `(||) (mk_dir x)`), which presumably represents some operation related to projective geometry.

### Porting notes
When porting this definition to another proof assistant:
- Ensure that the underlying concepts of directions (`mk_dir`) and projective lines (`mk_line`) are properly formalized.
- The notation `(||)` needs to be correctly interpreted and implemented in the target system.
- The typing of vectors and projective lines should be maintained consistently.

---

## projp

### Name of formal statement
projp

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let projp = new_definition
 `projp x = mk_point(projl x)`;;
```

### Informal statement
The definition `projp` creates a projective point from a projective line. Specifically, it is defined as:

$$\text{projp}(x) = \text{mk\_point}(\text{projl}(x))$$

where:
- $x$ is a projective line
- $\text{projl}(x)$ extracts the projective line representation
- $\text{mk\_point}$ constructs a projective point from a projective line representation

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition establishes a mapping from projective lines to projective points, which is a fundamental operation in projective geometry. In projective geometry, there is a duality between points and lines - a concept that allows geometric theorems to be transformed into other theorems by swapping the roles of points and lines.

The `projp` function captures one direction of this duality transformation, converting a line to its dual point representation. This is useful for implementing the principle of duality in projective geometry, where statements about points and lines can be interchanged.

This function likely forms part of a pair with another function that performs the inverse operation (converting projective points to projective lines).

### Dependencies
#### Definitions
- `mk_point` - Constructor for projective points
- `projl` - Function that extracts the projective line representation

### Porting notes
When porting this definition to another system, ensure that the underlying representations of projective points and lines are compatible with the dual nature required by projective geometry. The implementation will depend on how projective geometry is formalized in the target system, particularly how the duality between points and lines is handled.

---

## PROJL_TOTAL

### PROJL_TOTAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any line $l$ in projective space, there exists a non-zero vector $x$ such that $l = \operatorname{projl}(x)$.

### Informal proof
The proof shows that any line can be represented by a non-zero vector through the projective mapping:

* First, we use the line bijection property to express the line $l$ in terms of a direction $d$: $l = \text{mk\_line}(\|d\|)$.
* Then we rewrite using the definition of $\operatorname{projl}$.
* We choose $x = \text{dest\_dir}(d)$ as our witness.
* Finally, we apply the direction bijection property to show that $x$ is non-zero and that $l = \operatorname{projl}(x)$.

### Mathematical insight
This theorem establishes the surjectivity of the projection mapping from non-zero vectors to projective lines. It shows that every projective line can be represented by some non-zero vector through the $\operatorname{projl}$ mapping. This is a fundamental result in projective geometry, confirming that the homogeneous coordinate representation covers the entire projective space of lines.

The theorem complements the bijection between directions and lines, showing how we can move between different representations of projective geometry.

### Dependencies
- `line_tybij`: Bijection between lines and directions
- `direction_tybij`: Bijection between directions and non-zero vectors
- `projl`: Definition of projection from vectors to projective lines

### Porting notes
When implementing this in another system, ensure that the representation of projective lines and the projection function are consistently defined. The proof relies on the bijections between various representations of projective geometry (lines, directions, and vectors), so these mappings need to be established first.

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
The `homol` specification introduces a function that guarantees the existence of a projection function for the right element of a pair. Specifically, it defines:

$$\forall x. \exists y. x = (y, \text{homol}(x))$$

This means that for any value `x`, there exists a value `y` such that `x` can be written as the pair `(y, homol(x))`, where `homol(x)` represents the second component of the pair.

### Informal sketch
This specification is established by applying Skolemization (`SKOLEM_THM`) to the `PROJL_TOTAL` theorem, which asserts that every value can be represented as a pair. The Skolem theorem transforms the existential quantifier in the statement into a function (`homol`).

The proof essentially involves:
- Starting with the `PROJL_TOTAL` theorem, which states that for any value, there exists a decomposition into a pair
- Applying Skolemization to introduce the function `homol` that extracts the second component of this pair
- Creating a new specification with this function

### Mathematical insight
The `homol` function essentially provides a way to extract the second component of a pair, assuming that any value can be represented as a pair. This is a foundational utility in HOL Light's type theory, allowing manipulation of pair structures.

This specification is part of HOL Light's foundation for working with product types and demonstrates how the system formalizes the extraction of components from structured data.

The approach uses Skolemization, a common technique in formal logic that replaces existential quantifiers with functions (known as Skolem functions) to simplify expressions and reasoning.

### Dependencies
- **Theorems**: 
  - `PROJL_TOTAL`: Asserts that any value can be represented as a pair
  - `SKOLEM_THM`: Used for Skolemization, converting existential quantifiers to functions

### Porting notes
When porting to other proof assistants:
- Ensure the target system has appropriate support for pair types
- The implementation might vary based on how the target system handles product types
- The Skolemization approach may need adaptation depending on the logical foundations of the target system

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
For any projective point $p$, there exists a non-zero vector $x$ such that $p = \text{projp}(x)$.

### Informal proof
The proof begins by rewriting the goal using the definition of `projp`. Then, it applies `MESON_TAC` with the theorems `PROJL_TOTAL` and `point_tybij`.

The theorem `PROJL_TOTAL` states that for any projective line $l$, there exists a non-zero vector $v$ such that $l = \text{projl}(v)`.

The theorem `point_tybij` relates projective points and lines, establishing a bijection between them.

By using these two theorems, the proof establishes that since every projective line can be represented by a non-zero vector, and there's a bijection between points and lines, every projective point can also be represented by a non-zero vector through the `projp` function.

### Mathematical insight
This theorem establishes the surjectivity of the `projp` function, which maps non-zero vectors to projective points. In projective geometry, points are often represented as equivalence classes of non-zero vectors, where vectors are equivalent if they're scalar multiples of each other.

This result confirms that every projective point can be represented by at least one non-zero vector, which is fundamental for working with projective geometry in a formal system. It provides a concrete way to represent abstract projective points using vectors.

### Dependencies
- Definitions:
  - `projp`: Function mapping a vector to a projective point
- Theorems:
  - `PROJL_TOTAL`: States that every projective line can be represented by a non-zero vector
  - `point_tybij`: Establishes a bijection between projective points and lines

### Porting notes
When porting this theorem, ensure that your target system has appropriate definitions for projective geometry, particularly the representation of projective points and lines using vectors. The bijection between points and lines (point-line duality) is a key concept that should be established before porting this theorem.

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
For a given point $p$, $\text{homop}(p)$ is defined as the homology $\text{homol}(\text{dest\_point}(p))$. 

This definition connects the homology operation to points, where $\text{dest\_point}(p)$ extracts the underlying representation of the point $p$, and $\text{homol}$ computes the homology for that representation.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition establishes a connection between points (geometric objects) and homologies (transformations). The function `homop` allows us to directly apply homology operations to points by:
1. First extracting the underlying representation of the point using `dest_point`
2. Then applying the homology operation `homol` to that representation

This definition creates a more convenient interface for working with homologies in geometric contexts, allowing direct application to geometric points rather than having to manually extract the point representation first.

### Dependencies
#### Definitions
- `homol` - Function that computes homology for a representation
- `dest_point` - Function that extracts the underlying representation from a point

### Porting notes
When porting this definition:
- Ensure that the corresponding `homol` and `dest_point` functions are implemented first
- The definition simply composes these two functions, which is straightforward to port
- Be aware of the type system in the target proof assistant and ensure that the composition makes sense in that context

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
For all projective points $p$, the homogeneous coordinate vector $\text{homop}(p)$ is non-zero and $p$ equals the projective point corresponding to $\text{homop}(p)$, i.e., $p = \text{projp}(\text{homop}(p))$.

### Informal proof
The proof proceeds as follows:

1. We start with a goal to prove that for all projective points $p$:
   - $\text{homop}(p) \neq \vec{0}$, and
   - $p = \text{projp}(\text{homop}(p))$

2. We use the definitions of `homop_def` and `projp`.

3. We rewrite the goal using the fact that for any point $p$, $p = \text{mk\_point}(l)$ if and only if $\text{dest\_point}(p) = l$, which is established by the `point_tybij` theorem.

4. Finally, we complete the proof by applying the theorem `homol`, which relates homogeneous coordinates to projective points.

### Mathematical insight
This theorem establishes a fundamental relationship between projective points and their homogeneous coordinate representations. It ensures that:

1. The homogeneous coordinates of any projective point are non-zero (as required by the definition of projective space).
2. The mapping between projective points and their homogeneous representations is consistent - applying `projp` to the homogeneous coordinates of a point recovers the original point.

This relationship is essential for working with projective geometry in a computational context, as it allows us to switch between the abstract projective points and their concrete vector representations.

### Dependencies
- Definitions:
  - `homop_def` - Definition of homogeneous coordinates for a projective point
  - `projp` - Function mapping a homogeneous vector to a projective point
  - `point_tybij` - Theorem establishing the bijection between points and their internal representations
  - `homol` - Theorem relating homogeneous coordinates and projective points

### Porting notes
When porting this theorem:
- Ensure that your projective geometry formalization maintains the non-zero constraint on homogeneous coordinates
- Verify that your implementation of projective points preserves the round-trip property demonstrated here
- The proof depends on the specific representation of projective points in HOL Light, so you might need to adapt the proof strategy to match your system's representation

---

## parallel

### parallel
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let parallel = new_definition
 `parallel x y <=> x cross y = vec 0`;;
```

### Informal statement
Two vectors $x, y \in \mathbb{R}^3$ are parallel (denoted as $\text{parallel}(x, y)$) if and only if their cross product is the zero vector:
$$\text{parallel}(x, y) \Leftrightarrow x \times y = \vec{0}$$

### Informal proof
This is a definition, not a theorem, so there is no proof to translate.

### Mathematical insight
This definition captures the standard geometric notion of parallelism between vectors in $\mathbb{R}^3$. Two non-zero vectors are parallel if and only if they point in the same or opposite directions (i.e., one is a scalar multiple of the other). The cross product of two vectors is zero precisely when they are linearly dependent, which for non-zero vectors means they are parallel.

The definition is useful in the context of projective geometry and homogeneous coordinates (as suggested by the comment), where:
- Parallel vectors in $\mathbb{R}^3$ correspond to the same point in the projective plane $\mathbb{P}^2$
- The condition $x \times y = \vec{0}$ provides a computationally convenient way to check for parallelism

This definition serves as a fundamental building block for working with projective geometry in HOL Light.

### Dependencies
#### Definitions:
- `cross`: The cross product of two vectors in $\mathbb{R}^3$, defined as:
  ```
  (a:real^3) cross (b:real^3) =
      vector [a$2 * b$3 - a$3 * b$2;
              a$3 * b$1 - a$1 * b$3;
              a$1 * b$2 - a$2 * b$1] :real^3
  ```

### Porting notes
When porting this definition to other proof assistants:
1. Ensure that the target system has an existing cross product operation for 3D vectors
2. The definition itself is straightforward and should translate easily
3. Consider how the target system represents the zero vector (in HOL Light it's `vec 0`)
4. This definition will be particularly relevant when porting projective geometry theorems

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
For any point $p$ and line $l$, $p$ is on $l$ if and only if the homogeneous representation of point $p$ is orthogonal to the homogeneous representation of line $l$.

Formally:
$$\forall p, l. \; p \text{ on } l \Leftrightarrow \text{orthogonal}(\text{homop}(p), \text{homol}(l))$$

Where:
- $\text{homop}(p)$ is the homogeneous representation of point $p$
- $\text{homol}(l)$ is the homogeneous representation of line $l$
- $\text{orthogonal}(v, w)$ indicates that vectors $v$ and $w$ are orthogonal

### Informal proof
The proof establishes the equivalence between a point being on a line and their homogeneous representations being orthogonal:

1. Start with the goal $\forall p, l. \; p \text{ on } l \Leftrightarrow \text{orthogonal}(\text{homop}(p), \text{homol}(l))$

2. Rewrite using the definitions of homogeneous representations:
   - Expand the homogeneous representation of point ($\text{homop}$) and line ($\text{homol}$)
   
3. Rewrite using the definition of "on" relation and the projective representations:
   - Use the definition of a point being "on" a line in terms of projective coordinates
   - Apply the point type bijection rule

4. Rewrite using perpendicular line theorem ($\text{perpl\_th}$):
   - Express the orthogonality condition in terms of perpendicular directions

5. Apply binary operations to both sides to establish the equivalence

6. Complete the proof using MESON theorem prover with the homogeneous representations and the direction type bijection

### Mathematical insight
This theorem establishes a fundamental connection in projective geometry between incidence (a point being on a line) and orthogonality of homogeneous coordinates. In projective geometry, a point can be represented as a homogeneous vector, and a line can similarly be represented as a homogeneous vector. The theorem shows that the geometric relation of incidence directly corresponds to the algebraic relation of orthogonality between these homogeneous representations.

This relationship is central to the algebraic treatment of projective geometry and allows geometric problems to be translated into algebraic ones. It represents the duality between points and lines in projective geometry and provides an elegant computational method for determining when a point lies on a line.

### Dependencies
- `on`: Definition of when a point is on a line
- `homop`: Homogeneous representation of a point
- `homol`: Homogeneous representation of a line
- `projp`: Projective representation of a point
- `projl`: Projective representation of a line
- `orthogonal`: Definition of orthogonality between vectors
- `point_tybij`: Bijection related to point type
- `perpl_th`: Theorem about perpendicular lines
- `perpdir`: Definition of perpendicular directions
- `direction_tybij`: Bijection related to direction type

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the homogeneous representation of points and lines is defined consistently
- The duality between points and lines in projective geometry should be maintained
- The notion of orthogonality between homogeneous representations should be defined with the same semantic meaning

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
For all projective lines $l$ and $l'$, $l = l'$ if and only if $\text{homol}(l)$ is parallel to $\text{homol}(l')$.

In other words, two projective lines are equal precisely when their corresponding homologous Euclidean lines are parallel.

### Informal proof
The proof establishes the equivalence between equality of projective lines and parallelism of their homologous Euclidean lines:

1. We begin by converting the problem according to the definition of `homol`. The function $\text{homol}$ maps a projective line to its corresponding Euclidean line.

2. Using properties of the `projl` function and the line type bijection, we establish that:
   $\text{mk\_line}(||l) = \text{mk\_line}(||l') \iff ||l = ||l'$

   This uses the fact that `fst line_tybij` and `snd line_tybij` form a bijection between the representations.

3. The statement is further rewritten using `PARDIR_EQUIV`, which relates to the equivalence between parallel directions.

4. The proof is completed by expanding the definitions of `pardir` and `parallel`, and using the properties of the `homol` function and `direction_tybij`.

The essence of the proof relies on the bijective correspondence between projective lines and Euclidean directions, which allows us to translate equality in the projective space to parallelism in Euclidean space.

### Mathematical insight
This theorem captures a fundamental relationship between projective and Euclidean geometry. In projective geometry, lines that would be parallel in Euclidean space meet at points at infinity. The `homol` function maps projective lines to Euclidean lines, and this theorem establishes that two projective lines are identical precisely when their Euclidean counterparts are parallel.

This relationship is key to understanding the connection between projective and Euclidean spaces - equality in the projective space corresponds to parallelism in Euclidean space. The result is important for moving between these two geometric frameworks and understanding how concepts translate between them.

### Dependencies
- `homol`: Function mapping projective lines to Euclidean lines
- `parallel`: Relation indicating when two Euclidean lines are parallel
- `projl`: Function related to projective line representation
- `line_tybij`: Bijection for line types
- `PARDIR_EQUIV`: Theorem about equivalence of parallel directions
- `pardir`: Function related to parallel directions
- `direction_tybij`: Bijection for directions

### Porting notes
When porting this theorem to other systems:
- Ensure that the correspondence between projective and Euclidean geometry is established
- The bijections between different representations (`line_tybij`, `direction_tybij`) need to be properly defined
- The system should have means to express both projective equality and Euclidean parallelism

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
For any two points $p$ and $p'$, the equality $p = p'$ holds if and only if the homogeneous coordinates $\operatorname{homop}(p)$ and $\operatorname{homop}(p')$ are parallel vectors.

Formally:
$$\forall p, p' : \text{point}. \; (p = p') \Leftrightarrow \operatorname{parallel}(\operatorname{homop}(p), \operatorname{homop}(p'))$$

### Informal proof
The proof proceeds as follows:

1. First, we rewrite the goal using the definition of `homop` and the theorem `EQ_HOMOL`, which relates equality of points to parallelism of their homogeneous coordinates.

2. The goal is then solved using the `MESON_TAC` automated reasoning tool with the theorem `point_tybij`, which establishes that the type bijection between points and their homogeneous representations is well-defined.

In more detail, `homop` maps a point to its homogeneous coordinate representation. Two points are equal if and only if their homogeneous coordinates are parallel vectors (i.e., one is a scalar multiple of the other), which is exactly what this theorem establishes.

### Mathematical insight
This theorem establishes a fundamental connection between equality of points in projective geometry and the parallelism of their homogeneous coordinate representations. In projective geometry, points are typically represented by homogeneous coordinates where scalar multiples represent the same point. This theorem formalizes this key aspect of projective geometry.

The result is important because it allows us to translate questions about point equality into questions about vector parallelism, which can be more tractable in some contexts. This is a canonical result in the formalization of projective geometry.

### Dependencies
- **Definitions**:
  - `homop_def`: Definition of the homogeneous coordinates of a point.
  - `EQ_HOMOL`: Theorem relating equality of points to parallelism of their homogeneous coordinates.
  - `point_tybij`: Theorem establishing the type bijection for points.

### Porting notes
When porting this theorem to another system, ensure that:
1. The notion of "parallelism" between vectors is properly defined (two vectors are parallel if one is a scalar multiple of the other).
2. The homogeneous representation of points is consistent with projective geometry principles.
3. The type bijection between points and their homogeneous representations is established.

---

## PARALLEL_PROJL_HOMOL

### PARALLEL_PROJL_HOMOL
- `PARALLEL_PROJL_HOMOL`

### Type of the formal statement
- theorem

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
For any vector $x \in \mathbb{R}^3$, the vector $x$ is parallel to the homogeneous coordinate representation of the projection line of $x$, denoted as $\text{homol}(\text{projl}(x))$.

### Informal proof
The proof establishes that for any vector $x \in \mathbb{R}^3$, $x$ is parallel to $\text{homol}(\text{projl}(x))$.

- First, we unfold the definition of parallelism between vectors, which means their cross product is zero.

- We consider two cases:
  * Case 1: When $x = 0$. In this case, the cross product of $x$ with any vector is zero by the theorem `CROSS_0`. 
  
  * Case 2: When $x \neq 0$. We use the definition of `homol`, which gives us information about the homogeneous coordinate representation.
  
- Let's consider the projection line of $x$, denoted as `projl x`, which creates a line through the origin in the direction of $x$.

- By using the properties of `line_tybij` (which relates lines to their representations), and `PARDIR_EQUIV` (which relates parallelism to directions), we show that `x` must be parallel to `homol(projl x)`.

- This is because `projl` maps a vector to a line in its direction, and `homol` maps that line back to a vector in the same direction, ensuring that the resulting vector is parallel to the original vector.

### Mathematical insight
This theorem demonstrates a fundamental "well-definedness" property of the homogeneous coordinate mapping. It shows that the homol function, when applied to the projection line of a vector, produces a vector that is parallel to the original vector. 

This property is important in projective geometry and computer graphics, where homogeneous coordinates are used to represent points and lines in projective space. The theorem ensures that the directional information is preserved when mapping between different representations (vectors and lines), which is crucial for consistency in geometric computations.

### Dependencies
- Theorems:
  - `CROSS_0`: Establishes that the cross product of the zero vector with any vector is zero.
- Other dependencies (from context):
  - `parallel`: Definition of parallel vectors (vectors whose cross product is zero).
  - `homol`: Function that maps from lines to homogeneous coordinates.
  - `projl`: Function that maps a vector to a projection line.
  - `line_tybij`: Type bijection for lines.
  - `PARDIR_EQUIV`: Equivalence between parallel lines and directions.
  - `pardir`: Function related to parallel directions.
  - `direction_tybij`: Type bijection for directions.

### Porting notes
When porting this theorem, pay attention to:
- The representation of lines and directions in the target system
- How the bijections between different geometric representations are defined
- The definition of parallelism between vectors (cross product being zero)
- The homogeneous coordinate system implementation

Many proof assistants have different approaches to representing geometric objects, so the exact definitions of `projl`, `homol`, and the bijections may need adaptation.

---

## PARALLEL_PROJP_HOMOP

### PARALLEL_PROJP_HOMOP
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PARALLEL_PROJP_HOMOP = prove
 (`!x. parallel x (homop(projp x))`,
  REWRITE_TAC[homop_def; projp; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[PARALLEL_PROJL_HOMOL]);;
```

### Informal statement
For any projective point $x$, the lines $x$ and $\text{homop}(\text{projp}(x))$ are parallel.

Mathematically, this states that:
$$\forall x. \text{parallel}(x, \text{homop}(\text{projp}(x)))$$

Where:
- $\text{projp}$ is a function that maps a projective point to its corresponding homogeneous point
- $\text{homop}$ is a function that maps a homogeneous point to a projective line
- $\text{parallel}$ is a relation indicating that two lines are parallel

### Informal proof
The proof proceeds as follows:

1. First, we expand the definition of $\text{homop}$ and $\text{projp}$.
2. The definition $\text{homop}$ is rewritten using its definition.
3. The term $\text{projp}$ is also rewritten.
4. We use the point type bijection properties (from $\text{point\_tybij}$).
5. Finally, the proof is completed by applying the theorem $\text{PARALLEL\_PROJL\_HOMOL}$, which establishes a parallel relationship between projective lines and homogeneous operations.

In essence, this theorem extends a known parallel relationship from lines to points in projective geometry.

### Mathematical insight
This theorem establishes an important relationship between projective points and their corresponding lines in projective geometry. It shows that when we convert a projective point to its homogeneous representation and then map it to a projective line, the resulting line is parallel to the original point (when the point is interpreted as a line).

This result is significant in projective geometry because it demonstrates the duality principle - points and lines can be interchanged while preserving certain geometric relationships. The parallel nature of the lines shows a kind of invariance under the transformations defined by $\text{projp}$ and $\text{homop}$.

The theorem helps maintain consistency in the projective geometry formalization by ensuring that parallel relationships are preserved through these mapping operations.

### Dependencies
- `homop_def`: Definition of homogeneous operation on points
- `projp`: Definition of projection for points
- `point_tybij`: Theorem about type bijection for points
- `PARALLEL_PROJL_HOMOL`: Theorem establishing parallel relationship between projective lines and homogeneous operations

### Porting notes
When porting this theorem:
1. Ensure that the projective geometry foundations, particularly the concepts of projective points, homogeneous points, and the parallel relation, are properly defined.
2. The bijection between different representations of points should be established before this theorem.
3. The corresponding theorem for lines (`PARALLEL_PROJL_HOMOL`) should be ported before this one, as this theorem builds upon it.
4. The rewrite tactics used here suggest that the proof is relatively straightforward once the dependencies are in place, but proper type handling may require careful attention in typed systems.

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
For any vector $x \in \mathbb{R}^3$ where $x \neq \vec{0}$, there exists a real number $a$ such that $a \neq 0$ and $\text{homop}(\text{projp}(x)) = a \cdot x$, where $\text{homop}(\text{projp}(x))$ represents the homogeneous operation of the projection of $x$.

### Informal proof
The proof leverages the theorem `PARALLEL_PROJP_HOMOP`, which states that the homogeneous operation of the projection of a vector is parallel to the original vector.

1. We start with the theorem `PARALLEL_PROJP_HOMOP` and use `MONO_FORALL` to transform it.
2. We rewrite the parallelism condition using:
   - Definition of `parallel`, which states that two vectors are parallel if their cross product equals zero
   - Theorem `CROSS_EQ_0`, which states that the cross product of two vectors equals zero if and only if they are collinear with the zero vector
   - `COLLINEAR_LEMMA`, which relates collinearity to the existence of a scalar multiplier

3. For an arbitrary vector $x$, we consider two cases:
   - Case $x = \vec{0}$: This case is eliminated by our assumption.
   - Case $x \neq \vec{0}$: We use the definition of `homop` and proceed.

4. We then need to show the existence of a non-zero scalar $c$ such that $\text{homop}(\text{projp}(x)) = c \cdot x$.
   - We consider two subcases for the scalar $c$:
     - Case $c = 0$: This would make $c \cdot x = \vec{0}$, but since $\text{homop}(\text{projp}(x))$ is parallel to $x$ (and $x \neq \vec{0}$), this cannot happen.
     - Case $c \neq 0$: This satisfies our requirement, proving the existence of a non-zero scalar $a$ such that $\text{homop}(\text{projp}(x)) = a \cdot x$.

### Mathematical insight
This theorem provides an explicit representation of the homogeneous operation of the projection of a non-zero vector in $\mathbb{R}^3$. It shows that this operation produces a vector that is a non-zero scalar multiple of the original vector. This result is important in projective geometry, where it helps establish the relationship between projective transformations and their corresponding homogeneous representations.

The key insight is that projective operations preserve direction (up to scaling) for non-zero vectors, which is fundamental to understanding how projective geometry relates to Euclidean geometry.

### Dependencies
- Theorems:
  - `PARALLEL_PROJP_HOMOP`: States that the homogeneous operation of a projection of a vector is parallel to the original vector
  - `CROSS_EQ_0`: Establishes that the cross product of two vectors is zero if and only if they are collinear with the zero vector

- Functions and operations:
  - `homop`: The homogeneous operation
  - `projp`: The projection operation
  - `parallel`: The parallelism relation between vectors
  - `COLLINEAR_LEMMA`: A lemma relating collinearity to scalar multiplication

### Porting notes
When porting this theorem to another proof assistant:
1. Ensure that the projective operations (`projp` and `homop`) are properly defined.
2. The concept of parallelism between vectors might be defined differently in other systems.
3. The cross product and collinearity properties in $\mathbb{R}^3$ should be available.
4. The handling of special cases (like zero vectors) might require different approaches in other systems.

---

## bracket

### bracket

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let bracket = define
 `bracket[a;b;c] = det(vector[homop a;homop b;homop c])`;;
```

### Informal statement
The function `bracket[a;b;c]` is defined as the determinant of the matrix formed by the vectors obtained by applying the homogeneous coordinate map (`homop`) to the points a, b, and c:

$$\text{bracket}[a;b;c] = \det(\text{vector}[\text{homop}(a), \text{homop}(b), \text{homop}(c)])$$

where `homop` converts a point to its homogeneous coordinates, and `vector` arranges these coordinates into a matrix whose determinant is then calculated.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The bracket function is a fundamental concept in projective geometry, particularly for studying collinearity of points. The determinant of three homogeneous vectors is zero if and only if the three points are collinear.

This construction allows for a clean algebraic formulation of the geometric property of collinearity. When the determinant is zero, it indicates that the three homogeneous vectors are linearly dependent, which geometrically means the corresponding points are collinear.

The bracket notation is commonly used in projective geometry and has connections to the "bracket algebra" in geometric algebra. It provides an elegant way to express various geometric conditions using determinants.

### Dependencies
- Functions:
  - `det`: Calculates the determinant of a matrix
  - `vector`: Constructs a vector or matrix from elements
  - `homop`: Converts a point to its homogeneous coordinates

### Porting notes
When porting this definition to another system, ensure that:
1. The homogeneous coordinate mapping (`homop`) is correctly implemented
2. The determinant calculation works with the appropriate dimensions
3. The vector construction creates a matrix suitable for determinant calculation
4. The system can handle the bracket notation semantics correctly

---

## COLLINEAR

### COLLINEAR
- `COLLINEAR`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let COLLINEAR = new_definition
 `COLLINEAR s <=> ?l. !p. p IN s ==> p on l`;;
```

### Informal statement
A set of points $s$ is collinear if and only if there exists a line $l$ such that all points $p$ in $s$ lie on $l$.

Formally, $\text{COLLINEAR}(s) \Leftrightarrow \exists l. \forall p. p \in s \Rightarrow p \text{ on } l$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition captures the fundamental geometric concept of collinearity - when all points in a set lie on a single line. This is a basic concept in Euclidean geometry and serves as a foundation for many geometric theorems.

Collinearity is an important property in computational geometry and has applications in various geometric proofs. For example:
- Three or more points that are collinear cannot form a proper triangle or polygon
- Collinearity tests are used in many geometric algorithms
- Many geometric theorems have special cases when points are collinear

The definition uses the "on" relation between points and lines, assuming this relation is defined elsewhere in the formalization.

### Dependencies
- Relies on the following concepts (not explicitly listed in the dependencies):
  - The `on` relation between points and lines
  - Set membership operation `IN`

### Porting notes
When porting this definition:
- Ensure that the target system has appropriate representations for points, lines, and the "on" relation
- The definition is straightforward and should translate directly to most proof assistants
- Check if the target system has a standard library definition for collinearity; if so, consider using that instead

---

## COLLINEAR_SINGLETON

### COLLINEAR_SINGLETON
- COLLINEAR_SINGLETON

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let COLLINEAR_SINGLETON = prove
 (`!a. COLLINEAR {a}`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[AXIOM_1; AXIOM_3]);;
```

### Informal statement
For any point $a$, the singleton set $\{a\}$ is collinear.

In other words, any set containing exactly one point satisfies the collinearity property.

### Informal proof
The theorem is proven by:

- First, the definition of collinearity is applied and the universal quantifier over the singleton set $\{a\}$ is expanded.
- The theorem follows from the axioms of projective geometry, specifically:
  - Axiom 1 (AXIOM_1), which states that any two distinct points determine a unique line.
  - Axiom 3 (AXIOM_3), which states that there exist at least three non-collinear points.

The proof uses MESON (a model elimination theorem prover) to automatically derive the result from these axioms.

### Mathematical insight
This theorem states a trivial but necessary property of collinearity: a set with only a single point is always collinear. This is logically consistent with the definition of collinearity which requires that all points in a set lie on the same line.

The result forms part of the foundational properties of collinearity in projective geometry and helps establish boundary cases for theorems involving collinearity. While seemingly trivial, establishing such base cases is important for formal developments to ensure completeness.

### Dependencies
- **Definitions:**
  - `COLLINEAR` - Definition of collinear points
- **Axioms:**
  - `AXIOM_1` - Two distinct points determine a unique line
  - `AXIOM_3` - There exist at least three non-collinear points

### Porting notes
When porting this theorem:
- Ensure that the definition of collinearity in the target system has the appropriate handling of degenerate cases like singletons
- The theorem is straightforward and should be easily provable in any system with the corresponding axioms of projective geometry

---

## COLLINEAR_PAIR

### COLLINEAR_PAIR
- `COLLINEAR_PAIR`

### Type of the formal statement
- theorem

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
For all points $a$ and $b$, the set $\{a, b\}$ is collinear.

### Informal proof
The proof proceeds as follows:

* First, we consider two cases: either $a = b$ or $a \neq b$.
* If $a = b$, then $\{a, b\} = \{a\}$, which is a singleton set. By `COLLINEAR_SINGLETON`, any singleton set of points is collinear.
* If $a \neq b$, we use the definition of collinearity: a set of points is collinear if every three distinct points in the set are collinear.
* Since $\{a, b\}$ contains only two points, there cannot be three distinct points within this set.
* Therefore, the condition for collinearity is trivially satisfied (the universal quantifier over an empty set is true).
* Additionally, the proof uses `AXIOM_1`, which likely states that two distinct points determine a unique line.

### Mathematical insight
This theorem establishes the basic fact that any two points (whether distinct or not) are always collinear. This is fundamentally consistent with the geometric intuition that two points always lie on a straight line. The theorem handles both the case where the points are the same (resulting in a singleton set) and where they are distinct.

In Euclidean geometry, collinearity is a fundamental concept, and this theorem affirms that the minimum requirement for points to be on a line is satisfied by any pair of points. This result is often used as a building block for more complex geometric theorems.

### Dependencies
- `COLLINEAR_SINGLETON`: Theorem stating that a singleton set of points is collinear
- `COLLINEAR`: Definition of collinearity for a set of points
- `AXIOM_1`: Likely the axiom that two distinct points determine a unique line

### Porting notes
When porting this theorem:
1. Ensure that your target system has an equivalent definition of collinearity
2. The handling of the empty universal quantifier case may differ between proof assistants
3. The set-theoretic operations and notation might need adjustment depending on the target system's library

---

## COLLINEAR_TRIPLE

### COLLINEAR_TRIPLE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let COLLINEAR_TRIPLE = prove
 (`!a b c. COLLINEAR{a,b,c} <=> ?l. a on l /\ b on l /\ c on l`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY]);;
```

### Informal statement
For any three points $a$, $b$, and $c$, the set $\{a, b, c\}$ is collinear if and only if there exists a line $l$ such that $a$ lies on $l$, $b$ lies on $l$, and $c$ lies on $l$.

In mathematical notation:
$$\forall a, b, c.~ \text{COLLINEAR}\{a, b, c\} \iff \exists l.~ (a \text{ on } l) \land (b \text{ on } l) \land (c \text{ on } l)$$

### Informal proof
The proof is completed by rewriting with the definition of `COLLINEAR`, and reducing the set membership condition using `FORALL_IN_INSERT` and `NOT_IN_EMPTY`.

The theorem follows directly from expanding the definition of `COLLINEAR` for a set of three points and simplifying the set-theoretic expressions.

### Mathematical insight
This theorem provides a clear and intuitive characterization of collinearity for three points. While the general definition of `COLLINEAR` might involve more complex set-theoretic concepts, this theorem simplifies the notion to its most basic understanding: three points are collinear precisely when they all lie on the same line.

This characterization is particularly useful in geometric proofs where collinearity of three specific points needs to be established or used. It reduces the property of collinearity to the existence of a common line containing the three points, which is often easier to work with in practical applications.

### Dependencies
- `COLLINEAR` - Definition of collinearity for a set of points
- `FORALL_IN_INSERT` - Theorem about universal quantification over inserted elements in a set
- `NOT_IN_EMPTY` - Theorem stating that no element is in the empty set

---

## COLLINEAR_BRACKET

### COLLINEAR_BRACKET
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
The theorem states that three points $p_1$, $p_2$, and $p_3$ are collinear if and only if their bracket is zero, i.e.,
$$\text{COLLINEAR} \{p_1, p_2, p_3\} \iff \text{bracket}[p_1; p_2; p_3] = 0$$

Here, $\text{COLLINEAR}$ refers to the property that all points in the given set lie on a single line, and $\text{bracket}[p_1; p_2; p_3]$ is the triple scalar product that gives the signed volume of the parallelepiped formed by the vectors represented by these points.

### Informal proof
The proof proceeds in both directions:

1. First, we prove that if the points are collinear, then their bracket is zero:
   - We use the fact that collinearity can be expressed in terms of homologies (via `COLLINEAR_TRIPLE` and `ON_HOMOL`).
   - We simplify using the definition of determinant for 3×3 matrices and properties of dot products in 3D space.
   - The result follows by algebraic manipulation.

2. For the converse, we prove that if the bracket is zero, then the points are collinear:
   - We handle the special case where $p_1 = p_2$ separately. In this case, collinearity follows trivially.
   - For the general case, we show that if the bracket is zero, then there exists a line containing all three points.
   - This is done by using the cross product of the homogeneous representations of $p_1$ and $p_2$ to define a direction.
   - The key insight is that if the bracket (which relates to the determinant) is zero, then the vectors are linearly dependent.
   - We use `lemma` to show that if $p_3$ is orthogonal to this cross product, it must lie on the same line.
   - We utilize properties of cross products like `ORTHOGONAL_CROSS` and the relationship between cross products and determinants (`DOT_CROSS_DET`).

### Mathematical insight
This theorem establishes an important connection between the geometric concept of collinearity and an algebraic condition using the bracket operation. The bracket (also known as the scalar triple product) gives the signed volume of the parallelepiped defined by three vectors. When this volume is zero, the vectors are coplanar, and in the context of projective geometry, this means the corresponding points are collinear.

This result is fundamental in projective geometry and computational geometry, as it provides an algebraic test for collinearity. It's also closely related to the concept of determinants in linear algebra, highlighting the deep connection between geometric properties and algebraic structures.

### Dependencies
- **Theorems:**
  - `ORTHOGONAL_CROSS`: States that cross product of two vectors is orthogonal to both vectors
  - `CROSS_TRIPLE`: Relates dot products of cross products in a cycle of three vectors
  - `DOT_CROSS_DET`: Relates the dot product of a vector with a cross product to a determinant
- **Definitions:**
  - `cross`: Definition of the cross product of two 3D vectors

### Porting notes
When porting this theorem:
- Ensure your system has an appropriate representation for projective geometry, especially if it differs from HOL Light's implementation.
- The proof relies heavily on properties of cross products in 3D space and their relationship to determinants, so these foundational results should be ported first.
- The concept of homogeneous coordinates might need to be adapted depending on how your target system handles projective geometry.

---

## homogeneous_conic

### homogeneous_conic

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
A set $con$ is a homogeneous conic if and only if there exist real numbers $a$, $b$, $c$, $d$, $e$, and $f$, not all zero, such that
$$con = \{x \in \mathbb{R}^3 \mid ax_1^2 + bx_2^2 + cx_3^2 + dx_1x_2 + ex_1x_3 + fx_2x_3 = 0\}$$

This defines a conic section in homogeneous coordinates, represented as the zero set of a homogeneous quadratic polynomial in three variables.

### Informal proof
No proof is provided as this is a definition.

### Mathematical insight
This definition represents conic sections in projective geometry using homogeneous coordinates. The homogeneous equation $ax_1^2 + bx_2^2 + cx_3^2 + dx_1x_2 + ex_1x_3 + fx_2x_3 = 0$ captures all types of conics (ellipses, parabolas, and hyperbolas) as well as degenerate cases (pairs of lines, single lines, or points).

The requirement that not all coefficients are zero ensures that the equation defines a proper geometric locus. In projective geometry, working with homogeneous coordinates allows for a unified treatment of conics, including those passing through "points at infinity."

This definition is used in projective geometry for results like Pascal's theorem about hexagons inscribed in conics, as suggested by the file name.

### Dependencies
#### Definitions
- Not explicitly mentioned in the provided dependencies.

### Porting notes
When porting this definition:
1. Ensure the target system has support for set comprehension notation
2. Verify that the system has a well-defined notion of homogeneous coordinates and vectors
3. The indexing notation `x$1`, `x$2`, `x$3` refers to components of a 3D vector - adapt to the target system's vector component access syntax

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
A set $\text{con}$ is a projective conic if and only if there exists a homogeneous conic $c$ such that $\text{con} = \{p \mid \text{homop}(p) \in c\}$.

In other words, a projective conic is the set of projective points that, when mapped to their homogeneous coordinates via the function $\text{homop}$, satisfy a homogeneous quadratic equation.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition formalizes the concept of a projective conic section in projective geometry. Projective conics are important geometric objects that generalize the Euclidean conic sections (ellipses, parabolas, and hyperbolas) to projective space.

The key insight is that projective conics can be defined via homogeneous coordinates. A homogeneous conic is defined as a set of points in $\mathbb{R}^3$ satisfying a homogeneous quadratic equation:
$ax_1^2 + bx_2^2 + cx_3^2 + dx_1x_2 + ex_1x_3 + fx_2x_3 = 0$

The projective conic is then obtained by considering the corresponding points in the projective plane. The function $\text{homop}$ maps projective points to their homogeneous coordinates, establishing the connection between projective geometry and linear algebra.

This definition is particularly useful for formalizing results like Pascal's theorem and other projective geometry theorems involving conics.

### Dependencies
#### Definitions
- `homogeneous_conic`: Defines a conic section in homogeneous coordinates as a set of points in $\mathbb{R}^3$ satisfying a homogeneous quadratic equation.

### Porting notes
When porting this definition:
1. Ensure that the target system has a formalization of homogeneous coordinates and projective geometry.
2. The function `homop` (not shown in the dependencies) likely maps projective points to their homogeneous coordinates - ensure this function is properly defined in the target system.
3. The definition relies on set comprehension notation which may need to be adapted to the target system's syntax.

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
For any homogeneous conic section $\text{con}$ in projective space $\mathbb{R}^3$ and six points $x_1, x_2, x_3, x_4, x_5, x_6 \in \text{con}$ on this conic, the following identity holds:
$$\det(x_6, x_1, x_4) \cdot \det(x_6, x_2, x_3) \cdot \det(x_5, x_1, x_3) \cdot \det(x_5, x_2, x_4) = \det(x_6, x_1, x_3) \cdot \det(x_6, x_2, x_4) \cdot \det(x_5, x_1, x_4) \cdot \det(x_5, x_2, x_3)$$

where $\det(x, y, z)$ represents the determinant of the matrix formed by column vectors $x$, $y$, and $z$.

### Informal proof
The proof proceeds as follows:

1. We start with the definition of a homogeneous conic section, which is a set of points $\{x \in \mathbb{R}^3 \mid ax_1^2 + bx_2^2 + cx_3^2 + dx_1x_2 + ex_1x_3 + fx_2x_3 = 0\}$ where at least one of $a, b, c, d, e, f$ is non-zero.

2. For the six points on the conic, we know that they all satisfy the homogeneous quadratic equation defining the conic.

3. The determinant expressions in the theorem involve 3×3 matrices formed by these points. When we expand these determinants and consider the algebraic relations satisfied by the coordinates of these points (since they all lie on the conic), the equality can be verified through algebraic manipulation.

4. The final step uses `REAL_RING`, a decision procedure for polynomial equations over real numbers, which completes the proof by algebraic verification.

The theorem essentially represents a projective invariant relation between determinants formed by points on a conic section.

### Mathematical insight
This theorem is a fundamental result in projective geometry that relates to Pascal's theorem for conics. It establishes an invariant relationship between determinants formed by six points on a conic section, which can be seen as a form of the "cross-ratio" preserved under projective transformations.

The result is important because:

1. It provides a pure algebraic characterization of when six points lie on a conic without explicitly using the conic equation.

2. It's related to broader concepts in algebraic geometry, particularly to the structure of Cayley-Menger determinants and the geometry of quadrics.

3. Such invariant relationships are crucial in computer vision, geometric modeling, and projective invariant computations.

The theorem can be viewed as a higher-dimensional analogue of cross-ratio preservation, which is a fundamental principle in projective geometry.

### Dependencies
- **Definitions**
  - `homogeneous_conic`: Defines a homogeneous conic in projective space as the zero set of a homogeneous quadratic polynomial in three variables where not all coefficients are zero.
- **Theorems** (implicitly used)
  - `DET_3`: Theorem for evaluating 3×3 determinants
  - `VECTOR_3`: Properties of 3-dimensional vectors

### Porting notes
When porting this theorem:
1. Ensure the target system has a suitable representation of homogeneous conics and determinants.
2. The proof relies on a decision procedure for real arithmetic (`REAL_RING`), so you'll need a similar capability in the target system or may need to provide a more detailed algebraic proof.
3. The result is purely algebraic once the definitions are established, so the port should be straightforward if the target system has good support for multivariate polynomial arithmetic.

---

## PROJECTIVE_CONIC_BRACKET

### PROJECTIVE_CONIC_BRACKET
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PROJECTIVE_CONIC_BRACKET = prove
 (`!con p1 p2 p3 p4 p5 p6.
        projective_conic con /\
        p1 IN con /\ p2 IN con /\ p3 IN con /\
        p4 IN con /\ p5 IN con /\ p6 IN con
        ==> bracket[p6;p1;p4] * bracket[p6;p2;p3] *
            bracket[p5;p1;p3] * bracket[p5;p2;p4] =
            bracket[p6;p1;p3] * bracket[p6;p2;p4] *
            bracket[p5;p1;p4] * bracket[p5;p2;p3]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bracket; projective_conic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC HOMOGENEOUS_CONIC_BRACKET THEN ASM_MESON_TAC[]);;
```

### Informal statement
For any projective conic $\text{con}$ and points $p_1, p_2, p_3, p_4, p_5, p_6$ on the conic, the following equality holds:
$$\text{bracket}[p_6, p_1, p_4] \cdot \text{bracket}[p_6, p_2, p_3] \cdot \text{bracket}[p_5, p_1, p_3] \cdot \text{bracket}[p_5, p_2, p_4] = \text{bracket}[p_6, p_1, p_3] \cdot \text{bracket}[p_6, p_2, p_4] \cdot \text{bracket}[p_5, p_1, p_4] \cdot \text{bracket}[p_5, p_2, p_3]$$

Where $\text{bracket}[p, q, r]$ represents the determinant of the matrix formed by the homogeneous coordinates of the projective points.

### Informal proof
This theorem extends the result from homogeneous conics to projective conics. The proof proceeds as follows:

1. We use the definition of projective conics: a set $\text{con}$ is a projective conic if and only if there exists a homogeneous conic $c$ such that $\text{con} = \{p \mid \text{homop}(p) \in c\}$, where $\text{homop}$ maps a projective point to its homogeneous representation.

2. Since all points $p_1$ through $p_6$ lie on the projective conic $\text{con}$, their homogeneous representations $\text{homop}(p_1)$ through $\text{homop}(p_6)$ must lie on the corresponding homogeneous conic $c$.

3. We know from the bracket definition that $\text{bracket}[p,q,r] = \text{det}(\text{vector}[\text{homop}(p), \text{homop}(q), \text{homop}(r)])$.

4. The result now follows directly by applying the theorem `HOMOGENEOUS_CONIC_BRACKET` to the homogeneous representations of the points, which states that for any homogeneous conic and six points on it, the corresponding product of determinants satisfies the same equality.

### Mathematical insight
This theorem represents an important invariant relationship for points lying on a projective conic. The equality of these two products of brackets has profound geometric significance in projective geometry. It's a manifestation of Pascal's theorem in the language of projective coordinates.

The bracket notation represents the determinant of homogeneous coordinates, which effectively measures the "projective volume" spanned by three points. This theorem provides a way to relate these volumes in a specific pattern when the points lie on a conic.

This result is important as it gives a coordinate-free way of expressing projective relationships and can be used to prove other properties of conics without resorting to specific coordinate systems.

### Dependencies
- **Theorems**:
  - `HOMOGENEOUS_CONIC_BRACKET`: States a similar relationship for points on a homogeneous conic

- **Definitions**:
  - `projective_conic`: Defines a projective conic in terms of a homogeneous conic
  - `bracket`: (Implicit) Represents the determinant of homogeneous coordinates

### Porting notes
When porting this theorem:
1. Ensure the underlying definitions of projective conics and homogeneous conics are correctly established.
2. The proof relies heavily on the corresponding theorem for homogeneous conics, so that should be ported first.
3. The proof uses HOL Light's `ASM_MESON_TAC` for automated reasoning in the final step - in other proof assistants, this might require more explicit intermediate steps.

---

## PASCAL_DIRECT

### PASCAL_DIRECT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
        ~COLLINEAR {x3,x4,x6} /\
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
    --bracket[x1;x5;x7] * bracket[x3;x5;x8]` THEN
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

This theorem states a direct form of Pascal's theorem in projective geometry. 

Let $x_1, x_2, x_3, x_4, x_5, x_6$ be six points lying on a projective conic $con$, with several non-collinearity conditions ensuring the configuration is non-degenerate. 

If we define points $x_7, x_8, x_9$ such that:
- $x_1, x_9, x_5$ are collinear
- $x_1, x_8, x_6$ are collinear
- $x_2, x_9, x_4$ are collinear
- $x_2, x_7, x_6$ are collinear
- $x_3, x_8, x_4$ are collinear
- $x_3, x_7, x_5$ are collinear

Then the three points $x_7, x_8, x_9$ are collinear.

### Informal proof

The proof applies the projective conic bracket relation (theorem `PROJECTIVE_CONIC_BRACKET`) and uses properties of the determinant-based bracket function to establish the collinearity of points $x_7, x_8, x_9$.

The proof proceeds as follows:

- First, we reformulate the theorem to isolate the final collinearity claim as the conclusion.
- We apply the `PROJECTIVE_CONIC_BRACKET` theorem which relates products of bracket expressions for points on a projective conic.
- The proof then establishes a key intermediate claim that involves multiple bracket relations. This intermediate claim consists of seven equations relating various bracket expressions.
- The proof verifies these bracket equations are valid using properties of the determinant and vector operations.
- We then use our given collinearity conditions (which can be expressed using the bracket function) to simplify the equations.
- The non-collinearity assumptions ensure that various bracket expressions are non-zero, allowing us to cancel them from both sides of equations.
- Finally, through algebraic manipulations of the bracket expressions, we establish that $[x_7,x_8,x_9] = 0$, which proves the collinearity of points $x_7, x_8, x_9$.

### Mathematical insight

Pascal's theorem is a fundamental result in projective geometry. It states that if six points are arranged in any order on a conic section, then the three intersection points of the opposite sides of the resulting hexagon are collinear.

The theorem presented here is a direct formulation of Pascal's theorem with explicitly stated non-degeneracy conditions. These conditions ensure that all the relevant intersections are well-defined.

The proof uses the bracket notation, which represents the determinant of three points. When the bracket $[p,q,r]$ equals zero, it indicates that the three points $p$, $q$, and $r$ are collinear.

This result is important in the study of projective geometry and conic sections, providing a powerful way to establish collinearity relationships. The theorem is named after the French mathematician Blaise Pascal, who discovered it at the age of 16.

### Dependencies
- Theorems:
  - `PROJECTIVE_CONIC_BRACKET`: States a key relationship between bracket products for points on a projective conic.
- Definitions:
  - `projective_conic`: Defines a projective conic as the set of projective points whose homogeneous coordinates lie on a homogeneous conic.

### Porting notes
When porting this theorem to another proof assistant:
- Ensure the bracket notation is properly defined as the determinant of three points.
- The handling of projective geometry concepts may vary between systems; ensure that projective points and conics are appropriately defined.
- The proof relies heavily on algebraic manipulations of determinant expressions, which might require different approaches in systems with different automation capabilities.
- The numerous non-collinearity conditions are important for the proof's validity; ensure they are properly represented.

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
Pascal's theorem states that:

For any projective conic `con` and points $x_1, x_2, x_3, x_4, x_5, x_6$ (all distinct and lying on the conic), if we assume:
- None of the triplets of points from $\{x_1, x_2, x_3, x_4, x_5, x_6\}$ are collinear
- Points $x_9$ lies on the line through $x_1$ and $x_5$
- Points $x_8$ lies on the line through $x_1$ and $x_6$
- Points $x_9$ lies on the line through $x_2$ and $x_4$
- Points $x_7$ lies on the line through $x_2$ and $x_6$
- Points $x_8$ lies on the line through $x_3$ and $x_4$
- Points $x_7$ lies on the line through $x_3$ and $x_5$

Then the three points $x_7, x_8, x_9$ are collinear.

### Informal proof
The proof employs Pascal's direct form (`PASCAL_DIRECT`) and proceeds through careful manipulation of the non-degeneracy conditions.

The proof strategy is:
- Use the principle that if we can prove $(¬p ⇒ p)$, then $p$ must be true
- Assume $x_7, x_8, x_9$ are not collinear (the negation of our conclusion)
- Apply the direct form of Pascal's theorem (`PASCAL_DIRECT`) to derive a contradiction
- The direct form contains more specific conditions about non-collinearity
- Show that the non-collinearity conditions in this theorem are sufficient to fulfill the requirements of the direct form
- Use algebraic manipulation with the bracket algebra and determinants to verify the conditions

The core part of the proof relies on the algebraic representation of collinearity using brackets (determinants) and on the algebraic properties of projective conics.

### Mathematical insight
Pascal's theorem is a fundamental result in projective geometry, describing a surprising relation between six points on a conic. When connecting these points in a specific pattern, the three intersection points of opposite sides of the resulting hexagon are always collinear.

The theorem presented here uses a particularly clean formulation with non-degeneracy conditions that are easy to understand: no three points from the six points on the conic should be collinear. This makes the theorem intuitive while still capturing its essence.

The line formed by points $x_7, x_8, x_9$ is often called "Pascal's line" in classical projective geometry. This result has many applications in geometry, including helping to construct conics through five given points and in proving other fundamental theorems in projective geometry.

### Dependencies
- Definitions:
  - `projective_conic`: Defines a projective conic as the projective image of a homogeneous conic
  
- Theorems:
  - `PASCAL_DIRECT`: A more direct form of Pascal's theorem with specific non-degeneracy conditions
  - Related collinearity and bracket algebra theorems

### Porting notes
When porting this theorem:
1. Ensure that the underlying projective geometry framework is in place, particularly the definitions of projective conics and collinearity
2. Be careful with the non-degeneracy conditions, which can be expressed differently in different systems
3. The proof relies on algebraic manipulation of determinants and bracket algebra, which might require different techniques in other proof assistants
4. The implementation of Pascal's direct theorem (`PASCAL_DIRECT`) is essential and should be ported first

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
The `homogenize` function maps points from the affine plane $\mathbb{R}^2$ to the projective plane $\mathbb{R}^3$ by adding a homogeneous coordinate with value 1.

Formally, for any vector $x \in \mathbb{R}^2$, the function is defined as:
$$\text{homogenize}(x) = \begin{bmatrix} x_1 \\ x_2 \\ 1 \end{bmatrix}$$

where $x_1$ and $x_2$ are the components of the 2D vector $x$.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition establishes the conversion between affine coordinates and projective coordinates, which is fundamental in projective geometry. The homogenize function embeds the affine plane into the projective plane by adding a third coordinate with value 1.

In projective geometry, points in the projective plane are typically represented using homogeneous coordinates $(x:y:z)$ where $(x,y,z) \neq (0,0,0)$ and two triples $(x_1,y_1,z_1)$ and $(x_2,y_2,z_2)$ represent the same point if one is a non-zero scalar multiple of the other. 

The homogenize function maps a point $(x,y)$ in the affine plane to the projective point $(x:y:1)$. This mapping allows affine transformations to be represented as linear transformations in the projective space, which is mathematically elegant and computationally advantageous.

Points at infinity in the projective plane correspond to directions in the affine plane and have homogeneous coordinates with $z = 0$.

### Dependencies
#### Definitions
- `homogenize` from pascal.ml

### Porting notes
When porting this definition to other proof assistants:
- Ensure the target system has appropriate vector types and operations
- The indexing of vector components might differ between systems (e.g., 0-based vs. 1-based indexing)
- The notation for creating vectors may vary; HOL Light uses `vector[...]` while other systems might use different syntax

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
The function $\text{projectivize}$ is defined as the composition of the functions $\text{projp}$ and $\text{homogenize}$, i.e.,
$$\text{projectivize} = \text{projp} \circ \text{homogenize}$$

Here, $\text{homogenize}$ maps a point in $\mathbb{R}^2$ to its homogeneous representation in $\mathbb{R}^3$ by adding a 1 as the third coordinate, and $\text{projp}$ presumably maps from $\mathbb{R}^3$ to projective space $\mathbb{P}^2(\mathbb{R})$.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition creates a function that converts points from the standard Euclidean plane $\mathbb{R}^2$ directly to projective space $\mathbb{P}^2(\mathbb{R})$. 

The function operates in two steps:
1. First, $\text{homogenize}$ converts a point $(x, y) \in \mathbb{R}^2$ to its homogeneous coordinate representation $(x, y, 1) \in \mathbb{R}^3$.
2. Then, $\text{projp}$ maps this homogeneous representation to the corresponding point in projective space.

This is a standard approach for embedding the Euclidean plane into projective space. The embedding is important in projective geometry and has applications in computer vision, graphics, and computational geometry where projective transformations are used.

The function allows for seamless transition between Euclidean and projective geometry, enabling the application of projective techniques to solve problems in Euclidean space.

### Dependencies
#### Definitions
- `homogenize`: Maps a point in $\mathbb{R}^2$ to its homogeneous representation in $\mathbb{R}^3$ by adding a 1 as the third coordinate
- `projp`: (Not directly provided in the dependencies but used in the definition) Presumably maps from $\mathbb{R}^3$ to projective space $\mathbb{P}^2(\mathbb{R})$

### Porting notes
When porting this definition to other proof assistants:
- Ensure that `projp` exists or is properly defined in the target system
- Verify that function composition has the same directionality (right-to-left) as in HOL Light
- Confirm that the type of `homogenize` matches the expected input type of `projp`

---

## HOMOGENIZE_NONZERO

### HOMOGENIZE_NONZERO
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HOMOGENIZE_NONZERO = prove
 (`!x. ~(homogenize x = vec 0)`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_3;
              homogenize] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
This theorem states that for all vectors $x \in \mathbb{R}^2$, the homogenized vector $\text{homogenize}(x)$ is never equal to the zero vector in $\mathbb{R}^3$.

In mathematical notation:
$$\forall x \in \mathbb{R}^2. \text{homogenize}(x) \neq \vec{0}$$

where $\text{homogenize}(x) = (x_1, x_2, 1)$ is the function that maps a 2D vector to a 3D vector by appending a 1 as the third component.

### Informal proof
The proof proceeds by:

- Rewriting the equality between vectors as component-wise equality using `CART_EQ`
- Expanding the definition of `homogenize` which shows that $\text{homogenize}(x) = (x_1, x_2, 1)$
- Using arithmetic reasoning to prove that this vector can't equal $(0,0,0)$ because the third component is always 1

The key observation is that since the third component of $\text{homogenize}(x)$ is always 1, and the third component of the zero vector is 0, these vectors can never be equal.

### Mathematical insight
This theorem establishes an important property of the homogenization function used in projective geometry. The homogenization process embeds a point from Euclidean space into projective space by adding a non-zero homogeneous coordinate (in this case, 1).

The fact that $\text{homogenize}(x)$ is never the zero vector is important because the zero vector doesn't correspond to a valid point in projective space. This result ensures that the homogenization function always produces valid projective points.

This homogenization is used in projective geometry to convert between Euclidean and projective coordinates, which is particularly useful in computational geometry and computer graphics.

### Dependencies
- Definitions:
  - `homogenize`: Maps a 2D vector to a 3D vector by appending 1 as the third component: $\text{homogenize}(x) = (x_1, x_2, 1)$

### Porting notes
When porting this theorem:
- Ensure your target system has a way to define vectors with specific components
- The proof relies on simple arithmetic reasoning (since the third component is always 1, the vector can't be all zeros)
- Most proof assistants will have built-in tactics for arithmetic reasoning that can handle this proof straightforwardly

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
A set $con$ is an affine conic if there exist real numbers $a$, $b$, $c$, $d$, $e$, $f$, not all zero, such that $con$ consists of all points $x \in \mathbb{R}^2$ satisfying the equation:
$$a \cdot x_1^2 + b \cdot x_2^2 + c \cdot x_1 \cdot x_2 + d \cdot x_1 + e \cdot x_2 + f = 0$$

where $x_1$ and $x_2$ are the first and second components of the point $x$, respectively.

### Informal proof
There is no proof as this is a definition.

### Mathematical insight
This definition formalizes the concept of an affine conic section in the planar Euclidean geometry. Conic sections are fundamental objects in geometry, representing the curves obtained by intersecting a cone with a plane.

The general equation $ax_1^2 + bx_2^2 + cx_1x_2 + dx_1 + ex_2 + f = 0$ can represent various types of conics:
- Ellipses (including circles as a special case)
- Hyperbolas
- Parabolas
- Degenerate conics (e.g., a point, a line, a pair of lines)

The condition that at least one coefficient must be non-zero ensures that the equation defines a meaningful geometric object (otherwise, it would be either the entire plane or the empty set).

This definition provides a purely algebraic characterization of conics, which is particularly useful in computational geometry and for formal proofs involving conic sections.

### Dependencies
- Definitions:
  - `affine_conic` (self-referential)

### Porting notes
When porting this definition to other proof assistants:
1. Ensure the target system has a good library for real vector spaces, particularly $\mathbb{R}^2$.
2. Pay attention to how the indexing of vector components is handled in the target system. In HOL Light, `x$1` refers to the first component (indexed from 1).
3. The notation `&0` in HOL Light represents the numeral 0 as a real number; adapt this to the target system's convention for type-specific constants.
4. Ensure the target system supports the set-builder notation `{x:real^2 | ...}` or provide an appropriate alternative.

---

## COLLINEAR_PROJECTIVIZE

### COLLINEAR_PROJECTIVIZE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem states that for any three points $a$, $b$, and $c$ in $\mathbb{R}^2$, the set $\{a, b, c\}$ is collinear in the affine plane if and only if their projectivized versions $\{\text{projectivize}(a), \text{projectivize}(b), \text{projectivize}(c)\}$ are collinear in the projective plane.

More precisely:
$$\forall a,b,c \in \mathbb{R}^2: \text{collinear}\{a,b,c\} \Leftrightarrow \text{COLLINEAR}\{\text{projectivize}(a), \text{projectivize}(b), \text{projectivize}(c)\}$$

where $\text{projectivize}$ is the composition of $\text{projp}$ (projection to projective space) and $\text{homogenize}$ (mapping a point $(x,y) \in \mathbb{R}^2$ to $(x,y,1) \in \mathbb{R}^3$).

### Informal proof
The proof establishes the equivalence between affine collinearity and projective collinearity:

* First, we rewrite collinearity in terms of vectors using `COLLINEAR_3`, which relates collinearity to parallel vectors.

* We further rewrite using `DOT_CAUCHY_SCHWARZ_EQUAL` to express collinearity in terms of dot products, and `COLLINEAR_BRACKET` to express it in terms of the bracket (determinant) operation.

* The proof then proceeds by establishing a transitive equality with the statement that $\det(\text{homogenize}(a), \text{homogenize}(b), \text{homogenize}(c)) = 0$.

* The proof splits into two parts:
  1. The first part shows that collinearity of points in the affine plane is equivalent to the determinant of their homogenized vectors being zero. This uses the explicit definition of determinant and algebraic manipulation.
  
  2. The second part shows that this determinant condition is equivalent to collinearity in projective space, using:
     - `PARALLEL_PROJP_HOMOP` which relates parallel vectors in projective space
     - `HOMOGENIZE_NONZERO` which establishes that homogenized vectors are non-zero
     - Properties of the homogeneous operation `homop`
     - Properties of cross products and determinants in 3D space

* The proof concludes with algebraic manipulations using `REAL_RING` to establish the equivalence.

### Mathematical insight
This theorem establishes a fundamental connection between affine geometry and projective geometry. It shows that the collinearity property is preserved when mapping points from the affine plane to the projective plane through projectivization.

Projective geometry can be viewed as an extension of affine geometry where parallel lines meet at infinity. The projectivize function embeds the affine plane into the projective plane, and this theorem verifies that collinearity is preserved under this embedding.

This result is important because it allows us to translate collinearity problems between affine and projective settings, leveraging the strengths of each geometric framework depending on the problem at hand.

### Dependencies
- Theorems:
  - `HOMOGENIZE_NONZERO`: Asserts that the homogenization of any vector is non-zero
  - `COLLINEAR_3`: Characterization of collinearity for three points
  - `DOT_CAUCHY_SCHWARZ_EQUAL`: Equality case of Cauchy-Schwarz for dot products
  - `COLLINEAR_BRACKET`: Relation between collinearity and the bracket (determinant)
  - `PARALLEL_PROJP_HOMOP`: Relates parallel vectors in projective space

- Definitions:
  - `cross`: Vector cross product in 3D
  - `homogenize`: Maps a 2D point $(x,y)$ to the 3D point $(x,y,1)$
  - `projectivize`: Composition of projection to projective space and homogenization

### Porting notes
When porting this theorem:
1. Ensure that the underlying projective geometry foundations are in place, particularly the definitions of homogenization and projection to projective space.
2. The proof makes heavy use of determinant computations and algebraic manipulations - a good automation tactic for ring arithmetic will be helpful.
3. Pay attention to how vectors are represented and indexed in the target system, as HOL Light uses 1-based indexing with the `$` notation.

---

## AFFINE_PROJECTIVE_CONIC

### AFFINE_PROJECTIVE_CONIC
- AFFINE_PROJECTIVE_CONIC

### Type of the formal statement
- theorem

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
This theorem establishes the relationship between affine and projective conics:

$$\forall \text{con}. \text{affine\_conic}(\text{con}) \Leftrightarrow \exists \text{con}'. \text{projective\_conic}(\text{con}') \wedge \text{con} = \{x \mid \text{projectivize}(x) \in \text{con}'\}$$

This states that a set is an affine conic if and only if it is the intersection of a projective conic with the affine plane, i.e., it can be obtained by taking a projective conic and restricting it to points that come from the projectivization of points in the affine plane.

### Informal proof

The proof establishes the equivalence between affine conics and the affine restrictions of projective conics:

- Begin by expanding the definitions of `affine_conic`, `projective_conic`, and `homogeneous_conic`.

- Rearrange the quantifiers to move the coefficients $a, b, c, d, e, f$ to the front, which simplifies the proof structure.

- Apply function extensionality to focus on the core equivalence.

- For any point $x$ in the affine plane $\mathbb{R}^2$, we use the fact that `homogenize(x)` is non-zero (from `HOMOGENIZE_NONZERO`).

- Apply `PARALLEL_PROJP_HOMOP_EXPLICIT` to establish that for some non-zero scalar $k$, the projection of the homogenized point represents the same projective point.

- The proof then works with the explicit component forms of vectors and the definitions of the conics.

- Complete the proof using real arithmetic to show that the point $x$ satisfies the affine conic equation if and only if its projectivization satisfies the corresponding projective conic equation.

### Mathematical insight
This theorem formalizes the fundamental relationship between affine and projective geometry for conics. In projective geometry, conics are defined by homogeneous quadratic equations, while in affine geometry, they are defined by general quadratic equations.

The key insight is that affine conics can be viewed as "sections" of projective conics by the affine plane. Projectivization embeds the affine plane into the projective plane, and this theorem shows that every affine conic arises as the intersection of a projective conic with this embedded affine plane.

This correspondence is crucial in algebraic geometry and helps translate problems between affine and projective settings. It allows us to use the more symmetric and cleaner structure of projective geometry while maintaining the connection to the more concrete affine setting.

### Dependencies

#### Theorems:
- `HOMOGENIZE_NONZERO`: States that the homogenization of any point is a non-zero vector

#### Definitions:
- `homogeneous_conic`: Defines a homogeneous conic in $\mathbb{R}^3$ as a set defined by a homogeneous quadratic equation
- `projective_conic`: Defines a projective conic as the projectivization of a homogeneous conic
- `homogenize`: Maps a point from $\mathbb{R}^2$ to $\mathbb{R}^3$ by adding a homogeneous coordinate 1
- `projectivize`: Composes the projection to projective space with homogenization
- `affine_conic`: Defines an affine conic in $\mathbb{R}^2$ as a set defined by a general quadratic equation

### Porting notes
When porting this theorem:
1. Pay attention to the distinction between conics as sets and their defining equations
2. Ensure your projective maps correctly handle the equivalence relation of projective spaces
3. Homogenization in different systems might have different conventions for the placement of the homogeneous coordinate
4. The algebraic manipulation at the end relies on real arithmetic; you may need to use a specialized tactic or lemma in your target system

---

## PASCAL_AFFINE

### PASCAL_AFFINE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
Let $con$ be a set of points in the affine plane $\mathbb{R}^2$ and let $x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9$ be points in $\mathbb{R}^2$ such that:

1. None of the triples $\{x_1, x_2, x_4\}$, $\{x_1, x_2, x_5\}$, $\{x_1, x_2, x_6\}$, $\{x_1, x_3, x_4\}$, $\{x_1, x_3, x_5\}$, $\{x_1, x_3, x_6\}$, $\{x_2, x_3, x_4\}$, $\{x_2, x_3, x_5\}$, $\{x_2, x_3, x_6\}$, $\{x_4, x_5, x_1\}$, $\{x_4, x_5, x_2\}$, $\{x_4, x_5, x_3\}$, $\{x_4, x_6, x_1\}$, $\{x_4, x_6, x_2\}$, $\{x_4, x_6, x_3\}$, $\{x_5, x_6, x_1\}$, $\{x_5, x_6, x_2\}$, $\{x_5, x_6, x_3\}$ are collinear.

2. $con$ is an affine conic section containing the points $x_1, x_2, x_3, x_4, x_5, x_6$.

3. The points $\{x_1, x_9, x_5\}$, $\{x_1, x_8, x_6\}$, $\{x_2, x_9, x_4\}$, $\{x_2, x_7, x_6\}$, $\{x_3, x_8, x_4\}$, $\{x_3, x_7, x_5\}$ are each collinear.

Then the points $\{x_7, x_8, x_9\}$ are collinear.

### Informal proof
This theorem proves Pascal's theorem in the affine plane by leveraging the projective version of the theorem.

The proof proceeds as follows:

* We first apply the theorem `COLLINEAR_PROJECTIVIZE`, which states that three points in the affine plane are collinear if and only if their projective images are collinear:
  $\forall a, b, c. \text{collinear}\{a,b,c\} \Leftrightarrow \text{COLLINEAR}\{\text{projectivize}(a), \text{projectivize}(b), \text{projectivize}(c)\}$

* Next, we apply `AFFINE_PROJECTIVE_CONIC`, which establishes the relationship between affine and projective conics:
  $\forall con. \text{affine\_conic}(con) \Leftrightarrow \exists con'. \text{projective\_conic}(con') \wedge con = \{x | \text{projectivize}(x) \in con'\}$

* After applying these transformations, we can invoke the projective version of Pascal's theorem (`PASCAL`), which was previously established.

* We need to show that there exists a projective conic $con'$ such that the points $x_1$ through $x_6$ map to points on $con'$ under projectivization, and that the collinearity conditions in the affine plane translate to collinearity conditions in the projective plane.

* Since all the collinearity conditions are preserved by projectivization, and since the affine conic maps to a projective conic containing the projectivized points, the conditions of the projective Pascal's theorem (`PASCAL`) are satisfied.

* Therefore, we can conclude that the projectivized points $\{x_7, x_8, x_9\}$ are collinear in the projective plane, which implies that the original points $\{x_7, x_8, x_9\}$ are collinear in the affine plane.

### Mathematical insight
Pascal's theorem is a fundamental result in projective geometry, stating that if six points lie on a conic section, then the three points of intersection of the opposite sides of the hexagon formed by the six points lie on a straight line (called the Pascal line).

This theorem provides the affine version of Pascal's theorem, which is its restriction to the affine plane $\mathbb{R}^2$. The proof elegantly illustrates how results in projective geometry can be transferred to the affine setting by using appropriate transformations (projectivization).

The key insight is that collinearity and conic membership are preserved under projectivization, allowing us to use the projective result to establish the affine one. This demonstrates the power of projective geometry - often, problems in affine geometry become more elegant when viewed through the lens of projective geometry.

The numerous non-collinearity conditions in the hypothesis ensure that the six points are in general position on the conic, which is necessary for the theorem to apply.

### Dependencies
- Theorems:
  - `PASCAL`: The projective version of Pascal's theorem
  - `COLLINEAR_PROJECTIVIZE`: Relates collinearity in affine and projective planes
  - `AFFINE_PROJECTIVE_CONIC`: Relates affine and projective conics

- Definitions:
  - `affine_conic`: Definition of a conic section in the affine plane

### Porting notes
When porting this theorem to another system:
1. Ensure the projective geometry framework is in place, particularly the projectivization map from the affine plane to the projective plane.
2. The definition of affine and projective conics should be established.
3. The proof relies heavily on the relationship between affine and projective geometry, so these foundations must be solid.
4. The numerous non-collinearity conditions might be tedious to handle in other systems, but they are essential for the theorem.

---

## COLLINEAR_NOT_COCIRCULAR

### COLLINEAR_NOT_COCIRCULAR
- COLLINEAR_NOT_COCIRCULAR

### Type of the formal statement
- theorem

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
This theorem states that three distinct points that lie on the same circle cannot be collinear. Formally:

For any real number $r > 0$, any point $c \in \mathbb{R}^2$, and any three distinct points $x, y, z \in \mathbb{R}^2$, if all three points lie on the circle with center $c$ and radius $r$ (i.e., $\textrm{dist}(c,x) = r$, $\textrm{dist}(c,y) = r$, and $\textrm{dist}(c,z) = r$), then the three points are not collinear (i.e., $\neg \textrm{collinear} \{x,y,z\}$).

### Informal proof
The proof proceeds by reformulating the collinearity condition and applying algebraic properties:

1. First, we rewrite the equality conditions using vector subtraction: $x \neq y$ is equivalent to $x - y \neq 0$.

2. We then apply the fact that a vector is non-zero if and only if its dot product with itself is non-zero.

3. The collinearity of three points is reformulated using the condition that for collinear points, the vectors joining them are parallel, which means their cross product is zero.

4. We use the Cauchy-Schwarz inequality, which states that for vectors $u$ and $v$, the dot product $u \cdot v$ equals $\|u\|\|v\|$ if and only if the vectors are linearly dependent.

5. We expand distances in terms of the Euclidean norm and dot products in $\mathbb{R}^2$.

6. Finally, the proof is completed using ring arithmetic on the resulting equations, showing that the constraints on circle points force the collinearity condition to be false.

### Mathematical insight
This theorem captures an important geometric fact: three distinct points on a circle can never form a straight line. The key insight is that the constraint of all points being equidistant from a center point (the definition of a circle) is incompatible with the points being collinear.

The result is fundamental in computational geometry and has applications in various geometric algorithms, including those for determining whether points form a valid circle. It's also related to the fact that a circle is a curve with constant non-zero curvature, whereas a straight line has zero curvature.

### Dependencies
- Equality and vector operations: `VECTOR_SUB_EQ`, `DOT_EQ_0`
- Collinearity conditions: `COLLINEAR_3`
- Dot product properties: `DOT_CAUCHY_SCHWARZ_EQUAL`, `DOT_2`
- Distance and norm definitions: `dist`, `NORM_EQ_SQUARE`
- Cartesian space operations: `CART_EQ`, `DIMINDEX_2`, `FORALL_2`, `VECTOR_SUB_COMPONENT`
- Automation: `REAL_RING`

### Porting notes
When porting this theorem:
- Ensure your target system has a similar representation of Euclidean space and vector operations
- The proof relies heavily on algebraic manipulation, so a system with strong automation for algebraic reasoning will make the port easier
- The definition of collinearity might differ between systems; ensure you're using an equivalent formulation
- Note that the proof uses the two-dimensional properties of the vectors, so porting to a general n-dimensional setting would require additional work

---

## PASCAL_AFFINE_CIRCLE

### PASCAL_AFFINE_CIRCLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For all points $c, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9$ in $\mathbb{R}^2$ and a real number $r$, if:
- The points $x_1, x_2, x_3, x_4, x_5, x_6$ are pairwise distinct
- All points $x_1, x_2, x_3, x_4, x_5, x_6$ lie on a circle with center $c$ and radius $r$ (i.e., $\text{dist}(c, x_i) = r$ for $i = 1,2,3,4,5,6$)
- The points $\{x_1, x_9, x_5\}$ are collinear
- The points $\{x_1, x_8, x_6\}$ are collinear
- The points $\{x_2, x_9, x_4\}$ are collinear
- The points $\{x_2, x_7, x_6\}$ are collinear
- The points $\{x_3, x_8, x_4\}$ are collinear
- The points $\{x_3, x_7, x_5\}$ are collinear

Then the points $\{x_7, x_8, x_9\}$ are collinear.

### Informal proof
This is an application of Pascal's Theorem for affine conics, specialized to circles.

The proof proceeds as follows:

1. We start by specializing `PASCAL_AFFINE` to the set $\{x \in \mathbb{R}^2 \mid \text{dist}(c, x) = r\}$, which defines a circle.

2. We need to verify two main conditions:
   - All the non-collinearity conditions required by `PASCAL_AFFINE`
   - That our circle is indeed an affine conic

3. For the non-collinearity conditions, we apply `COLLINEAR_NOT_COCIRCULAR` which states that three distinct points on a circle cannot be collinear.
   
4. To prove that a circle is an affine conic, we rewrite the equation of a circle:
   - When $r \geq 0$, a circle with center $(c_1, c_2)$ and radius $r$ can be written as:
     $(x_1 - c_1)^2 + (x_2 - c_2)^2 = r^2$, which expands to:
     $x_1^2 + x_2^2 - 2c_1x_1 - 2c_2x_2 + c_1^2 + c_2^2 - r^2 = 0$
     
   - This matches the general form of an affine conic with coefficients:
     $a = 1, b = 1, c = 0, d = -2c_1, e = -2c_2, f = c_1^2 + c_2^2 - r^2$

   - For the degenerate case where $r < 0$ (which represents an empty set), we use the equation $1 = 0$, which corresponds to the coefficients $a=b=c=d=e=0, f=1$.

5. Once we establish that all conditions of `PASCAL_AFFINE` are satisfied, we can apply it to conclude that $\{x_7, x_8, x_9\}$ are collinear.

### Mathematical insight
This theorem is a specialized version of Pascal's Theorem for the specific case of circles. Pascal's Theorem states that if six points lie on a conic section, then the three points of intersection of the three pairs of opposite sides of the resulting hexagon will lie on a straight line.

In the circle case, this becomes especially elegant, as circles are the most symmetric type of conic section. The theorem demonstrates that the projective properties of conics apply to circles specifically, which is important in projective geometry.

This result is part of the rich tradition of projective geometry theorems that connect points on conics with collinearity relationships. The fact that it works for circles reinforces the fundamental connection between projective properties and metric properties in geometry.

### Dependencies
- **Theorems**:
  - `PASCAL_AFFINE`: The affine version of Pascal's Theorem for general conics
  - `COLLINEAR_NOT_COCIRCULAR`: Theorem stating that three distinct points on a circle cannot be collinear

- **Definitions**:
  - `affine_conic`: Definition of an affine conic as a set of points satisfying a quadratic equation in two variables

### Porting notes
When porting this theorem:
- You'll need to ensure that your system has a proper definition of circles and distance in $\mathbb{R}^2$
- The representation of conics might differ between systems - make sure to verify that your definition of affine conics captures circles properly
- The proof relies on algebraic manipulations of the circle equation - these may need different tactics in other proof assistants
- Be aware that the degenerate case for $r < 0$ is handled separately, though some systems might treat this differently or enforce positive radii

---

