# desargues.ml

## Overview

Number of statements: 52

This file formalizes and proves Desargues's theorem in projective geometry, which states that if two triangles are in perspective from a point, then they are in perspective from a line. Building on the cross product operations from `Multivariate/cross.ml`, it develops the necessary projective geometry concepts and presents a complete formal proof of this classic geometric theorem. The formalization demonstrates the application of HOL Light to synthetic geometry.

## NORMAL_EXISTS

### NORMAL_EXISTS
- This is the name of the theorem as it appears in HOL Light.

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
For any two vectors $u, v \in \mathbb{R}^3$, there exists a non-zero vector $w$ such that $w$ is orthogonal to both $u$ and $v$.

More formally: $\forall u, v \in \mathbb{R}^3. \exists w. w \neq \vec{0} \wedge w \perp u \wedge w \perp v$, where $\perp$ denotes orthogonality.

### Informal proof
The proof uses the fact that we can find a non-zero vector orthogonal to any subspace of $\mathbb{R}^3$ with dimension less than 3.

1. We start by applying the symmetry of orthogonality and rewriting the goal to find $w$ such that $u \perp w$ and $v \perp w$.

2. We apply the theorem `ORTHOGONAL_TO_SUBSPACE_EXISTS` to the set $\{u, v\}$, which states that if a set of vectors spans a subspace with dimension strictly less than the dimension of the whole space, then there exists a non-zero vector orthogonal to all vectors in that set.

3. We need to prove that the dimension of the subspace spanned by $\{u, v\}$ is less than 3 (the dimension of $\mathbb{R}^3$).

4. To show this, we use the fact that the dimension of a subspace is at most the cardinality of any spanning set, so $\dim(\{u, v\}) \leq |\{u, v\}|$.

5. The cardinality of $\{u, v\}$ is at most 2 (it's either 1 or 2, depending on whether $u$ and $v$ are linearly independent).

6. Since 2 < 3, we have $\dim(\{u, v\}) \leq 2 < 3$, which completes the proof.

### Mathematical insight
This theorem confirms a fundamental property of $\mathbb{R}^3$: any two vectors must lie in some plane, and therefore there must exist a non-zero vector perpendicular to both of them. This is equivalent to the existence of the cross product in $\mathbb{R}^3$: given two vectors $u$ and $v$, their cross product $u \times v$ (when non-zero) gives exactly such an orthogonal vector.

The result is a direct consequence of the dimensionality of $\mathbb{R}^3$ - it wouldn't hold in $\mathbb{R}^2$ (where two linearly independent vectors span the entire space) but would generalize to higher dimensions (where more than two vectors are needed to constrain all possible orthogonal directions).

This theorem is particularly important in 3D geometry and plays a role in Desargues's theorem of projective geometry, as noted in the comment.

### Dependencies
- **Theorems**:
  - `ORTHOGONAL_SYM`: States that orthogonality is symmetric, i.e., if $u \perp v$ then $v \perp u$.
  - `ORTHOGONAL_TO_SUBSPACE_EXISTS`: If a set of vectors spans a subspace with dimension less than the dimension of the space, there exists a non-zero vector orthogonal to all vectors in that set.
  - `DIM_LE_CARD`: The dimension of a subspace spanned by a finite set is at most the cardinality of that set.
  - `LET_TRANS`: Transitivity of the less-than relation.

- **Definitions**:
  - `orthogonal`: The orthogonality relation between vectors.
  - `DIMINDEX_3`: Represents the dimension of $\mathbb{R}^3$, which is 3.

### Porting notes
When porting this result to other proof assistants:
1. Be aware of how vector spaces and orthogonality are defined in the target system.
2. This proof uses standard properties of dimensionality in vector spaces, which should be available in most systems but might have different names.
3. The proof approach is standard and should translate well across systems, as it relies on fundamental properties of finite-dimensional vector spaces.

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
A new type `direction` is defined, representing directions in 3D space. The type is defined via a bijection with the set of non-zero vectors in $\mathbb{R}^3$.

The bijection consists of two functions:
- `mk_dir` maps from non-zero vectors in $\mathbb{R}^3$ to the `direction` type
- `dest_dir` maps from the `direction` type to non-zero vectors in $\mathbb{R}^3$

The existence of a non-zero vector in $\mathbb{R}^3$ is established by the MESON tactic using the facts that basis vectors are non-zero, and that the dimension of $\mathbb{R}^3$ is at least 1.

### Informal proof
The type definition requires proving that the representing set is non-empty. In this case, we need to show that there exists a non-zero vector in $\mathbb{R}^3$.

The proof uses the MESON tactic with three facts:
- `BASIS_NONZERO`: The basis vectors of $\mathbb{R}^n$ are non-zero
- `LE_REFL`: The relation $\leq$ is reflexive
- `DIMINDEX_GE_1`: The dimension of any Euclidean space $\mathbb{R}^n$ is at least 1

Since $\mathbb{R}^3$ has dimension 3 (which is ≥ 1), there exists at least one basis vector, and all basis vectors are non-zero, we can conclude that there exists a non-zero vector in $\mathbb{R}^3$.

### Mathematical insight
The `direction` type represents unit directions in 3D space, which is a fundamental concept in geometry and physics. This definition creates an abstract type for directions that is distinct from the concrete representation as non-zero vectors in $\mathbb{R}^3$.

The bijection between the abstract type and its concrete representation allows properties of directions to be established using properties of non-zero vectors, while maintaining the conceptual distinction.

This type is likely used in contexts like computer graphics, physics simulations, or geometric modeling where directions need to be treated as first-class objects distinct from vectors.

### Dependencies
- `BASIS_NONZERO`: Theorem stating that basis vectors are non-zero
- `LE_REFL`: Theorem stating that the relation $\leq$ is reflexive 
- `DIMINDEX_GE_1`: Theorem stating that the dimension of a Euclidean space is at least 1

### Porting notes
When porting to other systems:
1. Most theorem provers have built-in mechanisms for defining new types via a bijection with a subset of an existing type.
2. In some systems like Isabelle/HOL, this might be accomplished using a `typedef` command.
3. In systems like Lean, you might use a subtype definition.
4. Ensure the target system has the necessary vector space library to represent $\mathbb{R}^3$ and its properties.
5. The non-emptiness proof is straightforward but might need to be adapted to the specific vector libraries of the target system.

---

## perpdir

### perpdir
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let perpdir = new_definition
 `x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)`;;
```

### Informal statement
This definition introduces a new infix notation `x _|_ y` which means that two directions `x` and `y` are perpendicular. Formally, it states that:

For two direction vectors `x` and `y`:
$x \perp y \iff \text{orthogonal}(\text{dest\_dir}(x), \text{dest\_dir}(y))$

where `dest_dir` extracts the underlying vector from a direction object, and `orthogonal` determines whether two vectors are perpendicular to each other.

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
This definition introduces a convenient infix notation `_|_` for expressing perpendicularity between directions. It leverages the existing `orthogonal` predicate but operates on direction objects rather than on raw vectors.

The definition abstracts away the need to explicitly convert direction objects to their underlying vectors when checking orthogonality, making formulas involving perpendicular directions more readable and closer to standard mathematical notation.

In geometry, perpendicular directions are fundamental for constructing coordinate systems, defining reflections, and expressing many geometric constraints.

### Dependencies
- `orthogonal`: Predicate determining whether two vectors are orthogonal
- `dest_dir`: Function that extracts the underlying vector from a direction object

### Porting notes
When porting this definition:
1. Ensure the target system has equivalent notions of directions and vectors
2. Check how the target system handles infix notation, as the `_|_` symbol may need different syntax
3. Verify that the underlying `orthogonal` and `dest_dir` functions have been properly ported first

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
Two directions $x$ and $y$ are parallel, denoted as $x \parallel y$, if and only if their cross product is the zero vector, i.e., $\text{dest\_dir}(x) \times \text{dest\_dir}(y) = \vec{0}$, where $\text{dest\_dir}$ extracts the direction vector from a direction.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition formalizes the mathematical notion of parallel directions in 3D space. The cross product $\times$ of two vectors is zero if and only if the vectors are linearly dependent (i.e., one is a scalar multiple of the other, or at least one is zero). When applied to direction vectors, this precisely captures the concept of parallelism.

The definition operates on direction objects (as suggested by the `dest_dir` function) rather than directly on vectors, which suggests that the system has a specific type or representation for directions that is distinct from ordinary vectors. The `dest_dir` function extracts the actual vector component from these direction objects before computing the cross product.

This is a standard geometric definition of parallelism using the cross product, which is particularly useful in 3D geometric reasoning and computational geometry.

### Dependencies
#### Definitions
- `cross`: Defines the cross product of two vectors in $\mathbb{R}^3$ as $a \times b = \langle a_2b_3 - a_3b_2, a_3b_1 - a_1b_3, a_1b_2 - a_2b_1 \rangle$

### Porting notes
When porting this definition to another system, ensure that:
1. The target system has a representation for directions separate from vectors
2. The cross product is properly defined for 3D vectors
3. The system can handle the equality test between vectors

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
This theorem establishes the relationship between quantification over directions (represented by `dest_dir x`) and quantification over non-zero vectors. Specifically:

1. $\forall x. P(\text{dest\_dir}(x)) \iff \forall x. (x \neq \vec{0} \Rightarrow P(x))$
2. $\exists x. P(\text{dest\_dir}(x)) \iff \exists x. (x \neq \vec{0} \land P(x))$

Where `dest_dir` is a function that transforms elements from a direction type to vectors.

### Informal proof
The proof is accomplished by applying the `MESON_TAC` tactic with the `direction_tybij` theorem.

This is a straightforward application of the bijection properties established in `direction_tybij`. Since `dest_dir` provides a bijection between the direction type and non-zero vectors:

- Universal quantification over directions is equivalent to universal quantification over non-zero vectors.
- Existential quantification over directions is equivalent to existential quantification over non-zero vectors.

The `MESON_TAC` automatically handles the logical manipulation required to establish these equivalences.

### Mathematical insight
This theorem provides a way to convert between statements about directions and statements about non-zero vectors. This is particularly useful in geometry and physics contexts where directions are represented as unit vectors or normalized vectors.

The theorem eliminates the need to work directly with the direction type by allowing equivalent statements to be made about non-zero vectors, which may be more convenient in many contexts. It essentially lets us translate between the abstract concept of a "direction" and its concrete representation as a vector, while preserving the logical properties of quantification.

### Dependencies
- `direction_tybij`: Establishes the bijection relationship between directions and non-zero vectors via the `dest_dir` function.

### Porting notes
When porting this theorem:
1. Ensure that the target system has a similar representation of directions and vectors.
2. The bijection between directions and non-zero vectors must be established first (via `direction_tybij` or equivalent).
3. The automated reasoning in `MESON_TAC` might need to be replaced with more explicit steps in systems with different automation capabilities.

---

## [PARDIR_REFL;

### PARDIR_REFL

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
This theorem consists of three parts establishing that the parallel direction relation `||` is an equivalence relation:
1. $\forall x. x \parallel x$ (reflexivity)
2. $\forall x,y. x \parallel y \Leftrightarrow y \parallel x$ (symmetry)
3. $\forall x,y,z. (x \parallel y \land y \parallel z) \Rightarrow x \parallel z$ (transitivity)

Where $x \parallel y$ means that the cross product of the directions represented by $x$ and $y$ is the zero vector: $(dest\_dir \, x) \times (dest\_dir \, y) = \vec{0}$.

### Informal proof
We prove that the parallel direction relation forms an equivalence relation by establishing its reflexivity, symmetry, and transitivity properties.

The proof uses `REWRITE_TAC[pardir; DIRECTION_CLAUSES]`, which unfolds the definition of the parallel relation and applies properties of directions, followed by `VEC3_TAC`, which automatically solves vector algebra problems in 3D space.

For the detailed steps:

1. **Reflexivity**: For any direction $x$, we have $x \parallel x$ because $(dest\_dir \, x) \times (dest\_dir \, x) = \vec{0}$ by the property that the cross product of any vector with itself is zero.

2. **Symmetry**: For any directions $x$ and $y$, we have $x \parallel y \Leftrightarrow y \parallel x$ because $(dest\_dir \, x) \times (dest\_dir \, y) = \vec{0} \Leftrightarrow (dest\_dir \, y) \times (dest\_dir \, x) = \vec{0}$, as the cross product changes sign when operands are swapped: $a \times b = -(b \times a)$, and $\vec{0} = -\vec{0}$.

3. **Transitivity**: For any directions $x$, $y$, and $z$, if $x \parallel y$ and $y \parallel z$, then $x \parallel z$. This follows from the properties of collinearity in 3D vectors: if $(dest\_dir \, x) \times (dest\_dir \, y) = \vec{0}$ and $(dest\_dir \, y) \times (dest\_dir \, z) = \vec{0}$, then $(dest\_dir \, x) \times (dest\_dir \, z) = \vec{0}$.

### Mathematical insight
This theorem establishes that the parallel direction relation is an equivalence relation, which is a fundamental property for working with projective geometry. 

The mathematical insight here is that directions in 3D space are considered parallel when their cross product is zero, which means they are collinear (lie on the same line through the origin). This equivalence relation partitions the set of directions into equivalence classes, each representing a specific direction in projective space.

The theorem forms the foundation for working with projective geometry concepts like points at infinity and projective lines, as it provides a rigorous way to handle parallel lines in a unified framework.

### Dependencies
- **Theorems**:
  - `DIRECTION_CLAUSES`: Provides properties for working with the `dest_dir` function, relating quantification over directions to quantification over nonzero vectors.
  
- **Definitions**:
  - `pardir`: Defines the parallel relation `x || y` as the cross product of their directions being zero.

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the appropriate vector algebra library is available, especially one that supports cross products in 3D space.
- The `VEC3_TAC` tactic is specific to HOL Light and automatically proves vector algebra facts. In other systems, you might need to manually prove these vector properties or use a different automated tactic.
- In systems with dependent types, you might want to ensure that directions are represented as unit vectors or equivalence classes of nonzero vectors to match HOL Light's treatment.

---

## PARDIR_EQUIV

### PARDIR_EQUIV
- PARDIR_EQUIV

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PARDIR_EQUIV = prove
 (`!x y. ((||) x = (||) y) <=> x || y`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS]);;
```

### Informal statement
For any points $x$ and $y$, the statement $(||)x = (||)y$ is equivalent to $x || y$.

Here, $(||)x$ denotes the equivalence class of point $x$ under the parallel relation, and $x || y$ means that points $x$ and $y$ are parallel.

### Informal proof
The proof proceeds as follows:

- First, we apply `REWRITE_TAC[FUN_EQ_THM]` which transforms the goal by using the function equality theorem. This reduces the left-hand side $(||)x = (||)y$ to $\forall z. ((x || z) \Leftrightarrow (y || z))$.

- Then, we use `MESON_TAC` with the properties of the parallel relation:
  - `PARDIR_REFL`: The parallel relation is reflexive (i.e., $x || x$ for any $x$)
  - `PARDIR_SYM`: The parallel relation is symmetric (i.e., if $x || y$ then $y || x$)
  - `PARDIR_TRANS`: The parallel relation is transitive (i.e., if $x || y$ and $y || z$ then $x || z$)

- Using these properties, the automated reasoning establishes that $(\forall z. (x || z) \Leftrightarrow (y || z))$ if and only if $x || y$.

- The key insight is that two equivalence classes $(||)x$ and $(||)y$ are equal precisely when the points $x$ and $y$ belong to the same equivalence class, which is exactly when they are parallel to each other.

### Mathematical insight
This theorem establishes the expected relationship between equivalence classes of the parallel relation and the parallel relation itself. It shows that two points have the same equivalence class under the parallel relation if and only if they are parallel.

The theorem is important because it connects the extensional view of parallelism (comparing equivalence classes) with the intensional view (the direct relation between points). This connection is fundamental when working with quotient spaces or when reasoning about directions in projective geometry.

### Dependencies
- `FUN_EQ_THM`: Function equality theorem
- `PARDIR_REFL`: Reflexivity of the parallel relation
- `PARDIR_SYM`: Symmetry of the parallel relation
- `PARDIR_TRANS`: Transitivity of the parallel relation

### Porting notes
When porting this theorem to other systems, ensure that:
1. The parallel relation is properly defined as an equivalence relation
2. The notation for equivalence classes is consistent with the target system
3. Function equality is properly handled in the target system

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
For any two directions $p$ and $p'$ that are not parallel, there exists a direction $l$ such that $l$ is perpendicular to both $p$ and $p'$, and for any other direction $l'$ that is perpendicular to both $p$ and $p'$, $l'$ is parallel to $l$.

In terms of the formal HOL Light statement:
- $p \parallel p'$ means directions $p$ and $p'$ are parallel
- $p \perp l$ means directions $p$ and $l$ are perpendicular
- The theorem states that for non-parallel directions, there exists a unique direction (up to parallelism) that is perpendicular to both.

### Informal proof
The proof leverages basic facts from 3D vector geometry:

1. First, we convert the statement about directions to equivalent statements about non-zero vectors using the definitions of perpendicular and parallel directions (`perpdir`, `pardir`), and the properties from `DIRECTION_CLAUSES`.
   
2. We then apply the theorem `NORMAL_EXISTS` which states that for any two vectors $u$ and $v$ in $\mathbb{R}^3$, there exists a non-zero vector $w$ that is orthogonal to both $u$ and $v$.

3. After applying `MONO_EXISTS` to properly handle the existential quantifier, the proof is completed using vector algebra manipulations (via the `VEC3_TAC` tactic).

The key insight is that for two non-parallel directions in 3D space, their corresponding vectors span a plane, and there is a unique direction (up to scalar multiplication) perpendicular to that plane.

### Mathematical insight
This theorem states a fundamental property of 3D projective geometry: for any two non-parallel directions, there exists a unique direction (up to parallelism) that is perpendicular to both. 

Geometrically, this corresponds to finding the normal vector to the plane defined by two non-parallel vectors. This normal vector is unique up to scalar multiplication, which translates to uniqueness up to parallelism in terms of directions.

This theorem is important in projective geometry and is used for defining perpendicular lines in space and for constructing orthogonal frames.

### Dependencies
- **Theorems:**
  - `NORMAL_EXISTS`: States that for any two vectors in $\mathbb{R}^3$, there exists a non-zero vector orthogonal to both.
  - `DIRECTION_CLAUSES`: Provides the relationship between quantification over directions and quantification over non-zero vectors.

- **Definitions:**
  - `perpdir`: Defines when two directions are perpendicular.
  - `pardir`: Defines when two directions are parallel.

### Porting notes
When porting this theorem:
1. Ensure the underlying vector space is 3-dimensional.
2. Make sure the direction type and its operations (especially perpendicular and parallel relations) are properly defined.
3. The theorem relies on the existence of a normal vector to two vectors in 3D space, which is a standard result but might need to be proved separately in some systems.
4. The `VEC3_TAC` tactic handles vector algebra automatically in HOL Light; in other systems, you might need to provide more explicit vector algebra steps.

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
For any two directions $l$ and $l'$, there exists a direction $p$ that is perpendicular to both $l$ and $l'$.

Formally, $\forall l, l' \in \text{direction}. \exists p \in \text{direction}. p \perp l \land p \perp l'$, where $\perp$ represents perpendicularity between directions.

### Informal proof
The proof proceeds as follows:

1. First, we rewrite the perpendicularity relation using its definition: $p \perp l$ means that the vectors represented by directions $p$ and $l$ are orthogonal, i.e., `orthogonal (dest_dir p) (dest_dir l)`.

2. We then use `DIRECTION_CLAUSES` to transform the quantification over directions to quantification over non-zero vectors, since directions are essentially equivalence classes of non-zero vectors.

3. Finally, we apply the theorem `NORMAL_EXISTS`, which states that for any two vectors $u$ and $v$ in $\mathbb{R}^3$, there exists a non-zero vector $w$ such that $w$ is orthogonal to both $u$ and $v$.

4. The orthogonality relation is symmetric (from `ORTHOGONAL_SYM`), which allows us to complete the proof.

### Mathematical insight
This theorem establishes a fundamental property of 3D geometry: for any two directions in space, we can always find a direction perpendicular to both. This corresponds to the intuitive notion that given two lines with arbitrary directions in 3D space, there always exists a line perpendicular to both.

The result is important in projective geometry and in the formalization of Desargues' theorem, as it helps establish properties of perpendicular lines and planes. In physical terms, this represents the well-known fact that any two directions determine a plane, and the direction perpendicular to this plane is perpendicular to both original directions.

### Dependencies
- **Theorems:**
  - `NORMAL_EXISTS`: For any two vectors in $\mathbb{R}^3$, there exists a non-zero vector orthogonal to both.
  - `DIRECTION_CLAUSES`: Conversion rules between quantification over directions and quantification over non-zero vectors.
  - `ORTHOGONAL_SYM`: Orthogonality is a symmetric relation.

- **Definitions:**
  - `perpdir`: Defines perpendicularity between directions, where `x _|_ y` means the vectors represented by directions x and y are orthogonal.

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the representation of directions as equivalence classes of non-zero vectors is properly defined.
2. The proof relies on the existence of a normal vector to any two vectors in 3D space, which may require different proof techniques in other systems depending on how vector spaces are formalized.
3. The notation `_|_` for perpendicularity may need to be defined or replaced with standard notation in the target system.

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
1. $p$ is not parallel to $p'$,
2. $p'$ is not parallel to $p''$,
3. $p$ is not parallel to $p''$, and
4. there is no direction $l$ that is perpendicular to all of $p$, $p'$, and $p''$.

### Informal proof
The proof establishes the existence of three mutually non-parallel directions that have no common perpendicular direction.

- The proof begins by rewriting the goal using the definitions of perpendicular directions (`perpdir`), parallel directions (`pardir`), and properties of directions (`DIRECTION_CLAUSES`).

- It then introduces three specific directions by instantiating them to the standard basis vectors in $\mathbb{R}^3$:
  * $p = \text{basis}_1$ (the unit vector along the x-axis)
  * $p' = \text{basis}_2$ (the unit vector along the y-axis)
  * $p'' = \text{basis}_3$ (the unit vector along the z-axis)

- The basis vectors are non-zero vectors (proven by `BASIS_NONZERO`), and since $\mathbb{R}^3$ has dimension 3 (`DIMINDEX_3`), all three basis vectors exist.

- The standard basis vectors in $\mathbb{R}^3$ are mutually orthogonal and have unit length, which means:
  * Their cross products are non-zero, establishing they are not parallel to each other
  * There cannot exist a vector perpendicular to all three basis vectors in $\mathbb{R}^3$, as this would require a non-zero vector simultaneously orthogonal to three linearly independent vectors, which is impossible in 3D space.

- The final step uses `VEC3_TAC`, which is a tactic for reasoning about 3D vector arithmetic to complete the proof.

### Mathematical insight
This theorem establishes a fundamental property of projective 3D space by proving the existence of three directions with no common perpendicular. This is equivalent to showing that three mutually non-collinear points in the projective plane do not have a common polar line.

In the context of projective geometry, this result helps establish the axiom system for projective spaces. Specifically, it demonstrates that in 3D projective space, we can find three directions that don't share any perpendicular direction, which is a crucial property distinguishing 3D projective geometry from 2D projective geometry.

The proof uses the standard basis vectors in $\mathbb{R}^3$ as a concrete example of directions satisfying these properties, leveraging the fact that no vector can be simultaneously perpendicular to three orthogonal vectors in 3D space.

### Dependencies
- **Definitions**:
  - `perpdir`: Defines when two directions are perpendicular
  - `pardir`: Defines when two directions are parallel

- **Theorems**:
  - `DIRECTION_CLAUSES`: Properties relating quantification over directions to quantification over non-zero vectors
  - `BASIS_NONZERO`: Establishes that basis vectors are non-zero
  - `DIMINDEX_3`: Relates to the dimension of the vector space $\mathbb{R}^3$

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-defined notion of directions in 3D projective geometry
2. Check that the target system has appropriate representations for vector operations, particularly cross products and orthogonality
3. The proof relies on properties of basis vectors in $\mathbb{R}^3$, so equivalent functionality must be available in the target system

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
For any direction $l$, there exist directions $p$ and $p'$ such that:
1. $p$ is not parallel to $p'$ (i.e., $\neg(p \parallel p')$)
2. $p$ is perpendicular to $l$ (i.e., $p \perp l$)
3. $p'$ is perpendicular to $l$ (i.e., $p' \perp l$)

### Informal proof
The proof establishes that for any direction $l$, we can find two directions perpendicular to $l$ that are not parallel to each other.

* First, we rewrite the goal using `DIRECTION_CLAUSES`, `pardir`, and `perpdir` to work with vector representations instead of abstract directions.
* The key step is to prove that at least one of the following must be true:
  1. Both $(l \times e_1)$ and $(l \times e_2)$ are orthogonal to $l$, and their cross product is non-zero, or
  2. Both $(l \times e_1)$ and $(l \times e_3)$ are orthogonal to $l$, and their cross product is non-zero, or
  3. Both $(l \times e_2)$ and $(l \times e_3)$ are orthogonal to $l$, and their cross product is non-zero

  where $e_1$, $e_2$, and $e_3$ are the standard basis vectors.
* This is proven by vector reasoning with `VEC3_TAC`.
* The final step uses `MESON_TAC` with `CROSS_0` to complete the proof, which essentially shows that if $l$ is a non-zero vector, at least one of the pairs of cross products will give non-parallel perpendicular directions.

### Mathematical insight
This theorem is a weak form of the fourth axiom for projective geometry in the context of directions. It establishes that for any direction in 3D space, we can find two distinct perpendicular directions that are not parallel to each other.

The result demonstrates an important property of 3-dimensional space: given any direction, there is not just one but an infinite plane of directions perpendicular to it. This theorem explicitly shows we can find at least two non-parallel directions in this perpendicular plane.

The proof leverages the properties of the cross product: if $v$ and $w$ are vectors, then $v \times w$ is perpendicular to both $v$ and $w$. By using the standard basis vectors, the proof guarantees the existence of the required perpendicular directions.

### Dependencies
- **Theorems:**
  - `CROSS_0`: Establishes that the cross product with the zero vector always yields the zero vector
  - `DIRECTION_CLAUSES`: Relates quantification over directions to quantification over non-zero vectors

- **Definitions:**
  - `cross`: Definition of the cross product operation for 3D vectors
  - `perpdir`: Defines perpendicularity of directions (`_|_`) in terms of orthogonality of their vector representations
  - `pardir`: Defines parallelism of directions (`||`) in terms of their cross product being zero

### Porting notes
When porting this theorem:
1. Ensure your target system has a suitable implementation of 3D vectors, cross product, and orthogonality.
2. Be aware of how directions (equivalence classes of parallel vectors) are represented in your target system.
3. The proof relies on vector reasoning and the properties of the cross product in 3D space, so automation for linear algebra or specific vector tactics may be helpful.
4. The standard basis vectors must be correctly defined in the target system.

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
For any vectors $x$, $a$, and $b$ in $\mathbb{R}^3$, if $a$ is orthogonal to $x$, $b$ is orthogonal to $x$, and $a$ is not parallel to $b$, then there exists a vector $c$ such that:
- $c$ is orthogonal to $x$
- $a$ is not parallel to $c$
- $b$ is not parallel to $c$

Here, vectors being orthogonal ($\_|\_$) means their directions are perpendicular, and vectors being parallel ($||$) means their cross product is zero.

### Informal proof
We need to find a vector $c$ that satisfies the given conditions. The proof proceeds as follows:

- First, we rewrite the directional predicates using `DIRECTION_CLAUSES`, `pardir`, and `perpdir` to work with the underlying vector properties directly.
- The orthogonality relation $a \_|\_\  x$ means that the direction of $a$ is orthogonal to the direction of $x$.
- The parallel relation $a || b$ means that the cross product of the directions of $a$ and $b$ is zero.
- We claim that $c = a + b$ satisfies our requirements.
- Using vector algebra (applied by the `VEC3_TAC` tactic), we can verify that:
  - $c = a + b$ is orthogonal to $x$ because both $a$ and $b$ are orthogonal to $x$, and orthogonality is preserved under addition in this case.
  - $a$ is not parallel to $c = a + b$ because $a$ is not parallel to $b$.
  - $b$ is not parallel to $c = a + b$ because $a$ is not parallel to $b$.

### Mathematical insight
This theorem shows that we can combine two non-parallel vectors that are orthogonal to a given vector to create a third vector that is orthogonal to the given vector and not parallel to either of the original vectors. This is particularly useful in 3D geometry and vector space theory.

The construction $c = a + b$ is a natural choice because:
1. The sum of two vectors orthogonal to a third vector remains orthogonal to that vector
2. Adding a vector to another non-parallel vector produces a result that is not parallel to either of the original vectors

This result can be useful in constructing orthogonal bases or finding additional directions in a plane perpendicular to a given vector.

### Dependencies
- **Theorems:**
  - `DIRECTION_CLAUSES`: Relates quantification over directions to quantification over non-zero vectors
- **Definitions:**
  - `perpdir`: Defines orthogonality between directions
  - `pardir`: Defines when two directions are parallel (cross product is zero)

### Porting notes
When porting this to other proof assistants:
- Make sure the system has a good representation of 3D vectors and cross products
- The `VEC3_TAC` in HOL Light is a specialized tactic for vector algebra in 3D space - you'll need to either find an equivalent automated tactic or manually prove the vector algebraic properties
- The direction type may be represented differently in other systems - understand how the direction abstraction works and adapt accordingly
- The perpendicular and parallel notation might need to be defined manually in the target system

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
For any direction $l$, there exist three directions $p$, $p'$, and $p''$ such that:
1. $p$ is not parallel to $p'$
2. $p'$ is not parallel to $p''$
3. $p$ is not parallel to $p''$
4. $p$ is perpendicular to $l$
5. $p'$ is perpendicular to $l$
6. $p''$ is perpendicular to $l$

where $||$ denotes parallel directions and $_|_$ denotes perpendicular directions.

### Informal proof
This theorem is proved using two previously established theorems:

1. First, we apply `DIRECTION_AXIOM_4_WEAK`, which states that for any direction $l$, there exist two non-parallel directions $p$ and $p'$ that are both perpendicular to $l$.

2. Then, we use `ORTHOGONAL_COMBINE`, which states that if we have two non-parallel directions $a$ and $b$ that are both perpendicular to a direction $x$, then there exists a third direction $c$ such that:
   - $c$ is perpendicular to $x$
   - $c$ is not parallel to $a$
   - $c$ is not parallel to $b$

By applying `DIRECTION_AXIOM_4_WEAK` to get the first two perpendicular directions, and then using `ORTHOGONAL_COMBINE` to construct the third direction that is perpendicular to $l$ and not parallel to either of the first two directions, we obtain the desired result.

### Mathematical insight
This theorem establishes the existence of three mutually non-parallel directions that are all perpendicular to a given direction. In three-dimensional space, this is intuitively clear because the set of all directions perpendicular to a given direction forms a plane, and within that plane, we can find infinitely many directions that are not parallel to each other.

This result is important in projective and Euclidean geometry, particularly in the context of Desargues' theorem and related geometrical constructions. It formalizes the fact that the orthogonal complement of a direction in 3D space has dimension 2, and therefore contains at least three linearly independent directions.

### Dependencies
- **Theorems:**
  - `DIRECTION_AXIOM_4_WEAK`: States that for any direction, there exist two non-parallel directions perpendicular to it
  - `ORTHOGONAL_COMBINE`: States that given two non-parallel directions perpendicular to a third direction, there exists a third direction perpendicular to that third direction and not parallel to either of the first two

### Porting notes
When porting this theorem, ensure that the underlying vector space is three-dimensional, as the proof implicitly relies on this fact. The representation of directions in other proof assistants might differ, but the core mathematical concept (orthogonality and parallelism of directions) should be similar. The use of the `MESON_TAC` tactic suggests that the proof is relatively straightforward once the dependencies are established.

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
This defines a new type `line` as a quotient type based on an equivalence relation `(||)` (which represents parallelism between vectors). The type is equipped with two functions:
- `mk_line`: A function that maps from the base type to the new quotient type `line`
- `dest_line`: A function that maps from the quotient type `line` back to a representative of the equivalence class in the base type

### Mathematical insight
This definition creates the projective concept of a line by identifying parallel vectors. In projective geometry, lines are often represented as equivalence classes of vectors under the parallelism relation.

The `define_quotient_type` command automates the creation of a new type that represents the quotient of an existing type modulo an equivalence relation. In this case, the new type `line` represents equivalence classes of some original type (likely vectors) under the parallelism relation.

This is a standard way to formalize projective geometry in a theorem prover, where lines are defined as equivalence classes of vectors that point in the same direction (i.e., parallel vectors).

### Dependencies
- The equivalence relation `(||)` (not provided in the dependencies list)

### Porting notes
When porting to other systems:
- Ensure that the parallelism relation `(||)` is properly defined as an equivalence relation
- In systems with built-in quotient types (like Lean), you might use those mechanisms directly
- In systems without direct quotient type support, you might need to use other approaches such as defining the type as a subset of the powerset of the base type, where each element is an equivalence class

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
For any directions $x$, $y$, $x'$, and $y'$, if $x$ is parallel to $x'$ and $y$ is parallel to $y'$, then $x$ is perpendicular to $y$ if and only if $x'$ is perpendicular to $y'$.

Mathematically:
$\forall x, y, x', y' : \text{direction}. (x \parallel x' \land y \parallel y') \Rightarrow (x \perp y \Leftrightarrow x' \perp y')$

### Informal proof
This theorem states that perpendicularity is well-defined with respect to parallel directions.

The proof proceeds by:
- First, rewriting the goal using the definitions of perpendicularity (`perpdir`) and parallelism (`pardir`) between directions
- By the definition, $x \perp y$ means that the vectors representing these directions are orthogonal, and $x \parallel y$ means that the cross product of their vector representations is zero
- Using the properties of directions from `DIRECTION_CLAUSES` to properly handle the direction type
- The proof is completed using vector algebra tactics (`VEC3_TAC`), which handles the algebraic properties of orthogonality and parallelism in 3D space

### Mathematical insight
This theorem establishes that perpendicularity is a well-defined relation on directions, meaning it respects the equivalence relation of parallelism. In geometry, this is a fundamental property: if two lines are perpendicular, then any line parallel to the first is perpendicular to any line parallel to the second.

This theorem is important in projective and affine geometry, as it allows us to consistently define perpendicular directions regardless of which specific representative vectors we choose for those directions. It ensures that geometric constructions involving perpendicular directions are well-defined.

### Dependencies
#### Theorems
- `DIRECTION_CLAUSES`: Provides properties for quantification over the direction type

#### Definitions
- `perpdir`: Defines perpendicularity between directions: $x \perp y \Leftrightarrow \text{orthogonal}(\text{dest\_dir}(x), \text{dest\_dir}(y))$
- `pardir`: Defines parallelism between directions: $x \parallel y \Leftrightarrow \text{dest\_dir}(x) \times \text{dest\_dir}(y) = \vec{0}$

### Porting notes
When porting to other systems:
- Ensure the direction type is properly defined as an abstraction over non-zero vectors
- The theorem relies on vector algebra properties, particularly orthogonality and cross products
- The `VEC3_TAC` tactic in HOL Light handles vector algebra automatically; in other systems, you may need to implement similar automation or explicitly prove the vector algebraic steps

---

## perpl,perpl_th

### Name of formal statement
perpl

### Type of the formal statement
new_definition (via `lift_function`)

### Formal Content
```ocaml
let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;
```

### Informal statement
The function `perpl` defines the perpendicularity relation between lines. It lifts the perpendicular direction relation (`_|_`) from representatives of lines to the abstract lines themselves.

Formally, if `l₁` and `l₂` are lines, then `perpl l₁ l₂` holds if and only if for any vectors `v₁` and `v₂` representing the directions of `l₁` and `l₂` respectively, `v₁ _|_ v₂` holds (i.e., the vectors are perpendicular).

### Informal proof
This definition uses the `lift_function` mechanism to lift the perpendicular relation from vector representatives to the quotient type of lines.

The lifting is justified by the theorem `PERPDIR_WELLDEF`, which ensures that perpendicularity is well-defined with respect to the equivalence relation on directions: if `x || x'` and `y || y'` (i.e., vectors are parallel), then `x _|_ y` if and only if `x' _|_ y'`.

The construction uses `line_tybij` which defines the quotient type for lines, where lines are represented by equivalence classes of parallel vectors. The parameters `PARDIR_REFL` and `PARDIR_TRANS` are used to establish that the parallelism relation is an equivalence relation.

### Mathematical insight
The perpendicularity relation between lines is a fundamental concept in geometry. This definition formalizes the notion that two lines are perpendicular if their direction vectors are perpendicular.

The definition works with the quotient type of lines, where each line is represented by an equivalence class of parallel vectors. The key insight is that perpendicularity is well-defined with respect to these equivalence classes: if we replace a vector with a parallel one, the perpendicularity relation remains unchanged.

This approach allows us to work with abstract lines rather than their vector representatives, simplifying many geometric arguments.

### Dependencies
- Theorems:
  - `PERPDIR_WELLDEF`: Proves that perpendicularity is well-defined with respect to parallel vectors
  - `PARDIR_REFL`: Reflexivity of the parallelism relation
  - `PARDIR_TRANS`: Transitivity of the parallelism relation

- Definitions:
  - `line_tybij`: Defines the quotient type for lines based on the parallelism relation
  - `perpdir`: The underlying perpendicular direction relation for vectors (denoted as `_|_`)
  - `pardir`: The parallelism relation for vectors (denoted as `||`)

### Porting notes
When porting this definition:
1. Ensure the quotient type mechanism is properly set up in the target system
2. Verify that the parallelism relation is established as an equivalence relation
3. The perpendicular relation between vectors may need to be defined first
4. The lifting of functions to quotient types might require different constructions in different proof assistants

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
This theorem establishes the transfer principles for operations on lines, which are defined as equivalence classes of line representations (pairs of points) under the parallel relation. The lifting principle enables reasoning about lines as abstract objects rather than their concrete representations.

### Informal proof
This theorem is created by applying the `lift_theorem` function to:

1. The `line_tybij` which defines the quotient type "line"
2. A triple of theorems proving that the parallel relation `(||)` is an equivalence relation:
   - `PARDIR_REFL`: The reflexivity of parallelism
   - `PARDIR_SYM`: The symmetry of parallelism 
   - `PARDIR_TRANS`: The transitivity of parallelism
3. A list containing the theorem `perpl_th` which likely establishes properties about perpendicular lines

The lifting theorem mechanism establishes that operations defined on concrete representations of lines (pairs of points) can be "lifted" to operations on the abstract line type, preserving the properties expressed in the provided theorems.

### Mathematical insight
This theorem is crucial for the formalization of projective geometry, allowing reasoning about lines as first-class objects rather than their concrete representations as pairs of points. The lifting principle is a standard technique in quotient-based constructions, ensuring that operations defined on representatives are well-defined on equivalence classes.

In projective geometry, lines can be represented in different ways (e.g., by different pairs of points lying on them), and the lifting theorem ensures that properties of lines are independent of the particular representation chosen. This abstraction is essential for formal reasoning about geometry without getting caught in representational details.

### Dependencies
- **Definitions**:
  - `line_tybij`: The bijection that defines the quotient type "line" using the parallel relation
- **Theorems**:
  - `PARDIR_REFL`: Reflexivity of the parallel relation
  - `PARDIR_SYM`: Symmetry of the parallel relation
  - `PARDIR_TRANS`: Transitivity of the parallel relation
  - `perpl_th`: Likely a theorem about perpendicular lines

### Porting notes
When porting this to another proof assistant:
1. Ensure that the target system has a mechanism for defining quotient types similar to HOL Light's `define_quotient_type`.
2. The parallelism relation must be established as an equivalence relation before defining the quotient.
3. Some systems may require more explicit proofs that operations on lines are well-defined (respect the equivalence relation).
4. The specific lifting theorem mechanisms vary across proof assistants - some may require manual proof of congruence properties rather than having an automated lifting mechanism.

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
This theorem is a lifted version of the `DIRECTION_AXIOM_1` theorem to the context of lines. It states:

For any two lines $p$ and $p'$ that are not parallel, there exists a line $l$ such that:
1. $p$ is perpendicular to $l$
2. $p'$ is perpendicular to $l$
3. For any line $l'$ that is perpendicular to both $p$ and $p'$, $l'$ is parallel to $l$

### Informal proof
The theorem is directly derived from `DIRECTION_AXIOM_1` using the function `line_lift_thm`. This function lifts theorems about vectors in $\mathbb{R}^3$ to corresponding statements about lines in projective geometry.

The original theorem `DIRECTION_AXIOM_1` states that for non-parallel direction vectors, there exists a direction perpendicular to both, which is unique up to parallelism. The lifting process translates this statement from the context of direction vectors to the context of lines.

### Mathematical insight
This theorem establishes a fundamental property of perpendicularity in projective geometry: given two non-parallel lines, there is a unique (up to parallelism) line that is perpendicular to both. This can be considered as a statement about the existence and uniqueness of a common perpendicular to two skew lines in 3D space.

The lifting mechanism used here is a common technique in the formalization of projective geometry, where theorems proved for direction vectors in $\mathbb{R}^3$ are systematically transferred to statements about lines in projective space. This approach allows for reusing results about vectors rather than proving the corresponding statements directly for lines.

### Dependencies
- **Theorems**:
  - `DIRECTION_AXIOM_1`: States that for non-parallel vectors in $\mathbb{R}^3$, there exists a direction perpendicular to both that is unique up to parallelism.
- **Functions**:
  - `line_lift_thm`: A function that lifts theorems about direction vectors to theorems about lines.

### Porting notes
When porting this theorem to another proof assistant:
1. You'll need to first implement the lifting mechanism (`line_lift_thm`) that translates statements between vector and line contexts.
2. Ensure that the dependency `DIRECTION_AXIOM_1` is ported first.
3. The notation for perpendicularity (`_|_`) and parallelism (`||`) might require appropriate definitions in the target system.
4. Consider how the target system handles the representation of lines and the concept of direction vectors.

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
For any two lines $l$ and $l'$, there exists a point $p$ that is perpendicular to both lines, i.e., $p \perp l$ and $p \perp l'$.

### Informal proof
This theorem is obtained by applying the function `line_lift_thm` to the theorem `DIRECTION_AXIOM_2`.

The theorem `DIRECTION_AXIOM_2` states that for any two directions $l$ and $l'$, there exists a direction $p$ that is orthogonal to both $l$ and $l'$. This theorem about directions is lifted to the corresponding theorem about lines using `line_lift_thm`.

The lifting mechanism transforms the statement about orthogonality of directions into the corresponding statement about perpendicularity of lines.

### Mathematical insight
This theorem establishes the existence of a point that is perpendicular to any two given lines in the projective plane. It's a fundamental property in projective geometry and is derived from the corresponding property of directions.

In projective geometry, the notion of perpendicularity between points and lines is an important concept. This theorem guarantees that for any two lines, we can find a point that stands in a perpendicular relationship to both lines.

The theorem is obtained by lifting a corresponding result about directions (DIRECTION_AXIOM_2) to the level of lines, which showcases the dualities and correspondences in projective geometry.

### Dependencies
- **Theorems**:
  - `DIRECTION_AXIOM_2`: For any two directions, there exists a direction orthogonal to both
- **Functions**:
  - `line_lift_thm`: A function that lifts theorems about directions to corresponding theorems about lines

### Porting notes
When porting this theorem to other proof assistants, one should first ensure that the underlying concepts of projective geometry, particularly the notion of perpendicularity between points and lines, are properly defined. Additionally, the mechanism for lifting theorems from directions to lines should be implemented, as this is crucial for the proof of this theorem.

---

## LINE_AXIOM_3

### Name of formal statement
LINE_AXIOM_3

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
```

### Informal statement
There exist three lines $p$, $p'$, and $p''$ such that:
1. $p$ is not parallel to $p'$
2. $p'$ is not parallel to $p''$
3. $p$ is not parallel to $p''$
4. There does not exist a line $l$ such that $p$ is perpendicular to $l$, $p'$ is perpendicular to $l$, and $p''$ is perpendicular to $l$.

### Informal proof
This theorem is derived from `DIRECTION_AXIOM_3` using the function `line_lift_thm`. The function `line_lift_thm` lifts theorems about directions to theorems about lines.

The original theorem `DIRECTION_AXIOM_3` proves that there exist three directions $p$, $p'$, and $p''$ such that:
- No two of them are parallel
- There does not exist a direction $l$ such that all three are perpendicular to $l$

In the proof of `DIRECTION_AXIOM_3`, the basis vectors of $\mathbb{R}^3$ (specifically `basis 1`, `basis 2`, and `basis 3`) are used as concrete examples of three directions that satisfy these properties.

Since directions correspond to lines in projective geometry, the `line_lift_thm` function translates this result about directions into the corresponding statement about lines in 3D space.

### Mathematical insight
This theorem establishes a fundamental property of 3D projective geometry: the existence of three lines that are mutually non-parallel and do not share a common perpendicular line. 

In 3D space, this is significant because it demonstrates that not all triples of lines have a common perpendicular, even when no two of the lines are parallel. This contrasts with the 2D case where any two non-parallel lines always have a unique point of intersection.

This result is part of the axiomatization of projective geometry and contributes to characterizing the geometric properties of 3D space.

### Dependencies
- **Theorems**: 
  - `DIRECTION_AXIOM_3`: Establishes the existence of three directions with specific properties
- **Functions/Definitions**:
  - `line_lift_thm`: A function that lifts theorems about directions to theorems about lines

### Porting notes
When porting this to another system, one should:
1. First implement the corresponding theorem about directions (`DIRECTION_AXIOM_3`)
2. Implement the lifting mechanism from direction theorems to line theorems
3. The proof likely depends on a specific representation of 3D Euclidean space and projective geometry, so ensure that the target system has compatible abstractions

The original proof uses concrete basis vectors in $\mathbb{R}^3$, so any port should have a similar way to represent and reason about these geometric objects.

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
For every plane $\alpha$, there exists a line $L$ and three distinct points $P$, $P'$, and $P''$ such that:
1. $P$, $P'$, and $P''$ are non-collinear (i.e., there is no single line containing all three points)
2. $L$ is orthogonal to each of the lines determined by pairs of these points (i.e., $L \perp \overline{PP'}$, $L \perp \overline{P'P''}$, and $L \perp \overline{PP''}$)

### Informal proof
This theorem is derived directly from `DIRECTION_AXIOM_4` using the `line_lift_thm` function. The function `line_lift_thm` lifts a theorem about lines in a single plane to a theorem about lines in any plane.

The original theorem `DIRECTION_AXIOM_4` states that for any line $l$, there exist three non-collinear points $p$, $p'$, and $p''$ such that $l$ is orthogonal to each of the lines determined by these points. The `line_lift_thm` function then generalizes this statement to apply to any plane.

### Mathematical insight
This axiom is part of a system of axioms for plane geometry, specifically dealing with orthogonality and the existence of certain configurations of lines and points. It ensures that in any plane, we can find a line that is simultaneously perpendicular to three different lines determined by three non-collinear points. This is an important structural property in projective and Euclidean geometry.

The theorem can be viewed as a statement about the richness of the geometric structure - it guarantees that orthogonality relationships exist in sufficient abundance to create certain configurations.

### Dependencies
- **Theorems**:
  - `DIRECTION_AXIOM_4`: States that for any line, there exist three non-collinear points such that the line is orthogonal to each of the lines determined by these points.

- **Functions**:
  - `line_lift_thm`: A function that lifts theorems about lines in a single plane to theorems about lines in any plane.

### Porting notes
When porting this theorem to other systems:
- Ensure that the notion of orthogonality (`_|_`) is properly defined
- The function `line_lift_thm` may need to be implemented in the target system
- The representation of planes and the lifting from 2D to 3D geometry might require different approaches in other proof assistants

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
This introduces a new type `point` with two bijective functions:
- `mk_point : line -> point` (the constructor)
- `dest_point : point -> line` (the destructor)

The new type is defined based on the existence of at least one element of type `line` satisfying the trivial condition `T` (true).

### Informal proof
The proof obligation for creating this type definition is to show that there exists at least one element of type `line` that satisfies the condition (in this case, the trivial condition `T`). 

The proof is simply done by applying `REWRITE_TAC[]` to the goal `?x:line. T`. Since `T` is always true, this tactic immediately solves the goal, establishing that the type `line` is non-empty, which is the only requirement for defining the new type `point`.

### Mathematical insight
This definition creates a new type `point` that is isomorphic to the type `line`, or more precisely, to the subset of `line` satisfying the condition `T` (which is the entire type `line`). 

The functions `mk_point` and `dest_point` establish the bijection between these types. This is a standard way in HOL Light to create a new type that is isomorphic to an existing type or a subset of an existing type.

In this specific case, the trivial condition `T` means that `point` and `line` are essentially the same type with different names. This might be part of a formalization of geometry where points and lines are treated as distinct but related concepts.

### Dependencies
No specific dependencies are listed or used beyond the basic HOL Light system.

### Porting notes
When porting this to other proof assistants:
- In systems with more sophisticated type systems (like Coq or Lean), you might use type aliases or records instead of this bijection approach.
- In Isabelle/HOL, you would use the `typedef` command which is specifically designed for this purpose.
- Note that this definition assumes the existence of the `line` type, which should be defined before this or imported from somewhere else.

---

## on

### on
- `on`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let on = new_definition `p on l <=> perpl (dest_point p) l`;;
```

### Informal statement
For a point $p$ and a line $l$, the relation "$p$ on $l$" is defined as:
$$p \text{ on } l \iff \text{perpl}(\text{dest\_point}(p), l)$$

This defines when a point lies on a line, where:
- $\text{dest\_point}(p)$ extracts the coordinate representation of the point $p$
- $\text{perpl}$ is a predicate determining if the coordinates are perpendicular to the line $l$

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition establishes a fundamental geometric relation between points and lines. The predicate "on" captures the incidence relation in the geometric context, specifying when a point lies on a line. 

The implementation uses the perpendicularity relation (`perpl`), which suggests this is operating in a projective geometry framework where lines might be represented as normal vectors, and a point is on a line when its coordinates are perpendicular to that normal vector.

This definition is essential for expressing basic geometric statements about points and lines in the formal system, and forms part of the foundational vocabulary for projective geometry formalization.

### Dependencies
**Definitions:**
- `perpl` - Predicate determining perpendicularity
- `dest_point` - Function extracting coordinates from a point

### Porting notes
When porting this definition to another proof assistant:
- Ensure that the underlying representation of points and lines is compatible
- Verify that `perpl` and `dest_point` have been properly defined first
- Consider whether the target system has a more natural way to express point-on-line incidence relations, which might avoid the need for coordinate extraction

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
The theorem `POINT_CLAUSES` establishes three key properties about the `point` type and its bijection with `line`:

1. Two points $p$ and $p'$ are equal if and only if their corresponding line representations under `dest_point` are equal:
   $$p = p' \iff \text{dest\_point}(p) = \text{dest\_point}(p')$$

2. A property $P$ holds for all `dest_point p` if and only if it holds for all lines:
   $$(\forall p. P(\text{dest\_point}(p))) \iff (\forall l. P(l))$$

3. There exists a point $p$ such that property $P$ holds for `dest_point p` if and only if there exists a line $l$ such that $P$ holds for $l$:
   $$(\exists p. P(\text{dest\_point}(p))) \iff (\exists l. P(l))$$

### Informal proof
The proof follows directly from the type bijection established by `point_tybij`, which defines a bijective correspondence between the types `point` and `line` through the functions `mk_point` and `dest_point`.

Since `mk_point` and `dest_point` form a bijection:
- The first clause follows from the injectivity of `dest_point`
- The second and third clauses follow from the surjectivity of `dest_point`

The theorem is proved using the `MESON_TAC` automated reasoning tool with the `point_tybij` theorem as the key input.

### Mathematical insight
This theorem establishes the fundamental properties of the bijection between points and lines in the formalization. It ensures that working with points is equivalent to working with their line representations. 

The bijection between points and lines is a key part of the formalization of projective geometry, where points can be represented by lines (or dually, lines by points). This theorem provides the necessary transfer principles that allow properties to be moved between the two representations.

These clauses are essential for working with the abstractly defined `point` type, allowing us to translate between statements about points and statements about their representations as lines.

### Dependencies
- **Theorems:**
  - `point_tybij`: Establishes the type bijection between `point` and `line` using the functions `mk_point` and `dest_point`

### Porting notes
When porting this theorem to other systems:
1. Ensure that the type definition mechanism in the target system supports creating new types via bijections with existing types
2. The corresponding type bijection theorems need to be established first
3. Many proof assistants (like Isabelle/HOL, Coq with subset types, or Lean) have mechanisms for defining subtypes or new types via bijections, but the exact syntax and theorems may differ

---

## POINT_TAC

### Name of formal statement
POINT_TAC

### Type of the formal statement
Tactic definition

### Formal Content
```ocaml
let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;
```

### Informal statement
`POINT_TAC` is a tactic that, given a theorem `th`, applies rewriting using the definitions of `on` and `POINT_CLAUSES`, and then accepts the theorem `th` as the goal. Specifically, it:
1. Rewrites the current goal using the definition of relation `on` and the point equality/quantifier clauses
2. Then immediately accepts theorem `th` as establishing the goal

### Informal proof
This is a tactic definition, not a theorem with a proof. The tactic:

1. Applies `REWRITE_TAC[on; POINT_CLAUSES]` which rewrites the goal by:
   - Replacing occurrences of `p on l` with `perpl (dest_point p) l`
   - Using the point identity and quantifier clauses from `POINT_CLAUSES`

2. Then applies `ACCEPT_TAC th` which completes the proof using the provided theorem `th`

### Mathematical insight
This tactic serves as a utility for simplifying proofs in projective geometry where points are represented as an abstract type with conversions to and from lines. It handles the common pattern of:
- Converting abstract point operations to concrete operations on lines (via `dest_point`)
- Handling point equality and quantification over points
- Then applying a theorem that directly proves the resulting goal

The tactic encapsulates a common proof pattern in projective geometry, where one often needs to translate between the abstract point representation and the underlying line representation, then apply a known result.

### Dependencies
- **Theorems**:
  - `POINT_CLAUSES`: Provides properties for point equality and quantification over points
- **Definitions**:
  - `on`: Relation indicating when a point lies on a line

### Porting notes
When porting to other proof assistants:
- This is a proof automation utility designed to simplify proofs in projective geometry
- The main consideration is whether the target system handles abstract types and type bijections similarly
- In systems with stronger type theory, this pattern might be replaced with more direct type conversions or type class mechanisms
- The pattern can be implemented as a tactic, method, or tactic notation depending on the system

---

## AXIOM_1

### AXIOM_1
- AXIOM_1

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
For any two distinct points $p$ and $p'$, there exists a unique line $l$ such that both $p$ and $p'$ are on $l$.

More precisely, for all points $p$ and $p'$, if $p \neq p'$, then there exists a line $l$ such that:
- $p$ is on $l$
- $p'$ is on $l$
- For any line $l'$, if $p$ is on $l'$ and $p'$ is on $l'$, then $l' = l$ (uniqueness property)

### Informal proof
This theorem appears to be proven using the tactics `POINT_TAC` and `LINE_AXIOM_1`, which suggests it is referring to a fundamental axiom in planar geometry. The proof likely applies basic axioms of projective geometry without requiring complex steps.

The proof essentially establishes that:
1. Two distinct points determine a unique line
2. The proof uses `LINE_AXIOM_1`, suggesting this is a direct application of a basic axiom rather than a complex derivation

### Mathematical insight
This statement is one of the fundamental axioms of projective geometry, sometimes called the "incidence axiom" or "two-point axiom". It expresses that:
1. Any two distinct points determine a line
2. This line is unique

This axiom is essential in the construction of projective geometry and forms the basis for many further results. It establishes the basic relationship between points and lines, ensuring that the geometry is well-defined in terms of incidence relationships.

### Dependencies
- Definitions:
  - `on`: Defines when a point is on a line using the `perpl` relation and `dest_point` function
- Tactics:
  - `POINT_TAC`: A tactic likely handling point-specific reasoning
  - `LINE_AXIOM_1`: A tactic implementing an axiom about lines

### Porting notes
When porting to other proof assistants:
- This is a fundamental axiom, so it might be part of the basic axiomatization in other systems that formalize projective geometry
- The implementation of `on` using `perpl` and `dest_point` should be properly translated, as the meaning of a point being on a line is system-dependent
- Consider whether the target system has a built-in notion of projective geometry or whether you need to define the concepts from scratch

---

## AXIOM_2

### AXIOM_2
- AXIOM_2

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AXIOM_2 = prove
 (`!l l'. ?p. p on l /\ p on l'`,
  POINT_TAC LINE_AXIOM_2);;
```

### Informal statement
For any two lines $l$ and $l'$, there exists a point $p$ such that $p$ lies on both line $l$ and line $l'$.

Formally: $\forall l, l' \exists p, p \text{ on } l \wedge p \text{ on } l'$.

In this formalization, the relation "$p \text{ on } l$" represents that point $p$ lies on line $l$, which is encoded in the system using the predicate `on`.

### Informal proof
This theorem represents an axiom of projective geometry which states that any two lines have a point of intersection. The proof is accomplished using the specialized tactics `POINT_TAC` and `LINE_AXIOM_2`.

The tactic `LINE_AXIOM_2` applies the underlying geometric axiom asserting the existence of an intersection point between any two lines, while `POINT_TAC` handles the appropriate representation of points and their relation to lines in the formalization.

### Mathematical insight
This axiom is fundamental in projective geometry, stating that any two lines have a point of intersection. In Euclidean geometry, this statement would require an exception for parallel lines, but in projective geometry, parallel lines are considered to meet at points "at infinity."

The theorem establishes that the geometric space being formalized is connected in a specific way - there are no "isolated" lines that don't intersect with others. This property is crucial for many theorems in projective geometry.

The formulation in terms of the `on` relation encodes the geometric relation between points and lines in HOL Light.

### Dependencies
- **Definitions:**
  - `on`: Defines when a point lies on a line

### Porting notes
When porting this to another system, ensure that:
1. The underlying geometric representation (how points and lines are encoded) is properly set up
2. The interpretation of "on" as the relation between points and lines is maintained consistently
3. The axiom of projective geometry (any two lines intersect) is available in some form
4. The tactics `POINT_TAC` and `LINE_AXIOM_2` might need to be reimplemented depending on the target system's tactics

---

## AXIOM_3

### AXIOM_3
- State the exact name of the formal item as it appears in the HOL Light source.

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
This theorem states that there exist three distinct points $p$, $p'$, and $p''$ such that no line contains all three of them. Formally:

$\exists p, p', p''. \, p \neq p' \, \land \, p' \neq p'' \, \land \, p \neq p'' \, \land \, \lnot (\exists l. \, p \text{ on } l \, \land \, p' \text{ on } l \, \land \, p'' \text{ on } l)$

Here, "$p \text{ on } l$" means that point $p$ lies on line $l$, which is defined as the perpendicular relation between the destination of point $p$ and line $l$.

### Informal proof
This theorem is proven by directly applying the tactics `POINT_TAC` and `LINE_AXIOM_3`. 

The proof relies on the axioms of projective geometry, particularly the axiom stating that not all points lie on the same line. In projective geometry, this is a fundamental property - that there exist three non-collinear points.

The tactic `POINT_TAC` likely handles the conversion of the points into their appropriate representation, while `LINE_AXIOM_3` presumably applies the corresponding axiom from the underlying geometrical system.

### Mathematical insight
This theorem represents one of the fundamental axioms of projective geometry. It establishes that the projective plane is truly two-dimensional by ensuring that there are at least three non-collinear points.

The existence of three points that do not all lie on the same line is essential for defining a proper plane in projective geometry. Without this axiom, we might end up with a degenerate space where all points lie on a single line, effectively reducing the dimension to one.

This axiom is crucial for constructing projective planes and is generally paired with other axioms, such as "any two distinct points determine a unique line" to develop the full theory of projective geometry.

### Dependencies
- Definitions:
  - `on`: Defines when a point lies on a line using the perpendicular relation: `p on l <=> perpl (dest_point p) l`

### Porting notes
When porting this theorem to another system:
- Ensure the system has an appropriate representation of projective geometry
- Verify that the definition of points and lines matches the HOL Light implementation
- The implementation of `POINT_TAC` and `LINE_AXIOM_3` tactics may need to be replicated or replaced with equivalent proof methods in the target system
- This axiom is fundamental to projective geometry, so it might already exist in target systems with projective geometry libraries

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
For every line $l$, there exist distinct points $p$, $p'$, and $p''$ such that all three points lie on the line $l$.

More formally: $\forall l. \exists p, p', p''. (p \neq p') \wedge (p' \neq p'') \wedge (p \neq p'') \wedge (p \text{ on } l) \wedge (p' \text{ on } l) \wedge (p'' \text{ on } l)$

Here, "$p \text{ on } l$" means that the point $p$ lies on the line $l$, which is defined as the perpendicular relation between the point's coordinates and the line.

### Informal proof
This theorem is proven by applying the tactics `POINT_TAC` and `LINE_AXIOM_4`, which represent higher-level proof strategies in this formalization of geometry.

The proof relies on the axiom of three-point existence on a line (LINE_AXIOM_4), which is a fundamental axiom in projective geometry stating that every line contains at least three distinct points.

The `POINT_TAC` likely handles the proper representation of points and their properties in this formalization.

### Mathematical insight
This theorem formalizes an important axiom of projective geometry: every line contains at least three distinct points. This property is fundamental in projective geometry and distinguishes it from other geometries.

In projective geometry, this axiom ensures that lines are "rich" enough with points to support the development of the theory. It rules out geometries where lines might contain only one or two points.

This axiom, together with other basic axioms about points, lines, and their incidence relations, forms the foundation of projective geometry, allowing for the derivation of more complex theorems about projective spaces.

### Dependencies
#### Definitions
- `on`: Defines when a point lies on a line, expressed as a perpendicular relation between the point's coordinates and the line.

#### Tactics
- `POINT_TAC`: A custom tactic for handling point-related reasoning in this formalization.
- `LINE_AXIOM_4`: A tactic or theorem representing the axiom that every line contains at least three distinct points.

### Porting notes
When porting this theorem to another system:
1. Ensure that the system has a representation of points and lines with an appropriate "on" relation.
2. The corresponding axiom in the target system might be named differently but should express the same fundamental geometric property.
3. The proof might need to be rewritten according to the target system's proof style, especially if the source system uses custom tactics without direct equivalents.

---

## projl

### projl
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let projl = new_definition
 `projl x = mk_line((||) (mk_dir x))`;;
```

### Informal statement
The definition `projl` maps a vector $x$ in $\mathbb{R}^3$ to a projective line by:

$$\text{projl}(x) = \text{mk\_line}((||)(\text{mk\_dir}(x)))$$

where:
- $\text{mk\_dir}(x)$ converts the vector $x$ to a direction
- $(||)$ is an operator that takes a direction and returns its parallel class
- $\text{mk\_line}$ converts a parallel class to a projective line

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition creates a mapping from vectors in three-dimensional space to projective lines. It works by:
1. First converting a vector to a direction using `mk_dir`
2. Then finding the parallel class of that direction using the parallel operator `(||)`
3. Finally constructing a projective line from this parallel class using `mk_line`

The function plays an important role in projective geometry by establishing connections between vector geometry and projective geometry. It allows us to represent projective lines using vectors, which is useful for computational purposes and theoretical development in projective geometry.

This definition is part of a family of mappings between different geometric representations (vectors, directions, projective points, projective lines) that are fundamental for working with projective geometries in a formalized setting.

### Dependencies
#### Definitions
- `mk_line` - Creates a projective line from a parallel class
- `mk_dir` - Creates a direction from a vector
- `(||)` - Maps a direction to its parallel class

### Porting notes
When porting this definition, ensure that the underlying concepts of directions, parallel classes, and projective lines are properly defined in the target system. The specific representations of these geometric objects might differ between proof assistants, so the implementation details of `mk_dir`, `(||)`, and `mk_line` should be carefully examined and adapted.

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
The function `projp` is defined as:

$$\text{projp}(x) = \text{mk\_point}(\text{projl}(x))$$

where `projl(x)` represents the line parallel to the direction of point $x$, and `mk_point` creates a point from a line.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition relates to projective geometry. The function `projp` takes a point $x$ and returns a new point that is obtained by:
1. First finding the line `projl(x)` parallel to the direction of $x$
2. Then converting this line back to a point using `mk_point`

This operation is useful in projective geometry for operations involving projections. It essentially provides a way to map a point to another point via an intermediate line construction. The result represents a kind of projection of the original point.

### Dependencies
#### Definitions
- `projl`: Definition that maps a point to a line parallel to the direction of the point.
- `mk_point`: Function that creates a point from a line (implied, not shown in dependencies).
- `mk_dir`: Function that extracts the direction from a point (implied, used inside `projl`).

### Porting notes
When porting this definition to another system, ensure that the underlying concepts of projective geometry (points, lines, directions) and their operations (`mk_point`, `mk_line`, `mk_dir`) are properly implemented first. The definition itself is straightforward once these dependencies are in place.

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
For any line $l$, there exists a non-zero vector $x$ such that $l = \text{projl}(x)$, where $\text{projl}$ maps a vector to the line it represents in projective geometry.

### Informal proof
The proof shows that any line can be represented by some non-zero vector in homogeneous coordinates:

1. Given an arbitrary line $l$, we first prove that there exists a direction $d$ such that $l = \text{mk\_line}((||) \, d)$.
   - This follows from the bijection between lines and equivalence classes of directions (represented by `line_tybij`).

2. Once we have such a direction $d$, we set $x = \text{dest\_dir}(d)$ and show:
   - $x$ is non-zero (by properties of directions)
   - $l = \text{projl}(x)$ (by definition of `projl`)

3. This is achieved using the properties of the bijection between directions and non-zero vectors (represented by `direction_tybij`).

### Mathematical insight
This theorem establishes the surjectivity of the `projl` mapping from vectors to projective lines. It ensures that every projective line can be represented by homogeneous coordinates (non-zero vectors), which is a fundamental property in projective geometry. The theorem helps establish the correspondence between the algebraic representation (vectors) and the geometric objects (lines) in projective space.

This result is part of a pair of mappings between geometric entities and their homogeneous coordinate representations, allowing geometric problems to be translated into algebraic ones and vice versa.

### Dependencies
- Definitions:
  - `line_tybij`: Defines the bijection between lines and equivalence classes of directions
  - `projl`: Maps a vector to the projective line it represents

- Used implicitly:
  - `direction_tybij`: The bijection between directions and non-zero vectors
  - `mk_dir` and `dest_dir`: Functions for creating and extracting direction values

### Porting notes
When porting this to other proof assistants, ensure that:
1. The quotient type for projective lines is properly defined
2. The bijection between directions and non-zero vectors is established
3. The mapping between vectors and projective lines (`projl`) is defined correctly

In systems without quotient types, you might need to work directly with equivalence classes or provide explicit representatives for projective objects.

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
The specification `homol` states that for every line `l`, there exists a non-zero vector `x` such that `l = projl(x)`. Formally:

$$\forall l. \exists x. (x \neq \vec{0}) \land (l = \text{projl}(x))$$

### Informal proof
This specification is created using the `new_specification` mechanism in HOL Light by applying Skolem's theorem to the theorem `PROJL_TOTAL`. The Skolemization process essentially introduces a function (which we call `homol`) that, given a line `l`, returns a non-zero vector `x` such that `l = projl(x)`.

The underlying theorem `PROJL_TOTAL` proves that for any line `l`, there exists a non-zero vector `x` such that `l = projl(x)`. This result comes from the fact that:
- Every line can be represented in the form `mk_line((||) d)` for some direction `d`
- For such a line, `projl(dest_dir d)` gives the line, and `dest_dir d` is non-zero

### Mathematical insight
This specification establishes a function that gives a concrete non-zero vector representation for any projective line. In projective geometry, a line in projective space can be represented by any non-zero vector (up to scalar multiplication). The `homol` function provides a canonical choice of such a vector for each line.

This is important for constructive work in projective geometry, where we need to explicitly produce a vector representing a given line rather than just knowing one exists. The function provides a way to move from the abstract representation of lines to their concrete vector form.

### Dependencies
- **Theorems**:
  - `PROJL_TOTAL`: Establishes that for any line, there exists a non-zero vector that projects to that line

### Porting notes
When porting this to other systems:
- This is a Skolemization, so you'll need to create a function (often called a "choice function") that picks a specific non-zero vector for each line
- The function should satisfy the property that for any line `l`, `homol(l)` is a non-zero vector and `projl(homol(l)) = l`
- Different proof assistants have different mechanisms for introducing such specification functions - in some systems you might need to use the axiom of choice or a choice operator explicitly

---

## PROJP_TOTAL

### PROJP_TOTAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Theorem (prove)

### Formal Content
```ocaml
let PROJP_TOTAL = prove
 (`!p. ?x. ~(x = vec 0) /\ p = projp x`,
  REWRITE_TAC[projp] THEN MESON_TAC[PROJL_TOTAL; point_tybij]);;
```

### Informal statement
For any point $p$, there exists a non-zero vector $x$ such that $p = \text{projp}(x)$.

Formally:
$$\forall p. \exists x. x \neq \vec{0} \land p = \text{projp}(x)$$

### Informal proof
The theorem is proven by first rewriting using the definition of `projp`, then applying the `MESON_TAC` tactic with the theorems `PROJL_TOTAL` and `point_tybij`.

The proof follows directly from:
- The definition of `projp`, which states that $\text{projp}(x) = \text{mk\_point}(\text{projl}(x))$
- The theorem `PROJL_TOTAL`, which states that for any line $l$, there exists a non-zero vector $x$ such that $l = \text{projl}(x)$
- The type bijection `point_tybij` that establishes the relationship between points and lines via the constructor/destructor functions `mk_point` and `dest_point`

Combining these results, we can construct any point by applying `mk_point` to a line, and any line can be represented as `projl x` for some non-zero vector $x$.

### Mathematical insight
This theorem establishes the surjectivity of the `projp` function, which maps non-zero vectors to projective points. In projective geometry, this indicates that every point in the projective space can be represented by (homogeneous coordinates of) a non-zero vector.

This result is fundamental in projective geometry as it connects the algebraic representation (vectors) with geometric objects (projective points). It ensures that we have a complete representation of the projective space through the `projp` mapping.

### Dependencies
- **Theorems**:
  - `PROJL_TOTAL`: For any line $l$, there exists a non-zero vector $x$ such that $l = \text{projl}(x)$
  - `point_tybij`: Type bijection establishing the relationship between points and lines

- **Definitions**:
  - `projp`: Maps a vector to a projective point, defined as `projp x = mk_point(projl x)`

### Porting notes
When porting this theorem to another proof assistant:
- Ensure that the representation of projective points and lines is established
- The bijection between points and lines needs to be properly defined
- The projective mappings (`projl` and `projp`) need to be defined consistently
- The theorem is quite straightforward once these foundations are in place

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
The function $\text{homop}$ is defined as:

$$\text{homop}(p) = \text{homol}(\text{dest\_point}(p))$$

where $p$ is a projective point, $\text{dest\_point}$ extracts the underlying representation of the projective point, and $\text{homol}$ is a function that applies a homogeneous transformation to that representation.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The function $\text{homop}$ maps projective points to their homogeneous coordinates by converting a projective point to its underlying representation using $\text{dest\_point}$ and then applying the $\text{homol}$ function. 

This definition creates a bridge between projective geometry and vector spaces, allowing points in projective space to be manipulated using homogeneous coordinates. It's particularly useful in projective geometry and computer graphics where projective transformations need to be applied to points.

From the dependent theorem `homop`, we can see that $\text{homop}$ has two important properties:
1. The resulting vector is non-zero: $\text{homop}(p) \neq \vec{0}$
2. Applying $\text{projp}$ to $\text{homop}(p)$ returns the original point: $p = \text{projp}(\text{homop}(p))$

This establishes a bijection between projective points and their homogeneous representations (modulo scaling).

### Dependencies
- **Theorems**:
  - `homop`: The theorem stating that homop of a point is non-zero and projp(homop(p)) = p
  - `homol`: Implicit dependency used in the definition
- **Functions**:
  - `dest_point`: Function that extracts the underlying representation of a projective point

### Porting notes
When porting this definition to another system, ensure that:
1. The projective geometry framework with concepts like `projp` and `dest_point` is already implemented
2. The `homol` function for representing homogeneous coordinates is available
3. The type system can handle the relationship between projective points and their vector representations

---

## homop

### homop

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
For all points $p$, the homogeneous coordinate vector of $p$ (denoted by $\text{homop}(p)$) is non-zero, and $p$ equals the projection of its homogeneous coordinate vector (i.e., $p = \text{projp}(\text{homop}(p))$).

### Informal proof
The proof establishes that for any point $p$:
1. $\text{homop}(p) \neq \vec{0}$
2. $p = \text{projp}(\text{homop}(p))$

The proof proceeds as follows:
- Start with an arbitrary point $p$.
- Expand the definitions of $\text{homop}$ and $\text{projp}$.
- Use a property from the type bijection for points: $p = \text{mk\_point}(l) \Leftrightarrow \text{dest\_point}(p) = l$.
- This reduces the goal to showing that $\text{homol}(l) \neq \vec{0}$ and $l = \text{projl}(\text{homol}(l))$ for a line $l$, which is exactly the statement of the theorem $\text{homol}$.

### Mathematical insight
This theorem establishes fundamental properties of the homogeneous coordinates for points in projective geometry:
1. The homogeneous coordinate vector of a point is never the zero vector, which aligns with the projective geometry principle that homogeneous coordinates are defined up to a non-zero scalar multiple.
2. The projection operation is a left inverse of the homogeneous coordinate mapping, showing that we can recover the original point from its homogeneous coordinates through projection.

These properties ensure that the representation of points using homogeneous coordinates is well-defined and consistent with the projective geometry framework. This theorem is part of a larger formalization of projective geometry, particularly related to Desargues' theorem.

### Dependencies
- **Theorems**:
  - `point_tybij`: Type bijection for points
  - `homol`: Corresponding theorem for lines
- **Definitions**:
  - `projp`: Projection operation for points
  - `homop_def`: Definition of homogeneous coordinates for points

### Porting notes
When porting to another proof assistant, be careful with the bijection between abstract points and their concrete representations. Different proof assistants have different mechanisms for defining new types with bijections to existing types. In particular, ensure that the relationship between `mk_point`, `dest_point`, and the representation of lines is properly established.

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
Two vectors $x$ and $y$ in $\mathbb{R}^3$ are parallel (denoted as $\text{parallel}(x, y)$) if and only if their cross product is the zero vector:
$$\text{parallel}(x, y) \Leftrightarrow x \times y = \vec{0}$$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition formalizes the geometric concept of parallel vectors using the cross product. Two non-zero vectors are parallel if and only if they point in the same or exactly opposite directions, which mathematically corresponds to their cross product being zero.

In projective geometry, this concept is particularly important when working with homogeneous coordinates, where parallel lines in Euclidean space are represented by points at infinity in projective space. The definition connects the algebraic property (zero cross product) with the geometric notion of parallelism.

The cross product approach provides a clean and computationally efficient way to test for parallelism without dealing with normalization or angle calculations.

### Dependencies
#### Definitions
- `cross`: Defines the cross product of two vectors in $\mathbb{R}^3$ as 
  $a \times b = \text{vector}[a_2 \cdot b_3 - a_3 \cdot b_2; a_3 \cdot b_1 - a_1 \cdot b_3; a_1 \cdot b_2 - a_2 \cdot b_1]$

### Porting notes
When porting this definition to other proof assistants:
- Ensure that the cross product is defined for 3D vectors
- Be mindful that some systems might represent vectors differently or have different conventions for indexing vector components
- The definition is straightforward but relies on the cross product being properly defined

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
For any point $p$ and line $l$, $p$ is on $l$ if and only if the homogeneous coordinates representing $p$ are orthogonal to the homogeneous coordinates representing $l$.

Formally, 
$$\forall p, l. \, p \text{ on } l \Leftrightarrow \text{orthogonal}(\text{homop}(p), \text{homol}(l))$$

where $\text{homop}(p)$ represents the homogeneous coordinates of point $p$, and $\text{homol}(l)$ represents the homogeneous coordinates of line $l$.

### Informal proof
The proof establishes the equivalence between the incidence relation "on" in projective geometry and the orthogonality of homogeneous coordinates:

* Begin by applying the definitions of `homop` and `homol` to transform the statement into a form involving their implementations.
* Expand the definition of the `on` relation, which is defined in terms of the perpendicularity relation `perpl` on the underlying representations.
* Use the definitions of `projp` and `projl` which map between vector space and projective geometry representations.
* Apply `point_tybij` which relates the abstract type `point` with its representation.
* Apply `perpl_th` to rewrite the perpendicularity condition.
* Use the definition of `perpdir` which relates the perpendicularity of directions to orthogonality of vectors.
* Finally, apply `homol` and `homop` theorems along with `direction_tybij` to complete the proof.

The proof essentially traces through the definitions to show that the incidence relation in projective geometry corresponds precisely to orthogonality in the underlying vector space when using homogeneous coordinates.

### Mathematical insight
This theorem captures a fundamental correspondence in projective geometry: the incidence relation between points and lines is equivalent to orthogonality of their homogeneous coordinate representations. This duality is at the heart of projective geometry and allows algebraic methods (like linear algebra) to be applied to geometric problems.

In projective geometry, a point can be represented by homogeneous coordinates (a vector up to scaling), and similarly, a line can be represented by homogeneous coordinates. The relationship "point lies on line" is then characterized by the orthogonality of these coordinate vectors.

This result is particularly useful for computational implementations of projective geometry, as it allows incidence tests to be performed using simple dot products of homogeneous coordinates.

### Dependencies
- **Definitions**:
  - `on`: Defines when a point is on a line 
  - `perpdir`: Defines perpendicularity of directions
  - `projl`: Maps from a vector to a projective line
  - `projp`: Maps from a vector to a projective point
  
- **Theorems**:
  - `point_tybij`: Relates the abstract type `point` with its representation
  - `homop`: Properties of homogeneous point coordinates
  - `homol`: Properties of homogeneous line coordinates
  - `perpl_th`: Theorem about perpendicular lines
  - `direction_tybij`: Relates the abstract type `direction` with its representation

### Porting notes
When porting this theorem:
1. Ensure that your system has appropriate representations for projective geometry, particularly homogeneous coordinates for points and lines.
2. The abstract type bijections (`point_tybij`, `direction_tybij`) may need special attention, as different proof assistants handle abstract types differently.
3. The orthogonality relation between vectors should be established first.
4. The duality between incidence in projective geometry and orthogonality in vector spaces should be formalized explicitly.

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
For any lines $l$ and $l'$, the lines are equal if and only if their homologous vectors are parallel:
$$\forall l, l' \in \text{line}.\, (l = l' \iff \text{parallel}(\text{homol}(l), \text{homol}(l')))$$

Where:
- $\text{parallel}(x, y)$ means the cross product of vectors $x$ and $y$ is zero: $x \times y = \vec{0}$
- $\text{homol}(l)$ denotes the homologous vector for a line $l$

### Informal proof
The proof establishes that two lines are equal if and only if their homologous vectors are parallel.

1. First, we rewrite the left-hand side of the equivalence using the definition of `homol`.

2. We use the properties of the quotient type `line` to show that:
   $$\text{mk\_line}((||) \, l) = \text{mk\_line}((||) \, l') \iff (||) \, l = (||) \, l'$$
   where $(||)$ represents the equivalence relation used to define the line type.

3. By `PARDIR_EQUIV`, we know that:
   $$((||) \, x = (||) \, y) \iff x \, || \, y$$

4. We then expand the definitions of the parallel direction relation `pardir` (denoted by $||$) and the `parallel` predicate:
   - $x \, || \, y \iff \text{dest\_dir}(x) \times \text{dest\_dir}(y) = \vec{0}$
   - $\text{parallel}(x, y) \iff x \times y = \vec{0}$

5. Finally, using the properties of the homologous vector and the bijection between directions and vectors, we complete the proof that two lines are equal if and only if their homologous vectors are parallel.

### Mathematical insight
This theorem establishes a fundamental relationship between equality of lines and parallelism of their homologous vectors in projective geometry. It connects the abstract projective line representation with concrete vector operations, providing a computational means to check line equality using the parallelism of vectors.

The result is important because:
1. It provides a concrete computational method to test line equality using vector operations
2. It bridges the gap between the abstract projective setting (quotient types for lines) and vector geometry
3. It establishes that the homologous vector representation of lines preserves their essential properties

This theorem is part of the formalization of projective geometry in HOL Light, specifically in the context of Desargues' theorem.

### Dependencies
- **Theorems**:
  - `PARDIR_EQUIV`: Shows that the equivalence relation on directions can be expressed using parallel direction relation
  
- **Definitions**:
  - `parallel`: Defines when two vectors are parallel (their cross product is zero)
  - `pardir`: Defines the parallel direction relation
  - `line_tybij`: Defines the quotient type for lines
  - `projl`: Defines the projection from vectors to lines
  - `homol`: (Not explicitly listed but used) Gives the homologous vector of a line

### Porting notes
When porting this theorem:
1. Ensure the quotient type mechanism for lines is correctly implemented in the target system
2. The cross product and vector operations need proper definitions 
3. The bijection between directions and vectors (direction_tybij) would need to be ported
4. The handling of type bijections and quotient types may differ significantly between systems

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
For any two points $p$ and $p'$, we have $p = p'$ if and only if the homogeneous vectors $\text{homop}(p)$ and $\text{homop}(p')$ are parallel.

### Informal proof
The proof proceeds by first rewriting the goal using the definition of `homop` and the theorem `EQ_HOMOL`:

1. By the definition of `homop`, we have $\text{homop}(p) = \text{homol}(\text{dest\_point}(p))$ and $\text{homop}(p') = \text{homol}(\text{dest\_point}(p'))$.

2. Using the theorem `EQ_HOMOL`, which states that two lines $l$ and $l'$ are equal if and only if their homogeneous representations $\text{homol}(l)$ and $\text{homol}(l')$ are parallel, we can rewrite our goal.

3. The theorem `point_tybij` establishes a bijection between points and lines through the functions `mk_point` and `dest_point`, which means that two points are equal if and only if their corresponding lines obtained via `dest_point` are equal.

4. By combining these facts, we can conclude that $p = p'$ if and only if $\text{dest\_point}(p) = \text{dest\_point}(p')$, which is equivalent to $\text{homol}(\text{dest\_point}(p))$ and $\text{homol}(\text{dest\_point}(p'))$ being parallel, which is exactly $\text{homop}(p)$ and $\text{homop}(p')$ being parallel.

### Mathematical insight
This theorem establishes a key relationship between the equality of projective points and the parallelism of their homogeneous vector representations. In projective geometry, points can be represented by homogeneous coordinates (vectors), and two points are the same if their homogeneous coordinates are parallel (i.e., one is a scalar multiple of the other). 

This theorem provides a formal characterization of point equality in terms of vector parallelism, which is fundamental in projective geometry and enables the algebraic manipulation of projective points through their homogeneous representations.

### Dependencies
- **Definitions:**
  - `parallel`: Defines when two vectors are parallel (their cross product is zero)
  - `homop_def`: Defines homogeneous representation of a point

- **Theorems:**
  - `point_tybij`: Establishes the bijection between points and lines
  - `homop`: States properties of the homogeneous representation of a point
  - `EQ_HOMOL`: States that two lines are equal if their homogeneous representations are parallel

### Porting notes
When implementing this in another proof assistant, ensure that:
1. The bijection between points and lines is properly established
2. The homogeneous representation functions are properly defined
3. Vector operations, particularly the cross product and parallelism test, are available

The concept of parallelism between vectors (being scalar multiples of each other) might be defined differently in other systems, so ensure the definition is consistent with the one used here.

---

## PARALLEL_PROJL_HOMOL

### PARALLEL_PROJL_HOMOL
- State the exact name of the formal item as it appears in the HOL Light source.

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
For all $x \in \mathbb{R}^3$, the vector $x$ is parallel to the homologous coordinates of the projective line determined by $x$, i.e., $\text{parallel}(x, \text{homol}(\text{projl}(x)))$.

Here:
- $\text{parallel}(x, y)$ means that the cross product of vectors $x$ and $y$ is zero: $x \times y = \vec{0}$
- $\text{projl}(x)$ constructs a projective line from a vector $x$
- $\text{homol}(l)$ returns the homologous coordinates of a projective line $l$

### Informal proof
The proof establishes that a vector is parallel to the homologous coordinates of its corresponding projective line:

- We start with an arbitrary vector $x \in \mathbb{R}^3$.
- We need to show $\text{parallel}(x, \text{homol}(\text{projl}(x)))$, which by definition means $x \times \text{homol}(\text{projl}(x)) = \vec{0}$.
- First, we consider the case where $x = \vec{0}$. In this case, $x \times \text{homol}(\text{projl}(x)) = \vec{0} \times \text{homol}(\text{projl}(\vec{0})) = \vec{0}$ by the property that the cross product of $\vec{0}$ with any vector is $\vec{0}$ (from CROSS_0).
- For the case where $x \neq \vec{0}$, we use properties of homologous coordinates:
  - We apply the theorem about homologous coordinates (`homol`), which gives us that the homologous coordinates of a projective line are in the same direction as the line.
  - We expand the definition of $\text{projl}(x)$ to show it represents the equivalence class of directions parallel to $x$.
  - Using the bijection between projective lines and equivalence classes of parallel directions, we can show that $\text{dest_line}(\text{mk_line}((||) l)) = (||) l$, where $(||)$ represents the equivalence class of parallel directions.
  - By the definition of the parallel direction relation ($\text{pardir}$), two directions are parallel if and only if their cross product is $\vec{0}$.
  - Therefore, $x \times \text{homol}(\text{projl}(x)) = \vec{0}$, which means $x$ is parallel to $\text{homol}(\text{projl}(x))$.

### Mathematical insight
This theorem establishes a fundamental "well-definedness" result in projective geometry, showing consistency in the mapping between vectors in $\mathbb{R}^3$ and their corresponding projective lines. 

Specifically, it shows that when we map a vector to projective space (creating a projective line) and then obtain the homologous coordinates of that line, those coordinates will be parallel to the original vector. This is essential for the coherence of the homogeneous coordinate representation in projective geometry.

This result validates that the homologous coordinate map preserves directional information when moving between Euclidean and projective spaces, which is a desirable property for working with projective geometry.

### Dependencies
- **Theorems**:
  - `CROSS_0`: The cross product of the zero vector with any other vector is zero
  - `PARDIR_EQUIV`: Two directions are equal if and only if they are parallel
- **Definitions**:
  - `parallel`: Two vectors are parallel if their cross product is zero
  - `pardir`: Two directions are parallel if the cross product of their representative vectors is zero
  - `line_tybij`: Bijection between projective lines and equivalence classes of parallel directions
  - `projl`: Maps a vector to a projective line representing its direction

### Porting notes
When porting this theorem:
1. Ensure the projective geometry foundations are in place, particularly the quotient construction for projective lines.
2. The homologous coordinate map (`homol`) needs to be defined first along with its properties.
3. The bijection between directions and projective lines needs careful handling, especially in systems where quotient types are handled differently from HOL Light.
4. Cross product operations and their properties need to be available in the target system.

---

## PARALLEL_PROJP_HOMOP

### PARALLEL_PROJP_HOMOP

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
For all vectors $x \in \mathbb{R}^3$, $x$ is parallel to $\text{homop}(\text{projp}(x))$.

In the context of projective geometry, this states that for any line $x$, it is parallel to the result of first projecting it into the projective plane (via $\text{projp}$) and then transforming it back to a line (via $\text{homop}$).

### Informal proof
The proof shows that the statement about points can be reduced to the corresponding statement about lines that was already established in `PARALLEL_PROJL_HOMOL`.

The proof proceeds as follows:
- We rewrite using the definitions of `homop` and `projp`
- Using the bijection between points and lines established by `point_tybij`, we have:
  $\text{homop}(\text{projp}(x)) = \text{homol}(\text{dest\_point}(\text{projp}(x))) = \text{homol}(\text{dest\_point}(\text{mk\_point}(\text{projl}(x)))) = \text{homol}(\text{projl}(x))$
- After this reduction, we can apply the theorem `PARALLEL_PROJL_HOMOL` which states that $\text{parallel}(x, \text{homol}(\text{projl}(x)))$

### Mathematical insight
This theorem establishes a fundamental relationship in projective geometry between the original line and its projection followed by homomorphism. It shows that the direction of a line is preserved when we project it to the projective plane and then map it back.

This result is part of the formalization of Desargues' theorem, which is a central theorem in projective geometry. The parallel relationship established here helps maintain the geometric invariants necessary for projective transformations.

### Dependencies
- **Theorems**:
  - `point_tybij`: Establishes type bijection for points.
  - `homop`: Properties of the homomorphism on points.
  - `PARALLEL_PROJL_HOMOL`: Establishes that a line is parallel to its projection followed by homomorphism.

- **Definitions**:
  - `parallel`: Two vectors are parallel if their cross product is zero.
  - `projp`: Projects a vector to a point.
  - `homop_def`: Defines homomorphism on points.

### Porting notes
When porting this theorem:
- Ensure the corresponding theorems for lines (`PARALLEL_PROJL_HOMOL`) is ported first
- The bijection between points and lines needs to be carefully implemented, as different proof assistants handle type bijections differently
- The definition of parallelism as zero cross product should be maintained for this proof strategy to work

---

## PARALLEL_PROJP_HOMOP_EXPLICIT

### PARALLEL_PROJP_HOMOP_EXPLICIT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any vector $x \in \mathbb{R}^3$ where $x \neq \vec{0}$, there exists a non-zero real number $a \neq 0$ such that $\text{homop}(\text{projp}(x)) = a \cdot x$.

### Informal proof
This theorem establishes a concrete relationship between a vector $x$ and the result of applying the composition of projective mappings $\text{homop} \circ \text{projp}$ to it.

The proof proceeds as follows:

- Start with the theorem `PARALLEL_PROJP_HOMOP` which states that $\forall x. \text{parallel}(x, \text{homop}(\text{projp}(x)))$.
- Apply the monotonicity of universal quantification (`MONO_FORALL`).
- Rewrite using the definition of `parallel`, which states that $\text{parallel}(x, y) \iff x \times y = \vec{0}$.
- Further rewrite using `CROSS_EQ_0`, which states that $x \times y = \vec{0} \iff \text{collinear}\{\vec{0}, x, y\}$.
- Rewrite using `COLLINEAR_LEMMA`, which relates collinearity to scalar multiplication.
- For any vector $x$, consider two cases:
  - Case $x = \vec{0}$: This case is excluded by our assumption.
  - Case $x \neq \vec{0}$: Apply properties of `homop`.
- Introduce an existential variable $c$ and show that when $c \neq 0$, we have $\text{homop}(\text{projp}(x)) = c \cdot x$.
- Complete the proof by rewriting using the definition of `homop` and vector multiplication properties.

### Mathematical insight
This theorem provides a concrete connection between vectors in $\mathbb{R}^3$ and their projective mappings. Specifically, it shows that applying the composition of projective mappings `homop ∘ projp` to a non-zero vector results in a scalar multiple of the original vector.

This is a key result in projective geometry that establishes how projective transformations preserve the direction of vectors, changing only their magnitude by a scalar factor. The theorem formalizes the intuition that projective mappings preserve collinearity.

The property is particularly important for calculations in projective geometry, as it allows us to relate the homogeneous coordinates representation back to the original vector space in a concrete way.

### Dependencies
- Theorems:
  - `CROSS_EQ_0`: Relates cross product being zero to collinearity
  - `homop`: Properties of the homogeneous operator
  - `PARALLEL_PROJP_HOMOP`: States that a vector is parallel to the result of applying homop ∘ projp
- Definitions:
  - `parallel`: Defines parallel vectors in terms of cross product
  - `projp`: Projective mapping for points

### Porting notes
When porting this theorem to other systems:
- Ensure that the projective geometry foundations, including the definitions of `projp` and `homop`, are properly implemented.
- The proof relies on collinearity properties and vector operations that may have different representations in other systems.
- The theorem uses the cross product in $\mathbb{R}^3$, so the target system should have an appropriate implementation of cross products.

---

## bracket

### bracket
- bracket

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let bracket = define
 `bracket[a;b;c] = det(vector[homop a;homop b;homop c])`;;
```

### Informal statement
The bracket of three projective points $a$, $b$, and $c$ is defined as the determinant of the matrix formed by their homogeneous coordinates:

$$\text{bracket}[a, b, c] = \det(\text{vector}[\text{homop}(a), \text{homop}(b), \text{homop}(c)])$$

where:
- $\text{homop}(p)$ denotes the homogeneous coordinates of a projective point $p$
- $\text{vector}[v_1, v_2, v_3]$ constructs a matrix with columns $v_1, v_2, v_3$
- $\det$ is the determinant function

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
The bracket notation, also known as the "determinant bracket," is a fundamental concept in projective geometry. It provides an elegant algebraic way to express geometric properties of projective points:

1. **Collinearity test**: The bracket $[a, b, c] = 0$ if and only if the three points $a$, $b$, and $c$ are collinear.

2. **Projective invariance**: The bracket value is invariant under projective transformations up to a scalar factor, making it a useful tool for proving theorems in projective geometry.

3. **Coordinate-free approach**: While the definition uses coordinates (via homop), the geometric properties expressed by the bracket are independent of the coordinate system.

This definition establishes the connection between the algebraic representation (determinants) and the geometric notions in projective space, providing a powerful tool for proving theorems in projective geometry, such as Desargues' theorem.

### Dependencies
**Theorems:**
- `homop` - Theorem establishing properties of homogeneous coordinates: their non-zero nature and their relationship with projective points

**Definitions:**
- `homop` (implicitly used) - Function that returns the homogeneous coordinates of a projective point
- `vector` (implicitly used) - Creates a matrix from column vectors
- `det` (implicitly used) - Determinant function

### Porting notes
When porting this definition to another system:
1. Ensure that the underlying representation of projective points and their homogeneous coordinates is established first
2. The implementation of determinants and vector/matrix operations might differ between systems
3. The syntax for lists or sequences might need adaptation depending on the target system's conventions

---

## COLLINEAR

### COLLINEAR

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let COLLINEAR = new_definition
 `COLLINEAR s <=> ?l. !p. p IN s ==> p on l`;;
```

### Informal statement
A set $s$ is collinear if and only if there exists a line $l$ such that for all points $p \in s$, $p$ lies on $l$.

In symbols: $\text{COLLINEAR}(s) \iff \exists l. \forall p. p \in s \implies p \text{ on } l$

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
This definition formalizes the standard geometric concept of collinearity - that a set of points all lie on the same line. This is a fundamental concept in projective geometry and is used in many theorems, including Desargues' theorem.

In this context, the definition uses the predicate `on` which relates points to lines. The collinearity property is defined for any set of points, allowing us to express statements about arbitrary collections of points lying on a common line.

This definition is stated in terms of the existence of a line containing all points in the set, which is the standard way to express collinearity in geometric contexts.

### Dependencies
#### Definitions:
- `on` - Indicates that a point lies on a line, defined as `p on l <=> perpl (dest_point p) l`

### Porting notes
When porting this definition:
- Ensure the underlying representation of points and lines in the target system is compatible
- Verify that the `on` relation is properly defined in the target system
- Consider whether the target system uses different conventions for geometric predicates

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
For any point $a$, the singleton set $\{a\}$ is collinear.

More precisely, $\forall a. \text{COLLINEAR}(\{a\})$ where $\text{COLLINEAR}(s)$ means there exists a line $l$ such that every point $p \in s$ lies on $l$.

### Informal proof
We need to show that for any point $a$, the set $\{a\}$ is collinear, meaning there exists a line containing all points in the set.

The proof proceeds by:

* First, we rewrite the goal using the definition of `COLLINEAR` and simplify the quantification over elements in the singleton set.
  * `COLLINEAR {a}` means $\exists l. \forall p \in \{a\}. p \text{ on } l$
  * After rewriting with `FORALL_IN_INSERT` and `NOT_IN_EMPTY`, this becomes $\exists l. a \text{ on } l$

* The existence of such a line follows from the axioms of projective geometry:
  * From `AXIOM_3`, we know there exist at least three non-collinear points, so at least one line exists
  * From `AXIOM_1`, for any point, there exists more than one line passing through it
  * Therefore, there must exist some line passing through point $a$, which is all we need to prove our goal

### Mathematical insight
This theorem establishes a basic property of collinearity: a singleton set is always collinear. This is a trivial but necessary result in projective geometry because:

1. Collinearity is defined in terms of the existence of a line containing all points in a set
2. For a singleton set, we only need to show that there exists at least one line passing through that point
3. In a projective plane, every point must lie on at least one line

This result serves as a base case for many inductive proofs concerning collinearity of larger sets of points.

### Dependencies
- **Theorems:**
  - `AXIOM_1`: For any two distinct points, there exists a unique line passing through them
  - `AXIOM_3`: There exist three non-collinear points (i.e., not all points lie on a single line)
- **Definitions:**
  - `COLLINEAR`: A set of points is collinear if there exists a line containing all points in the set

### Porting notes
When porting this theorem:
1. Ensure that the definition of collinearity in the target system matches HOL Light's definition
2. Check that the basic axioms of projective geometry (particularly the existence of lines through points) are available
3. The proof is short and relies on standard logical reasoning and the axioms of projective geometry, so it should port straightforwardly to other systems

---

## COLLINEAR_PAIR

### COLLINEAR_PAIR
- COLLINEAR_PAIR

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
For any two points $a$ and $b$, the set $\{a, b\}$ is collinear.

Here, a set of points is collinear if there exists a line that contains all points in the set.

### Informal proof
We prove that for any two points $a$ and $b$, the set $\{a, b\}$ is collinear.

* Case 1: If $a = b$, then $\{a, b\} = \{a\}$. By `COLLINEAR_SINGLETON`, any singleton set of points is collinear.

* Case 2: If $a \neq b$, then by Axiom 1 (`AXIOM_1`), there exists a unique line $l$ such that both $a$ and $b$ are on $l$. This means that all points in the set $\{a, b\}$ lie on the line $l$, which is exactly the definition of collinearity.

Therefore, for any two points $a$ and $b$, the set $\{a, b\}$ is collinear.

### Mathematical insight
This theorem establishes a fundamental property in projective geometry: any two distinct points determine a unique line, and hence form a collinear set. This is a direct consequence of Axiom 1 in the axiomatic system being used.

While the result may seem trivial, it provides a building block for more complex geometric theorems and helps establish the basic properties of collinearity. Collinearity is a key concept in projective geometry, and this theorem serves as a foundational result about the simplest non-trivial case of collinear points.

### Dependencies
- Theorems:
  - `AXIOM_1`: For any two distinct points, there exists a unique line passing through them
  - `COLLINEAR_SINGLETON`: Any singleton set of points is collinear
  
- Definitions:
  - `COLLINEAR`: A set of points is collinear if there exists a line containing all points in the set

### Porting notes
When porting this theorem, ensure that:
1. The definition of collinearity is consistent with the target system
2. The axiom about the existence of a unique line through two distinct points is available
3. The theorem about singleton sets being collinear is established first

The proof structure is straightforward and should translate well to most formal systems that support case analysis.

---

## COLLINEAR_TRIPLE

### COLLINEAR_TRIPLE
- COLLINEAR_TRIPLE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let COLLINEAR_TRIPLE = prove
 (`!a b c. COLLINEAR{a,b,c} <=> ?l. a on l /\ b on l /\ c on l`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY]);;
```

### Informal statement
For any three points $a$, $b$, and $c$, the set $\{a, b, c\}$ is collinear if and only if there exists a line $l$ such that all three points $a$, $b$, and $c$ lie on line $l$.

Formally, $\text{COLLINEAR}\{a, b, c\} \iff \exists l. (a \text{ on } l) \land (b \text{ on } l) \land (c \text{ on } l)$

### Informal proof
This theorem follows directly from the definition of `COLLINEAR`. 

By definition, a set $s$ is collinear (i.e., $\text{COLLINEAR } s$) if and only if there exists a line $l$ such that for all points $p \in s$, $p$ lies on line $l$.

The proof applies this definition to the specific set $\{a, b, c\}$ and uses the following HOL Light rules:
- `REWRITE_TAC[COLLINEAR]`: Expands the definition of collinearity
- `FORALL_IN_INSERT`: Handles the set membership quantification 
- `NOT_IN_EMPTY`: Handles the empty set property

When these rules are applied to the set $\{a, b, c\}$, they transform the statement "for all points $p$ in $\{a, b, c\}$, $p$ lies on line $l$" into the explicit conjunction "point $a$ lies on line $l$ AND point $b$ lies on line $l$ AND point $c$ lies on line $l$".

### Mathematical insight
This theorem provides a more direct and explicit characterization of collinearity for a set of exactly three points. While the general definition of `COLLINEAR` is formulated in terms of an arbitrary set and a universal quantification over its elements, this theorem specializes it to the common case of checking whether three specific points lie on the same line.

This is a fundamental concept in projective geometry and is often used as a basic building block for more complex geometric theorems. The explicit form makes it easier to apply in specific geometric arguments where exactly three points are involved.

### Dependencies
- **Definitions:**
  - `on`: Defines when a point lies on a line: `p on l <=> perpl (dest_point p) l`
  - `COLLINEAR`: Defines collinearity of a set of points: `COLLINEAR s <=> ?l. !p. p IN s ==> p on l`

### Porting notes
When porting this theorem, ensure that:
1. The set notation is properly translated to the target system
2. The membership relation (`IN`) and set construction (`{a,b,c}`) are correctly handled
3. The definition of `COLLINEAR` is consistent with the general definition before attempting to prove this specialized version

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
For any three points $p_1, p_2, p_3$ in the projective plane, the set $\{p_1, p_2, p_3\}$ is collinear if and only if $\text{bracket}[p_1, p_2, p_3] = 0$.

Here, the bracket $\text{bracket}[p_1, p_2, p_3]$ is defined as the determinant of the matrix formed by the homogeneous coordinates of the three points: $\det(\text{vector}[\text{homop } p_1; \text{homop } p_2; \text{homop } p_3])$, where $\text{homop}$ maps a projective point to its homogeneous representation in $\mathbb{R}^3$.

### Informal proof
The proof establishes the equivalence between collinearity of three points in projective geometry and the vanishing of their bracket.

First, we prove a lemma: if vectors $x$ and $y$ are parallel (i.e., $x \times y = 0$), and $x \neq 0$, then any three vectors $a$, $b$, and $c$ that are orthogonal to $x$ are also orthogonal to $y$.

For the main proof:
- **($\Rightarrow$)** If $\{p_1, p_2, p_3\}$ is collinear:
  - By the definition of collinearity, there exists a line $l$ such that all three points lie on it
  - Using the fact that a point lies on a line if and only if its homogeneous coordinates are orthogonal to the homogeneous coordinates of the line ($p \text{ on } l \iff \text{orthogonal}(\text{homop } p, \text{homol } l)$)
  - The determinant of the matrix formed by the homogeneous coordinates of the three points (which is the bracket) equals zero by algebraic manipulation.

- **($\Leftarrow$)** If $\text{bracket}[p_1, p_2, p_3] = 0$:
  - We handle the special case where $p_1 = p_2$ separately, which is trivially collinear
  - For the general case, we show that $\det(\text{vector}[\text{homop } p_1; \text{homop } p_2; \text{homop } p_3]) = 0$ implies that the three homogeneous vectors are linearly dependent
  - We construct a line $l = \text{mk\_line}((||) (\text{mk\_dir}(\text{homop } p_1 \times \text{homop } p_2)))$
  - Using the lemma and properties of cross products, we show that all three points lie on this line, thus proving collinearity.

The proof relies heavily on the duality between projective points and lines, using the fact that the homogeneous coordinates of a line are orthogonal to the homogeneous coordinates of any point on that line.

### Mathematical insight
This theorem establishes a fundamental connection between the algebraic notion of the bracket (a determinant of homogeneous coordinates) and the geometric concept of collinearity in projective geometry. The bracket is essentially calculating whether the three points' homogeneous coordinates are linearly dependent, which is precisely the condition for collinearity in projective space.

This result is particularly important because:
1. It provides a simple algebraic criterion for testing collinearity
2. It connects the synthetic projective geometry with analytic methods
3. It forms a basis for many other results in projective geometry, including cross-ratios and projective transformations

The bracket notation is reminiscent of the classical notation used in projective geometry for determinants that represent geometric conditions, and is closely related to Plücker coordinates in line geometry.

### Dependencies
- **Theorems:**
  - `ORTHOGONAL_CROSS`: Orthogonality relationships between vectors and their cross products
  - `CROSS_TRIPLE`: The triple product identity relating dot and cross products
  - `DOT_CROSS_DET`: Relation between the triple scalar product and determinant
  - `homop`: Properties of the homogeneous coordinates map for points
  - `ON_HOMOL`: Condition for a point to lie on a line using homogeneous coordinates
  - `EQ_HOMOP`: Points are equal iff their homogeneous coordinates are parallel
  - `PARALLEL_PROJL_HOMOL`: Parallelism relation between a vector and its projected line
  - `COLLINEAR_PAIR`: Any two points are collinear
  - `COLLINEAR_TRIPLE`: Characterization of collinearity for three points

- **Definitions:**
  - `cross`: Vector cross product in 3D
  - `parallel`: Two vectors are parallel iff their cross product is zero
  - `projl`: Projection of a vector to a line
  - `bracket`: Determinant of the matrix of homogeneous coordinates
  - `COLLINEAR`: Set of points is collinear iff they all lie on some line

### Porting notes
When porting this theorem:
1. Ensure that the homogeneous coordinate system and projective geometry foundations are properly established
2. The determinant calculation for the bracket should be implemented for 3×3 matrices
3. Take care with the duality between points and lines in projective space, as different systems might represent this differently
4. Be mindful of the distinction between projective points and their homogeneous coordinate representations

---

## BRACKET_SWAP,BRACKET_SHUFFLE

### Name of formal statement
BRACKET_SWAP, BRACKET_SHUFFLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BRACKET_SWAP,BRACKET_SHUFFLE = (CONJ_PAIR o prove)
 (`bracket[x;y;z] = --bracket[x;z;y] /\
   bracket[x;y;z] = bracket[y;z;x] /\
   bracket[x;y;z] = bracket[z;x;y]`,
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING);;
```

### Informal statement
This theorem proves two key properties of the bracket operation:

1. `BRACKET_SWAP`: For any three points $x$, $y$, and $z$, 
   $\text{bracket}[x;y;z] = -\text{bracket}[x;z;y]$

2. `BRACKET_SHUFFLE`: For any three points $x$, $y$, and $z$,
   $\text{bracket}[x;y;z] = \text{bracket}[y;z;x] = \text{bracket}[z;x;y]$

These properties establish that the bracket operation changes sign when two adjacent elements are swapped, and remains invariant under cyclic permutation of its arguments.

### Informal proof
The proof relies on properties of determinants and vectors in 3-dimensional space.

First, we expand the definition of `bracket[x;y;z]` as `det(vector[homop x; homop y; homop z])`, which is the determinant of a matrix whose columns are the homogeneous coordinates of the three points.

By applying the properties of 3×3 determinants (`DET_3`) and the structure of 3-dimensional vectors (`VECTOR_3`), we can see that:

1. Swapping two columns in a determinant changes its sign, which gives us `bracket[x;y;z] = -bracket[x;z;y]`.

2. A cyclic permutation of columns preserves the value of the determinant, yielding `bracket[x;y;z] = bracket[y;z;x] = bracket[z;x;y]`.

The proof is completed using real arithmetic simplification (`REAL_RING`), which handles the algebraic manipulations after the expansions.

### Mathematical insight
This theorem establishes fundamental properties of the bracket operation, which is used in projective geometry. The bracket represents the oriented volume of the parallelepiped formed by three points in projective space.

The alternating property (changing sign when two elements are swapped) identifies the bracket as a determinant-like operation, while the cyclic invariance shows it has a symmetric structure with respect to its arguments.

These properties are crucial for manipulations in projective geometry calculations, allowing for canonical ordering of points in bracket expressions and simplifying geometric proofs. They follow directly from the properties of determinants, connecting projective geometry with linear algebra.

### Dependencies
#### Theorems
- `DET_3`: Properties of 3×3 determinants
- `VECTOR_3`: Structure of 3-dimensional vectors

#### Definitions
- `bracket`: Defined as `bracket[a;b;c] = det(vector[homop a;homop b;homop c])`, represents a determinant of homogeneous coordinates

### Porting notes
When porting this theorem:
1. Ensure that the target system has appropriate definitions for determinants and vector operations
2. The proof relies heavily on determinant properties, so these need to be available in the target system
3. The algebraic simplification (`REAL_RING`) might need to be replaced with an equivalent tactic in the target system

---

## BRACKET_SWAP_CONV

### BRACKET_SWAP_CONV

### Type of the formal statement
- new_definition (of a conversion function)

### Formal Content
```ocaml
let BRACKET_SWAP_CONV =
  let conv = GEN_REWRITE_CONV I [BRACKET_SWAP] in
  fun tm -> let th = conv tm in
            let tm' = rand(rand(concl th)) in
            if term_order tm tm' then th else failwith "BRACKET_SWAP_CONV";;
```

### Informal statement
This defines a conversion function `BRACKET_SWAP_CONV` that applies bracket swapping to a given term. It works as follows:

1. The function takes a term `tm` as input
2. It applies a general rewrite conversion using the theorem `BRACKET_SWAP` to the term
3. The conversion extracts the right-hand side of the resulting equality (using `rand(rand(concl th))`)
4. It then performs a term ordering check using `term_order` to determine if the original term `tm` is lexicographically before the new term `tm'`
5. If `tm` comes before `tm'` in the term ordering, it returns the theorem; otherwise, it fails with an error message "BRACKET_SWAP_CONV"

This ensures the conversion only applies bracket swapping in a direction that follows the term ordering.

### Informal proof
This is a definition rather than a theorem, so there is no proof to translate.

### Mathematical insight
`BRACKET_SWAP_CONV` is a directed version of the bracket swapping conversion that enforces a particular term ordering direction. It's designed to prevent infinite loops that might occur when rewriting systems apply bracket swapping repeatedly in both directions.

The key insight is in the use of `term_order`, which ensures that the conversion only succeeds when the transformation moves from a "smaller" to a "larger" term according to some lexicographic ordering. This makes the conversion suitable for use in automated simplification strategies where termination is important.

The transformation is based on the associativity of operations, where `(a op b) op c` and `a op (b op c)` are mathematically equivalent, but might have different representations in the theorem prover.

### Dependencies
- **Theorems:**
  - `BRACKET_SWAP`: Likely an associativity theorem that states something like `(a op b) op c = a op (b op c)`

- **Functions and Conversions:**
  - `GEN_REWRITE_CONV`: A general rewriting conversion
  - `term_order`: A function implementing a lexicographic ordering on terms
  - `rand`: Function to extract the right-hand part of an application
  - `concl`: Function to extract the conclusion of a theorem

### Porting notes
When porting this to another system:
1. Ensure the target system has an equivalent of `term_order` or create such a function to enforce directionality
2. The error handling using `failwith` should be adapted to the target system's error mechanism
3. The theorem `BRACKET_SWAP` needs to be available in the target system
4. Term manipulation functions like `rand` and `concl` need appropriate equivalents

In systems with more sophisticated rewrite engines, this might be implemented using rewrite rules with explicit directionality controls rather than post-checking term ordering.

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
The theorem proves Desargues' theorem directly. Given points $A, A', B, B', C, C', P, Q, R, S$ satisfying specific non-collinearity conditions and arrangement conditions, if:

1. $P, A', A$ are collinear
2. $P, B, B'$ are collinear
3. $P, C', C$ are collinear
4. $B, C, Q$ are collinear
5. $B', C', Q$ are collinear
6. $A, R, C$ are collinear
7. $A', C', R$ are collinear
8. $B, S, A$ are collinear
9. $A', S, B'$ are collinear

Then points $Q, S, R$ are collinear.

The non-collinearity conditions, numerous in the hypothesis, ensure the geometric configuration is non-degenerate.

### Informal proof
The proof follows a direct approach using bracket algebra, where $\text{bracket}[p_1; p_2; p_3] = \det(\text{vector}[\text{homop}(p_1), \text{homop}(p_2), \text{homop}(p_3)])$ represents the determinant of the homogeneous coordinates of the three points. Points are collinear if and only if their bracket equals zero.

* First, we rewrite all collinearity conditions using the `COLLINEAR_BRACKET` theorem, which states that $\text{COLLINEAR}\{p_1,p_2,p_3\} \iff \text{bracket}[p_1;p_2;p_3] = 0$.

* Next, we establish a key algebraic result: for each assumed collinearity in the hypothesis, there is a corresponding algebraic identity relating various brackets. For example:
  - If $\text{bracket}[P;A';A] = 0$, then $\text{bracket}[P;A';R] \cdot \text{bracket}[P;A;C] = \text{bracket}[P;A';C] \cdot \text{bracket}[P;A;R]$
  - Eight other similar identities are established, one for each assumed collinearity

* Using these identities and bracket algebra properties (such as $\text{BRACKET_SHUFFLE}$ and $\text{BRACKET_SWAP_CONV}$), the proof reduces the problem to showing that:
  $\text{bracket}[B;Q;S] \cdot \text{bracket}[A';R;S] = \text{bracket}[B;R;S] \cdot \text{bracket}[A';Q;S]$

* This equation is proven to imply that $\text{bracket}[Q;S;R] = 0$, which is equivalent to showing that $Q$, $S$, and $R$ are collinear.

* The algebraic manipulations rely heavily on properties of determinants and the bracket algebra, as well as real algebraic simplifications.

### Mathematical insight
This theorem provides a direct proof of Desargues' theorem using bracket algebra, which is a powerful tool in projective geometry. Desargues' theorem is a fundamental result in projective geometry that relates the perspective relationship between triangles.

In the projective plane, the theorem states that if two triangles are in perspective from a point (i.e., lines joining corresponding vertices are concurrent), then the three points of intersection of corresponding sides are collinear. This direct proof approach demonstrates how algebraic methods can be used to establish geometric results without relying on geometric intuition.

The proof follows Richter-Gebert's approach in "Meditations on Ceva's Theorem," applying bracket algebra to reduce a geometric problem to an algebraic one. It shows how multilinear algebra can capture the essence of projective geometric relationships.

### Dependencies
- **Theorems**:
  - `COLLINEAR_BRACKET`: Establishes the equivalence between collinearity and the bracket being zero
  - `BRACKET_SHUFFLE`: Properties of the bracket function
  - `BRACKET_SWAP_CONV`: Conversion for swapping elements in bracket expressions

- **Definitions**:
  - `bracket`: Defines the bracket as the determinant of the homogeneous coordinates
  - `COLLINEAR`: Defines collinearity as points lying on the same line

### Porting notes
When porting to another proof assistant:
- The bracket algebra would need to be implemented, along with its properties and conversions.
- The proof heavily relies on algebraic manipulations and real arithmetic, so a system with strong automation for these tasks would be beneficial.
- The numerous non-collinearity conditions are essential for ensuring the geometric configuration is well-defined; these represent degenerate cases that would need careful treatment.

---

