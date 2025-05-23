# pascal.ml

## Overview

Number of statements: 64

The `pascal.ml` file formalizes Pascal's hexagon theorem for projective and affine planes. It builds upon concepts from the `Multivariate/cross.ml` module, suggesting a focus on geometric or algebraic aspects. The file's purpose is to define and prove the theorem, potentially establishing key properties or constructions related to these geometric structures. Its scope is likely limited to the specific theorem and its immediate consequences, contributing to a broader library of formalized mathematical results.

## NORMAL_EXISTS

### Name of formal statement
NORMAL_EXISTS

### Type of the formal statement
Theorem

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
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC)
```

### Informal statement
For all vectors `u` and `v` in 3-dimensional real space, there exists a non-zero vector `w` such that `w` is orthogonal to both `u` and `v`.

### Informal sketch
* The proof starts by assuming two arbitrary vectors `u` and `v` in 3-dimensional real space.
* It then applies the `ORTHOGONAL_TO_SUBSPACE_EXISTS` theorem to find a vector `w` orthogonal to the subspace spanned by `u` and `v`.
* The `ORTHOGONAL_SYM` property is used to establish symmetry in orthogonality.
* The existence of `w` is then justified by considering the cardinality of the set containing `u` and `v`, and using properties of finite sets and dimensions.
* The proof involves a series of simplifications and transformations using `REWRITE_TAC`, `SIMP_TAC`, and `ARITH_TAC` to establish the final result.

### Mathematical insight
This theorem is important because it guarantees the existence of a normal vector to any two given vectors in 3-dimensional space, which is a fundamental concept in geometry and linear algebra. It has implications for various geometric constructions and proofs, especially those involving orthogonality and subspaces.

### Dependencies
* Theorems:
  * `ORTHOGONAL_TO_SUBSPACE_EXISTS`
  * `ORTHOGONAL_SYM`
* Definitions:
  * `orthogonal`
  * `vec`
* Other:
  * `DIMINDEX_3`
  * `FORALL_IN_INSERT`
  * `NOT_IN_EMPTY`
  * `DIM_LE_CARD`
  * `FINITE_INSERT`
  * `FINITE_EMPTY`
  * `CARD_CLAUSES`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to the handling of vector spaces, orthogonality, and the `ORTHOGONAL_TO_SUBSPACE_EXISTS` theorem, as these may be represented differently in other systems. Additionally, the use of `REPEAT`, `GEN_TAC`, and `MATCH_MP_TAC` tactics may need to be adapted to the target system's tactic language.

---

## direction_tybij

### Name of formal statement
direction_tybij

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let direction_tybij = new_type_definition "direction" ("mk_dir","dest_dir") (MESON[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] `?x:real^3. ~(x = vec 0)`);;
```

### Informal statement
The `direction_tybij` is a new type definition for a "direction" type, constructed using the `new_type_definition` mechanism. It introduces two new constants, `mk_dir` and `dest_dir`, and is defined using the `MESON` tactic, which proves the existence of a type based on certain properties. Specifically, it asserts the existence of a real-valued vector `x` in 3-dimensional space such that `x` is not equal to the zero vector.

### Informal sketch
* The definition begins by invoking the `new_type_definition` mechanism, specifying the name "direction" and the constructors `mk_dir` and `dest_dir`.
* The `MESON` tactic is used to prove the existence of this new type, relying on the following lemmas:
  + `BASIS_NONZERO`
  + `LE_REFL`
  + `DIMINDEX_GE_1`
* The goal of the proof is to show that there exists a non-zero vector `x` in 3-dimensional real space, which is formalized as `?x:real^3. ~(x = vec 0)`.
* The proof strategy involves using the `MESON` tactic to combine the given lemmas and establish the existence of the "direction" type.

### Mathematical insight
The `direction_tybij` definition provides a way to represent directions in 3-dimensional space, which is a fundamental concept in geometry and physics. By defining a new type for directions, this formal item enables the development of geometric and physical theories that rely on directional information. The use of the `MESON` tactic and the specific lemmas employed in the proof reflect the mathematical structure of the underlying theory.

### Dependencies
* `BASIS_NONZERO`
* `LE_REFL`
* `DIMINDEX_GE_1`
* `MESON`
* `new_type_definition`
* `mk_dir` and `dest_dir` (as part of the `direction_tybij` definition)

### Porting notes
When porting this definition to another proof assistant, special attention should be paid to the `MESON` tactic and the `new_type_definition` mechanism, as these may have different counterparts in the target system. Additionally, the lemmas `BASIS_NONZERO`, `LE_REFL`, and `DIMINDEX_GE_1` will need to be ported or re-proven in the target system. The `mk_dir` and `dest_dir` constructors may also require special handling, depending on the target system's type definition mechanisms.

---

## perpdir

### Name of formal statement
perpdir

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let perpdir = new_definition `x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)`;;
```

### Informal statement
Two objects `x` and `y` are perpendicular (`x _|_ y`) if and only if the destination directions of `x` and `y` are orthogonal.

### Informal sketch
* The definition `perpdir` introduces a new notion of perpendicularity (`_ _|_`) between two objects `x` and `y`.
* This relation is defined in terms of the `orthogonal` relation between the destination directions (`dest_dir`) of `x` and `y`.
* To prove that two objects are perpendicular, one would need to show that their destination directions are orthogonal.

### Mathematical insight
The `perpdir` definition provides a way to express the geometric concept of perpendicularity in terms of the `orthogonal` relation between direction vectors. This definition is likely used in geometric or spatial reasoning contexts, where establishing perpendicularity relationships between objects is crucial.

### Dependencies
* `orthogonal`
* `dest_dir`

### Porting notes
When translating this definition into another proof assistant, ensure that the `orthogonal` relation and `dest_dir` function are defined and available. Additionally, consider the specific syntax and semantics of the target system's relation and function definitions, as they may differ from HOL Light's `new_definition` syntax.

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
The `pardir` relation between two objects `x` and `y` holds if and only if the cross product of the destination directions of `x` and `y` equals the zero vector.

### Informal sketch
* The definition of `pardir` involves the `dest_dir` function, which presumably extracts the direction from an object.
* The `cross` function computes the cross product of two vectors.
* The `vec 0` represents the zero vector, indicating that the cross product of the two directions is zero, implying the directions are parallel.
* The `||` symbol denotes the `pardir` relation, which is defined using the equivalence `<=>`.

### Mathematical insight
The `pardir` relation captures the concept of parallelism between two objects based on their directions. This definition is likely used in a geometric or spatial reasoning context, where determining parallelism is essential. The use of the cross product to define parallelism is a common technique in linear algebra and geometry.

### Dependencies
* `dest_dir`
* `cross`
* `vec 0`

### Porting notes
When translating this definition to other proof assistants, pay attention to the handling of vector operations and the representation of the zero vector. In some systems, the zero vector might be represented differently, or the cross product might be defined with different notation or properties. Additionally, the `dest_dir` function and its properties will need to be ported or defined appropriately in the target system.

---

## DIRECTION_CLAUSES

### Name of formal statement
DIRECTION_CLAUSES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRECTION_CLAUSES = prove
 (`((!x. P(dest_dir x)) <=> (!x. ~(x = vec 0) ==> P x)) /\
   ((?x. P(dest_dir x)) <=> (?x. ~(x = vec 0) /\ P x))`,
  MESON_TAC[direction_tybij])
```

### Informal statement
The theorem `DIRECTION_CLAUSES` states that for any predicate `P`, the following two statements are equivalent: 
1. For all `x`, `P` holds for the destination direction of `x`.
2. For all `x` not equal to the zero vector, `P` holds for `x`. 
Additionally, it states that the following two statements are equivalent: 
1. There exists an `x` such that `P` holds for the destination direction of `x`.
2. There exists an `x` not equal to the zero vector such that `P` holds for `x`.

### Informal sketch
* The proof involves establishing two equivalences using the `MESON_TAC` tactic, which applies a set of meson rules to prove the goal.
* The first equivalence is between a universal quantification over the destination direction of `x` and a universal quantification over `x` with the condition that `x` is not the zero vector.
* The second equivalence is between an existential quantification over the destination direction of `x` and an existential quantification over `x` with the condition that `x` is not the zero vector.
* The `direction_tybij` term is used in the tactic, indicating that it plays a crucial role in establishing these equivalences, likely due to its properties related to direction and bijection.

### Mathematical insight
This theorem provides a way to transform statements about predicates applied to destination directions into equivalent statements about predicates applied to vectors, under the condition that the vectors are not zero. This is useful in geometric and vector-based proofs where the direction of a vector is of interest, but the magnitude (or the vector itself) needs to be considered under certain conditions.

### Dependencies
* `direction_tybij`
 
### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to how each system handles quantifiers, especially in the context of non-zero vectors. The `MESON_TAC` tactic may not have a direct equivalent, so the proof might need to be reconstructed using the native tactics of the target system, potentially involving manual application of meson rules or leveraging the system's built-in automation features.

---

## [PARDIR_REFL;

### Name of formal statement
PARDIR_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let [PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS] = (CONJUNCTS o prove)
 (`(!x. x || x) /\
   (!x y. x || y <=> y || x) /\
   (!x y z. x || y /\ y || z ==> x || z)`,
  REWRITE_TAC[pardir; DIRECTION_CLAUSES] THEN VEC3_TAC)
```

### Informal statement
For all `x`, `x` is parallel to `x`. For all `x` and `y`, `x` is parallel to `y` if and only if `y` is parallel to `x`. For all `x`, `y`, and `z`, if `x` is parallel to `y` and `y` is parallel to `z`, then `x` is parallel to `z`.

### Informal sketch
* The proof involves establishing three properties of the parallel relation `||`:
 + Reflexivity: `x || x` for all `x`
 + Symmetry: `x || y` if and only if `y || x` for all `x` and `y`
 + Transitivity: if `x || y` and `y || z`, then `x || z` for all `x`, `y`, and `z`
* The `REWRITE_TAC` tactic is used with `pardir` and `DIRECTION_CLAUSES` to simplify the statements
* The `VEC3_TAC` tactic is then applied to prove the resulting statements

### Mathematical insight
This statement defines the basic properties of the parallel relation `||`, which is a fundamental concept in geometry. The reflexive, symmetric, and transitive properties ensure that the parallel relation is well-behaved and can be used to reason about geometric objects.

### Dependencies
* `pardir`
* `DIRECTION_CLAUSES`

### Porting notes
When translating this item into other proof assistants, note that the `REWRITE_TAC` and `VEC3_TAC` tactics may not have direct equivalents. Instead, use the corresponding tactics or methods for rewriting and proving statements in the target system. Additionally, ensure that the `pardir` and `DIRECTION_CLAUSES` definitions are properly ported and available in the target system.

---

## PARDIR_EQUIV

### Name of formal statement
PARDIR_EQUIV

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PARDIR_EQUIV = prove
 (`!x y. ((||) x = (||) y) <=> x || y`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS])
```

### Informal statement
For all `x` and `y`, the equality of the parallelity relations `||` applied to `x` and `y` holds if and only if `x` is parallel to `y`.

### Informal sketch
* The proof starts with the statement `!x y. ((||) x = (||) y) <=> x || y`, which is to be proven.
* The `REWRITE_TAC` with `FUN_EQ_THM` is applied, which likely rewrites the equality of functions in terms of their arguments.
* Then, `MESON_TAC` is applied with `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` as premises, which suggests using these properties of parallelity to derive the conclusion.
* The properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` likely correspond to reflexivity, symmetry, and transitivity of the parallelity relation, respectively.

### Mathematical insight
This theorem provides a fundamental property of the parallelity relation `||`, linking the equality of the relations applied to two elements with the fact that these elements are parallel to each other. This kind of statement is crucial in geometric and spatial reasoning, ensuring that the notion of parallelity behaves as expected under equality.

### Dependencies
* Theorems:
  - `PARDIR_REFL`
  - `PARDIR_SYM`
  - `PARDIR_TRANS`
  - `FUN_EQ_THM`
* Definitions:
  - `||` (parallelity relation)

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to how the system handles function equality (`FUN_EQ_THM`) and how it supports the `MESON_TAC` style of proof, which might be represented differently. Additionally, the properties of the parallelity relation (`PARDIR_REFL`, `PARDIR_SYM`, `PARDIR_TRANS`) need to be defined or imported appropriately in the target system.

---

## DIRECTION_AXIOM_1

### Name of formal statement
DIRECTION_AXIOM_1

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let DIRECTION_AXIOM_1 = prove
 (`!p p'. ~(p || p') ==> ?l. p _|_ l /\ p' _|_ l /\
                             !l'. p _|_ l' /\ p' _|_ l' ==> l' || l`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real^3`; `p':real^3`] NORMAL_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC)
```

### Informal statement
For all `p` and `p'`, if `p` and `p'` are not parallel, then there exists a line `l` such that `p` is perpendicular to `l` and `p'` is perpendicular to `l`, and for all lines `l'` such that `p` is perpendicular to `l'` and `p'` is perpendicular to `l'`, `l'` is parallel to `l`.

### Informal sketch
* The proof starts by assuming that `p` and `p'` are not parallel.
* It then applies `REWRITE_TAC` with `perpdir`, `pardir`, and `DIRECTION_CLAUSES` to simplify the expression.
* The `REPEAT STRIP_TAC` tactic is used to strip away the quantifiers.
* The `MP_TAC` tactic is applied with `NORMAL_EXISTS` to introduce the existence of a line `l`.
* The `MATCH_MP_TAC` tactic with `MONO_EXISTS` is used to apply the monotonicity of existence.
* The `POP_ASSUM_LIST` tactic is used to handle the assumptions, and `VEC3_TAC` is applied to reason about vectors in 3D space.
* The key idea is to use the properties of perpendicularity and parallelism to find a line `l` that satisfies the conditions.

### Mathematical insight
This axiom is important because it establishes a fundamental property of directions in 3D space. It states that if two directions are not parallel, then there exists a line that is perpendicular to both, and any other line that is perpendicular to both must be parallel to this line. This axiom is a foundation for further reasoning about directions and lines in 3D geometry.

### Dependencies
* `perpdir`
* `pardir`
* `DIRECTION_CLAUSES`
* `NORMAL_EXISTS`
* `MONO_EXISTS`

### Porting notes
When porting this axiom to another proof assistant, note that the handling of quantifiers and the `REPEAT` tactic may differ. Additionally, the `VEC3_TAC` tactic may need to be replaced with a similar tactic that handles vector reasoning in 3D space. The `MATCH_MP_TAC` and `POP_ASSUM_LIST` tactics may also require special attention due to differences in how assumptions are handled.

---

## DIRECTION_AXIOM_2

### Name of formal statement
DIRECTION_AXIOM_2

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let DIRECTION_AXIOM_2 = prove
 (`!l l'. ?p. p _|_ l /\ p _|_ l'`,
  REWRITE_TAC[perpdir; DIRECTION_CLAUSES] THEN
  MESON_TAC[NORMAL_EXISTS; ORTHOGONAL_SYM]);;
```

### Informal statement
For all lines `l` and `l'`, there exists a point `p` such that `p` is orthogonal to `l` and `p` is orthogonal to `l'`.

### Informal sketch
* The proof involves finding a point `p` that satisfies the condition of being orthogonal to two given lines `l` and `l'`.
* The `REWRITE_TAC` tactic is used with `perpdir` and `DIRECTION_CLAUSES` to rewrite the goal in terms of orthogonal directions.
* The `MESON_TAC` tactic is then applied with `NORMAL_EXISTS` and `ORTHOGONAL_SYM` to deduce the existence of point `p` and establish the orthogonality conditions.

### Mathematical insight
This axiom is crucial in establishing the relationship between points and lines in a geometric context, particularly in proving the existence of points orthogonal to given lines. It underlies various geometric constructions and theorems.

### Dependencies
* `perpdir`
* `DIRECTION_CLAUSES`
* `NORMAL_EXISTS`
* `ORTHOGONAL_SYM`

### Porting notes
When translating this axiom into other proof assistants like Lean, Coq, or Isabelle, special attention should be given to how these systems handle existential quantification and orthogonality. The `REWRITE_TAC` and `MESON_TAC` tactics may have direct counterparts or require manual rewriting and application of rules in the target system. Additionally, the handling of `perpdir` and `DIRECTION_CLAUSES` may vary, requiring adjustments to match the target system's geometric primitives and theorems.

---

## DIRECTION_AXIOM_3

### Name of formal statement
DIRECTION_AXIOM_3

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let DIRECTION_AXIOM_3 = prove
 (`?p p' p''.
        ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
        ~(?l. p _|_ l /\ p' _|_ l /\ p'' _|_ l)`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN MAP_EVERY
   (fun t -> EXISTS_TAC t THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH])
   [`basis 1 :real^3`; `basis 2 : real^3`; `basis 3 :real^3`] THEN
  VEC3_TAC)
```

### Informal statement
For all `p`, `p'`, and `p''`, if `p` is not parallel to `p'`, `p'` is not parallel to `p''`, and `p` is not parallel to `p''`, and there does not exist a line `l` such that `p` is perpendicular to `l`, `p'` is perpendicular to `l`, and `p''` is perpendicular to `l`, then a certain geometric condition is satisfied.

### Informal sketch
* The proof starts by assuming the existence of three non-parallel `p`, `p'`, and `p''` that do not all intersect with a common line `l`.
* It then applies `REWRITE_TAC` with `perpdir`, `pardir`, and `DIRECTION_CLAUSES` to transform the goal.
* The `MAP_EVERY` tactic is used to instantiate the existential quantifier for each basis vector (`basis 1 :real^3`, `basis 2 :real^3`, `basis 3 :real^3`) and simplify the resulting expressions using `SIMP_TAC` with `BASIS_NONZERO`, `DIMINDEX_3`, and `ARITH`.
* Finally, `VEC3_TAC` is applied to complete the proof.

### Mathematical insight
This axiom formalizes a geometric condition in 3D space, ensuring that certain lines are not all parallel and do not all intersect with a common line. The proof involves transforming the goal using rewrite rules and then using basis vectors to satisfy the existential quantifier.

### Dependencies
* Theorems:
 + `perpdir`
 + `pardir`
 + `DIRECTION_CLAUSES`
 + `BASIS_NONZERO`
 + `DIMINDEX_3`
 + `ARITH`
* Definitions:
 + `basis`
* Inductive rules: None

### Porting notes
When porting this axiom to another proof assistant, special attention should be paid to the handling of `REWRITE_TAC` and `MAP_EVERY` tactics, as well as the use of `SIMP_TAC` with specific theorems. The `VEC3_TAC` tactic may need to be replaced with a similar tactic or a custom proof step in the target system. Additionally, the basis vectors and their properties may need to be defined or imported from a relevant library in the target system.

---

## DIRECTION_AXIOM_4_WEAK

### Name of formal statement
DIRECTION_AXIOM_4_WEAK

### Type of the formal statement
new_axiom

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
  MP_TAC THENL [POP_ASSUM MP_TAC THEN VEC3_TAC; MESON_TAC[CROSS_0]])
```

### Informal statement
For all lines `l`, there exist planes `p` and `p'` such that `p` and `p'` are not parallel, `p` is orthogonal to `l`, and `p'` is orthogonal to `l`.

### Informal sketch
* The proof starts by assuming the existence of a line `l`.
* It then applies the `REWRITE_TAC` tactic with `DIRECTION_CLAUSES`, `pardir`, and `perpdir` to transform the goal.
* The `REPEAT STRIP_TAC` tactic is used to simplify the goal by stripping away any universal quantifiers.
* The `SUBGOAL_THEN` tactic is applied to introduce a subgoal that involves the `orthogonal` relation and the cross product of vectors.
* The proof then proceeds by cases, using the `MP_TAC` tactic to apply modus ponens and the `VEC3_TAC` tactic to reason about vectors in 3D space.
* The `MESON_TAC` tactic is used with the `CROSS_0` theorem to establish the final result.

### Mathematical insight
This axiom provides a fundamental property of lines and planes in 3D space, specifically regarding orthogonality and the existence of non-parallel planes. It is a key component in establishing the foundations of geometry within the proof assistant.

### Dependencies
* Theorems:
	+ `DIRECTION_CLAUSES`
	+ `CROSS_0`
* Definitions:
	+ `pardir`
	+ `perpdir`
	+ `orthogonal`
	+ `cross`
	+ `basis`

### Porting notes
When translating this axiom into other proof assistants, care should be taken to ensure that the `orthogonal` relation and the `cross` product are defined and handled correctly. Additionally, the use of `SUBGOAL_THEN` and `MP_TAC` tactics may need to be adapted to the target system's tactic language.

---

## ORTHOGONAL_COMBINE

### Name of formal statement
ORTHOGONAL_COMBINE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ORTHOGONAL_COMBINE = prove
 (`!x a b. a _|_ x /\ b _|_ x /\ ~(a || b)
           ==> ?c. c _|_ x /\ ~(a || c) /\ ~(b || c)`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `a + b:real^3` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC)
```

### Informal statement
For all vectors `x`, `a`, and `b`, if `a` is orthogonal to `x` and `b` is orthogonal to `x` and `a` is not parallel to `b`, then there exists a vector `c` such that `c` is orthogonal to `x` and `a` is not parallel to `c` and `b` is not parallel to `c`.

### Informal sketch
* The proof starts by assuming the premises: `a` is orthogonal to `x`, `b` is orthogonal to `x`, and `a` is not parallel to `b`.
* It then applies `REWRITE_TAC` with `DIRECTION_CLAUSES`, `pardir`, and `perpdir` to rewrite the assumptions.
* The `REPEAT STRIP_TAC` tactic is used to strip away the universal quantifiers and implications.
* The existence of a vector `c` is asserted using `EXISTS_TAC`, where `c` is defined as the sum of `a` and `b`.
* The `POP_ASSUM_LIST` and `MP_TAC` tactics are used to apply the assumptions to the conclusion.
* Finally, `VEC3_TAC` is applied to reason about the vector properties.

### Mathematical insight
This theorem provides a way to construct a new vector `c` that is orthogonal to a given vector `x`, given two other vectors `a` and `b` that are also orthogonal to `x` but not parallel to each other. This construction is useful in geometric and linear algebraic contexts where orthogonal vectors are necessary.

### Dependencies
* `DIRECTION_CLAUSES`
* `pardir`
* `perpdir`

### Porting notes
When porting this theorem to other proof assistants, note that the `REWRITE_TAC` and `EXISTS_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `VEC3_TAC` tactic may require a different approach to reason about vector properties, depending on the specific vector library or theory used in the target system.

---

## DIRECTION_AXIOM_4

### Name of formal statement
DIRECTION_AXIOM_4

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let DIRECTION_AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
                  p _|_ l /\ p' _|_ l /\ p'' _|_ l`,
  MESON_TAC[DIRECTION_AXIOM_4_WEAK; ORTHOGONAL_COMBINE])
```

### Informal statement
For all lines `l`, there exist points `p`, `p'`, and `p''` such that `p` is not equal to `p'`, `p'` is not equal to `p''`, and `p` is not equal to `p''`, and `p` is orthogonal to `l`, and `p'` is orthogonal to `l`, and `p''` is orthogonal to `l`.

### Informal sketch
* The proof involves finding points `p`, `p'`, and `p''` that satisfy certain conditions with respect to a given line `l`.
* The conditions include that `p`, `p'`, and `p''` are distinct from each other and each is orthogonal to `l`.
* The `MESON_TAC` tactic is used, which suggests a goal-directed proof search, potentially leveraging `DIRECTION_AXIOM_4_WEAK` and `ORTHOGONAL_COMBINE` to establish the existence of such points.
* The proof may involve constructing or assuming the existence of these points and then showing they meet the required properties.

### Mathematical insight
This axiom provides a fundamental property about the relationship between points and lines, specifically concerning orthogonality. It ensures that for any line, there are at least three distinct points, each of which is orthogonal to the line. This is crucial for establishing various geometric and spatial reasoning principles in the formal system.

### Dependencies
* `DIRECTION_AXIOM_4_WEAK`
* `ORTHOGONAL_COMBINE`

### Porting notes
When translating this axiom into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles existential quantification and orthogonality. The `MESON_TAC` tactic may not have a direct counterpart, so understanding its role in the proof and finding an equivalent tactic or strategy in the target system will be essential. Additionally, consider how the target system represents geometric objects and relations, as this may affect how the axiom and its proof are formulated.

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
The `line_tybij` is defined as a quotient type named "line" with constructors `mk_line` and `dest_line`, and it is based on the proposition `(||)`, which is always true.

### Informal sketch
* The definition introduces a new type `line` using the `define_quotient_type` function.
* This function takes three arguments: the name of the type, a pair of constructor and destructor functions (`mk_line` and `dest_line`), and a proposition that defines the equivalence relation for the quotient type.
* In this case, the proposition `(||)` is a tautology, implying that all elements of the underlying type are equivalent, and thus, the quotient type `line` will have a single equivalence class.

### Mathematical insight
The `line_tybij` definition provides a way to create a new type `line` that can be used to represent lines in a geometric or algebraic context. The use of a quotient type allows for the definition of lines as equivalence classes of points or other geometric objects, enabling the capture of geometric properties and relationships in a formal and abstract manner.

### Dependencies
* `define_quotient_type`
* `mk_line`
* `dest_line`

### Porting notes
When translating this definition to another proof assistant, care should be taken to ensure that the equivalent of `define_quotient_type` is used correctly, as the specifics of quotient types and their constructors may vary between systems. Additionally, the representation of the proposition `(||)` and its implications for the equivalence relation should be carefully considered to ensure that the resulting type `line` behaves as intended in the target system.

---

## PERPDIR_WELLDEF

### Name of formal statement
PERPDIR_WELLDEF

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PERPDIR_WELLDEF = prove
 (`!x y x' y'. x || x' /\ y || y' ==> (x _|_ y <=> x' _|_ y')`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN VEC3_TAC)
```

### Informal statement
For all vectors `x`, `y`, `x'`, and `y'`, if `x` is parallel to `x'` and `y` is parallel to `y'`, then `x` is perpendicular to `y` if and only if `x'` is perpendicular to `y'`.

### Informal sketch
* The proof involves assuming `x || x'` and `y || y'`, which implies that `x` and `x'` have the same direction, and `y` and `y'` have the same direction.
* Using the `REWRITE_TAC` with `perpdir`, `pardir`, and `DIRECTION_CLAUSES` theorems, we can rewrite the perpendicularity condition in terms of vector operations.
* The `VEC3_TAC` tactic is then applied to simplify the resulting expression and derive the desired equivalence.

### Mathematical insight
This theorem establishes a fundamental property of perpendicularity in the context of vector geometry. It shows that the perpendicularity relation between two vectors is preserved under parallel transformations, which is a crucial insight in various geometric and physical applications.

### Dependencies
* `perpdir`
* `pardir`
* `DIRECTION_CLAUSES`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of vector operations and the `REWRITE_TAC` and `VEC3_TAC` tactics. The `REWRITE_TAC` tactic may need to be replaced with equivalent rewriting mechanisms in the target system, and the `VEC3_TAC` tactic may require manual expansion or substitution of vector operations to achieve the same simplification.

---

## perpl,perpl_th

### Name of formal statement
perpl, perpl_th

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;
```

### Informal statement
The `perpl` function is defined by lifting a function of type `line_tybij` (specifically, its second component) using the properties `PARDIR_REFL` and `PARDIR_TRANS`, and it is well-defined according to `PERPDIR_WELLDEF`.

### Informal sketch
* The definition involves `lift_function`, which suggests a process of transforming or extending a given function.
* The `line_tybij` type and its second component (`snd line_tybij`) are crucial, indicating a bijection or an isomorphism related to lines.
* Properties `PARDIR_REFL` and `PARDIR_TRANS` imply reflexivity and transitivity of a relation, possibly related to parallel directions.
* The term `PERPDIR_WELLDEF` indicates that the definition of `perpl` relies on a well-defined concept of perpendicular directions.

### Mathematical insight
This definition appears to be part of a geometric or spatial reasoning framework, where `perpl` likely denotes a relation or property concerning perpendicularity. The use of `lift_function` and the specific properties suggests a structured approach to defining geometric concepts in a rigorous and generalizable manner.

### Dependencies
- Definitions: `line_tybij`, `PARDIR_REFL`, `PARDIR_TRANS`, `PERPDIR_WELLDEF`
- Theorems: possibly those related to the well-definedness of `PERPDIR_WELLDEF` and properties of `line_tybij`

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles function lifting and the representation of geometric concepts. Specifically, consider how to express the `lift_function` operation and ensure that the properties `PARDIR_REFL` and `PARDIR_TRANS` are appropriately defined and applied. Additionally, verify that the concept of `PERPDIR_WELLDEF` is correctly interpreted and utilized in the target system.

---

## line_lift_thm

### Name of formal statement
line_lift_thm

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let line_lift_thm = lift_theorem line_tybij (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th]
```

### Informal statement
The theorem `line_lift_thm` is derived by applying the `lift_theorem` function to `line_tybij` with the properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS`, and using the theorem `perpl_th` as a premise.

### Informal sketch
* The proof involves lifting a theorem (`line_tybij`) to a higher level of abstraction using `lift_theorem`.
* The properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` are used to guide the lifting process, ensuring that the resulting theorem (`line_lift_thm`) preserves the relevant properties.
* The `perpl_th` theorem is used as a premise to support the lifting process, providing necessary assumptions or constraints.
* The `lift_theorem` function is applied to `line_tybij` with the specified properties and premise to yield the `line_lift_thm` theorem.

### Mathematical insight
The `line_lift_thm` theorem is likely used to establish a fundamental property or relationship in a geometric or spatial context, given the involvement of `line_tybij` and properties related to parallel directions (`PARDIR_REFL`, `PARDIR_SYM`, `PARDIR_TRANS`). The use of `lift_theorem` suggests a desire to generalize or abstract the underlying mathematical structure, making it applicable to a broader range of situations or contexts.

### Dependencies
* Theorems: `perpl_th`
* Definitions or properties: `line_tybij`, `PARDIR_REFL`, `PARDIR_SYM`, `PARDIR_TRANS`
* Inductive rules or functions: `lift_theorem`

### Porting notes
When translating this theorem to another proof assistant, pay close attention to the `lift_theorem` function and its equivalent in the target system. Ensure that the properties `PARDIR_REFL`, `PARDIR_SYM`, and `PARDIR_TRANS` are properly defined and applied in the new context. Additionally, verify that the `perpl_th` theorem is correctly ported or rederived in the target system to support the lifting process.

---

## LINE_AXIOM_1

### Name of formal statement
LINE_AXIOM_1

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let LINE_AXIOM_1 = line_lift_thm DIRECTION_AXIOM_1;;
```

### Informal statement
The axiom `LINE_AXIOM_1` is defined as the result of applying the `line_lift_thm` function to `DIRECTION_AXIOM_1`.

### Informal sketch
* The `line_lift_thm` function is applied to `DIRECTION_AXIOM_1` to derive `LINE_AXIOM_1`.
* This step involves lifting a theorem related to direction, as defined by `DIRECTION_AXIOM_1`, to a line-related context.
* The `line_lift_thm` function is expected to perform the necessary logical transformations to establish the line axiom based on the direction axiom.

### Mathematical insight
This axiom is likely foundational in establishing properties of lines in a geometric or spatial context, building upon the basic principles defined by `DIRECTION_AXIOM_1`. The use of `line_lift_thm` suggests a structured approach to deriving geometric properties from more fundamental axioms.

### Dependencies
* `line_lift_thm`
* `DIRECTION_AXIOM_1`

### Porting notes
When porting this axiom to another proof assistant, ensure that the equivalent of `line_lift_thm` is defined and applied correctly. The porting process may require careful handling of the logical structure and any geometric or spatial primitives involved. Pay particular attention to how the target system represents and manipulates geometric objects and their properties.

---

## LINE_AXIOM_2

### Name of formal statement
LINE_AXIOM_2

### Type of the formal statement
new_axiom or theorem, derived from another axiom using `line_lift_thm`

### Formal Content
```ocaml
let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
```

### Informal statement
The axiom `LINE_AXIOM_2` is defined as the result of applying the `line_lift_thm` theorem to `DIRECTION_AXIOM_2`, effectively lifting the direction axiom to a line axiom.

### Informal sketch
* The proof or construction involves applying the `line_lift_thm` to `DIRECTION_AXIOM_2`, which implies that the resulting `LINE_AXIOM_2` inherits properties from the original direction axiom.
* The `line_lift_thm` is used to establish a relationship between directions and lines, likely involving geometric or spatial reasoning.
* The main logical stage is the application of `line_lift_thm`, which may involve substitutions, quantifier manipulations, or other logical transformations to derive the new axiom.

### Mathematical insight
The `LINE_AXIOM_2` axiom is important because it extends the foundational properties of directions to lines, providing a basis for further geometric constructions or theorems. This axiom is likely used to establish consistency and coherence in the geometric framework, ensuring that lines behave as expected in relation to directions.

### Dependencies
* Theorems:
  + `line_lift_thm`
* Axioms:
  + `DIRECTION_AXIOM_2`

### Porting notes
When translating `LINE_AXIOM_2` into other proof assistants, pay attention to how directions and lines are represented and related. The `line_lift_thm` may need to be adapted or re-proven in the target system, taking into account differences in type systems, quantifier handling, or geometric primitives. Additionally, ensure that the target system's axiomatization of geometry is compatible with the original `DIRECTION_AXIOM_2` and its lifted version, `LINE_AXIOM_2`.

---

## LINE_AXIOM_3

### Name of formal statement
LINE_AXIOM_3

### Type of the formal statement
new_axiom or theorem, derived from `line_lift_thm`

### Formal Content
```ocaml
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
```

### Informal statement
The formal statement `LINE_AXIOM_3` is defined as the result of applying the `line_lift_thm` to `DIRECTION_AXIOM_3`. This implies that `LINE_AXIOM_3` is a theorem or axiom that has been lifted or transformed from `DIRECTION_AXIOM_3` using the `line_lift_thm` theorem or function.

### Informal sketch
* The proof or construction of `LINE_AXIOM_3` involves applying the `line_lift_thm` to `DIRECTION_AXIOM_3`, which suggests a transformation or lifting of geometric or directional properties.
* The `line_lift_thm` likely encapsulates specific geometric or logical reasoning steps that are applied to `DIRECTION_AXIOM_3` to yield `LINE_AXIOM_3`.
* Key logical stages may involve recognizing the applicability of `line_lift_thm` to `DIRECTION_AXIOM_3`, ensuring the prerequisites for the theorem are met, and then applying the necessary transformations or proofs to derive `LINE_AXIOM_3`.

### Mathematical insight
The `LINE_AXIOM_3` is likely an important geometric axiom or theorem that follows from the application of `line_lift_thm` to `DIRECTION_AXIOM_3`, indicating a structured approach to deriving properties of lines based on directional axioms. This suggests a careful construction of geometric principles, possibly within a broader theory of geometry or spatial reasoning.

### Dependencies
* `line_lift_thm`
* `DIRECTION_AXIOM_3`

### Porting notes
When translating `LINE_AXIOM_3` into another proof assistant, ensure that an equivalent to `line_lift_thm` is available or can be constructed. Pay special attention to how the target system handles geometric transformations and the application of theorems to axioms. The process may require recreating `line_lift_thm` or finding an analogous mechanism for lifting or transforming geometric properties.

---

## LINE_AXIOM_4

### Name of formal statement
LINE_AXIOM_4

### Type of the formal statement
new_axiom or theorem, derived from `line_lift_thm`

### Formal Content
```ocaml
let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4;;
```

### Informal statement
The axiom `LINE_AXIOM_4` is defined as the result of applying the `line_lift_thm` theorem to `DIRECTION_AXIOM_4`. This implies that `LINE_AXIOM_4` holds true based on the principles established by `line_lift_thm` in relation to the direction axiom `DIRECTION_AXIOM_4`.

### Informal sketch
* The proof or construction of `LINE_AXIOM_4` involves applying the `line_lift_thm` to `DIRECTION_AXIOM_4`, which suggests a lifting of properties or relations from one context to another, possibly involving geometric or spatial relationships.
* The `line_lift_thm` theorem itself might involve specific logical stages or tactics, such as assuming certain premises, using existing theorems, or employing proof by contradiction, but these details are not explicitly provided in the given formal content.
* The key idea is to leverage existing knowledge (`DIRECTION_AXIOM_4`) to derive new knowledge (`LINE_AXIOM_4`) through a systematic application of principles (`line_lift_thm`).

### Mathematical insight
The `LINE_AXIOM_4` is significant because it demonstrates how axiomatic systems can be extended or enriched by applying theorems that "lift" properties from one domain to another. This process is fundamental in building comprehensive formal systems, especially in geometry or spatial reasoning, where directions and lines are basic constructs.

### Dependencies
- Theorems: `line_lift_thm`
- Axioms: `DIRECTION_AXIOM_4`

### Porting notes
When translating `LINE_AXIOM_4` into another proof assistant, ensure that an equivalent of `line_lift_thm` is available or can be derived. The main challenge might lie in replicating the exact behavior of `line_lift_thm` in the target system, especially if it involves custom tactics or strategic proof construction. Pay close attention to how binders, quantifiers, and spatial relationships are handled in the target system to ensure a faithful translation of `LINE_AXIOM_4`.

---

## point_tybij

### Name of formal statement
point_tybij

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let point_tybij = new_type_definition "point" ("mk_point","dest_point") (prove(`?x:line. T`,REWRITE_TAC[]))
```

### Informal statement
For some type `line`, there exists an `x` of type `line` such that a proposition `T` holds, which is used to define a new type `point` with constructors `mk_point` and destructors `dest_point`.

### Informal sketch
* The definition of `point_tybij` involves creating a new type `point` based on the existence of an `x` of type `line` for which a certain proposition `T` is true.
* The `prove` function is used with `REWRITE_TAC` to establish this proposition, which is a crucial step in defining the `point` type.
* The `mk_point` and `dest_point` functions serve as the constructor and destructor for the `point` type, respectively.

### Mathematical insight
This definition is important because it introduces a new type `point` that is intimately connected with the `line` type, leveraging the existence of a specific `x` in `line` for which a proposition `T` holds. This construction is likely foundational in a geometric or topological context, where points are defined in relation to lines or other geometric objects.

### Dependencies
* `line`
* `T`
* `mk_point`
* `dest_point`
* `REWRITE_TAC`

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles type definitions, especially those that depend on the existence of certain elements in other types. The `REWRITE_TAC` tactic may have an analogue in the target system, but its application and the underlying logic might differ, requiring adjustments to the proof strategy. Additionally, the representation of `line`, `T`, `mk_point`, and `dest_point` must be appropriately translated, considering the type systems and constructs available in the target proof assistant.

---

## on

### Name of formal statement
on

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let on = new_definition `p on l <=> perpl (dest_point p) l;;
```

### Informal statement
The predicate `on` is defined such that a point `p` is `on` a line `l` if and only if the destination point of `p` is perpendicular to `l`.

### Informal sketch
* The definition of `on` relies on the `perpl` predicate, which checks for perpendicularity between a point and a line.
* The `dest_point` function is used to extract the destination point from `p`.
* The definition uses a bi-implication (`<=>`), indicating that the `on` predicate holds if and only if the perpendicularity condition is met.

### Mathematical insight
This definition formalizes the geometric concept of a point lying on a line, using the property of perpendicularity to define the relationship between the point and the line. The `on` predicate is likely used to express geometric statements and theorems involving points and lines.

### Dependencies
* `perpl`
* `dest_point`

### Porting notes
When translating this definition to other proof assistants, ensure that the equivalent of `perpl` and `dest_point` are defined and accessible. Additionally, consider the specific syntax and semantics of bi-implications in the target system, as well as any differences in how geometric concepts are formalized.

---

## POINT_CLAUSES

### Name of formal statement
POINT_CLAUSES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let POINT_CLAUSES = prove
 (`((p = p') <=> (dest_point p = dest_point p')) /\
   ((!p. P (dest_point p)) <=> (!l. P l)) /\
   ((?p. P (dest_point p)) <=> (?l. P l))`,
  MESON_TAC[point_tybij])
```

### Informal statement
The theorem `POINT_CLAUSES` states that three logical equivalences hold: 
1. Two points `p` and `p'` are equal if and only if their destinations `dest_point p` and `dest_point p'` are equal.
2. For all points `p`, a property `P` holds for `dest_point p` if and only if `P` holds for all locations `l`.
3. There exists a point `p` such that a property `P` holds for `dest_point p` if and only if there exists a location `l` for which `P` holds.

### Informal sketch
* The proof involves using the `MESON_TAC` tactic with the `point_tybij` theorem to establish the equivalences.
* The first equivalence is proven by showing that `p = p'` implies `dest_point p = dest_point p'` and vice versa.
* The second and third equivalences involve quantifier manipulation, using the fact that `!p. P (dest_point p)` is equivalent to `!l. P l` and `?p. P (dest_point p)` is equivalent to `?l. P l`.
* The `point_tybij` theorem likely plays a crucial role in establishing the connection between points and locations.

### Mathematical insight
The `POINT_CLAUSES` theorem provides a fundamental connection between points and locations, allowing for the translation of properties and statements between these two concepts. This is crucial in geometric or spatial reasoning, where points and locations may be used interchangeably or have distinct properties.

### Dependencies
* `point_tybij`

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the quantifier manipulations are handled correctly, and the `point_tybij` theorem or its equivalent is available. Additionally, the `MESON_TAC` tactic may need to be replaced with a similar tactic or a manual proof, depending on the target proof assistant's capabilities.

---

## POINT_TAC

### Name of formal statement
POINT_TAC

### Type of the formal statement
Theorem/tactic definition

### Formal Content
```ocaml
let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;
```

### Informal statement
The `POINT_TAC` tactic applies `REWRITE_TAC` with `on` and `POINT_CLAUSES` to a given theorem `th`, and then applies `ACCEPT_TAC` to `th`.

### Informal sketch
* The tactic starts by applying `REWRITE_TAC` to the input theorem `th`, using `on` and `POINT_CLAUSES` as rewrite rules.
* The `REWRITE_TAC` tactic rewrites the theorem using the provided rules.
* After rewriting, `ACCEPT_TAC` is applied to the resulting theorem `th`, effectively accepting it as the final result.
* The use of `on` and `POINT_CLAUSES` suggests that this tactic is intended for manipulating points or geometric objects, potentially in a specific context or theory.

### Mathematical insight
The `POINT_TAC` tactic appears to be a specialized tool for working with geometric or topological structures, leveraging the `POINT_CLAUSES` to apply specific rewrite rules. This tactic is likely important for proving theorems or constructing proofs in a geometric or spatial reasoning context.

### Dependencies
* `REWRITE_TAC`
* `ACCEPT_TAC`
* `on`
* `POINT_CLAUSES`

### Porting notes
When porting this tactic to another proof assistant, pay attention to the handling of rewrite rules and tactics. The equivalent of `REWRITE_TAC` and `ACCEPT_TAC` should be identified, and the `on` and `POINT_CLAUSES` rules should be translated accordingly. Additionally, consider the context in which this tactic is used, as the `POINT_CLAUSES` may rely on specific geometric or topological axioms or definitions.

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
  POINT_TAC LINE_AXIOM_1)
```

### Informal statement
For all points `p` and `p'`, if `p` is not equal to `p'`, then there exists a line `l` such that `p` is on `l` and `p'` is on `l`, and for all lines `l'` such that `p` is on `l'` and `p'` is on `l'`, `l'` is equal to `l`.

### Informal sketch
* The proof assumes two distinct points `p` and `p'`.
* It aims to show the existence of a line `l` that passes through both `p` and `p'`.
* The proof then asserts the uniqueness of such a line by stating that any other line `l'` passing through `p` and `p'` must be identical to `l`.
* The `POINT_TAC` and `LINE_AXIOM_1` suggest that the proof involves basic point and line properties, possibly leveraging axiomatic definitions of points and lines.

### Mathematical insight
This axiom formalizes a fundamental property of geometric objects, specifically that two distinct points define a unique line. This concept is crucial in geometry, ensuring that lines can be consistently defined and manipulated. The axiom's importance lies in its role as a foundation for more complex geometric constructions and theorems.

### Dependencies
* `POINT_TAC`
* `LINE_AXIOM_1`

### Porting notes
When translating this axiom into another proof assistant, ensure that the target system supports a similar concept of points and lines, possibly as part of a geometric library or module. Pay attention to how the system handles equality and distinctness of geometric objects, as these are central to the axiom's statement. Additionally, consider how the target system's tactic or proof language accommodates existential quantification and uniqueness assertions, as these are key components of the axiom's proof structure.

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
For all lines `l` and `l'`, there exists a point `p` such that `p` is on `l` and `p` is on `l'`.

### Informal sketch
* The axiom `AXIOM_2` asserts the existence of a common point `p` between any two lines `l` and `l'`.
* The proof involves applying the `POINT_TAC` tactic, which is likely used to introduce the point `p` and establish its relationship with the lines `l` and `l'`.
* The `LINE_AXIOM_2` reference suggests that this axiom is related to a specific property or definition of lines, which is used to justify the existence of the common point `p`.

### Mathematical insight
This axiom is likely a fundamental property of the geometric system being formalized, ensuring that any two lines intersect at a point. This is a basic assumption in many geometric theories, allowing for the development of more complex geometric concepts and theorems.

### Dependencies
* `LINE_AXIOM_2`
* `POINT_TAC`

### Porting notes
When translating this axiom into other proof assistants, ensure that the concept of a point being "on" a line is properly defined and that the axiom is stated in a way that is consistent with the target system's geometric theory. Additionally, the `POINT_TAC` tactic may need to be replaced with a similar tactic or proof step that is native to the target system.

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
  POINT_TAC LINE_AXIOM_3)
```

### Informal statement
For all points `p`, `p'`, and `p''`, if `p` is not equal to `p'`, `p'` is not equal to `p''`, and `p` is not equal to `p''`, then there does not exist a line `l` such that `p` is on `l`, `p'` is on `l`, and `p''` is on `l`.

### Informal sketch
* The axiom `AXIOM_3` asserts a geometric property about points and lines.
* It involves a universal quantification over three distinct points `p`, `p'`, and `p''`.
* The `POINT_TAC` and `LINE_AXIOM_3` suggest that the proof or construction involves basic point and line axioms, focusing on the relationship between these geometric objects.
* The key logical stage is establishing the non-existence of a line that intersects all three distinct points, which is a fundamental concept in geometry.

### Mathematical insight
This axiom is important because it formalizes a basic geometric intuition that three non-collinear points cannot all lie on the same line. It is a foundational concept in geometry, ensuring that the geometric structures built upon it have the expected properties, such as the ability to define unique lines through two distinct points.

### Dependencies
* `POINT_TAC`
* `LINE_AXIOM_3`

### Porting notes
When translating `AXIOM_3` into other proof assistants like Lean, Coq, or Isabelle, special attention should be given to how these systems handle geometric axioms and the representation of points and lines. The porting process may involve identifying equivalent tactics or axioms in the target system, such as those related to `POINT_TAC` and `LINE_AXIOM_3`, and ensuring that the geometric intuitions and properties are preserved.

---

## AXIOM_4

### Name of formal statement
AXIOM_4

### Type of the formal statement
new_axiom

### Formal Content
```ocaml
let AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p on l /\ p' on l /\ p'' on l`,
  POINT_TAC LINE_AXIOM_4);;
```

### Informal statement
For all lines `l`, there exist three distinct points `p`, `p'`, and `p''` such that `p`, `p'`, and `p''` are on `l`.

### Informal sketch
* The axiom asserts the existence of three distinct points `p`, `p'`, and `p''` on any given line `l`.
* The proof involves using the `POINT_TAC` tactic to establish the existence of these points.
* The `LINE_AXIOM_4` is used to justify the assertion, implying that it is a fundamental property of lines in this formal system.

### Mathematical insight
This axiom is a basic property of geometric objects, ensuring that every line contains at least three distinct points. This is a foundational assumption in many geometric theories, allowing for the construction of more complex geometric objects and the proof of various geometric properties.

### Dependencies
* `POINT_TAC`
* `LINE_AXIOM_4`

### Porting notes
When translating this axiom into other proof assistants, ensure that the concept of a line and points is defined similarly, and that the axiom is stated in a way that aligns with the target system's handling of existential quantification and geometric objects. Note that the `POINT_TAC` tactic may not have a direct equivalent in other systems, so the porting process may require reformulating the proof in terms of the target system's tactics and proof construction mechanisms.

---

## projl

### Name of formal statement
projl

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let projl = new_definition
 `projl x = mk_line((||) (mk_dir x))`
```

### Informal statement
The function `projl` is defined as a mapping that takes a vector `x` and returns a projective line, where the line is constructed from a direction given by `x`. Specifically, `projl x` is defined as `mk_line` applied to the result of `mk_dir x`, where `mk_dir x` presumably constructs a direction from the vector `x`, and `mk_line` then constructs a line from this direction.

### Informal sketch
* The definition involves constructing a projective line from a given vector `x`.
* The `mk_dir` function is applied to `x` to obtain a direction.
* This direction is then used by `mk_line` to construct the projective line.
* The definition assumes the existence of `mk_dir` and `mk_line` functions that operate on vectors and directions to produce lines.

### Mathematical insight
This definition is part of a broader framework for mapping vectors in 3-dimensional space to projective lines and points, providing a way to translate between different geometric representations. The `projl` function specifically enables the construction of projective lines from vectors, which is a fundamental operation in projective geometry.

### Dependencies
* `mk_dir`
* `mk_line`

### Porting notes
When porting this definition to another proof assistant, ensure that equivalent functions for `mk_dir` and `mk_line` are defined and properly linked to the geometric structures they operate on. Note that different systems may handle vector and direction types, as well as line constructions, differently, so careful attention to type compatibility and geometric interpretations is necessary.

---

## projp

### Name of formal statement
projp

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let projp = new_definition `projp x = mk_point(projl x)`;;
```

### Informal statement
The function `projp` is defined such that for any input `x`, `projp x` equals the result of applying `mk_point` to the projection of `x` onto the first component, denoted as `projl x`.

### Informal sketch
* The definition of `projp` relies on applying `mk_point` to the result of `projl x`, which suggests that `projp` is constructing a point from a projected value.
* The use of `projl` indicates that the first component of `x` is being extracted and then used to create a point.
* Understanding the behavior of `mk_point` and `projl` is crucial for grasping how `projp` operates.

### Mathematical insight
The definition of `projp` seems to be part of a geometric or spatial construction, where points are created from projections. This could be related to projections in a Cartesian space or another geometric framework. The key idea is to take an object `x`, extract a specific component from it (in this case, the first component via `projl`), and then use this component to define a new point.

### Dependencies
#### Definitions
* `mk_point`
* `projl`
#### Other
None

### Porting notes
When translating `projp` into another proof assistant, ensure that the equivalents of `mk_point` and `projl` are properly defined and understood. Pay special attention to how these functions handle their inputs and how points are constructed in the target system. Additionally, verify that the projection operation `projl` behaves as expected in the context of the target proof assistant's type system and geometric constructions.

---

## PROJL_TOTAL

### Name of formal statement
PROJL_TOTAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PROJL_TOTAL = prove
 (`!l. ?x. ~(x = vec 0) /\ l = projl x`,
  GEN_TAC THEN
  SUBGOAL_THEN `?d. l = mk_line((||) d)` (CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[fst line_tybij; snd line_tybij];
    REWRITE_TAC[projl] THEN EXISTS_TAC `dest_dir d` THEN
    MESON_TAC[direction_tybij]])
```

### Informal statement
For all lines `l`, there exists a non-zero vector `x` such that `l` is equal to the projection of `x` onto a line, and this projection is not the zero vector.

### Informal sketch
* The proof starts by assuming an arbitrary line `l`.
* It then asserts the existence of a direction `d` such that `l` can be represented as a line defined by `d`.
* The tactic `GEN_TAC` is used to introduce a generic line `l`, and `SUBGOAL_THEN` is used to find a direction `d` that satisfies the condition `l = mk_line((||) d)`.
* The proof then proceeds in two branches:
  + The first branch uses `MESON_TAC` with `fst line_tybij` and `snd line_tybij` to establish the relationship between the line `l` and the direction `d`.
  + The second branch uses `REWRITE_TAC` with `projl` to rewrite the projection of `x` onto the line, and `EXISTS_TAC` to introduce the existence of a vector `x` that satisfies the condition `l = projl x`.
  + The `direction_tybij` theorem is used to establish the bijection between directions and lines.

### Mathematical insight
The `PROJL_TOTAL` theorem provides a way to map lines to non-zero vectors, which is essential in geometric and algebraic reasoning. This theorem is crucial in establishing the connection between lines and vectors, allowing for the representation of lines as projections of non-zero vectors.

### Dependencies
* Theorems:
  + `fst line_tybij`
  + `snd line_tybij`
  + `direction_tybij`
* Definitions:
  + `projl`
  + `mk_line`
  + `dest_dir`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of lines, vectors, and directions. The `GEN_TAC` and `SUBGOAL_THEN` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `MESON_TAC` and `REWRITE_TAC` tactics may require manual rewriting to accommodate differences in the underlying logic and automation.

---

## homol

### Name of formal statement
homol

### Type of the formal statement
new_specification

### Formal Content
```ocaml
let homol = new_specification ["homol"] (REWRITE_RULE[SKOLEM_THM] PROJL_TOTAL);;
```

### Informal statement
The `homol` is defined as a new specification, named "homol", which applies the `REWRITE_RULE` tactic with `SKOLEM_THM` to `PROJL_TOTAL`.

### Informal sketch
* The definition of `homol` involves applying a rewrite rule based on `SKOLEM_THM` to `PROJL_TOTAL`.
* This step likely involves using the `SKOLEM_THM` theorem to transform or simplify `PROJL_TOTAL` in some way, resulting in a new specification.
* The `REWRITE_RULE` tactic is used to perform this transformation, which is a common approach in HOL Light for applying theorems to rewrite expressions.

### Mathematical insight
The `homol` definition seems to be related to applying a specific theorem (`SKOLEM_THM`) to a total projection (`PROJL_TOTAL`), which suggests it might be part of a larger development involving projections or Skolem functions. Understanding the context in which `homol` is used is crucial for grasping its significance.

### Dependencies
* Theorems:
  + `SKOLEM_THM`
* Definitions or specifications:
  + `PROJL_TOTAL`

### Porting notes
When translating this into another proof assistant, pay close attention to how rewrite rules and Skolem functions are handled. Different systems may have varying levels of support for these concepts, and direct translation might require adjustments to tactic scripts or theorem applications.

---

## PROJP_TOTAL

### Name of formal statement
PROJP_TOTAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PROJP_TOTAL = prove
 (`!p. ?x. ~(x = vec 0) /\ p = projp x`,
  REWRITE_TAC[projp] THEN MESON_TAC[PROJL_TOTAL; point_tybij])
```

### Informal statement
For all `p`, there exists an `x` such that `x` is not equal to the zero vector and `p` is equal to the projection of `x`.

### Informal sketch
* The proof involves finding an `x` for any given `p` such that `x` is not the zero vector and `p` equals the projection of `x`.
* The `REWRITE_TAC[projp]` step suggests using the definition of `projp` to rewrite the equation `p = projp x`.
* The `MESON_TAC[PROJL_TOTAL; point_tybij]` step implies using the `PROJL_TOTAL` and `point_tybij` theorems to derive the conclusion, likely through a series of logical deductions.

### Mathematical insight
This theorem seems to establish a relationship between a projection function `projp` and its ability to produce any `p` from a non-zero vector `x`. The projection function likely plays a critical role in a geometric or vector space context, and this theorem ensures that every `p` can be achieved through the projection of some non-zero vector, which is a fundamental property in understanding the behavior of projections in these spaces.

### Dependencies
* Theorems:
  + `PROJL_TOTAL`
* Definitions:
  + `projp`
  + `point_tybij`
* Note: These dependencies are crucial for the proof as they provide the necessary logical foundation for the derivation of `PROJP_TOTAL`.

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how projections and vector operations are handled. The `REWRITE_TAC` and `MESON_TAC` tactics in HOL Light may have direct counterparts or require manual rewriting and derivation in the target system. Additionally, ensuring that the `PROJL_TOTAL` and `point_tybij` theorems (or their equivalents) are available and correctly applied in the new context is essential for a successful port.

---

## homop_def

### Name of formal statement
homop_def

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let homop_def = new_definition `homop p = homol(dest_point p)`;;
```

### Informal statement
The function `homop` of a point `p` is defined as the `homol` of the destination point of `p`.

### Informal sketch
* The definition involves applying the `homol` function to the result of `dest_point` applied to `p`.
* This suggests a two-stage process: first, extracting the destination point from `p` using `dest_point`, and then applying `homol` to this point.
* The `homop` function seems to be a composition of these two operations, `homol` and `dest_point`.

### Mathematical insight
This definition appears to be part of a geometric or topological context, where `homol` might denote a homology operation and `dest_point` could relate to the endpoint of a path or a geometric object. The `homop` function then represents a specific transformation or property applied to these geometric objects.

### Dependencies
* `homol`
* `dest_point`

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, ensure that the `homol` and `dest_point` functions are defined and accessible. The main challenge might be in translating the `new_definition` syntax into the target system's equivalent for defining a new function or constant. For example, in Lean, this might involve using the `def` keyword, while in Coq, it could involve using `Definition`.

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
For all points `p`, it is not the case that `homop p` equals the zero vector, and `p` is equal to the projection of `homop p`.

### Informal sketch
* The proof starts by generalizing over all points `p` using `GEN_TAC`.
* It then applies `REWRITE_TAC` with the definitions of `homop`, `projp`, and a meson rule derived from `point_tybij`, which relates points and their representations.
* The `REWRITE_TAC` step is used to simplify the expression `p = projp(homop p)` based on these definitions and rules.
* The proof concludes by applying `MATCH_ACCEPT_TAC` with the tactic `homol`, which presumably resolves any remaining goals.

### Mathematical insight
This theorem establishes a relationship between the `homop` function, which presumably applies some kind of homogenization or homogeneous transformation to points, and the `projp` function, which projects points. The theorem ensures that applying `homop` to a point and then projecting it back results in the original point, provided that `homop` does not map the point to the zero vector.

### Dependencies
* Theorems:
  + `point_tybij`
* Definitions:
  + `homop_def`
  + `projp`
* Tactics and rules:
  + `GEN_TAC`
  + `REWRITE_TAC`
  + `MATCH_ACCEPT_TAC`
  + `homol`
  + `MESON`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to how the `homop` and `projp` functions are defined and how these definitions are used in the proof. The use of `GEN_TAC` and `REWRITE_TAC` suggests that the proof relies on standard techniques of quantifier manipulation and rewriting, which should be straightforward to translate. However, the `MESON` rule and the `homol` tactic may require more careful consideration, as they seem to involve specific HOL Light mechanisms for deriving and applying rules.

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
The `parallel` relation between two vectors `x` and `y` holds if and only if their cross product is equal to the zero vector.

### Informal sketch
* The definition of `parallel` relies on the `cross` operation and the concept of the zero vector `vec 0`.
* To prove that two vectors are `parallel`, one would need to show that their cross product equals `vec 0`.
* The converse also holds: if the cross product of two vectors equals `vec 0`, then they are `parallel`.

### Mathematical insight
The `parallel` relation captures the geometric concept of two vectors being parallel in a projective space. This definition is important because it provides a way to express geometric properties of vectors in terms of algebraic operations, facilitating further reasoning about geometric objects.

### Dependencies
* `cross`
* `vec 0`

### Porting notes
When translating this definition into other proof assistants, ensure that the cross product operation and the representation of the zero vector are correctly defined and aligned with the target system's conventions. Note that different systems may handle vector operations and geometric concepts differently, so careful attention to these definitions and their properties will be necessary.

---

## ON_HOMOL

### Name of formal statement
ON_HOMOL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ON_HOMOL = prove
 (`!p l. p on l <=> orthogonal (homop p) (homol l)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [homop; homol] THEN
  REWRITE_TAC[on; projp; projl; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[GSYM perpl_th; perpdir] THEN BINOP_TAC THEN
  MESON_TAC[homol; homop; direction_tybij])
```

### Informal statement
For all points `p` and lines `l`, `p` is on `l` if and only if the orthogonal projection of `p` (`homop p`) is orthogonal to the homogeneous line `l` (`homol l`).

### Informal sketch
* The proof starts by generalizing the statement for all points `p` and lines `l`.
* It then applies `GEN_REWRITE_TAC` with `homop` and `homol` to transform the expressions for points and lines into their homogeneous forms.
* The `REWRITE_TAC` tactic is used to apply the definitions of `on`, `projp`, `projl`, and the bijection property `point_tybij` to simplify the statement.
* Further simplification is achieved by applying `REWRITE_TAC` again with `GSYM perpl_th` and `perpdir` to express the condition in terms of orthogonality.
* The `BINOP_TAC` tactic is used to break down the binary operation, and finally, `MESON_TAC` is applied with `homol`, `homop`, and `direction_tybij` to derive the conclusion.
* Key steps involve transforming between point and line representations and leveraging properties of orthogonality and projections.

### Mathematical insight
This theorem provides a fundamental relationship between points, lines, and their homogeneous representations, highlighting the equivalence between a point lying on a line and the orthogonality of their respective homogeneous projections. It showcases how geometric properties can be expressed and proved using algebraic manipulations in a formal system.

### Dependencies
#### Theorems
* `perpl_th`
#### Definitions
* `homop`
* `homol`
* `on`
* `projp`
* `projl`
* `point_tybij`
* `perpdir`
* `direction_tybij`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to the handling of homogeneous coordinates and the properties of orthogonality. The use of `GEN_REWRITE_TAC` and `REWRITE_TAC` suggests that the target system should efficiently support term rewriting and substitution. Additionally, the application of `MESON_TAC` indicates a need for a powerful automatic theorem-proving component or tactical. Differences in how binders are handled and how tactics are composed may require adjustments to the proof strategy.

---

## EQ_HOMOL

### Name of formal statement
EQ_HOMOL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EQ_HOMOL = prove
 (`!l l'. l = l' <=> parallel (homol l) (homol l')`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [homol] THEN
  REWRITE_TAC[projl; MESON[fst line_tybij; snd line_tybij]
   `mk_line((||) l) = mk_line((||) l') <=> (||) l = (||) l'`] THEN
  REWRITE_TAC[PARDIR_EQUIV] THEN REWRITE_TAC[pardir; parallel] THEN
  MESON_TAC[homol; direction_tybij])
```

### Informal statement
For all lines `l` and `l'`, `l` is equal to `l'` if and only if the homology of `l` is parallel to the homology of `l'`.

### Informal sketch
* Start with the statement to be proven: `!l l'. l = l' <=> parallel (homol l) (homol l')`.
* Apply generalization and rewriting tactics to simplify the statement, utilizing the definition of `homol` and properties of `line_tybij`.
* Utilize `GEN_REWRITE_TAC` with `LAND_CONV` and `BINOP_CONV` to handle logical connectives and binary operations.
* Apply `REWRITE_TAC` with various theorems (`projl`, `PARDIR_EQUIV`, `pardir`, `parallel`) to simplify the expression involving `homol l` and `homol l'`.
* Employ `MESON_TAC` with `homol` and `direction_tybij` to derive the final result, leveraging the properties of homology and direction.

### Mathematical insight
This theorem establishes a relationship between the equality of lines and the parallelism of their homologies. The homology of a line is a way of describing its geometric properties, and this theorem shows that two lines are equal if and only if their homologies are parallel. This result is important in geometric and topological contexts, where lines and their properties play a crucial role.

### Dependencies
* Theorems:
	+ `homol`
	+ `line_tybij`
	+ `projl`
	+ `PARDIR_EQUIV`
	+ `pardir`
	+ `parallel`
* Definitions:
	+ `homol`
	+ `line_tybij`
	+ `projl`
	+ `pardir`
	+ `parallel`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of binders, quantifiers, and logical connectives. The `GEN_REWRITE_TAC` and `REWRITE_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `MESON_TAC` tactic, which is used for automatic proof search, may need to be replaced with a more explicit proof construction.

---

## EQ_HOMOP

### Name of formal statement
EQ_HOMOP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EQ_HOMOP = prove
 (`!p p'. p = p' <=> parallel (homop p) (homop p')`,
  REWRITE_TAC[homop_def; GSYM EQ_HOMOL] THEN
  MESON_TAC[point_tybij])
```

### Informal statement
For all `p` and `p'`, `p` is equal to `p'` if and only if `homop p` is parallel to `homop p'`.

### Informal sketch
* The proof involves rewriting the statement using the definition of `homop` (`homop_def`) and the symmetric version of `EQ_HOMOL` (`GSYM EQ_HOMOL`).
* The `REWRITE_TAC` tactic is used to apply these rewrites.
* The `MESON_TAC` tactic is then used with the `point_tybij` theorem to complete the proof.
* The key logical stage is establishing the equivalence between the equality of `p` and `p'` and the parallelism of `homop p` and `homop p'`.

### Mathematical insight
This theorem provides a condition for when two objects `p` and `p'` are equal, in terms of the parallelism of their images under the `homop` function. This is likely important in a geometric or topological context, where `homop` represents a homomorphism or a mapping that preserves certain properties.

### Dependencies
* Theorems:
	+ `EQ_HOMOL`
	+ `point_tybij`
* Definitions:
	+ `homop_def`

### Porting notes
When translating this theorem into another proof assistant, note that the `REWRITE_TAC` and `MESON_TAC` tactics may have direct analogs, but the specific rewrites and theorems used (`homop_def`, `GSYM EQ_HOMOL`, `point_tybij`) will need to be translated or re-proven in the target system. Additionally, the handling of binders and quantifiers may differ between systems, requiring careful attention to the translation of the `!p p'. p = p' <=> ...` statement.

---

## PARALLEL_PROJL_HOMOL

### Name of formal statement
PARALLEL_PROJL_HOMOL

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[direction_tybij])
```

### Informal statement
For all `x`, `x` is parallel to the homogeneous coordinate map of `projl x`.

### Informal sketch
* The proof starts by considering all `x` and applying the definition of `parallel`.
* It then proceeds by cases, depending on whether `x` is the zero vector `vec 0` in `real^3`.
* If `x` is not the zero vector, the proof applies the `homol` function to `projl x` and uses properties of `projl` and `homol` to establish the parallel relationship.
* Key steps involve rewriting using `CROSS_0`, applying `homol` to `projl x`, and using `GEN_REWRITE_TAC` to simplify expressions involving `projl`.
* The proof also involves using `MESON` to derive properties of `line_tybij` and `direction_tybij`, and applying `ASM_MESON_TAC` to conclude the parallel relationship.

### Mathematical insight
This theorem establishes a fundamental property of the homogeneous coordinate map `homol` in relation to the projection `projl`. It shows that for any `x`, `x` is parallel to its image under `homol` composed with `projl`. This result is crucial in geometric and algebraic manipulations involving projections and homogeneous coordinates, providing a basis for further theorems and constructions.

### Dependencies
* Theorems:
  + `homol`
  + `projl`
  + `parallel`
* Definitions:
  + `projl`
  + `homol`
  + `line_tybij`
  + `direction_tybij`
* Tactics and rules:
  + `GEN_TAC`
  + `REWRITE_TAC`
  + `ASM_CASES_TAC`
  + `MP_TAC`
  + `GEN_REWRITE_TAC`
  + `DISCH_THEN`
  + `ASM_MESON_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of vector operations, homogeneous coordinates, and the `parallel` relation. The use of `GEN_TAC` and `ASM_CASES_TAC` may need to be adapted to the target system's tactic language. Additionally, the `MESON` tactic and `ASM_MESON_TAC` may require manual translation or replacement with equivalent reasoning steps in the target system.

---

## PARALLEL_PROJP_HOMOP

### Name of formal statement
PARALLEL_PROJP_HOMOP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PARALLEL_PROJP_HOMOP = prove
 (`!x. parallel x (homop(projp x))`,
  REWRITE_TAC[homop_def; projp; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[PARALLEL_PROJL_HOMOL]);;
```

### Informal statement
For all `x`, `x` is parallel to the homomorphic projection of `x`.

### Informal sketch
* The proof starts by assuming an arbitrary `x` and aiming to show that `x` is parallel to `homop(projp x)`.
* It then applies rewriting using the definitions of `homop`, `projp`, and a rewrite rule derived from `point_tybij` to simplify the expression.
* Further simplification is achieved by applying another rewriting step using `PARALLEL_PROJL_HOMOL`, which likely establishes a relationship between projections and homomorphisms that helps in proving the parallelism.

### Mathematical insight
This theorem seems to establish a fundamental property relating projections and homomorphisms in a geometric or algebraic context, suggesting that every element `x` has a specific relationship with its homomorphic projection. This property could be crucial in various geometric or algebraic constructions, especially those involving projections and homomorphisms.

### Dependencies
- Theorems/Definitions:
  - `homop_def`
  - `projp`
  - `PARALLEL_PROJL_HOMOL`
  - `point_tybij`
- Inductive Rules: None

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how these systems handle quantifiers, rewriting tactics, and the application of theorems like `REWRITE_TAC`. Additionally, ensure that the definitions of `homop`, `projp`, and any other used terms are correctly translated and available in the target system. The use of rewriting tactics might need to be adapted, as different systems have different approaches to handling rewriting and simplification.

---

## PARALLEL_PROJP_HOMOP_EXPLICIT

### Name of formal statement
PARALLEL_PROJP_HOMOP_EXPLICIT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PARALLEL_PROJP_HOMOP_EXPLICIT = prove
 (`!x. ~(x = vec 0) ==> ?a. ~(a = &0) /\ homop(projp x) = a % x`,
  MP_TAC PARALLEL_PROJP_HOMOP THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[parallel; CROSS_EQ_0; COLLINEAR_LEMMA] THEN
  GEN_TAC THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[homop] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `c:real` THEN ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[homop; VECTOR_MUL_LZERO])
```

### Informal statement
For all non-zero vectors `x`, there exists a non-zero scalar `a` such that the homography of the projection of `x` is equal to `a` times `x`.

### Informal sketch
* The proof starts by assuming `x` is not the zero vector.
* It then uses the `PARALLEL_PROJP_HOMOP` theorem and applies `MATCH_MP_TAC` with `MONO_FORALL` to establish a relationship between the projection of `x` and its homography.
* The proof proceeds by case analysis on whether `x` is the zero vector, and then applies `ASM_REWRITE_TAC` with `homop` to simplify the expression.
* It then uses `MATCH_MP_TAC` with `MONO_EXISTS` to introduce an existential quantifier for a scalar `c`.
* The proof further proceeds by case analysis on whether `c` is zero, and applies `ASM_REWRITE_TAC` with `homop` and `VECTOR_MUL_LZERO` to derive the final result.

### Mathematical insight
This theorem provides a relationship between the homography of a vector's projection and the vector itself, which is crucial in understanding the properties of projections and homographies in geometric transformations. The existence of a non-zero scalar `a` that relates the homography of the projection to the original vector is a key insight in this context.

### Dependencies
* Theorems:
  + `PARALLEL_PROJP_HOMOP`
  + `MONO_FORALL`
  + `MONO_EXISTS`
* Definitions:
  + `homop`
  + `projp`
  + `parallel`
  + `CROSS_EQ_0`
  + `COLLINEAR_LEMMA`
  + `VECTOR_MUL_LZERO`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of vector operations and homographies. The `ASM_CASES_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the `REWRITE_TAC` and `ASM_REWRITE_TAC` tactics may require careful handling of rewriting rules and side conditions.

---

## bracket

### Name of formal statement
bracket

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let bracket = define `bracket[a;b;c] = det(vector[homop a;homop b;homop c])`
```

### Informal statement
The function `bracket` is defined as the determinant of a vector formed by the homogeneous coordinates of points `a`, `b`, and `c`.

### Informal sketch
* The definition involves calculating the determinant of a matrix constructed from the homogeneous coordinates of three points `a`, `b`, and `c` using the `homop` function.
* The `vector` function is used to create a vector from these homogeneous coordinates.
* The `det` function then computes the determinant of this vector, which is assigned to `bracket[a;b;c]`.
* This construction implies a geometric interpretation related to the orientation or collinearity of points in a projective space.

### Mathematical insight
The `bracket` definition is crucial in projective geometry, particularly in describing the relationship between points and lines. It can be used to determine if three points are collinear or to define the orientation of a triple of points. This concept is fundamental in various geometric and algebraic computations, including those involving projective transformations and geometric invariants.

### Dependencies
* `homop`
* `vector`
* `det`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that the equivalent of `homop`, `vector`, and `det` functions are defined and correctly applied. Note that the representation of vectors and the computation of determinants might differ between systems, requiring adjustments to the definition. Additionally, the handling of homogeneous coordinates and projective geometry concepts may vary, necessitating careful consideration of the underlying mathematical structures and their representations in the target proof assistant.

---

## COLLINEAR

### Name of formal statement
COLLINEAR

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let COLLINEAR = new_definition `COLLINEAR s <=> ?l. !p. p IN s ==> p on l`
```

### Informal statement
The `COLLINEAR` predicate holds for a set `s` if and only if there exists a line `l` such that for all points `p`, if `p` is in `s`, then `p` lies on `l`.

### Informal sketch
* The definition involves an existential quantification over lines `l`.
* For a given set `s`, the statement requires that there is at least one line `l` that contains all points `p` in `s`.
* The universal quantification over points `p` in `s` ensures that every point in `s` must lie on the line `l` for `COLLINEAR s` to hold.
* The key concept here is the idea of all points in a set lying on a single line, which is a fundamental geometric concept.

### Mathematical insight
The `COLLINEAR` definition captures the geometric notion of points being collinear, which is crucial in various geometric and algebraic contexts. It provides a way to express that a set of points lies on the same line, which is essential in many mathematical proofs and constructions, especially in geometry and linear algebra.

### Dependencies
* `new_definition`
* Basic set theory and geometric concepts, such as points, lines, and the notion of a point lying on a line (`p on l`).

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles existential and universal quantifications, as well as how geometric concepts like points and lines are represented. Specifically, consider how to express the `p on l` relation in the target system, as this might involve different data types or predicates. Additionally, ensure that the translation preserves the logical structure and quantifier scope to maintain the definition's original meaning.

---

## COLLINEAR_SINGLETON

### Name of formal statement
COLLINEAR_SINGLETON

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COLLINEAR_SINGLETON = prove
 (`!a. COLLINEAR {a}`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[AXIOM_1; AXIOM_3])
```

### Informal statement
For all `a`, the set containing only `a` is collinear.

### Informal sketch
* The proof starts with the assumption that we need to prove `COLLINEAR {a}` for any `a`.
* It then applies `REWRITE_TAC` to rewrite the `COLLINEAR` property using its definition, as well as `FORALL_IN_INSERT` and `NOT_IN_EMPTY` to simplify the expression.
* The `MESON_TAC` tactic is used with `AXIOM_1` and `AXIOM_3` to derive the conclusion that `{a}` is indeed collinear.

### Mathematical insight
This theorem establishes that a set containing a single point is collinear, which is a fundamental property in geometry. It provides a basic building block for more complex geometric constructions and theorems.

### Dependencies
* `COLLINEAR`
* `FORALL_IN_INSERT`
* `NOT_IN_EMPTY`
* `AXIOM_1`
* `AXIOM_3`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how they handle set notation and the `COLLINEAR` property. Additionally, the `REWRITE_TAC` and `MESON_TAC` tactics may need to be replaced with equivalent tactics or strategies in the target system, taking into account differences in automation and rewriting mechanisms.

---

## COLLINEAR_PAIR

### Name of formal statement
COLLINEAR_PAIR

### Type of the formal statement
Theorem

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
* The proof considers the case where `a` equals `b` and where `a` does not equal `b`.
* It applies `ASM_REWRITE_TAC` with `INSERT_AC` and `COLLINEAR_SINGLETON` to handle the case when `a` equals `b`.
* It then uses `REWRITE_TAC` with `COLLINEAR`, `FORALL_IN_INSERT`, and `NOT_IN_EMPTY` to simplify the statement.
* Finally, `ASM_MESON_TAC` is applied with `AXIOM_1` to derive the conclusion.

### Mathematical insight
This theorem establishes that any pair of points is collinear, which is a fundamental property in geometry. The proof relies on basic axioms and definitions, showcasing how these foundational elements can be used to derive intuitive geometric results.

### Dependencies
* Theorems: 
  * `AXIOM_1`
* Definitions: 
  * `COLLINEAR`
  * `COLLINEAR_SINGLETON`
  * `INSERT_AC`
  * `FORALL_IN_INSERT`
  * `NOT_IN_EMPTY`

---

## COLLINEAR_TRIPLE

### Name of formal statement
COLLINEAR_TRIPLE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COLLINEAR_TRIPLE = prove
 (`!a b c. COLLINEAR{a,b,c} <=> ?l. a on l /\ b on l /\ c on l`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY])
```

### Informal statement
For all points a, b, and c, the points are collinear if and only if there exists a line l such that point a is on line l, point b is on line l, and point c is on line l.

### Informal sketch
* The proof involves establishing a bidirectional implication between the `COLLINEAR` relation among three points and the existence of a line that passes through all three points.
* The forward direction involves assuming `COLLINEAR{a,b,c}` and finding a line l that contains a, b, and c.
* The backward direction assumes the existence of such a line l and deduces `COLLINEAR{a,b,c}`.
* The `REWRITE_TAC` tactic is used with theorems `COLLINEAR`, `FORALL_IN_INSERT`, and `NOT_IN_EMPTY` to simplify and establish the equivalence.

### Mathematical insight
This theorem provides a fundamental characterization of collinearity in terms of the existence of a line that passes through three given points. It is crucial for establishing various geometric properties and theorems that rely on the concept of collinearity.

### Dependencies
* Theorems:
  - `COLLINEAR`
  - `FORALL_IN_INSERT`
  - `NOT_IN_EMPTY`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how the target system handles existential quantification (`?l`) and how it defines and manipulates geometric concepts like lines and points. Additionally, the equivalents of `REWRITE_TAC` and the mentioned theorems need to be identified and applied appropriately to mirror the original proof strategy.

---

## COLLINEAR_BRACKET

### Name of formal statement
COLLINEAR_BRACKET

### Type of the formal statement
Theorem

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
    REWRITE_TAC[GSYM projl; GSYM parallel; PARALLEL_PROJL_HOMOL]])
```

### Informal statement
For all points `p1`, `p2`, and `p3`, the set `{p1, p2, p3}` is collinear if and only if the bracket `[p1; p2; p3]` equals the zero vector. This statement involves the `COLLINEAR` predicate and the `bracket` function, which are related through the `COLLINEAR_TRIPLE` and `ON_HOMOL` definitions.

### Informal sketch
* The proof starts by assuming the `COLLINEAR` condition and derives the `bracket` equation using various rewrites and the `homol` theorem.
* It then proceeds to prove the converse, assuming the `bracket` equation and deriving the `COLLINEAR` condition.
* The proof involves several key steps:
  + Using the `lemma` to establish a relationship between orthogonal vectors and cross products.
  + Applying `REWRITE_TAC` and `MATCH_MP_TAC` to manipulate the `COLLINEAR_TRIPLE` and `bracket` definitions.
  + Employing `ASM_CASES_TAC` to handle the case where `p1` equals `p2`.
  + Utilizing `EXISTS_TAC` to introduce a new line and apply the `lemma` to establish the desired orthogonality conditions.
* The proof concludes by rewriting and simplifying the resulting expressions to obtain the desired equation.

### Mathematical insight
This theorem establishes a fundamental relationship between the `COLLINEAR` predicate and the `bracket` function, which is crucial in geometric and algebraic computations. The `COLLINEAR` predicate determines whether a set of points lies on the same line, while the `bracket` function computes a vector value that can be used to determine this property. The theorem provides a way to translate between these two representations, facilitating various geometric and algebraic manipulations.

### Dependencies
* Theorems:
  + `homol`
  + `COLLINEAR_TRIPLE`
  + `ON_HOMOL`
  + `LEFT_IMP_EXISTS_THM`
  + `MONO_FORALL`
* Definitions:
  + `COLLINEAR`
  + `bracket`
  + `orthogonal`
  + `parallel`
  + `ON_HOMOL`
  + `DET_3`
  + `DOT_3`
  + `VECTOR_3`
  + `CART_EQ`
  + `DIMINDEX_3`
  + `FORALL_3`
  + `VEC_COMPONENT`
  + `GSYM`
  + `projl`
  + `PARALLEL_PROJL_HOMOL`
* Tactics:
  + `REWRITE_TAC`
  + `MATCH_MP_TAC`
  + `GEN_TAC`
  + `DISCH_THEN`
  + `CONJUNCT1`
  + `CONV_TAC`
  + `REAL_RING`
  + `ASM_CASES_TAC`
  + `EXISTS_TAC`
  + `ASM_REWRITE_TAC`
  + `ONCE_REWRITE_TAC`
  + `REPEAT`
  + `STRIP_TAC`

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
                         d * x$1 * x$2 + e * x$1 * x$3 + f * x$2 * x$3 = &0}`
```

### Informal statement
A `homogeneous_conic` is defined as a set `con` in three-dimensional real space, parameterized by real numbers `a`, `b`, `c`, `d`, `e`, and `f`, such that not all of `a`, `b`, `c`, `d`, `e`, and `f` are zero, and `con` consists of all points `x` in three-dimensional real space that satisfy the equation `a * x1^2 + b * x2^2 + c * x3^2 + d * x1 * x2 + e * x1 * x3 + f * x2 * x3 = 0`.

### Informal sketch
* The definition involves existential quantification over the coefficients `a`, `b`, `c`, `d`, `e`, and `f`.
* It asserts the existence of at least one non-zero coefficient among `a`, `b`, `c`, `d`, `e`, and `f`.
* The set `con` is defined as the set of points `x` in `real^3` that satisfy a specific quadratic equation involving the coefficients and the coordinates of `x`.
* The equation represents a conic section in three-dimensional space.

### Mathematical insight
This definition formalizes the concept of a homogeneous conic section in projective geometry, which is a fundamental object in algebraic geometry and computer vision. The `homogeneous_conic` definition provides a way to represent conic sections using a set of coefficients, which is essential for various applications, including computer vision, graphics, and geometric modeling.

### Dependencies
* `real`
* `pow`
* `&0`

### Porting notes
When porting this definition to other proof assistants, pay attention to the representation of real numbers, the definition of the `pow` function, and the notation for existential quantification. Additionally, ensure that the target system supports the same level of abstraction and expressiveness as HOL Light, particularly regarding the use of sets and predicates to define geometric objects.

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
A set `con` is a projective conic if and only if there exists a `c` such that `c` is a homogeneous conic and `con` is equal to the set of all points `p` such that the homogeneous point `p` is an element of `c`.

### Informal sketch
* The definition involves an existential quantifier `?c` indicating that for a set `con` to be a projective conic, there must exist some `c` that satisfies two conditions:
 + `c` must be a `homogeneous_conic`
 + The set `con` must be the set of all points `p` for which the `homop p` (homogeneous point `p`) is an element of `c`
* This construction implies that `projective_conic` is defined in terms of `homogeneous_conic` and a specific set transformation involving `homop`

### Mathematical insight
The `projective_conic` definition is crucial as it establishes a connection between projective geometry and homogeneous coordinates. It provides a way to describe conic sections in projective space using homogeneous conics, which is fundamental in algebraic geometry and computer vision.

### Dependencies
* `homogeneous_conic`
* `homop`

### Porting notes
When translating this definition into another proof assistant, pay attention to how existential quantification and set comprehension are handled. The definition relies on the existence of a `c` that satisfies two properties, and the set `con` is defined using a set comprehension involving a predicate on homogeneous points. Ensure that the target system can express these constructs naturally, and consider how to translate the `homogeneous_conic` and `homop` concepts, which are likely defined elsewhere in the HOL Light development.

---

## HOMOGENEOUS_CONIC_BRACKET

### Name of formal statement
HOMOGENEOUS_CONIC_BRACKET

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_RING)
```

### Informal statement
For all conics `con` and points `x1`, `x2`, `x3`, `x4`, `x5`, `x6` that lie on `con`, if `con` is a homogeneous conic, then the product of the determinants of the vectors formed by `x6`, `x1`, `x4` and `x6`, `x2`, `x3` and `x5`, `x1`, `x3` and `x5`, `x2`, `x4` is equal to the product of the determinants of the vectors formed by `x6`, `x1`, `x3` and `x6`, `x2`, `x4` and `x5`, `x1`, `x4` and `x5`, `x2`, `x3`.

### Informal sketch
* The proof begins by assuming the existence of a homogeneous conic `con` and six points `x1`, `x2`, `x3`, `x4`, `x5`, `x6` that lie on `con`.
* It then applies various rewriting and simplification steps using `homogeneous_conic`, `EXTENSION`, `IMP_CONJ`, and `LEFT_IMP_EXISTS_THM` to transform the goal into a more manageable form.
* The proof proceeds by using `GEN_TAC` and `DISCH_THEN` to manipulate the assumptions and conclusions, and `ASM_REWRITE_TAC` to apply specific rewrite rules such as `IN_ELIM_THM`, `DET_3`, and `VECTOR_3`.
* Finally, the proof concludes by applying `CONV_TAC REAL_RING` to ensure the result is expressed in terms of real numbers.

### Mathematical insight
This theorem provides a relationship between the determinants of vectors formed by points on a homogeneous conic, which is a fundamental concept in projective geometry. The theorem is important because it reveals a deep connection between the algebraic and geometric structures of conics, and has implications for various applications in mathematics and computer science.

### Dependencies
* `homogeneous_conic`
* `EXTENSION`
* `IMP_CONJ`
* `LEFT_IMP_EXISTS_THM`
* `IN_ELIM_THM`
* `DET_3`
* `VECTOR_3`
* `REAL_RING`

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the rewriting and simplification steps are properly aligned with the target system's tactics and rewrite rules. Additionally, the use of `CONV_TAC REAL_RING` may require special attention, as different systems may handle real numbers and algebraic manipulations differently.

---

## PROJECTIVE_CONIC_BRACKET

### Name of formal statement
PROJECTIVE_CONIC_BRACKET

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC HOMOGENEOUS_CONIC_BRACKET THEN ASM_MESON_TAC[])
```

### Informal statement
For all projective conics `con` and points `p1`, `p2`, `p3`, `p4`, `p5`, `p6` that lie on `con`, the following equation holds: `bracket[p6;p1;p4] * bracket[p6;p2;p3] * bracket[p5;p1;p3] * bracket[p5;p2;p4] = bracket[p6;p1;p3] * bracket[p6;p2;p4] * bracket[p5;p1;p4] * bracket[p5;p2;p3]`, given that `projective_conic con` and each point is in `con`.

### Informal sketch
* The proof starts by assuming the existence of a projective conic `con` and points `p1`, `p2`, `p3`, `p4`, `p5`, `p6` that lie on it.
* It then applies `REWRITE_TAC` to expand the `bracket` and `projective_conic` terms.
* The `DISCH_THEN` and `CONJUNCTS_THEN2` tactics are used to manipulate the assumptions and conclusions.
* The proof then applies `ASM_REWRITE_TAC` with `IN_ELIM_THM` to simplify the expression.
* Finally, it uses `MATCH_MP_TAC` with `HOMOGENEOUS_CONIC_BRACKET` to derive the conclusion, and `ASM_MESON_TAC` to check the result.

### Mathematical insight
This theorem provides an important property of projective conics, relating the `bracket` expressions of points on the conic. The `bracket` function is a key concept in projective geometry, and this result helps to establish a deeper understanding of the relationships between points on a projective conic.

### Dependencies
* Theorems:
	+ `HOMOGENEOUS_CONIC_BRACKET`
* Definitions:
	+ `projective_conic`
	+ `bracket`
* Axioms:
	+ `IN_ELIM_THM`

### Porting notes
When translating this theorem to another proof assistant, pay attention to the handling of the `bracket` function and the `projective_conic` predicate. The `REWRITE_TAC` and `ASM_REWRITE_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `MATCH_MP_TAC` tactic may require a different formulation, depending on the specific proof assistant being used.

---

## PASCAL_DIRECT

### Name of formal statement
PASCAL_DIRECT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PASCAL_DIRECT = prove
 (`!con x1 x2 x3 x4 x5 x6 x8 x9.
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
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING)
```

### Informal statement
For all points `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x8`, and `x9`, if the following conditions hold:
- None of the sets `{x2, x5, x7}`, `{x1, x2, x5}`, `{x1, x3, x6}`, `{x2, x4, x6}`, `{x3, x4, x5}`, `{x1, x5, x7}`, `{x2, x5, x9}`, `{x1, x2, x6}`, `{x3, x6, x8}`, `{x2, x4, x5}`, `{x2, x4, x7}`, `{x2, x6, x8}`, `{x3, x4, x6}`, `{x3, x5, x8}`, and `{x1, x3, x5}` are collinear,
then, if `con` is a projective conic and `x1`, `x2`, `x3`, `x4`, `x5`, `x6` are on `con`, and the sets `{x1, x9, x5}`, `{x1, x8, x6}`, `{x2, x9, x4}`, `{x2, x7, x6}`, `{x3, x8, x4}`, and `{x3, x7, x5}` are collinear,
it follows that the set `{x7, x8, x9}` is collinear.

### Informal sketch
* The proof starts by assuming the non-collinearity conditions and the existence of a projective conic `con` containing points `x1` through `x6`.
* It then applies the `PROJECTIVE_CONIC_BRACKET` theorem to establish relationships between the points.
* The proof involves a series of algebraic manipulations using `bracket` expressions and properties of determinants (`DET_3`) and vectors (`VECTOR_3`).
* Key steps involve:
  + Establishing equalities between products of `bracket` expressions
  + Applying `REAL_RING` properties for real numbers
  + Using `COLLINEAR_BRACKET` to relate `bracket` expressions to collinearity
  + Employing `CONJ_TAC` and `MATCH_MP_TAC` to manage the proof structure
* The goal is to show that `{x7, x8, x9}` is collinear based on the given conditions and the properties of projective conics.

### Mathematical insight
This theorem formalizes Pascal's theorem, a fundamental result in projective geometry, which states that if six points lie on a conic section (such as an ellipse or a circle) and are numbered consecutively (in any order), then the three lines formed by connecting points 1 and 4, 2 and 5, and 3 and 6 intersect in a single point. The formalization here ensures that all necessary non-degeneracy conditions are met (e.g., no three points are collinear) and applies to projective conics in general.

### Dependencies
#### Theorems
- `PROJECTIVE_CONIC_BRACKET`
- `REAL_RING`
#### Definitions
- `bracket`
- `COLLINEAR_BRACKET`
- `DET_3`
- `VECTOR_3`
- `projective_conic`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to:
- The handling of `bracket` expressions and their relation to determinants and vectors.
- The use of `REAL_RING` properties, which may differ between systems.
- The management of non-degeneracy conditions and their implications for geometric constructions.
- The application of `PROJECTIVE_CONIC_BRACKET` and its equivalent in the target system.

---

## PASCAL

### Name of formal statement
PASCAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PASCAL = prove
 (`!con x1 x2 x3 x4 x5 x6 x8 x9.
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
  CONV_TAC REAL_RING)
```

### Informal statement
For all points `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x8`, and `x9`, if the following conditions hold:
- No three points among `x1`, `x2`, and `x4`, `x1`, `x2`, and `x5`, `x1`, `x2`, and `x6`, `x1`, `x3`, and `x4`, `x1`, `x3`, and `x5`, `x1`, `x3`, and `x6`, `x2`, `x3`, and `x4`, `x2`, `x3`, and `x5`, `x2`, `x3`, and `x6`, `x4`, `x5`, and `x1`, `x4`, `x5`, and `x2`, `x4`, `x5`, and `x3`, `x4`, `x6`, and `x1`, `x4`, `x6`, and `x2`, `x4`, `x6`, and `x3`, `x5`, `x6`, and `x1`, `x5`, `x6`, and `x2`, `x5`, `x6`, and `x3` are collinear,
then if there exists a projective conic `con` such that `x1`, `x2`, `x3`, `x4`, `x5`, `x6` are on `con`, and `x1`, `x9`, `x5` are collinear, `x1`, `x8`, `x6` are collinear, `x2`, `x9`, `x4` are collinear, `x2`, `x7`, `x6` are collinear, `x3`, `x8`, `x4` are collinear, `x3`, `x7`, `x5` are collinear,
it follows that `x7`, `x8`, `x9` are collinear.

### Informal sketch
* The theorem starts by assuming a set of non-collinearity conditions among nine points `x1` through `x9`.
* It then assumes the existence of a projective conic `con` that contains points `x1` through `x6`.
* Additional collinearity conditions are assumed among certain subsets of these points and points `x7`, `x8`, `x9`.
* The proof involves using the `MATCH_MP_TAC` tactic to apply a tautology, followed by `DISCH_TAC` and `MP_TAC` to manage assumptions and apply `PASCAL_DIRECT`.
* The `REPEAT CONJ_TAC` and `REPEAT(POP_ASSUM MP_TAC)` steps are used to handle conjunctions and assumptions.
* Finally, `REWRITE_TAC` and `CONV_TAC REAL_RING` are applied to simplify and conclude the proof.
* Key steps involve applying `PASCAL_DIRECT` and using the `TAUT` tactic to handle logical implications.

### Mathematical insight
This theorem appears to be related to the properties of projective conics and the relationships between points and lines in projective geometry. The conditions given ensure that certain sets of points are not collinear unless they belong to specific subsets, suggesting a structured geometric configuration. The conclusion that `x7`, `x8`, `x9` are collinear given the other conditions implies a deeper geometric relationship, potentially related to the properties of conics and the intersections of lines.

### Dependencies
* `COLLINEAR`
* `projective_conic`
* `PASCAL_DIRECT`
* `TAUT`
* `MATCH_MP_TAC`
* `DISCH_TAC`
* `MP_TAC`
* `REPEAT`
* `GEN_TAC`
* `CONJUNCT2`
* `ASSUME_TAC`
* `CONV_TAC`
* `REAL_RING`
* `COLLINEAR_BRACKET`
* `bracket`
* `DET_3`
* `VECTOR_3`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to handling the quantifiers, the `COLLINEAR` predicate, and the projective conic `con`. The use of `MATCH_MP_TAC` and `TAUT` may require equivalent tactics or built-in support for logical tautologies in the target system. Additionally, the `REWRITE_TAC` and `CONV_TAC` steps may need to be adapted based on the specific rewriting and conversion mechanisms available in the target proof assistant.

---

## homogenize

### Name of formal statement
homogenize

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let homogenize = new_definition
 `(homogenize:real^2->real^3) x = vector[x$1; x$2; &1]`
```

### Informal statement
The function `homogenize` maps a vector `x` from the 2-dimensional real space to the 3-dimensional real space, where the resulting vector has components `x$1`, `x$2`, and `1`.

### Informal sketch
* The `homogenize` function is defined as a vector-valued function that takes a 2D real vector `x` as input.
* The output of the function is a 3D real vector with components `x$1`, `x$2`, and `1`, which is constructed using the `vector` function.
* This definition effectively embeds the 2D affine space into the 3D projective space.

### Mathematical insight
The `homogenize` function represents a canonical construction in projective geometry, where points in the affine plane are mapped to points in the projective plane by adding a third homogeneous coordinate. This allows for the extension of affine geometric concepts to the projective setting, enabling the study of geometric properties that are invariant under projective transformations.

### Dependencies
* `vector`
* `real`

### Porting notes
When translating this definition to other proof assistants, note that the `vector` function and the `&1` syntax may need to be adapted to the target system's notation. For example, in Lean, the equivalent definition might use the `vec` function and the `1` literal, while in Coq, the `Vector` type and the `Z.one` constant might be used. Additionally, the `real` type may need to be replaced with the corresponding type in the target system, such as `ℝ` in Lean or `R` in Coq.

---

## projectivize

### Name of formal statement
projectivize

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let projectivize = new_definition `projectivize = projp o homogenize`;;
```

### Informal statement
The function `projectivize` is defined as the composition of `projp` and `homogenize`.

### Informal sketch
* The definition of `projectivize` involves two main components: `projp` and `homogenize`.
* `projp` is applied after `homogenize` in a composition, indicating that the output of `homogenize` is the input to `projp`.
* This composition suggests a two-stage process where `homogenize` is used first, followed by `projp`.

### Mathematical insight
The `projectivize` function appears to be part of a process that involves transforming or normalizing some mathematical object, with `homogenize` potentially making the object homogeneous in some sense, and `projp` then projecting it, possibly onto a projective space or to extract some projective property.

### Dependencies
- `projp`
- `homogenize`

### Porting notes
When translating `projectivize` into another proof assistant, ensure that the composition of functions is correctly represented. Note that the order of composition may be important, as function composition is not necessarily commutative. Additionally, verify that the types of `projp` and `homogenize` are correctly aligned in the target system to ensure that the composition is well-typed.

---

## HOMOGENIZE_NONZERO

### Name of formal statement
HOMOGENIZE_NONZERO

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let HOMOGENIZE_NONZERO = prove
 (`!x. ~(homogenize x = vec 0)`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT; VECTOR_3;
              homogenize] THEN
  REAL_ARITH_TAC)
```

### Informal statement
For all `x`, it is not the case that the `homogenize` of `x` equals the zero vector.

### Informal sketch
* The proof starts with a universal quantifier `!x`, indicating that the statement applies to all `x`.
* The main goal is to show that the `homogenize` function of `x` does not equal the zero vector `vec 0`.
* The proof uses rewriting with several theorems, including `CART_EQ`, `DIMINDEX_3`, `FORALL_3`, `VEC_COMPONENT`, `VECTOR_3`, and the definition of `homogenize`.
* After rewriting, `REAL_ARITH_TAC` is applied, which suggests the use of real arithmetic properties to finalize the proof.

### Mathematical insight
This theorem provides a fundamental property of the `homogenize` function, ensuring that it does not map any input to the zero vector. This is crucial in various geometric and algebraic contexts where the `homogenize` function is used, as it guarantees that the function preserves certain properties of the input vectors.

### Dependencies
* Theorems:
  + `CART_EQ`
  + `DIMINDEX_3`
  + `FORALL_3`
  + `VEC_COMPONENT`
  + `VECTOR_3`
* Definitions:
  + `homogenize`
  + `vec`
  + `REAL_ARITH_TAC` (tactic)

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how universal quantification and vector operations are handled. The `REAL_ARITH_TAC` tactic may need to be replaced with equivalent arithmetic reasoning mechanisms available in the target system. Additionally, ensure that the `homogenize` function and related theorems are defined or proven in the target system before attempting to port this theorem.

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
                         d * x$1 + e * x$2 + f = &0}`
```

### Informal statement
The `affine_conic` definition states that a conic section `con` in the affine plane exists if and only if there exist real numbers `a`, `b`, `c`, `d`, `e`, and `f`, not all zero, such that `con` is the set of all points `x` in the affine plane satisfying the equation `a * x1^2 + b * x2^2 + c * x1 * x2 + d * x1 + e * x2 + f = 0`.

### Informal sketch
* The definition of `affine_conic` involves the existence of coefficients `a`, `b`, `c`, `d`, `e`, and `f` that are not all zero.
* These coefficients define a conic section `con` as the set of points `x` in the affine plane that satisfy a specific quadratic equation.
* The equation is of the form `a * x1^2 + b * x2^2 + c * x1 * x2 + d * x1 + e * x2 + f = 0`, which represents a general conic section.
* The definition uses the `?` quantifier to express the existence of the coefficients and the set comprehension to define the conic section.

### Mathematical insight
The `affine_conic` definition provides a way to represent conic sections in the affine plane using a set of coefficients. This definition is important in geometry and computer graphics, as conic sections are used to model a wide range of curves, including circles, ellipses, parabolas, and hyperbolas. The definition also highlights the relationship between the coefficients and the shape of the conic section.

### Dependencies
* `real`
* `pow`
* `&0`

### Porting notes
When porting this definition to other proof assistants, note that the `?` quantifier may be represented differently. For example, in Lean, it would be represented as `∃`. Additionally, the set comprehension may need to be rewritten using the specific syntax of the target proof assistant.

---

## COLLINEAR_PROJECTIVIZE

### Name of formal statement
COLLINEAR_PROJECTIVIZE

### Type of the formal statement
Theorem

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
    CONV_TAC REAL_RING])
```

### Informal statement
For all points `a`, `b`, and `c`, the points are collinear if and only if their projectivizations `projectivize a`, `projectivize b`, and `projectivize c` are collinear.

### Informal sketch
* The proof starts by applying `GEN_TAC` to introduce universal quantifiers for `a`, `b`, and `c`.
* It then applies `ONCE_REWRITE_TAC` with `COLLINEAR_3` to express collinearity in terms of a determinant condition.
* The `REWRITE_TAC` steps apply various definitions and properties, including `GSYM DOT_CAUCHY_SCHWARZ_EQUAL`, `COLLINEAR_BRACKET`, `projectivize`, `o_THM`, and `bracket`, to transform the expression.
* The proof then uses `MATCH_MP_TAC EQ_TRANS` to apply a transitivity argument, introducing an intermediate statement involving the determinant of a vector formed by homogenizing `a`, `b`, and `c`.
* The `EXISTS_TAC` introduces this determinant condition, which is then split into two conjuncts using `CONJ_TAC`.
* The first conjunct is proven using `REWRITE_TAC` with various definitions, followed by `CONV_TAC REAL_RING` to finalize the real arithmetic.
* The second conjunct involves applying several `MAP_EVERY` with specific tactics to establish properties about the homogenized points and their projectivizations, including `PARALLEL_PROJP_HOMOP`, `HOMOGENIZE_NONZERO`, and `homop`.
* Finally, `REWRITE_TAC` is used with several definitions to simplify the expression, and `CONV_TAC REAL_RING` is applied to conclude the real arithmetic.

### Mathematical insight
This theorem establishes a relationship between the affine notion of collinearity and its projective counterpart. It shows that three points are collinear in the affine space if and only if their projectivizations are collinear in the projective space. This is crucial for transferring geometric properties between these two spaces.

### Dependencies
#### Theorems
* `COLLINEAR_3`
* `DOT_CAUCHY_SCHWARZ_EQUAL`
* `COLLINEAR_BRACKET`
* `projectivize`
* `o_THM`
* `bracket`
* `PARALLEL_PROJP_HOMOP`
* `HOMOGENIZE_NONZERO`
* `homop`
#### Definitions
* `collinear`
* `COLLINEAR`
* `projectivize`
* `homogenize`
* `det`
* `vector`
* `parallel`
* `cross`
* `CART_EQ`
* `DIMINDEX_3`
* `FORALL_3`
* `VECTOR_3`
* `DET_3`
* `VEC_COMPONENT`

---

## AFFINE_PROJECTIVE_CONIC

### Name of formal statement
AFFINE_PROJECTIVE_CONIC

### Type of the formal statement
Theorem

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
  UNDISCH_TAC `~(k = &0)` THEN CONV_TAC REAL_RING)
```

### Informal statement
For all conic sections `con`, `con` is an affine conic if and only if there exists a projective conic `con'` such that `con` is equal to the set of all points `x` in the projectivization of `con'`.

### Informal sketch
* The proof starts by rewriting the `affine_conic` and `projective_conic` definitions using `REWRITE_TAC`.
* It then applies `GEN_TAC` to introduce a generic conic section `con`, followed by `REWRITE_TAC` with `LEFT_AND_EXISTS_THM` to handle existential quantification.
* The `MAP_EVERY` tactic is used to apply a series of rewrites and term manipulations to the variables `a`, `b`, `c`, `d`, `e`, and `f`.
* The proof proceeds with further rewrites and manipulations, including `RIGHT_EXISTS_AND_THM`, `UNWIND_THM2`, and `GSYM CONJ_ASSOC`, to simplify the expression and prepare for the main argument.
* The `BINOP_TAC` is used to split the proof into two branches, and `CONV_TAC TAUT` and `AP_TERM_TAC` are applied to each branch.
* The proof then focuses on the extensionality of the sets involved, using `REWRITE_TAC` with `EXTENSION`, and introduces a generic point `x` of type `real^2` using `X_GEN_TAC`.
* The `MP_TAC` and `MATCH_MP` tactics are used to apply the `PARALLEL_PROJP_HOMOP_EXPLICIT` theorem, followed by `DISCH_THEN` and `X_CHOOSE_THEN` to handle the existential quantification and introduce a scalar `k`.
* The proof concludes with a series of rewrites and manipulations, including `ASM_REWRITE_TAC`, `REWRITE_TAC` with `homogenize` and `VECTOR_3`, and finally `UNDISCH_TAC` and `CONV_TAC REAL_RING`.

### Mathematical insight
This theorem establishes a fundamental relationship between affine and projective conic sections, showing that an affine conic can be represented as the projectivization of a projective conic. This connection is crucial in understanding the geometry and algebra of conic sections, as it allows for the transfer of properties and results between the affine and projective settings.

### Dependencies
#### Theorems
* `HOMOGENIZE_NONZERO`
* `PARALLEL_PROJP_HOMOP_EXPLICIT`
#### Definitions
* `affine_conic`
* `projective_conic`
* `homogeneous_conic`
* `projectivize`
* `homogenize`
#### Other
* `LEFT_AND_EXISTS_THM`
* `RIGHT_EXISTS_AND_THM`
* `UNWIND_THM2`
* `GSYM CONJ_ASSOC`
* `IN_ELIM_THM`
* `EXTENSION`

---

## PASCAL_AFFINE

### Name of formal statement
PASCAL_AFFINE

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[])
```

### Informal statement
For all points `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x7`, `x8`, `x9` in the real affine plane, if the following conditions hold:
- `x1`, `x2`, `x4` are not collinear,
- `x1`, `x2`, `x5` are not collinear,
- `x1`, `x2`, `x6` are not collinear,
- `x1`, `x3`, `x4` are not collinear,
- `x1`, `x3`, `x5` are not collinear,
- `x1`, `x3`, `x6` are not collinear,
- `x2`, `x3`, `x4` are not collinear,
- `x2`, `x3`, `x5` are not collinear,
- `x2`, `x3`, `x6` are not collinear,
- `x4`, `x5`, `x1` are not collinear,
- `x4`, `x5`, `x2` are not collinear,
- `x4`, `x5`, `x3` are not collinear,
- `x4`, `x6`, `x1` are not collinear,
- `x4`, `x6`, `x2` are not collinear,
- `x4`, `x6`, `x3` are not collinear,
- `x5`, `x6`, `x1` are not collinear,
- `x5`, `x6`, `x2` are not collinear,
- `x5`, `x6`, `x3` are not collinear,
and if there exists an affine conic `con` such that `x1`, `x2`, `x3`, `x4`, `x5`, `x6` are all on `con`, and
- `x1`, `x9`, `x5` are collinear,
- `x1`, `x8`, `x6` are collinear,
- `x2`, `x9`, `x4` are collinear,
- `x2`, `x7`, `x6` are collinear,
- `x3`, `x8`, `x4` are collinear,
- `x3`, `x7`, `x5` are collinear,
then `x7`, `x8`, `x9` are collinear.

### Informal sketch
* The theorem starts by assuming a set of points `x1` through `x6` and `x7`, `x8`, `x9` in the real affine plane, with certain non-collinearity conditions.
* It then assumes the existence of an affine conic `con` that passes through `x1`, `x2`, `x3`, `x4`, `x5`, `x6`.
* Additional collinearity conditions are imposed on the points `x1` through `x6` with `x7`, `x8`, `x9`.
* The goal is to prove that `x7`, `x8`, `x9` are collinear.
* The proof involves using the `COLLINEAR_PROJECTIVIZE` and `AFFINE_PROJECTIVE_CONIC` theorems to establish the relationship between the points and the conic.
* It applies various tactics including `GEN_TAC`, `DISCH_TAC`, `MATCH_MP_TAC`, and `ASM_REWRITE_TAC` to manipulate the assumptions and goals.
* The `PASCAL` theorem is used as a key step in the proof.

### Mathematical insight
This theorem is a formulation of Pascal's theorem in the context of the real affine plane, which is a fundamental result in projective geometry. It describes a condition under which a set of points, related to a conic section, must be collinear. The theorem is important because it connects the geometric properties of conic sections with the combinatorial properties of sets of points, showcasing the deep interplay between geometry and algebra.

### Dependencies
* Theorems:
  - `COLLINEAR_PROJECTIVIZE`
  - `AFFINE_PROJECTIVE_CONIC`
  - `PASCAL`
* Definitions:
  - `collinear`
  - `affine_conic`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how the target system handles:
- Quantifiers over points in the affine plane
- Definitions and theorems related to collinearity and conic sections
- Tactics for manipulating assumptions and applying theorems, as the sequence of tactics (`REWRITE_TAC`, `GEN_TAC`, `DISCH_TAC`, etc.) may need to be adapted to the target system's proof scripting language.

---

## COLLINEAR_NOT_COCIRCULAR

### Name of formal statement
COLLINEAR_NOT_COCIRCULAR

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_RING)
```

### Informal statement
For all real numbers $r$ and points $c$, $x$, $y$, $z$ in $\mathbb{R}^2$, if the distance from $c$ to $x$, $y$, and $z$ is equal to $r$, and $x$, $y$, and $z$ are distinct, then the points $x$, $y$, and $z$ are not collinear.

### Informal sketch
* The proof starts by assuming the distance from a center point $c$ to three distinct points $x$, $y$, and $z$ in $\mathbb{R}^2$ is equal to some real number $r$.
* It then applies several rewrites using `VECTOR_SUB_EQ`, `DOT_EQ_0`, `COLLINEAR_3`, `DOT_CAUCHY_SCHWARZ_EQUAL`, and `DOT_2` to transform the expression and simplify the condition for collinearity.
* The proof continues by rewriting the distance and norm equations using `dist`, `NORM_EQ_SQUARE`, `CART_EQ`, `DIMINDEX_2`, `FORALL_2`, `DOT_2`, and `VECTOR_SUB_COMPONENT`.
* Finally, it uses `CONV_TAC REAL_RING` to conclude the proof, showing that under the given conditions, $x$, $y$, and $z$ cannot be collinear.

### Mathematical insight
This theorem is a special case related to the properties of circles and collinearity in $\mathbb{R}^2$. It states that given three distinct points on a circle (defined by equal distance $r$ from a center point $c$), these points cannot be collinear. This is important because it provides a fundamental property of geometric objects and their spatial relationships, which is crucial in various mathematical and computational geometry contexts.

### Dependencies
* `VECTOR_SUB_EQ`
* `DOT_EQ_0`
* `COLLINEAR_3`
* `DOT_CAUCHY_SCHWARZ_EQUAL`
* `DOT_2`
* `dist`
* `NORM_EQ_SQUARE`
* `CART_EQ`
* `DIMINDEX_2`
* `FORALL_2`
* `VECTOR_SUB_COMPONENT`
* `REAL_RING`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles real numbers, vectors, and geometric properties. The main challenge will be ensuring that the ported version correctly captures the geometric intuition and the specific properties of $\mathbb{R}^2$ used in the original proof. Additionally, the use of `CONV_TAC REAL_RING` for concluding the proof may need to be adapted, as different proof assistants have different mechanisms for handling real arithmetic and geometric deductions.

---

## PASCAL_AFFINE_CIRCLE

### Name of formal statement
PASCAL_AFFINE_CIRCLE

### Type of the formal statement
Theorem

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
For all points `c`, `x1`, `x2`, `x3`, `x4`, `x5`, `x6`, `x7`, `x8`, `x9` in the real plane, if the following conditions hold:
- `x1`, `x2`, `x3`, `x4`, `x5`, `x6` are pairwise distinct,
- `c` is at distance `r` from each of `x1`, `x2`, `x3`, `x4`, `x5`, `x6`,
- `x1`, `x9`, `x5` are collinear,
- `x1`, `x8`, `x6` are collinear,
- `x2`, `x9`, `x4` are collinear,
- `x2`, `x7`, `x6` are collinear,
- `x3`, `x8`, `x4` are collinear,
- `x3`, `x7`, `x5` are collinear,
then `x7`, `x8`, `x9` are collinear.

### Informal sketch
The proof of `PASCAL_AFFINE_CIRCLE` involves several key steps:
* Applying the `PASCAL_AFFINE` theorem to a specific set defined by `{x:real^2 | dist(c,x) = r}`,
* Using `GEN_TAC` and `MP_TAC` to set up the proof structure,
* Employing `MATCH_MP_TAC` with `MONO_FORALL` and `COLLINEAR_NOT_COCIRCULAR` to establish collinearity,
* Applying `REWRITE_TAC` with various theorems (`PAIRWISE`, `ALL`, `IN_ELIM_THM`, `IMP_IMP`, `affine_conic`, `dist`, `NORM_EQ_SQUARE`) to simplify and manipulate the expressions,
* Using `ASM_CASES_TAC` to consider cases based on the value of `r`,
* Finally, using `REAL_ARITH_TAC` to perform real arithmetic and conclude the proof.

### Mathematical insight
This theorem is related to Pascal's theorem in projective geometry, which states that if six points lie on a conic section, then the intersection points of the lines formed by these points, when taken three at a time, are collinear. Here, the `PASCAL_AFFINE_CIRCLE` theorem provides an affine version of this result, focusing on a circle as the conic section. The proof leverages the properties of circles, distance, and collinearity to establish the desired conclusion.

### Dependencies
* Theorems:
  + `PASCAL_AFFINE`
  + `COLLINEAR_NOT_COCIRCULAR`
  + `affine_conic`
  + `dist`
  + `NORM_EQ_SQUARE`
* Definitions:
  + `PAIRWISE`
  + `ALL`
  + `IN_ELIM_THM`
  + `IMP_IMP`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to the handling of:
- Quantifiers and their scope
- The `PAIRWISE` and `COLLINEAR` predicates
- The use of `REWRITE_TAC` and `GEN_REWRITE_TAC` for simplification
- The application of `MATCH_MP_TAC` and `MONO_FORALL` for establishing the main result
- The case analysis based on the value of `r` using `ASM_CASES_TAC`
- The final arithmetic manipulations using `REAL_ARITH_TAC`

---

